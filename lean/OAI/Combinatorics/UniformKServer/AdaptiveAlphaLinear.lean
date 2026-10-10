import Mathlib
import OAI.Combinatorics.UniformKServer.AdaptiveAlpha
import OAI.Combinatorics.UniformKServer.CoreFiltering

namespace OAI

                                          
section

/-! Exact affine old-state alpha coefficients on changing active domains.
 These are computed from the genuine regular/marked improper primitives.
 Their uniform bound is used before, not after, testing refresh events. -/
noncomputable section
namespace UniformKServer.ProportionParameters
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

def coefficient (p : Parameters ι) (a : ι → ℝ) : ι → ℝ :=
  match p.kind with
  | .regular => AlphaLinear.coefficient (fun i => Denominators.regular (p.h i))
      (fun _ => 0) (eta p) (p.C*p.ell) a
  | .marked o u => AlphaLinear.coefficient
      (fun i => if i=o then Denominators.marked u else Denominators.regular (p.h i))
      (fun i => if i=o then 1 else 0) (eta p) (p.C*p.ell) a
  | .singleton _ => fun _ => 0

theorem affine {p : Parameters ι} (hp : valid p) (B a : ι → ℝ)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1) :
    potential p B a=∑ i, coefficient p a i*B i := by
  have hk := hp.2.2.2.2
  cases he : p.kind with
  | regular =>
    simp only [he] at hk
    have hf := AlphaLinear.potential_affine (fun i => Denominators.regular (p.h i))
      (fun _ => 0) (eta p) (p.C*p.ell) B a (by intro i; simp) ha
      (fun i => AlphaStability.regular_integrable (hk.1 i) 1 0)
      (fun i => AlphaStability.regular_integrable (hk.1 i) 0 1)
    simpa only [potential,component,coefficient,he,AlphaLinear.potential,
      AlphaTracker.regularG,eta] using hf
  | marked o u =>
    simp only [he] at hk
    let D (i : ι) := if i=o then Denominators.marked u else Denominators.regular (p.h i)
    let base (i : ι) : ℝ := if i=o then 1 else 0
    have hf := AlphaLinear.potential_affine D base (eta p) (p.C*p.ell) B a
      (by intro i; dsimp [base]; split_ifs <;> simp) ha
      (by intro i; dsimp [D]; split_ifs with hi
          · exact AlphaStability.marked_integrable hk.1 hk.2.1 1 0
          · exact AlphaStability.regular_integrable (hk.2.2.2.1 i hi) 1 0)
      (by intro i; dsimp [D]; split_ifs with hi
          · exact AlphaStability.marked_integrable hk.1 hk.2.1 0 1
          · exact AlphaStability.regular_integrable (hk.2.2.2.1 i hi) 0 1)
    have hpot : potential p B a=AlphaLinear.potential D base (eta p) (p.C*p.ell) B a := by
      apply sum_congr rfl
      intro i _
      simp only [component,he,AlphaTracker.markedG,D,base,eta]
      have hF : AlphaTracker.markedF o u p.h i = D i := by
        funext x
        simp only [AlphaTracker.markedF,D]
        split_ifs <;> rfl
      rw [hF]
    rw [hpot,hf]
    simp only [coefficient,he]
    rfl
  | singleton o => simp [potential,component,coefficient,he]

end UniformKServer.ProportionParameters

namespace UniformKServer.AdaptiveAlphaLinear
open Finset AdaptiveAlpha
open scoped Classical
variable {ι : Type*} [Fintype ι]

def coefficient (p : Config ι) (a : ι → ℝ) : ι → ℝ :=
  DomainTransport.extend p.active (ProportionParameters.coefficient p.param (fun i => a i))

theorem affine {p : Config ι} (hp : valid p) (B a : ι → ℝ)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1) :
    potential p B a=∑ i, coefficient p a i*B i := by
  rw [potential,ProportionParameters.affine hp.2 _ _ (fun i => ha i)]
  rw [←DomainTransport.extend_sum p.active (fun i =>
    ProportionParameters.coefficient p.param (fun j => a j) i*B i)]
  apply sum_congr rfl
  intro i _
  unfold coefficient DomainTransport.extend
  split_ifs <;> simp

theorem bound {p : Config ι} (hp : valid p) (a : ι → ℝ)
    (ha : DomainTransport.simplex p.active a) (i : ι) :
    |coefficient p a i| ≤ 15*scale p := by
  have hai (j : ι) : a j ∈ Set.Icc (0:ℝ) 1 :=
    ⟨ha.1 j,by linarith [single_le_sum (s:=univ) (f:=a) (fun l _ => ha.1 l) (mem_univ j),ha.2.2]⟩
  exact AlphaLinear.coefficient_of_lipschitz (fun B => potential p B a) (coefficient p a)
    (15*scale p) (fun B => affine hp B a hai) (fun B B' => input_bound hp B B' a ha) i

variable {Ω R : Type*} [Fintype Ω] [Fintype R]

theorem filtering {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (F G : Setoid Ω) (hGF : ∀ ω v, G.r ω v → F.r ω v)
    (p : Ω → Config ι) (a : Ω → ι → ℝ) (flag : Ω → ι → R → Bool)
    (X : Ω → ι × R → ℝ) (hp : ∀ ω, valid (p ω))
    (ha : ∀ ω i, a ω i ∈ Set.Icc (0:ℝ) 1)
    (hdata : ∀ ω v, F.r ω v → p ω=p v ∧ a ω=a v)
    (hf : ∀ ω v, F.r ω v → ∀ i r, flag ω i r=flag v i r) :
    AdaptiveLedger.expect w (fun ω =>
      potential (p ω) (CoreFiltering.masked flag (AdaptiveLedger.post w G X) ω) (a ω)-
      potential (p ω) (CoreFiltering.masked flag (AdaptiveLedger.post w F X) ω) (a ω))=0 := by
  have hm : ∀ i, ConditionalLaw.measurable F (fun ω => coefficient (p ω) (a ω) i) := by
    intro i ω v h
    obtain ⟨hp',ha'⟩ := hdata ω v h
    dsimp only
    rw [hp',ha']
  simp_rw [affine (hp _) _ _ (ha _)]
  exact CoreFiltering.filtering_held hw F G hGF (fun ω => coefficient (p ω) (a ω)) flag X hm hf

end UniformKServer.AdaptiveAlphaLinear

end


end

end OAI
