import Mathlib
import OAI.Combinatorics.UniformKServer.AlphaLinear
import OAI.Combinatorics.UniformKServer.AdaptiveLedger

namespace OAI

                                    
section

/-! Source §04, filtering with held core flags.  The old-state coefficients
are tested on every step, before selecting any refresh or active-domain event. -/
namespace UniformKServer.CoreFiltering
noncomputable section
open Finset UniformKServer.ConditionalLaw UniformKServer.AdaptiveLedger
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

def masked (flag : Ω → ι → R → Bool) (p : Ω → ι × R → ℝ)
    (ω : Ω) (i : ι) : ℝ := ∑ r, if flag ω i r then p ω (i,r) else 0

def liftCoefficient (a : Ω → ι → ℝ) (flag : Ω → ι → R → Bool)
    (ω : Ω) (ir : ι × R) : ℝ := if flag ω ir.1 ir.2 then a ω ir.1 else 0

omit [Fintype Ω] in
theorem masked_linear (a : Ω → ι → ℝ) (flag : Ω → ι → R → Bool)
    (p : Ω → ι × R → ℝ) (ω : Ω) :
    (∑ i, a ω i*masked flag p ω i) =
      ∑ ir, liftCoefficient a flag ω ir*p ω ir := by
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  rw [masked,mul_sum]
  apply sum_congr rfl
  intro r _
  simp only [liftCoefficient]
  split_ifs <;> ring

omit [Fintype Ω] [Fintype ι] [Fintype R] in
theorem lift_measurable (F : Setoid Ω) (a : Ω → ι → ℝ)
    (flag : Ω → ι → R → Bool)
    (ha : ∀ i, measurable F (fun ω => a ω i))
    (hf : ∀ ω v, F.r ω v → ∀ i r, flag ω i r=flag v i r) :
    ∀ ir, measurable F (fun ω => liftCoefficient a flag ω ir) := by
  intro ir ω v h
  simp only [liftCoefficient, hf ω v h,ha ir.1 ω v h]

omit [Fintype Ω] [Fintype ι] [Fintype R] in
theorem lift_bound (a : Ω → ι → ℝ) (flag : Ω → ι → R → Bool)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ ω i, |a ω i| ≤ C) :
    ∀ ω ir, |liftCoefficient a flag ω ir| ≤ C := by
  intro ω ir
  simp only [liftCoefficient]
  split_ifs
  · exact ha ω ir.1
  · simpa only [abs_zero] using hC

theorem filtering_held {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (F G : Setoid Ω) (hGF : ∀ ω v, G.r ω v → F.r ω v)
    (a : Ω → ι → ℝ) (flag : Ω → ι → R → Bool) (X : Ω → ι × R → ℝ)
    (ha : ∀ i, measurable F (fun ω => a ω i))
    (hf : ∀ ω v, F.r ω v → ∀ i r, flag ω i r=flag v i r) :
    expect w (fun ω => (∑ i, a ω i*masked flag (post w G X) ω i)-
      (∑ i, a ω i*masked flag (post w F X) ω i)) = 0 := by
  have he : (fun ω => (∑ i, a ω i*masked flag (post w G X) ω i)-
      (∑ i, a ω i*masked flag (post w F X) ω i)) =
      increment w F G (liftCoefficient a flag) X := by
    funext ω
    rw [masked_linear,masked_linear,←sum_sub_distrib]
    apply sum_congr rfl
    intro ir _
    ring
  rw [he]
  exact filtering_zero hw F G hGF _ X (lift_measurable F a flag ha hf)

/-- A whole alpha-potential filtering identity for actual primitives, not
an assumed martingale interface. Shapes and parameters may depend on history. -/
theorem regular_filtering [DecidableEq ι] {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (F G : Setoid Ω) (hGF : ∀ ω v, G.r ω v → F.r ω v)
    (h η a : Ω → ι → ℝ) (scale : Ω → ℝ) (flag : Ω → ι → R → Bool)
    (X : Ω → ι × R → ℝ)
    (hh : ∀ ω i, 1 ≤ h ω i) (ha : ∀ ω i, a ω i ∈ Set.Icc (0:ℝ) 1)
    (hdata : ∀ ω v, F.r ω v → h ω=h v ∧ η ω=η v ∧ a ω=a v ∧ scale ω=scale v)
    (hf : ∀ ω v, F.r ω v → ∀ i r, flag ω i r=flag v i r) :
    expect w (fun ω =>
      AlphaLinear.potential (fun i => Denominators.regular (h ω i)) (fun _ => 0) (η ω)
        (scale ω) (masked flag (post w G X) ω) (a ω)-
      AlphaLinear.potential (fun i => Denominators.regular (h ω i)) (fun _ => 0) (η ω)
        (scale ω) (masked flag (post w F X) ω) (a ω)) = 0 := by
  let c (ω : Ω) := AlphaLinear.coefficient (fun i => Denominators.regular (h ω i))
    (fun _ => 0) (η ω) (scale ω) (a ω)
  have hc : ∀ i, measurable F (fun ω => c ω i) := by
    intro i ω v hωv
    obtain ⟨hh',hη',ha',hs'⟩ := hdata ω v hωv
    simp only [c,hh',hη',ha',hs']
  have he (ω : Ω) (B : ι → ℝ) :
      AlphaLinear.potential (fun i => Denominators.regular (h ω i)) (fun _ => 0) (η ω)
        (scale ω) B (a ω) = ∑ i, c ω i*B i := by
    exact AlphaLinear.potential_affine _ _ _ _ _ _ (by intro i; simp)
      (ha ω) (fun i => AlphaStability.regular_integrable (hh ω i) 1 0)
      (fun i => AlphaStability.regular_integrable (hh ω i) 0 1)
  simp_rw [he]
  exact filtering_held hw F G hGF c flag X hc hf

end
end UniformKServer.CoreFiltering

end

end OAI
