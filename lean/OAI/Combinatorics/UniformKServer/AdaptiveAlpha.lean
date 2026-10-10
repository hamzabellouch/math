import Mathlib
import OAI.Combinatorics.UniformKServer.Epochs
import OAI.Combinatorics.UniformKServer.ProportionParameters
import OAI.Combinatorics.UniformKServer.DomainTransport

namespace OAI

                                    
section

/-! The two compact minimizations and intermediate common-core transport of
 companion §04, on a fixed child set. All movement estimates use the actual
 weighted L1 distance, including changing active domains and singleton states. -/
noncomputable section
namespace UniformKServer.AdaptiveAlpha
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

structure Config (ι : Type*) where
  active : Finset ι
  param : ProportionParameters.Parameters active

def valid (p : Config ι) : Prop := p.active.Nonempty ∧ ProportionParameters.valid p.param

def potential (p : Config ι) (B a : ι → ℝ) : ℝ :=
  ProportionParameters.potential p.param (fun i => B i) (fun i => a i)

def eta (p : Config ι) (i : ι) : ℝ := DomainTransport.extend p.active
  (ProportionParameters.eta p.param) i

def scale (p : Config ι) : ℝ := p.param.C*p.param.ell

omit [Fintype ι] in
theorem scale_nonneg {p : Config ι} (hp : valid p) : 0 ≤ scale p :=
  mul_nonneg (ProportionParameters.C_pos hp.2).le hp.2.1.le

omit [Fintype ι] in
theorem potential_zero (p : Config ι) (a : ι → ℝ) : potential p (fun _ => 0) a=0 :=
  ProportionParameters.potential_zero _ _

theorem update {p : Config ι} (hp : valid p) (B a₀ : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hs : DomainTransport.Supported p.active B)
    (ha₀ : DomainTransport.simplex p.active a₀) :
    ∃ a, DomainTransport.simplex p.active a ∧
      (∀ i, (∑ j, B j)*a i ≤ (1+eta p i)*B i) ∧
      (∑ j, B j)*SimplexTracker.movement a a₀ ≤ potential p B a₀-potential p B a := by
  obtain ⟨a,ha,hf,hm⟩ := ProportionParameters.update hp.2 (fun i => B i)
    (fun i => a₀ i) (fun i => hB i) (DomainTransport.restrict_simplex ha₀)
  refine ⟨DomainTransport.extend p.active a,DomainTransport.extend_simplex ha,?_,?_⟩
  · intro i
    by_cases hi : i ∈ p.active
    · have h := hf ⟨i,hi⟩
      rw [DomainTransport.sum_restrict hs] at h
      simpa only [eta,DomainTransport.extend,hi,dite_true] using h
    · rw [DomainTransport.extend_supported p.active a i hi,hs i hi,mul_zero,mul_zero]
  · rw [DomainTransport.sum_restrict hs] at hm
    rw [DomainTransport.movement_extend p.active a ha₀.2.1]
    have he : (fun i : p.active => DomainTransport.extend p.active a i)=a := by
      funext i
      exact DomainTransport.extend_apply _ _ _
    simpa only [potential,he] using hm

theorem input_bound {p : Config ι} (hp : valid p) (B B' a : ι → ℝ)
    (ha : DomainTransport.simplex p.active a) :
    |potential p B a-potential p B' a| ≤ 15*scale p*(∑ i, |B i-B' i|) := by
  have h := ProportionParameters.input_bound hp.2 (fun i => B i) (fun i => B' i)
    (fun i => a i) (DomainTransport.restrict_simplex ha)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) (scale_nonneg hp)))
  rw [sum_coe_sort p.active (fun i : ι => |B i-B' i|)]
  exact sum_le_univ_sum_of_nonneg (fun i => abs_nonneg (B i-B' i))

theorem diameter {I J : Finset ι} {a b : ι → ℝ}
    (ha : DomainTransport.simplex I a) (hb : DomainTransport.simplex J b) :
    SimplexTracker.movement a b ≤ 2 := by
  calc
    _ ≤ ∑ i, (a i+b i) := sum_le_sum fun i _ =>
      (abs_sub _ _).trans (by rw [abs_of_nonneg (ha.1 i),abs_of_nonneg (hb.1 i)])
    _ = 2 := by rw [sum_add_distrib,ha.2.2,hb.2.2]; norm_num

theorem triangle (a b c : ι → ℝ) :
    SimplexTracker.movement a c ≤ SimplexTracker.movement a b+SimplexTracker.movement b c := by
  unfold SimplexTracker.movement
  rw [←sum_add_distrib]
  exact sum_le_sum fun i _ => abs_sub_le (a i) (b i) (c i)

theorem movement_nonneg (a b : ι → ℝ) : 0 ≤ SimplexTracker.movement a b :=
  sum_nonneg fun _ _ => abs_nonneg _

/-- A slightly sharper (two rather than four) weight-change error is available
 by applying the diameter bound after transport. In particular it proves the
 source's four-delta inequality, with no positive-weight division. -/
theorem weight_comparison {I J K : Finset ι} {old prep moved new : ι → ℝ}
    {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (hold : DomainTransport.simplex I old) (hmoved : DomainTransport.simplex J moved)
    (hnew : DomainTransport.simplex K new)
    (hfree : S*SimplexTracker.movement moved prep=0) :
    T*SimplexTracker.movement new old ≤
      S*SimplexTracker.movement prep old+T*SimplexTracker.movement new moved+4*(T-S) := by
  have ht := mul_le_mul_of_nonneg_left (triangle new moved old) (hS.trans hST)
  have hs := mul_le_mul_of_nonneg_left (triangle moved prep old) hS
  have hd := mul_le_mul_of_nonneg_left (diameter hmoved hold) (sub_nonneg.mpr hST)
  rw [mul_add,hfree,zero_add] at hs
  have hn := movement_nonneg new old
  have hdn := diameter hnew hold
  nlinarith

/-- The first minimizer and genuine (possibly zero-weight) domain transport.
 Feasibility is proved before changing domains, not imposed on the old state. -/
theorem prepare {p q : Config ι} (hp : valid p) (hq : valid q)
    (B a₀ : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hpB : DomainTransport.Supported p.active B) (hqB : DomainTransport.Supported q.active B)
    (ha₀ : DomainTransport.simplex p.active a₀) :
    ∃ a b, DomainTransport.simplex p.active a ∧ DomainTransport.simplex q.active b ∧
      (∀ i, (∑ j, B j)*a i ≤ (1+eta p i)*B i) ∧
      (∑ j, B j)*SimplexTracker.movement a a₀ ≤ potential p B a₀-potential p B a ∧
      (∑ j, B j)*SimplexTracker.movement b a=0 ∧
      potential p B b=potential p B a ∧
      (∀ i, (∑ j, B j)*b i ≤ (1+eta p i)*B i) := by
  obtain ⟨a,ha,hf,hm⟩ := update hp B a₀ hB hpB ha₀
  have hS : 0 ≤ ∑ j, B j := sum_nonneg fun i _ => hB i
  rcases hS.eq_or_lt with hz | hpos
  · have hBzero : B=fun _ => 0 := by
      funext i
      have hi := single_le_sum (s:=univ) (f:=B) (fun j _ => hB j) (mem_univ i)
      exact le_antisymm (by linarith) (hB i)
    obtain ⟨b,hb⟩ := DomainTransport.exists_simplex hq.1
    refine ⟨a,b,ha,hb,hf,hm,?_,?_,?_⟩
    · rw [←hz,zero_mul]
    · rw [hBzero,potential_zero,potential_zero]
    · intro i; rw [←hz,zero_mul,hBzero]; simp
  · have hs : DomainTransport.Supported q.active a := by
      intro i hi
      have h := hf i
      rw [hqB i hi,mul_zero] at h
      exact le_antisymm (by nlinarith : a i ≤ 0) (ha.1 i)
    refine ⟨a,a,ha,⟨ha.1,hs,ha.2.2⟩,hf,hm,?_,rfl,hf⟩
    simp [SimplexTracker.movement]

/-- Complete deterministic minimizing part of one nonswitch step. `jump` is
 not a hypothesis: it is the actual prepared parameter-potential difference,
 available next for componentwise size-charge estimates. -/
theorem step {p q : Config ι} (hp : valid p) (hq : valid q)
    (Bstar Bnew a₀ : ι → ℝ) (hB : ∀ i, 0 ≤ Bstar i) (hBn : ∀ i, 0 ≤ Bnew i)
    (hST : (∑ i, Bstar i) ≤ ∑ i, Bnew i)
    (hpB : DomainTransport.Supported p.active Bstar)
    (hqB : DomainTransport.Supported q.active Bstar)
    (hqN : DomainTransport.Supported q.active Bnew)
    (ha₀ : DomainTransport.simplex p.active a₀) :
    ∃ a b, DomainTransport.simplex q.active a ∧ DomainTransport.simplex q.active b ∧
      (∀ i, (∑ j, Bnew j)*a i ≤ (1+eta q i)*Bnew i) ∧
      (∀ i, (∑ j, Bstar j)*b i ≤ (1+eta p i)*Bstar i) ∧
      (∑ j, Bnew j)*SimplexTracker.movement a a₀ ≤
        potential p Bstar a₀-potential q Bnew a+
        (potential q Bstar b-potential p Bstar b)+
        15*scale q*(∑ i, |Bnew i-Bstar i|)+4*((∑ i, Bnew i)-(∑ i, Bstar i)) := by
  obtain ⟨a₁,b,ha₁,hb,hf,hm,hfree,he,hfb⟩ := prepare hp hq Bstar a₀ hB hpB hqB ha₀
  obtain ⟨a,ha,hn,hmn⟩ := update hq Bnew b hBn hqN hb
  refine ⟨a,b,ha,hb,hn,hfb,?_⟩
  have hc := weight_comparison (sum_nonneg fun i _ => hB i) hST ha₀ hb ha hfree
  have hi := input_bound hq Bnew Bstar b hb
  have hi' := (le_abs_self _).trans hi
  rw [←he] at hm
  linarith

end UniformKServer.AdaptiveAlpha

end


end

end OAI
