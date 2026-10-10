import Mathlib
import OAI.Analysis.HardSphere.FormDomain.RawCutoffGradientIntegral
import OAI.Analysis.HardSphere.FormDomain.RmsPermuteFunBosonic

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere

lemma iterated_insertion (C : ℝ) (_hC : 0<C)
    (hins : ∀ (n : ℕ) (L : Length) (r : ℝ), 0<r →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
      ∀ u : Jet n L, u∈dirichletDomain n L r →
      ∃ v : Jet (n+1) L, v∈dirichletDomain (n+1) L r ∧
        ‖v.1‖=‖u.1‖ ∧ energy v≤energy u+(C*(n:ℝ)*r/L.val^3)*‖u.1‖^2)
    (n m : ℕ) (L : Length) {r : ℝ} (hr : 0<r)
    (hs : ((n+m:ℕ):ℝ)*(2*Real.pi*r)^3≤L.val^3/2)
    (u : Jet n L) (hu : u∈dirichletDomain n L r) :
    ∃ v : Jet (n+m) L, v∈dirichletDomain (n+m) L r ∧ ‖v.1‖=‖u.1‖ ∧
      energy v≤energy u+(∑ j∈Finset.range m,C*((n+j:ℕ):ℝ)*r/L.val^3)*‖u.1‖^2 := by
  induction m with
  | zero => exact ⟨u,hu,rfl,by simp⟩
  | succ m ih =>
    have hs' : ((n+m:ℕ):ℝ)*(2*Real.pi*r)^3≤L.val^3/2 := by
      exact (mul_le_mul_of_nonneg_right
        (show ((n+m:ℕ):ℝ)≤((n+(m+1):ℕ):ℝ) by exact_mod_cast Nat.le_succ (n+m))
        (by positivity)).trans hs
    obtain ⟨v,hv,hn,he⟩ := ih hs'
    obtain ⟨w,hw,hnw,hew⟩ := hins (n+m) L r hr hs' v hv
    refine ⟨w,hw,hnw.trans hn,?_⟩
    rw [hn] at hew
    rw [Finset.sum_range_succ]
    nlinarith

lemma ground_energy_removal : ∃ C : ℝ, 0<C ∧
    ∀ (n m : ℕ) (L : Length) (r : ℝ), 0<r →
    ((n+m:ℕ):ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ u : Jet (n+m) L, IsGroundVector (n+m) L r u →
    ∀ v : Jet n L, v∈dirichletDomain n L r →
      (energy u-C*(m:ℝ)*((n+m:ℕ):ℝ)*r/L.val^3)*‖v.1‖^2≤energy v := by
  obtain ⟨C,hC,hins⟩ := uniform_insertion
  refine ⟨C,hC,fun n m L r hr hs u hu v hv ↦ ?_⟩
  have hL : 0<L.val := L.property
  obtain ⟨w,hw,hn,he⟩ := iterated_insertion C hC hins n m L hr hs v hv
  have hmin := hu.rayleigh_all w hw
  rw [hn] at hmin
  have hsum : (∑ j∈Finset.range m,C*((n+j:ℕ):ℝ)*r/L.val^3)≤
      C*(m:ℝ)*((n+m:ℕ):ℝ)*r/L.val^3 := by
    calc
      _ ≤ ∑ _j∈Finset.range m,C*((n+m:ℕ):ℝ)*r/L.val^3 := by
        apply Finset.sum_le_sum
        intro j hj
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hr.le
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact_mod_cast Nat.add_le_add_left (Nat.le_of_lt (Finset.mem_range.mp hj)) n
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring
  have := mul_le_mul_of_nonneg_right hsum (sq_nonneg ‖v.1‖)
  nlinarith
end HardSphere

end

end OAI
