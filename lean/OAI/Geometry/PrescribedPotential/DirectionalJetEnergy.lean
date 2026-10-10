import Mathlib
import OAI.Geometry.PrescribedPotential.JetNormEquivalence
import OAI.Geometry.PrescribedPotential.RealJetEnergy

namespace OAI

/-! Directional Jet Energy. -/

section

 
noncomputable section
open Set Filter Topology Finset Module
open scoped ContDiff
namespace HigherJet
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι]

def jetFamily (e : ι → E) (m : ℕ) (u : E → F) (σ : Fin m → ι) : E → F :=
  word (List.ofFn (fun i => e (σ i))) u

def jetEnergy (e : ι → E) (m : ℕ) (u : E → F) : E → ℝ :=
  familyEnergy (jetFamily e m u)

omit [Fintype ι] in
lemma jetFamily_smoothOn {U : Set E} (hU : IsOpen U) {u : E → F}
    (hu : ContDiffOn ℝ ∞ u U) (e : ι → E) (m : ℕ) (σ : Fin m → ι) :
    ContDiffOn ℝ ∞ (jetFamily e m u σ) U := word_smoothOn hU hu _

lemma jetEnergy_smoothOn {U : Set E} (hU : IsOpen U) {u : E → F}
    (hu : ContDiffOn ℝ ∞ u U) (e : ι → E) (m : ℕ) :
    ContDiffOn ℝ ∞ (jetEnergy e m u) U := familyEnergy_smoothOn (jetFamily_smoothOn hU hu e m)

lemma jetEnergy_nonneg (e : ι → E) (m : ℕ) (u : E → F) (x : E) :
    0 ≤ jetEnergy e m u x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma jetArray_energy {U : Set E} (hU : IsOpen U) {u : E → F}
    (hu : ContDiffOn ℝ ∞ u U) (e : ι → E) (m : ℕ) {x : E} (hx : x ∈ U) :
    ‖jetArray e m (iteratedFDeriv ℝ m u x)‖^2 = jetEnergy e m u x := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  exact congrArg norm (word_ofFn_eq hU hu m (fun i => e (σ i)) hx).symm

lemma norm_iteratedFDeriv_le_jetEnergy [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : Basis ι ℝ E) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set E), IsOpen U → ∀ u : E → F, ContDiffOn ℝ ∞ u U →
      ∀ x ∈ U, ‖iteratedFDeriv ℝ m u x‖ ≤ C*Real.sqrt (jetEnergy e m u x) := by
  obtain ⟨C,hC,hb⟩ := jetArray_norm_control (F := F) e m
  refine ⟨C,hC,fun U hU u hu x hx => ?_⟩
  have he : Real.sqrt (jetEnergy e m u x) = ‖jetArray e m (iteratedFDeriv ℝ m u x)‖ := by
    rw [← jetArray_energy hU hu e m hx,Real.sqrt_sq (norm_nonneg _)]
  rw [he]
  exact hb _

lemma family_laplace_norm_bound {κ : Type*} [Fintype κ]
    {v : ι → E} {f : κ → E → F} {x : E} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ j, ‖frameLaplace v (f j) x‖ ≤ C) :
    Real.sqrt (∑ j, ‖frameLaplace v (f j) x‖^2) ≤ (Fintype.card κ+1)*C := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  calc
    _ ≤ ∑ _j : κ, C^2 := Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hb j) 2)
    _ = (Fintype.card κ : ℝ)*C^2 := by simp
    _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg C) (sq_nonneg (Fintype.card κ : ℝ))]
end HigherJet

end
end

end OAI
