import OAI.Analysis.KadisonSimilarity.Derivation.GrothendieckUltrapower
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialSymmetryDilation

namespace OAI

/-! A four-by-four matrix corner supplies unitary norm-attaining tests for
an arbitrary bounded linear map without an additional convexity theorem. -/

noncomputable section
namespace KadisonSimilarity
open HochschildMatrixDilation Filter
open scoped ComplexOrder Topology

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Extract an entry with its actual C-star matrix norm bound. -/
def grothendieckEntry (i j : Fin 2) : Mat A →L[ℂ] A :=
  ({ toFun := fun X => X i j
     map_add' := fun X Y => rfl
     map_smul' := fun c X => rfl } : Mat A →ₗ[ℂ] A).mkContinuous 1
    (fun X => by
      change ‖X i j‖ ≤ 1 * ‖X‖
      simpa only [one_mul] using (CStarMatrix.norm_entry_le_norm (M := X) (i := i) (j := j)))

/-- The original map applied to the distinguished off-diagonal entry. -/
def grothendieckMatrixMap (T : A →L[ℂ] H) : Mat (Mat A) →L[ℂ] H :=
  T.comp ((grothendieckEntry 0 1).comp (grothendieckEntry 0 1))

omit [Nontrivial A] in
@[simp] theorem grothendieckMatrixMap_apply (T : A →L[ℂ] H) (X : Mat (Mat A)) :
    grothendieckMatrixMap T X = T (X 0 1 0 1) := rfl

omit [Nontrivial A] in
theorem grothendieckMatrixMap_norm_le (T : A →L[ℂ] H) :
    ‖grothendieckMatrixMap T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro X
  change ‖T (X 0 1 0 1)‖ ≤ ‖T‖ * ‖X‖
  exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    ((CStarMatrix.norm_entry_le_norm (M := X 0 1) (i := 0) (j := 1)).trans
      (CStarMatrix.norm_entry_le_norm (M := X) (i := 0) (j := 1))) (norm_nonneg T))

omit [Nontrivial A] in
/-- A norm-one map has norm-attaining unitary tests in its matrix extension. -/
theorem grothendieckMatrixMap_approximateUnitary (T : A →L[ℂ] H) (hT : ‖T‖ = 1) :
    ∃ u : ℕ → unitary (Mat (Mat A)),
      Tendsto (fun n => ‖grothendieckMatrixMap T (u n : Mat (Mat A))‖) atTop (𝓝 1) := by
  have hx : ∀ n : ℕ, ∃ a : A, ‖a‖ < 1 ∧ 1 - 1 / ((n : ℝ) + 1) < ‖T a‖ := by
    intro n
    apply T.exists_lt_apply_of_lt_opNorm
    rw [hT]
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose a ha hTa using hx
  let u n := contractionSymmetryUnitary (a n) (ha n).le
  refine ⟨u, ?_⟩
  have heval (n : ℕ) : grothendieckMatrixMap T (u n : Mat (Mat A)) = T (a n) := by
    rw [grothendieckMatrixMap_apply, contractionSymmetryUnitary_entry]
  simp only [heval]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 1) from by
      simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    tendsto_const_nhds (fun n => (hTa n).le)
  intro n
  exact (T.le_opNorm _).trans (by rw [hT, one_mul]; exact (ha n).le)

/-- The two diagonal corner maps used for the two states. -/
def grothendieckCorner00 : A →ₗ[ℂ] Mat (Mat A) where
  toFun a := diag (diag a 0) 0
  map_add' a b := by simp only [← diag_add, add_zero]
  map_smul' c a := by simp only [← diag_smul, smul_zero, RingHom.id_apply]

def grothendieckCorner11 : A →ₗ[ℂ] Mat (Mat A) where
  toFun a := diag 0 (diag 0 a)
  map_add' a b := by simp only [← diag_add, add_zero]
  map_smul' c a := by simp only [← diag_smul, smul_zero, RingHom.id_apply]

/-- The distinguished off-diagonal corner. -/
def grothendieckOffDiagonal (a : A) : Mat (Mat A) := offdiag (offdiag a 0) 0

omit [Nontrivial A] in
@[simp] theorem grothendieckOffDiagonal_entry (a : A) :
    grothendieckOffDiagonal a 0 1 0 1 = a := rfl

lemma grothendieck_diag_nonneg {D : Type*} [CStarAlgebra D] [PartialOrder D]
    [StarOrderedRing D] {a b : D} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ diag a b := by
  obtain ⟨c, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  obtain ⟨d, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hb
  rw [← diag_mul, ← star_diag]
  exact star_mul_self_nonneg _

omit [Nontrivial A] in
theorem grothendieckCorner00_nonneg {a : A} (ha : 0 ≤ a) :
    0 ≤ grothendieckCorner00 a :=
  grothendieck_diag_nonneg (grothendieck_diag_nonneg ha le_rfl) le_rfl

omit [Nontrivial A] in
theorem grothendieckCorner11_nonneg {a : A} (ha : 0 ≤ a) :
    0 ≤ grothendieckCorner11 a :=
  grothendieck_diag_nonneg le_rfl (grothendieck_diag_nonneg le_rfl ha)

theorem grothendieckCorner00_one_norm : ‖grothendieckCorner00 (1 : A)‖ ≤ 1 := by
  exact (norm_diag_le _ _).trans (max_le ((norm_diag_le _ _).trans (by simp)) (by simp))

theorem grothendieckCorner11_one_norm : ‖grothendieckCorner11 (1 : A)‖ ≤ 1 := by
  exact (norm_diag_le _ _).trans (max_le (by simp) ((norm_diag_le _ _).trans (by simp)))

omit [Nontrivial A] in
@[simp] theorem grothendieckOffDiagonal_star_mul (a : A) :
    star (grothendieckOffDiagonal a) * grothendieckOffDiagonal a =
      grothendieckCorner11 (star a * a) := by
  simp [grothendieckOffDiagonal, grothendieckCorner11, star_offdiag, offdiag_mul]

omit [Nontrivial A] in
@[simp] theorem grothendieckOffDiagonal_mul_star (a : A) :
    grothendieckOffDiagonal a * star (grothendieckOffDiagonal a) =
      grothendieckCorner00 (a * star a) := by
  simp [grothendieckOffDiagonal, grothendieckCorner00, star_offdiag, offdiag_mul]

/-- Restrict the first matrix state to its supporting corner. -/
def grothendieckState11 (f : Mat (Mat A) →ₚ[ℂ] ℂ) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (f.toLinearMap.comp grothendieckCorner11)
    (fun _ ha => f.map_nonneg (grothendieckCorner11_nonneg ha))

def grothendieckState00 (f : Mat (Mat A) →ₚ[ℂ] ℂ) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (f.toLinearMap.comp grothendieckCorner00)
    (fun _ ha => f.map_nonneg (grothendieckCorner00_nonneg ha))

omit [Nontrivial A] in
@[simp] theorem grothendieckState11_apply (f : Mat (Mat A) →ₚ[ℂ] ℂ) (a : A) :
    grothendieckState11 f a = f (grothendieckCorner11 a) := rfl

omit [Nontrivial A] in
@[simp] theorem grothendieckState00_apply (f : Mat (Mat A) →ₚ[ℂ] ℂ) (a : A) :
    grothendieckState00 f a = f (grothendieckCorner00 a) := rfl

lemma grothendieckState11_mass (f : Mat (Mat A) →ₚ[ℂ] ℂ) (hf : f 1 = 1) :
    (grothendieckState11 f 1).re ≤ 1 := by
  exact (Complex.re_le_norm _).trans <| (f.norm_apply_le_of_nonneg _
    (grothendieckCorner11_nonneg zero_le_one)).trans (by
      rw [hf, norm_one, one_mul]
      exact grothendieckCorner11_one_norm)

lemma grothendieckState00_mass (f : Mat (Mat A) →ₚ[ℂ] ℂ) (hf : f 1 = 1) :
    (grothendieckState00 f 1).re ≤ 1 := by
  exact (Complex.re_le_norm _).trans <| (f.norm_apply_le_of_nonneg _
    (grothendieckCorner00_nonneg zero_le_one)).trans (by
      rw [hf, norm_one, one_mul]
      exact grothendieckCorner00_one_norm)

/-- The two-state little Grothendieck inequality for a norm-one map. -/
theorem normOne_grothendieck (T : A →L[ℂ] H) (hT : ‖T‖ = 1) :
    ∃ f g : A →ₚ[ℂ] ℂ, (f 1).re ≤ 1 ∧ (g 1).re ≤ 1 ∧
      ∀ a, ‖T a‖ ^ 2 ≤ (f (star a * a)).re + (g (a * star a)).re := by
  obtain ⟨u, hu⟩ := grothendieckMatrixMap_approximateUnitary T hT
  obtain ⟨f, g, hf, hg, hfg⟩ := approximateUnitary_grothendieck
    (grothendieckMatrixMap T) ((grothendieckMatrixMap_norm_le T).trans hT.le) u hu
  refine ⟨grothendieckState11 f, grothendieckState00 g,
    grothendieckState11_mass f hf, grothendieckState00_mass g hg, fun a => ?_⟩
  simpa only [grothendieckMatrixMap_apply, grothendieckOffDiagonal_entry,
    grothendieckOffDiagonal_star_mul, grothendieckOffDiagonal_mul_star,
    grothendieckState11_apply, grothendieckState00_apply] using hfg (grothendieckOffDiagonal a)

/-- Homogeneity gives the published inequality with its exact operator-norm factor. -/
theorem littleGrothendieck_nontrivial : LittleGrothendieckInput A H := by
  intro T
  by_cases hT : T = 0
  · subst T
    exact ⟨0, 0, by simp, by simp, by simp⟩
  have hnorm : 0 < ‖T‖ := norm_pos_iff.mpr hT
  let S : A →L[ℂ] H := ‖T‖⁻¹ • T
  have hS : ‖S‖ = 1 := by
    change ‖‖T‖⁻¹ • T‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnorm.le), inv_mul_cancel₀ hnorm.ne']
  obtain ⟨f, g, hf, hg, hfg⟩ := normOne_grothendieck S hS
  refine ⟨f, g, hf, hg, fun a => ?_⟩
  have h := hfg a
  change ‖‖T‖⁻¹ • T a‖ ^ 2 ≤ _ at h
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnorm.le), mul_pow] at h
  have hc : 0 < ‖T‖ ^ 2 := sq_pos_of_pos hnorm
  have hmul := mul_le_mul_of_nonneg_left h hc.le
  simpa only [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hnorm.ne', one_pow, one_mul] using hmul

/-- Haagerup's two-state bound, including the zero algebra. -/
theorem littleGrothendieck_proved {D E : Type*} [CStarAlgebra D] [PartialOrder D]
    [StarOrderedRing D] [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    LittleGrothendieckInput D E := by
  cases subsingleton_or_nontrivial D with
  | inl h =>
    let := h
    intro T
    refine ⟨0, 0, by simp, by simp, fun a => ?_⟩
    have ha : a = 0 := Subsingleton.elim _ _
    simp [ha]
  | inr h =>
    let := h
    exact littleGrothendieck_nontrivial

end KadisonSimilarity

end

end OAI
