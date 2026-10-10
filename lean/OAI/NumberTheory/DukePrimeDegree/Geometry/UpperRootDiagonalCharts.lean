import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootMeasureCovariance

namespace OAI

/-! # The diagonal action on actual full upper-root quotient boxes -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def upperRootTransverseDiagonal {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) (s : UpperRootTransverse n) : UpperRootTransverse n :=
  ⟨s.val * diagonalOneParameter ell hell t, by
    constructor
    · intro p hp
      rw [mul_diagonalOneParameter_entry, s.prop.1 p hp, zero_mul]
    · intro r hr
      rw [mul_diagonalOneParameter_entry]
      exact mul_ne_zero (s.prop.2 r hr) (Real.exp_ne_zero _)⟩

lemma upperRootTransverseDiagonal_add {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t u : ℝ) (s : UpperRootTransverse n) :
    upperRootTransverseDiagonal ell hell (t + u) s =
      upperRootTransverseDiagonal ell hell u (upperRootTransverseDiagonal ell hell t s) := by
  apply Subtype.ext
  exact congrArg (s.val * ·) (diagonalOneParameter_add ell hell t u) |>.trans
    (mul_assoc _ _ _).symm

lemma upperRootTransverseDiagonal_zero {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (s : UpperRootTransverse n) :
    upperRootTransverseDiagonal ell hell 0 s = s := by
  apply Subtype.ext
  simp only [upperRootTransverseDiagonal, diagonalOneParameter_zero, mul_one]

def upperRootTransverseDiagonalHomeomorph {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) : UpperRootTransverse n ≃ₜ UpperRootTransverse n where
  toFun := upperRootTransverseDiagonal ell hell t
  invFun := upperRootTransverseDiagonal ell hell (-t)
  left_inv s := by
    rw [← upperRootTransverseDiagonal_add, add_neg_cancel, upperRootTransverseDiagonal_zero]
  right_inv s := by
    rw [← upperRootTransverseDiagonal_add, neg_add_cancel, upperRootTransverseDiagonal_zero]
  continuous_toFun := (continuous_subtype_val.mul continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.mul continuous_const).subtype_mk _

abbrev upperRootDiagonalCoordinates {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) :
    (UpperRootTransverse n × UpperRootTime n) ≃ₜ
      (UpperRootTransverse n × UpperRootTime n) :=
  (upperRootTransverseDiagonalHomeomorph ell hell t).prodCongr
    ((completeRootChain n).rootDilation ell (-t))

lemma upperRootDiagonalCoordinates_param {n : ℕ} (g : G n) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) (z : UpperRootTransverse n × UpperRootTime n) :
    upperRootQuotientParam n g (upperRootDiagonalCoordinates ell hell t z) =
      rightAction (upperRootQuotientParam n g z) (diagonalOneParameter ell hell t) := by
  rw [upperRootQuotientParam_eq_action, upperRootQuotientParam_eq_action]
  change Quotient.mk _ ((g * (z.1.val * diagonalOneParameter ell hell t)) *
    (completeRootChain n).word ((completeRootChain n).rootDilation ell (-t) z.2)) =
      Quotient.mk _ (((g * z.1.val) * (completeRootChain n).word z.2) *
        diagonalOneParameter ell hell t)
  rw [(completeRootChain n).word_rootDilation ell hell (-t), neg_neg,
    diagonalOneParameter_neg]
  congr 1
  group

namespace UpperRootBox
variable {n : ℕ} {g : G n}

def diagonal (B : UpperRootBox n g) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) : UpperRootBox n g := by
  let e := upperRootTransverseDiagonalHomeomorph ell hell t
  let f := (completeRootChain n).rootDilation ell (-t)
  let E := e.prodCongr f
  have hiff (z : UpperRootTransverse n × UpperRootTime n) :
      z ∈ B.domain ↔ E z ∈ (e '' B.transverse) ×ˢ (f '' B.time) := by
    change (z.1 ∈ B.transverse ∧ z.2 ∈ B.time) ↔
      (e z.1 ∈ e '' B.transverse ∧ f z.2 ∈ f '' B.time)
    rw [e.injective.mem_set_image, f.injective.mem_set_image]
  let eb := E.subtype hiff
  refine ⟨e '' B.transverse, f '' B.time,
    e.isOpenMap _ B.transverse_open, f.isOpenMap _ B.time_open, ?_⟩
  have H := (rightActionHomeomorph (diagonalOneParameter ell hell t)).isOpenEmbedding.comp
    (B.embedding.comp eb.symm.isOpenEmbedding)
  convert H using 1
  funext z
  have he : E (eb.symm z).val = z.val := congrArg Subtype.val (eb.apply_symm_apply z)
  change upperRootQuotientParam n g z.val =
    rightAction (upperRootQuotientParam n g (eb.symm z).val) (diagonalOneParameter ell hell t)
  rw [← he]
  exact upperRootDiagonalCoordinates_param g ell hell t _

lemma diagonal_domain (B : UpperRootBox n g) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) :
    (B.diagonal ell hell t).domain = upperRootDiagonalCoordinates ell hell t '' B.domain :=
  prod_image_image_eq

theorem diagonal_coordinateMeasure (B : UpperRootBox n g) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) (μ : Measure (X n))
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    (B.diagonal ell hell t).coordinateMeasure μ =
      (B.coordinateMeasure μ).map (upperRootDiagonalCoordinates ell hell t) := by
  let E := upperRootDiagonalCoordinates ell hell t
  let H := rightActionHomeomorph (diagonalOneParameter ell hell t)
  have hμ (S : Set (X n)) : μ (H '' S) = μ S := by
    calc
      μ (H '' S) = (μ.map H) (H '' S) := congrArg (fun ν => ν (H '' S)) hinv.symm
      _ = μ S := by
        rw [H.isOpenEmbedding.measurableEmbedding.map_apply, H.injective.preimage_image]
  ext S hS
  rw [Measure.map_apply E.continuous.measurable hS,
    coordinateMeasure_apply _ μ hS,
    coordinateMeasure_apply _ μ (E.continuous.measurable hS), diagonal_domain]
  rw [← hμ (upperRootQuotientParam n g '' (E ⁻¹' S ∩ B.domain))]
  congr 1
  ext x
  constructor
  · rintro ⟨z, ⟨hzS, w, hw, rfl⟩, rfl⟩
    refine ⟨upperRootQuotientParam n g w, ⟨w, ⟨hzS, hw⟩, rfl⟩, ?_⟩
    exact (upperRootDiagonalCoordinates_param g ell hell t w).symm
  · rintro ⟨_, ⟨w, ⟨hwS, hw⟩, rfl⟩, rfl⟩
    exact ⟨E w, ⟨hwS, ⟨w, hw, rfl⟩⟩, upperRootDiagonalCoordinates_param g ell hell t w⟩

theorem diagonal_conditionalKernel (B : UpperRootBox n g) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      (B.diagonal ell hell t).conditionalKernel μ (upperRootTransverseDiagonal ell hell t s) =
        (B.conditionalKernel μ s).map ((completeRootChain n).rootDilation ell (-t)) := by
  simp only [conditionalKernel, diagonal_coordinateMeasure B ell hell t μ hinv]
  exact condKernel_map_measurableEquiv (B.coordinateMeasure μ)
    (upperRootTransverseDiagonalHomeomorph ell hell t).toMeasurableEquiv
    ((completeRootChain n).rootDilation ell (-t)).toMeasurableEquiv

lemma diagonal_marginal (B : UpperRootBox n g) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) (μ : Measure (X n))
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    ((B.diagonal ell hell t).coordinateMeasure μ).fst =
      (B.coordinateMeasure μ).fst.map (upperRootTransverseDiagonalHomeomorph ell hell t) := by
  rw [B.diagonal_coordinateMeasure ell hell t μ hinv]
  exact fst_map_measurableEquiv (B.coordinateMeasure μ)
    (upperRootTransverseDiagonalHomeomorph ell hell t).toMeasurableEquiv
    ((completeRootChain n).rootDilation ell (-t)).toMeasurableEquiv

end UpperRootBox
end DukePrimeDegree

end

end OAI
