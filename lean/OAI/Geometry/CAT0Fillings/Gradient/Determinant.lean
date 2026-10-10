import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.Chart
import OAI.Geometry.CAT0Fillings.Gradient.HilbertAtlas

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator

namespace CAT0Fillings

noncomputable def rawCovector {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (v : Euc n) : Fin n → ℝ :=
  (CFC.sqrt P⁻¹)⁻¹.mulVec (WithLp.ofLp v)

lemma sqrt_inverse_matrix_det_ne_zero {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef) : (CFC.sqrt P⁻¹).det ≠ 0 := by
  have hh := hP.inv.posSemidef.det_sqrt
  rw [hh,RCLike.sqrt_real]
  exact (Real.sqrt_pos.mpr hP.inv.det_pos).ne'

lemma normalize_rawCovector {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef) (v : Euc n) :
    (CFC.sqrt P⁻¹).mulVec (rawCovector P v) = WithLp.ofLp v := by
  rw [rawCovector,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (sqrt_inverse_matrix_det_ne_zero P hP)),Matrix.one_mulVec]

lemma raw_normalizedCovector {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef) (a : Fin n → ℝ) :
    rawCovector P (WithLp.toLp 2 ((CFC.sqrt P⁻¹).mulVec a)) = a := by
  rw [rawCovector,WithLp.ofLp_toLp,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (sqrt_inverse_matrix_det_ne_zero P hP)),Matrix.one_mulVec]

lemma rawCovector_norm {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef) (v : Euc n) :
    Real.sqrt (rawCovector P v ⬝ᵥ P⁻¹.mulVec (rawCovector P v)) = ‖v‖ := by
  rw [dot_mulVec_sqrt P⁻¹ hP.inv.posSemidef,normalize_rawCovector P hP]
  have he : (WithLp.ofLp v) ⬝ᵥ (WithLp.ofLp v) = ‖v‖^2 := by
    rw [←real_inner_self_eq_norm_sq]
    simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
  rw [he,Real.sqrt_sq (norm_nonneg _)]

noncomputable def normalizedDet {n : ℕ} (P : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (R : Fin n → Fin (n+1) → ℝ) (v : Euc (n+1)) : ℝ :=
  Matrix.det (Matrix.vecCons (rawCovector P v) R) / Real.sqrt P.det

lemma normalizedDet_bound {n : ℕ} (P : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hP : P.PosDef) (R : Fin n → Fin (n+1) → ℝ)
    (hR : ∀ i, Real.sqrt (R i ⬝ᵥ P⁻¹.mulVec (R i)) ≤ 1) (v : Euc (n+1)) :
    |normalizedDet P R v| ≤ ‖v‖ := by
  have h := abs_det_le_first_dual_norm (Matrix.vecCons (rawCovector P v) R) P hP hR
  change |Matrix.det (Matrix.vecCons (rawCovector P v) R)| ≤
    Real.sqrt (rawCovector P v ⬝ᵥ P⁻¹.mulVec (rawCovector P v))*Real.sqrt P.det at h
  rw [rawCovector_norm P hP] at h
  rw [normalizedDet,abs_div,abs_of_pos (Real.sqrt_pos.mpr hP.det_pos)]
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hP.det_pos)).mpr h

lemma normalizedDet_bound_prod {n : ℕ} (P : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hP : P.PosDef) (R : Fin n → Fin (n+1) → ℝ) (K : Fin n → ℝ≥0)
    (hR : ∀ i, Real.sqrt (R i ⬝ᵥ P⁻¹.mulVec (R i)) ≤ K i) (v : Euc (n+1)) :
    |normalizedDet P R v| ≤ ‖v‖ * ∏ i, (K i : ℝ) := by
  have h := abs_det_le_prod_dual_norm (Matrix.vecCons (rawCovector P v) R) P hP
  rw [Fin.prod_univ_succ] at h
  simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] at h
  rw [rawCovector_norm P hP] at h
  have hprod := Finset.prod_le_prod₀ (fun i (_ : i ∈ Finset.univ) => Real.sqrt_nonneg
    (R i ⬝ᵥ P⁻¹.mulVec (R i))) (fun i _ => hR i)
  have hh := h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hprod (norm_nonneg v)) (Real.sqrt_nonneg _))
  rw [normalizedDet,abs_div,abs_of_pos (Real.sqrt_pos.mpr hP.det_pos)]
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hP.det_pos)).mpr hh

lemma normalizedDet_sub {n : ℕ} (P : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (R : Fin n → Fin (n+1) → ℝ) (v w : Euc (n+1)) :
    normalizedDet P R (v-w) = normalizedDet P R v-normalizedDet P R w := by
  have hr : rawCovector P (v-w) = rawCovector P v-rawCovector P w := by
    simp [rawCovector,Matrix.mulVec_sub]
  unfold normalizedDet
  rw [hr,←sub_div]
  congr 1
  have he (a : Fin (n+1) → ℝ) : Matrix.vecCons a R =
      Matrix.updateRow (Matrix.vecCons (0 : Fin (n+1) → ℝ) R) 0 a := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [Matrix.updateRow]
  have ha := Matrix.det_updateRow_add (Matrix.vecCons (0 : Fin (n+1) → ℝ) R) 0
    (rawCovector P v) ((-1:ℝ) • rawCovector P w)
  rw [Matrix.det_updateRow_smul (Matrix.vecCons (0 : Fin (n+1) → ℝ) R) 0 (-1:ℝ)
    (rawCovector P w)] at ha
  simpa only [←he,neg_one_smul,sub_eq_add_neg,neg_one_mul] using ha

local instance {n : ℕ} : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _
local instance {n : ℕ} : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

lemma aestronglyMeasurable_normalizedDet {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {n : ℕ} {P : α → Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    {R : α → Fin n → Fin (n+1) → ℝ} {v : α → Euc (n+1)}
    (hP : Measurable P) (hR : AEStronglyMeasurable R μ) (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun x => normalizedDet (P x) (R x) (v x)) μ := by
  have hQ := measurable_matrix_inverse _
    (measurable_matrix_sqrt.comp (measurable_matrix_inverse _ hP))
  have hc : Continuous (fun w : Matrix (Fin (n+1)) (Fin (n+1)) ℝ ×
      (Fin n → Fin (n+1) → ℝ) × Euc (n+1) =>
      Matrix.det (Matrix.vecCons (w.1.mulVec (WithLp.ofLp w.2.2)) w.2.1)) := by
    fun_prop
  have hh := hc.comp_aestronglyMeasurable (hQ.aestronglyMeasurable.prodMk (hR.prodMk hv))
  have hJ : Measurable (fun x => Real.sqrt (P x).det) := by fun_prop
  exact (hh.aemeasurable.div hJ.aemeasurable).aestronglyMeasurable

lemma orientation_bound (a : ℝ) : abs (a/abs a) ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [abs_div,abs_abs,div_self (abs_ne_zero.mpr ha)]

lemma orientation_density (a : ℝ) : abs a*(a/abs a) = a := by
  by_cases ha : a = 0
  · simp [ha]
  · field_simp

end CAT0Fillings
end

end OAI
