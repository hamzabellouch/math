import OAI.Probability.StrongRayleigh.Model

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate ComplexOrder

namespace Problem336AdditiveD139

lemma quadraticForm_eq_dotProduct {F : Type u_1} [Fintype F]
    (K : Matrix F F ℂ) (c : F → ℂ) :
    (∑ i : F, ∑ j : F, conj (c i) * K i j * c j) =
      star c ⬝ᵥ (K *ᵥ c) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

lemma PositiveContractionFinite.isHermitian {F : Type u_2} [Fintype F]
    {K : Matrix F F ℂ} (hK : PositiveContractionFinite K) :
    Matrix.IsHermitian K :=
  Matrix.IsHermitian.ext fun i j => (hK.1 i j).symm

lemma PositiveContractionFinite.posSemidef {F : Type u_3} [Fintype F]
    {K : Matrix F F ℂ} (hK : PositiveContractionFinite K) :
    Matrix.PosSemidef K := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨hK.isHermitian, fun c => ?_⟩
  rw [Complex.nonneg_iff]
  constructor
  · simpa only [quadraticForm_eq_dotProduct] using (hK.2 c).1
  · exact (hK.isHermitian.im_star_dotProduct_mulVec_self c).symm

lemma normSq_sum_eq_dotProduct_re {F : Type u_4} [Fintype F] (c : F → ℂ) :
    (∑ i : F, Complex.normSq (c i)) = (star c ⬝ᵥ c).re := by
  simp [dotProduct, Complex.mul_re, Complex.normSq_apply]

lemma PositiveContractionFinite.one_sub_posSemidef {F : Type u_5} [Fintype F]
    [DecidableEq F] {K : Matrix F F ℂ} (hK : PositiveContractionFinite K) :
    Matrix.PosSemidef ((1 : Matrix F F ℂ) - K) := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  have hHerm : Matrix.IsHermitian ((1 : Matrix F F ℂ) - K) := Matrix.isHermitian_one.sub hK.isHermitian
  refine ⟨hHerm, fun c => ?_⟩
  rw [Complex.nonneg_iff]
  constructor
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re]
    apply sub_nonneg.mpr
    simpa only [quadraticForm_eq_dotProduct, normSq_sum_eq_dotProduct_re] using (hK.2 c).2
  · exact (hHerm.im_star_dotProduct_mulVec_self c).symm

lemma positiveContractionFinite_iff_posSemidef {F : Type u_6} [Fintype F]
    [DecidableEq F] (K : Matrix F F ℂ) :
    PositiveContractionFinite K ↔
      Matrix.PosSemidef K ∧ Matrix.PosSemidef ((1 : Matrix F F ℂ) - K) := by
  constructor
  · intro hK
    exact ⟨hK.posSemidef, hK.one_sub_posSemidef⟩
  · rintro ⟨hK, hOne⟩
    refine ⟨fun i j => (hK.isHermitian.apply i j).symm, fun c => ?_⟩
    rw [quadraticForm_eq_dotProduct, normSq_sum_eq_dotProduct_re]
    refine ⟨hK.re_dotProduct_nonneg c, ?_⟩
    have h := hOne.re_dotProduct_nonneg c
    change 0 ≤ (star c ⬝ᵥ (((1 : Matrix F F ℂ) - K) *ᵥ c)).re at h
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re] at h
    exact sub_nonneg.mp h

lemma hermitian_pencil_ker_eq_zero {F : Type u_7} [Fintype F] [DecidableEq F]
    {K : Matrix F F ℂ} (hK : K.IsHermitian) (z : F → ℂ)
    (hz : ∀ i, 0 < (z i).im) (c : F → ℂ)
    (hc : ((1 - K + Matrix.diagonal z * K) : Matrix F F ℂ) *ᵥ c = 0) :
    c = 0 := by
  have hc' : c - K *ᵥ c + Matrix.diagonal z *ᵥ (K *ᵥ c) = 0 := by
    simpa only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_mulVec] using hc
  have hcoord (i : F) : c i = (1 - z i) * (K *ᵥ c) i := by
    have hi := congr_fun hc' i
    simp only [Pi.add_apply, Pi.sub_apply, Matrix.mulVec_diagonal,
      Pi.zero_apply] at hi
    linear_combination hi
  have him : (star c ⬝ᵥ (K *ᵥ c)).im = 0 :=
    hK.im_star_dotProduct_mulVec_self c
  have hsum : (∑ i : F, (z i).im * Complex.normSq ((K *ᵥ c) i)) = 0 := by
    convert him using 1
    simp only [dotProduct, Complex.im_sum, Pi.star_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcoord i]
    simp [Complex.mul_im, Complex.mul_re, Complex.normSq_apply]
    ring
  have hy : K *ᵥ c = 0 := by
    funext i
    have hterm : (z i).im * Complex.normSq ((K *ᵥ c) i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg (le_of_lt (hz j)) (Complex.normSq_nonneg _))).mp hsum
        i (Finset.mem_univ i)
    exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hz i)))
  funext i
  simpa [hy] using hcoord i

lemma hermitian_pencil_det_ne_zero {F : Type u_8} [Fintype F] [DecidableEq F]
    {K : Matrix F F ℂ} (hK : K.IsHermitian) (z : F → ℂ)
    (hz : ∀ i, 0 < (z i).im) :
    Matrix.det (1 - K + Matrix.diagonal z * K) ≠ 0 := by
  have hu : IsUnit ((1 - K + Matrix.diagonal z * K) : Matrix F F ℂ) := by
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro a b hab
    have hzero : ((1 - K + Matrix.diagonal z * K) : Matrix F F ℂ) *ᵥ (a - b) = 0 := by
      rw [Matrix.mulVec_sub, hab, sub_self]
    exact sub_eq_zero.mp (hermitian_pencil_ker_eq_zero hK z hz (a-b) hzero)
  exact (Matrix.isUnit_iff_isUnit_det _ |>.mp hu).ne_zero

end Problem336AdditiveD139

end

end OAI
