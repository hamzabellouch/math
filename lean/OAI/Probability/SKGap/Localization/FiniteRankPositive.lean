import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section

noncomputable section
open Real Matrix Set
open scoped BigOperators
namespace SKGap
variable {ι : Type*} [Fintype ι]

def rayleigh (M : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) : ℝ :=
  (WithLp.ofLp v) ⬝ᵥ (M *ᵥ WithLp.ofLp v)

lemma continuous_rayleigh : Continuous (fun p : Matrix ι ι ℝ × EuclideanSpace ℝ ι => rayleigh p.1 p.2) := by
  unfold rayleigh dotProduct mulVec
  fun_prop

lemma rayleigh_smul (M : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) (c : ℝ) :
    rayleigh M (c • v) = c^2*rayleigh M v := by
  simp only [rayleigh, WithLp.ofLp_smul, mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  ring

lemma rayleigh_zero (M : Matrix ι ι ℝ) : rayleigh M 0 = 0 := by
  simp [rayleigh]

def unitEuclidean (ι : Type*) [Fintype ι] := {v : EuclideanSpace ℝ ι | ‖v‖ = 1}

lemma isCompact_unitEuclidean : IsCompact (unitEuclidean ι) := by
  simpa only [unitEuclidean, Metric.sphere, dist_zero_right] using
    (isCompact_sphere (0 : EuclideanSpace ℝ ι) 1)

lemma unitEuclidean_nonempty [Nonempty ι] : (unitEuclidean ι).Nonempty := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨EuclideanSpace.single i (1:ℝ),?_⟩
  simp [unitEuclidean]

def lowerRayleigh (M : Matrix ι ι ℝ) : ℝ := sInf (rayleigh M '' unitEuclidean ι)

lemma continuous_lowerRayleigh : Continuous (lowerRayleigh (ι := ι)) := by
  exact isCompact_unitEuclidean.continuous_sInf continuous_rayleigh

lemma lowerRayleigh_attained [Nonempty ι] (M : Matrix ι ι ℝ) :
    ∃ v ∈ unitEuclidean ι, lowerRayleigh M = rayleigh M v ∧
      ∀ w ∈ unitEuclidean ι, rayleigh M v ≤ rayleigh M w := by
  exact isCompact_unitEuclidean.exists_sInf_image_eq_and_le unitEuclidean_nonempty
    (continuous_rayleigh.comp (continuous_const.prodMk continuous_id)).continuousOn

lemma lowerRayleigh_le [Nonempty ι] (M : Matrix ι ι ℝ) {v : EuclideanSpace ℝ ι}
    (hv : v ∈ unitEuclidean ι) : lowerRayleigh M ≤ rayleigh M v := by
  obtain ⟨w,_,he,hw⟩ := lowerRayleigh_attained M
  rw [he]
  exact hw v hv

lemma unitEuclidean_normalize {v : EuclideanSpace ℝ ι} (hv : v ≠ 0) :
    ‖v‖⁻¹ • v ∈ unitEuclidean ι := by
  change ‖‖v‖⁻¹ • v‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

lemma nonneg_rayleigh_of_unit {M : Matrix ι ι ℝ}
    (h : ∀ v ∈ unitEuclidean ι, 0 ≤ rayleigh M v) (v : EuclideanSpace ℝ ι) :
    0 ≤ rayleigh M v := by
  by_cases hv : v = 0
  · simp [hv,rayleigh_zero]
  have hh := h _ (unitEuclidean_normalize hv)
  rw [rayleigh_smul] at hh
  exact nonneg_of_mul_nonneg_right hh (sq_pos_of_pos (inv_pos.mpr (norm_pos_iff.mpr hv)))

lemma rayleigh_pos_of_unit {M : Matrix ι ι ℝ}
    (h : ∀ v ∈ unitEuclidean ι, 0 < rayleigh M v) {v : EuclideanSpace ℝ ι} (hv : v ≠ 0) :
    0 < rayleigh M v := by
  have hh := h _ (unitEuclidean_normalize hv)
  rw [rayleigh_smul] at hh
  exact pos_of_mul_pos_right hh (sq_nonneg _)

lemma lowerRayleigh_nonneg_iff [Nonempty ι] {M : Matrix ι ι ℝ} (hM : M.IsHermitian) :
    0 ≤ lowerRayleigh M ↔ M.PosSemidef := by
  constructor
  · intro h
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM
    intro x
    exact nonneg_rayleigh_of_unit (fun v hv => h.trans (lowerRayleigh_le M hv)) (WithLp.toLp 2 x)
  · intro h
    obtain ⟨v,_,he,_⟩ := lowerRayleigh_attained M
    rw [he]
    exact h.dotProduct_mulVec_nonneg _

lemma lowerRayleigh_pos_iff [Nonempty ι] {M : Matrix ι ι ℝ} (hM : M.IsHermitian) :
    0 < lowerRayleigh M ↔ M.PosDef := by
  constructor
  · intro h
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hM
    intro x hx
    apply rayleigh_pos_of_unit (fun v hv => h.trans_le (lowerRayleigh_le M hv))
      (v := WithLp.toLp 2 x)
    exact fun hz => hx (congrArg WithLp.ofLp hz)
  · intro h
    obtain ⟨v,hv,he,_⟩ := lowerRayleigh_attained M
    rw [he]
    exact h.dotProduct_mulVec_pos (fun hz => by
      have hz' : v = 0 := WithLp.ofLp_injective 2 hz
      have hv' : ‖v‖ = 1 := hv
      simp [hz'] at hv')

theorem matrix_path_posDef [DecidableEq ι] {a : ℝ} (ha : 0 ≤ a) (M : ℝ → Matrix ι ι ℝ)
    (hcont : Continuous M) (hherm : ∀ t ∈ Icc 0 a, (M t).IsHermitian)
    (hdet : ∀ t ∈ Icc 0 a, (M t).det ≠ 0) (hzero : (M 0).PosDef) : (M a).PosDef := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    let := h
    apply Matrix.PosDef.of_dotProduct_mulVec_pos (hherm a ⟨ha,le_rfl⟩)
    intro x hx
    exact (hx (Subsingleton.elim _ _)).elim
  | inr h =>
    let := h
    let f := fun t => lowerRayleigh (M t)
    have hf : Continuous f := continuous_lowerRayleigh.comp hcont
    have hnz : ∀ t ∈ Icc 0 a, f t ≠ 0 := by
      intro t ht hz
      have hpsd := (lowerRayleigh_nonneg_iff (hherm t ht)).mp (le_of_eq hz.symm)
      have hpd := hpsd.posDef_iff_det_ne_zero.mpr (hdet t ht)
      have hh := (lowerRayleigh_pos_iff (hherm t ht)).mpr hpd
      exact (ne_of_gt hh) hz
    have h0 : 0 < f 0 := (lowerRayleigh_pos_iff hzero.1).mpr hzero
    apply (lowerRayleigh_pos_iff (hherm a ⟨ha,le_rfl⟩)).mp
    by_contra hh
    have han : f a < 0 := lt_of_le_of_ne (not_lt.mp hh) (hnz a ⟨ha,le_rfl⟩)
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc' ha hf.continuousOn ⟨han.le,h0.le⟩
    exact hnz t ht he

end SKGap

noncomputable section
open Real Matrix Set
open scoped BigOperators
namespace SKGap

def limitingGram (b e s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![b,e,-2*e; e,e,b-3*e; -2*e,b-3*e,b/s-2*b+6*e]

def rankCoefficient (j b s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  j • !![1,0,0; 0,2-j*b/s,1; 0,1,0]

lemma limiting_rank_determinant (j b e s : ℝ) :
    (1-limitingGram b e s * rankCoefficient j b s).det =
      (1-j*b+2*j*e)*(1-j*b+j*e)^2 := by
  simp [Matrix.det_fin_three, limitingGram, rankCoefficient,
    Matrix.sub_apply, cons_val_two, vecHead, vecTail]
  ring

lemma rankCoefficient_hermitian (j b s : ℝ) : (rankCoefficient j b s).IsHermitian := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [rankCoefficient, Matrix.conjTranspose_apply]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def limitingPositiveMatrix (Q : Matrix ι (Fin 3) ℝ) (j b s : ℝ) : Matrix ι ι ℝ :=
  1-Q*rankCoefficient j b s*Qᵀ

lemma limitingPositiveMatrix_det (Q : Matrix ι (Fin 3) ℝ) {b e s : ℝ}
    (hQ : Qᵀ*Q = limitingGram b e s) (j : ℝ) :
    (limitingPositiveMatrix Q j b s).det = (1-j*b+2*j*e)*(1-j*b+j*e)^2 := by
  unfold limitingPositiveMatrix
  calc
    _ = (1-(rankCoefficient j b s*Qᵀ)*Q).det := by
      rw [Matrix.mul_assoc, Matrix.det_one_sub_mul_comm]
    _ = (1-rankCoefficient j b s*limitingGram b e s).det := by rw [Matrix.mul_assoc,hQ]
    _ = (1-limitingGram b e s*rankCoefficient j b s).det := Matrix.det_one_sub_mul_comm _ _
    _ = _ := limiting_rank_determinant _ _ _ _

end SKGap

namespace SKGap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma limitingPositiveMatrix_hermitian (Q : Matrix ι (Fin 3) ℝ) (j b s : ℝ) :
    (limitingPositiveMatrix Q j b s).IsHermitian := by
  unfold limitingPositiveMatrix
  apply Matrix.isHermitian_one.sub
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_mul_mul_conjTranspose Q (rankCoefficient_hermitian j b s)

omit [Fintype ι] in
lemma continuous_limitingPositiveMatrix (Q : Matrix ι (Fin 3) ℝ) (b s : ℝ) :
    Continuous (fun j => limitingPositiveMatrix Q j b s) := by
  unfold limitingPositiveMatrix rankCoefficient
  apply continuous_const.sub
  apply Continuous.matrix_mul ?_ continuous_const
  apply continuous_const.matrix_mul
  fun_prop

theorem limitingPositiveMatrix_posDef (Q : Matrix ι (Fin 3) ℝ) {j b e s : ℝ}
    (hj : 0 ≤ j) (hj1 : j < 1) (hb1 : b ≤ 1) (he : 0 ≤ e)
    (hQ : Qᵀ*Q = limitingGram b e s) : (limitingPositiveMatrix Q j b s).PosDef := by
  apply matrix_path_posDef hj _ (continuous_limitingPositiveMatrix Q b s)
    (fun r _ => limitingPositiveMatrix_hermitian Q r b s)
  · intro r hr
    rw [limitingPositiveMatrix_det Q hQ]
    have hrb : r*b < 1 := lt_of_le_of_lt (mul_le_of_le_one_right hr.1 hb1) (hr.2.trans_lt hj1)
    have hre : 0 ≤ r*e := mul_nonneg hr.1 he
    exact ne_of_gt (mul_pos (by nlinarith) (sq_pos_of_pos (by linarith)))
  · simpa [limitingPositiveMatrix,rankCoefficient] using
      (Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef)

end SKGap
end
end
end

end OAI
