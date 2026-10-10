import Mathlib
import OAI.Probability.SKRatio.Matrices.GaussianQuadratic
import OAI.Probability.SKRatio.Matrices.GaussianProductUpperTailLipschitz
import OAI.Probability.SKRatio.Matrices.GaussianTails

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators Topology
namespace SKRatioGaussian
variable {κ : Type*} [Fintype κ]

lemma gaussian_coordinates_norm_mean :
    (∫ x : κ → ℝ, ‖WithLp.toLp 2 x‖ ∂gaussianCoordinates κ) ≤
      sqrt (Fintype.card κ) := by
  have hsq (x : κ → ℝ) : ‖WithLp.toLp 2 x‖^2 = gaussianQuadratic (fun _ => 1) x := by
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs,
      gaussianQuadratic, one_mul]
  have hnorm (x : κ → ℝ) : ‖WithLp.toLp 2 x‖ = sqrt (gaussianQuadratic (fun _ => 1) x) := by
    rw [←hsq, sqrt_sq (norm_nonneg _)]
  have hi : MemLp (fun x : κ → ℝ => ‖WithLp.toLp 2 x‖) 2 (gaussianCoordinates κ) := by
    simp_rw [hnorm]
    exact memLp_sqrt_of_nonneg ((gaussianQuadratic_memLp (fun _ : κ => 1)).integrable (by norm_num))
      (fun x => Finset.sum_nonneg (fun i _ => by positivity))
  have hb := integral_abs_le_sqrt_sq hi
  simp only [abs_of_nonneg (norm_nonneg _),hsq,gaussianCoordinates,gaussianQuadratic_mean,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hb
  exact hb

lemma scaled_gaussian_radius_tail {r b R : ℝ} (hr : 0 < r)
    (hb : sqrt r * sqrt (Fintype.card κ) ≤ b) (hR : b ≤ R) :
    (Measure.pi (fun _ : κ => gaussianReal 0 (Real.toNNReal r))).real
      {v | R < ‖WithLp.toLp 2 v‖} ≤
      exp (-2*(R-b)^2/(Real.pi^2*r)) := by
  let f : (κ → ℝ) → ℝ := fun x => sqrt r * ‖WithLp.toLp 2 x‖
  have hi : Integrable (fun x : κ → ℝ => ‖WithLp.toLp 2 x‖) (gaussianCoordinates κ) := by
    have hsq (x : κ → ℝ) : ‖WithLp.toLp 2 x‖ = sqrt (gaussianQuadratic (fun _ => 1) x) := by
      simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs,sq_abs,
        gaussianQuadratic,one_mul]
    simp_rw [hsq]
    exact (memLp_sqrt_of_nonneg ((gaussianQuadratic_memLp (fun _ : κ => 1)).integrable (by norm_num))
      (fun x => Finset.sum_nonneg (fun i _ => by positivity))).integrable (by norm_num)
  have hm : (∫ x, f x ∂gaussianCoordinates κ) ≤ b := by
    change (∫ x : κ → ℝ, sqrt r * ‖WithLp.toLp 2 x‖ ∂gaussianCoordinates κ) ≤ b
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left gaussian_coordinates_norm_mean (sqrt_nonneg r)).trans hb
  have hl : LipschitzWith (Real.toNNReal (sqrt r))
      (fun x : EuclideanSpace ℝ κ => f x.ofLp) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (sqrt r * ‖x‖) (sqrt r * ‖y‖) ≤ _
    rw [Real.dist_eq, ←mul_sub, abs_mul,abs_of_nonneg (sqrt_nonneg r),
      Real.coe_toNNReal _ (sqrt_nonneg r)]
    exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (sqrt_nonneg r)
  have ht := gaussianProduct_upper_tail_lipschitz hl
    (Real.toNNReal_pos.mpr (sqrt_pos.mpr hr)) (sub_nonneg.mpr hR)
  rw [Real.coe_toNNReal _ (sqrt_nonneg r),sq_sqrt hr.le] at ht
  have he : MeasurableSet {v : κ → ℝ | R < ‖WithLp.toLp 2 v‖} := by
    apply measurableSet_lt measurable_const
    exact (continuous_norm.comp (PiLp.continuous_toLp 2 (fun _ : κ => ℝ))).measurable
  rw [←(gaussian_scaled_coordinates_hasLaw (κ := κ) hr.le).measureReal_eq he]
  apply (measureReal_mono (s₂ := {x : κ → ℝ | R-b ≤ f x - ∫ y, f y ∂gaussianCoordinates κ}) ?_).trans ht
  intro x hx
  have heq : WithLp.toLp 2 (fun i => sqrt r * x i) =
      sqrt r • (WithLp.toLp 2 x : EuclideanSpace ℝ κ) := rfl
  change R < ‖WithLp.toLp 2 (fun i => sqrt r * x i)‖ at hx
  rw [heq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg r)] at hx
  change R-b ≤ f x - ∫ y, f y ∂gaussianCoordinates κ
  dsimp [f] at *
  linarith

variable {n : ℕ}

lemma coupling_goe_row_tight_tail {j δ : ℝ} (hj : 0 < j) (hδ : 0 ≤ δ)
    (i : Fin n) :
    (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | j+δ < ∑ k, coupling (goeDisorder (j/(n:ℝ)) g) i k^2} ≤
      exp (-(2*(sqrt (j+δ)-sqrt j)^2/(Real.pi^2*j))*(n:ℝ)) := by
  classical
  have hn : (0:ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (fun hn => by simpa [hn] using i.isLt))
  let S : Finset (Fin n) := Finset.univ.erase i
  let e : S ↪ Fin n := ⟨Subtype.val,Subtype.val_injective⟩
  have havoid (k : S) : e k ≠ i := Finset.ne_of_mem_erase k.2
  have hsum (g : MatrixCoordinates (Fin n) → ℝ) :
      (∑ k, coupling (goeDisorder (j/(n:ℝ)) g) i k^2) =
        ∑ k : S, goeMatrix (j/(n:ℝ)) g i k^2 :=
    coupling_goe_row_square_sum (j/(n:ℝ)) g i Finset.univ
  simp_rw [hsum]
  have hm : MeasurableSet {v : S → ℝ | j+δ < ∑ k, v k^2} := by measurability
  have hl := (goe_row_hasLaw (div_nonneg hj.le hn.le) i e havoid).measureReal_eq hm
  change (gaussianCoordinates (MatrixCoordinates (Fin n))).real
    {g | j+δ < ∑ k : S, goeMatrix (j/(n:ℝ)) g i k^2} =
      (Measure.pi (fun _ : S => gaussianReal 0 (Real.toNNReal (j/(n:ℝ))))).real
        {v | j+δ < ∑ k, v k^2} at hl
  rw [hl]
  have heq : {v : S → ℝ | j+δ < ∑ k, v k^2} =
      {v : S → ℝ | sqrt (j+δ) < ‖WithLp.toLp 2 v‖} := by
    ext v
    have hnrm : ‖WithLp.toLp 2 v‖^2 = ∑ k, v k^2 := by
      simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
    simp only [Set.mem_ofPred_eq]
    calc
      j+δ < ∑ k, v k^2 ↔ sqrt (j+δ)^2 < ‖WithLp.toLp 2 v‖^2 := by
        rw [hnrm,sq_sqrt (by positivity : 0 ≤ j+δ)]
      _ ↔ _ := sq_lt_sq₀ (sqrt_nonneg (j+δ))
        (norm_nonneg (WithLp.toLp 2 v : EuclideanSpace ℝ S))
  rw [heq]
  have hcard : (Fintype.card S : ℝ) ≤ n := by
    rw [Fintype.card_coe]
    exact_mod_cast ((Finset.card_erase_le (s := Finset.univ) (a := i)).trans
      (by simp))
  have hb : sqrt (j/(n:ℝ))*sqrt (Fintype.card S) ≤ sqrt j := by
    rw [←sqrt_mul (by positivity : 0 ≤ j/(n:ℝ))]
    apply sqrt_le_sqrt
    calc
      _ ≤ (j/(n:ℝ))*(n:ℝ) := mul_le_mul_of_nonneg_left hcard (by positivity)
      _ = j := div_mul_cancel₀ j hn.ne'
  have ht := scaled_gaussian_radius_tail (κ := S) (div_pos hj hn) hb
    (sqrt_le_sqrt (by linarith : j ≤ j+δ))
  apply ht.trans_eq
  congr 1
  field_simp

lemma coupling_goe_all_rows_tight_tail {n : ℕ} (_hn : 0 < n) {j δ : ℝ}
    (hj : 0 < j) (hδ : 0 ≤ δ) :
    (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | ∃ i, j+δ < ∑ k, coupling (goeDisorder (j/(n:ℝ)) g) i k^2} ≤
      (n:ℝ)*exp (-(2*(sqrt (j+δ)-sqrt j)^2/(Real.pi^2*j))*(n:ℝ)) := by
  have he : {g : MatrixCoordinates (Fin n) → ℝ | ∃ i,
      j+δ < ∑ k, coupling (goeDisorder (j/(n:ℝ)) g) i k^2} =
      ⋃ i : Fin n, {g | j+δ < ∑ k, coupling (goeDisorder (j/(n:ℝ)) g) i k^2} := by
    ext g; simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  apply (Finset.sum_le_sum (fun i _ => coupling_goe_row_tight_tail hj hδ i)).trans_eq
  simp

end SKRatioGaussian

end
end

end OAI
