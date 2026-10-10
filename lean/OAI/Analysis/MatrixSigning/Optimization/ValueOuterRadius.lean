import Mathlib
import OAI.Analysis.MatrixSigning.Potential.PositiveMapMono
import OAI.Analysis.MatrixSigning.Optimization.PackValue

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
noncomputable section
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d n : ℕ}

lemma euclidean_norm_le_card (v : EuclideanSpace ℝ (Fin n)) {B : ℝ}
    (hB : 0 ≤ B) (hv : ∀ k, ‖v k‖ ≤ B) : ‖v‖ ≤ ((n:ℝ)+1)*B := by
  have hs : ‖v‖^2 ≤ (n:ℝ)*B^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    have hh := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) =>
      sq_le_sq₀ (norm_nonneg _) hB |>.mpr (hv k))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have hnum : (n:ℝ) ≤ ((n:ℝ)+1)^2 := by have := Nat.cast_nonneg (α := ℝ) n; nlinarith
  have hm := mul_le_mul_of_nonneg_right hnum (sq_nonneg B)
  have hp : 0 ≤ ((n:ℝ)+1)*B := by positivity
  nlinarith [norm_nonneg v]

lemma norm_hermitian_entry (A : H d) (i j : Fin d) : ‖A.val i j‖ ≤ ‖A‖ := by
  change ‖asL2 A.val i j‖ ≤ ‖asL2 A.val‖
  exact (PiLp.norm_apply_le (asL2 A.val i) j).trans (PiLp.norm_apply_le (asL2 A.val) i)

lemma abs_encode_le (A : H d) (ij : Fin d × Fin d) : |encode A ij| ≤ ‖A‖ := by
  unfold encode
  split
  · exact (Complex.abs_re_le_norm _).trans (norm_hermitian_entry A _ _)
  · exact (Complex.abs_im_le_norm _).trans (norm_hermitian_entry A _ _)

lemma norm_packValue (z : Point d) :
    ‖packValue z‖ ≤ ((valueDimension d:ℝ)+1)*(|z.1|+‖z.2.1‖+‖z.2.2‖) := by
  apply euclidean_norm_le_card _ (by positivity)
  intro k
  obtain ⟨j,rfl⟩ := (valueIndex d).surjective k
  rcases j with j | (ij | ij)
  · simp only [packValue,PiLp.toLp_apply,Equiv.symm_apply_apply,Real.norm_eq_abs]
    linarith [norm_nonneg z.2.1,norm_nonneg z.2.2]
  · simp only [packValue,PiLp.toLp_apply,Equiv.symm_apply_apply,Real.norm_eq_abs]
    have he := abs_encode_le z.2.1 ij
    linarith [abs_nonneg z.1,norm_nonneg z.2.2]
  · simp only [packValue,PiLp.toLp_apply,Equiv.symm_apply_apply,Real.norm_eq_abs]
    have he := abs_encode_le z.2.2 ij
    linarith [abs_nonneg z.1,norm_nonneg z.2.1]

lemma norm_psd_order_bound (U : H d) (hU : U ∈ psdCone d) {r : ℝ} (hr : 0 ≤ r)
    (hUr : U ≤ r • Hermitian.one) : ‖U‖ ≤ r*((d:ℝ)+1) := by
  have ht := realTrace_mono hUr
  rw [Hermitian.realTrace_smul,Hermitian.realTrace_one] at ht
  have hh := inner_nonneg_of_psd U (r • Hermitian.one-U) hU
    ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr hUr))
  rw [inner_sub_right,real_inner_smul_right U (Hermitian.one : H d) r,inner_one',real_inner_self_eq_norm_sq] at hh
  have hnt : ‖U‖^2 ≤ r^2*d := by nlinarith [mul_le_mul_of_nonneg_left ht hr]
  have hd : (0:ℝ)≤d := Nat.cast_nonneg d
  have hd' : (d:ℝ)≤(d+1)^2 := by nlinarith
  have hh' := mul_le_mul_of_nonneg_left hd' (sq_nonneg r)
  have hn : 0 ≤ r*((d:ℝ)+1) := by positivity
  nlinarith [norm_nonneg U]

def valueOuterRadius (d : ℕ) (ε : ℚ) : ℚ :=
  ((valueDimension d:ℚ)+1)*(100+400/ε*((d:ℚ)+1))
def valueInnerRadius (d : ℕ) : ℚ := 1/(4000*((d:ℚ)^2+1))

lemma valueOuterRadius_nonneg {ε : ℚ} (hε : 0 < ε) : 0 ≤ valueOuterRadius d ε := by
  unfold valueOuterRadius
  positivity
lemma valueInnerRadius_pos : 0 < valueInnerRadius d := by unfold valueInnerRadius; positivity
lemma valueInnerRadius_le : valueInnerRadius d ≤ 1 := by
  unfold valueInnerRadius
  apply (div_le_one (by positivity)).mpr
  nlinarith [sq_nonneg (d:ℚ)]

lemma oracleBox_norm_packValue {ε : ℚ} (hε : 0 < ε) (z : Point d) (hz : oracleBox (ε:ℝ) z) :
    ‖packValue z‖ ≤ (valueOuterRadius d ε:ℝ) := by
  have hX := (pd_of_lower (by norm_num : (0:ℝ)<1/400) hz.2.1.1).posSemidef
  have hY := (pd_of_lower (by norm_num : (0:ℝ)<1/400) hz.2.2.1).posSemidef
  have hεr : (0:ℝ)<ε := by exact_mod_cast hε
  have hx := norm_psd_order_bound z.2.1 hX (div_nonneg (by norm_num) hεr.le) hz.2.1.2
  have hy := norm_psd_order_bound z.2.2 hY (div_nonneg (by norm_num) hεr.le) hz.2.2.2
  have ht : |z.1| ≤ 100 := by rw [abs_of_nonneg hz.1.1]; exact hz.1.2
  apply (norm_packValue z).trans
  unfold valueOuterRadius
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ 100+(200/(ε:ℝ)*((d:ℝ)+1)+200/(ε:ℝ)*((d:ℝ)+1)) := by linarith
    _ = _ := by ring

lemma unpackValue_sub (v w : EuclideanSpace ℝ (Fin (valueDimension d))) :
    unpackValue (v-w)=unpackValue v-unpackValue w := by
  apply Prod.ext
  · change timeCoordinate d (v.ofLp-w.ofLp)=_
    exact (timeCoordinate (R := ℝ) d).map_sub _ _
  · apply Prod.ext
    all_goals
      simp only [unpackValue,WithLp.ofLp_sub,map_sub,WithLp.toLp_sub]
      exact (assembleLinear d).map_sub _ _

lemma timeCoordinate_norm (v : EuclideanSpace ℝ (Fin (valueDimension d))) :
    |timeCoordinate d v| ≤ ‖v‖ := by
  simpa only [timeCoordinate,LinearMap.proj_apply,Real.norm_eq_abs] using
    PiLp.norm_apply_le v (valueIndex d (.inl 0))

lemma unpackValue_matrix_norm (v : EuclideanSpace ℝ (Fin (valueDimension d))) :
    ‖(unpackValue v).2.1‖ ≤ 2*((d:ℝ)^2+1)*‖v‖ ∧
    ‖(unpackValue v).2.2‖ ≤ 2*((d:ℝ)^2+1)*‖v‖ := by
  constructor
  all_goals
    apply (norm_assemble _).trans
    exact (mul_le_mul_of_nonneg_left (matrixCoordinate_norm v _) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

lemma value_center_coordinate_ball (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d,η A ∈ psdCone d)
    (hη1 : η Hermitian.one ≤ (384:ℝ) • Hermitian.one)
    (hSlo : -(1:ℝ) • (Hermitian.one : H d) ≤ S)
    (hShi : S ≤ (1:ℝ) • (Hermitian.one : H d))
    {ε : ℚ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (v : EuclideanSpace ℝ (Fin (valueDimension d)))
    (hv : v ∈ Metric.closedBall (packValue (50,(1/20:ℝ) • (Hermitian.one : H d),
      (1/20:ℝ) • (Hermitian.one : H d))) (valueInnerRadius d:ℝ)) :
    unpackValue v ∈ valueSpectrahedron (ε:ℝ) S η := by
  let c : Point d := (50,(1/20:ℝ) • (Hermitian.one : H d),(1/20:ℝ) • Hermitian.one)
  have hr : ‖v-packValue c‖ ≤ (valueInnerRadius d:ℝ) := by
    rw [← dist_eq_norm]
    exact hv
  have hD : 0 < (d:ℝ)^2+1 := by positivity
  have hs : (valueInnerRadius d:ℝ) ≤ 1/1000 := by
    simp only [valueInnerRadius,Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_add,Rat.cast_pow,Rat.cast_natCast]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (d:ℝ)]
  have hm : 2*((d:ℝ)^2+1)*(valueInnerRadius d:ℝ) ≤ 1/1000 := by
    simp only [valueInnerRadius,Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_add,Rat.cast_pow,Rat.cast_natCast]
    field_simp
    nlinarith [sq_nonneg (d:ℝ)]
  have ht := (timeCoordinate_norm (v-packValue c)).trans (hr.trans hs)
  have hxy := unpackValue_matrix_norm (v-packValue c)
  have hx := hxy.1.trans ((mul_le_mul_of_nonneg_left hr (by positivity)).trans hm)
  have hy := hxy.2.trans ((mul_le_mul_of_nonneg_left hr (by positivity)).trans hm)
  have he := unpackValue_sub v (packValue c)
  rw [unpack_packValue] at he
  rw [he] at hx hy
  apply value_center_neighborhood S η hη hη1 hSlo hShi (by exact_mod_cast hε)
    (by exact_mod_cast hε1) (unpackValue v)
  · change |timeCoordinate d (v.ofLp) - 50| ≤ _
    change |timeCoordinate d (v.ofLp - (packValue c).ofLp)| ≤ _ at ht
    simp only [map_sub,time_packValue,c] at ht
    exact ht
  · exact hx
  · exact hy

end
end CurrentKS.RationalSDP

end OAI
