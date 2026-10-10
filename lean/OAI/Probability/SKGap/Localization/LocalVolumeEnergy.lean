import Mathlib
import OAI.Probability.SKGap.Gaussian.LocalGaussianMoments

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

lemma continuous_vectorNorm (n : ℕ) : Continuous (vectorNorm (n := n)) := by
  unfold vectorNorm
  exact continuous_norm.comp (PiLp.continuous_toLp 2 _)

lemma continuous_tapField {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) :
    Continuous (tapField j J h) := by
  exact continuous_iff_continuousAt.mpr (fun y => (tapField_hasFDerivAt j J h y).continuousAt)

lemma tap_remainder_sq_integrable {n : ℕ} (hn : 0 < n) {j K : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (h y : Field n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun g => vectorNorm (tapField j J h (y+A*ᵥg)-tapField j J h y-
      (fieldJacobian j J y)*ᵥ(A*ᵥg))^2) (gaussianCoordinates (Fin n)) := by
  apply ((matrix_fourth_sum_integrable A).const_mul (8*(j+K)^2+128*j^2)).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    exact ((continuous_vectorNorm n).comp
      (((continuous_tapField j J h).comp (by fun_prop)).sub continuous_const |>.sub (by fun_prop))).pow 2
  · filter_upwards [] with g
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact tap_remainder_sq hn hj hK J hJ h y (A*ᵥg)

theorem localGaussian_remainder_cond {n : ℕ} (hn : 0 < n) {j K : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (h y : Field n)
    {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.IsHermitian) {γ σ : ℝ} (hγ : 0 < γ)
    (hbound : ∀ g : Field n, vectorNorm (U*ᵥg) ≤ vectorNorm g/sqrt γ) :
    (∫ g,vectorNorm (tapField j J h (y+(σ • U)*ᵥg)-tapField j J h y-
      (fieldJacobian j J y)*ᵥ((σ • U)*ᵥg))^2
      ∂cond (gaussianCoordinates (Fin n)) (localGaussianBall n)) ≤
      6*(8*(j+K)^2+128*j^2)*(n:ℝ)*σ^4/γ^2 := by
  let C := 8*(j+K)^2+128*j^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hi := tap_remainder_sq_integrable hn hj hK J hJ h y (σ • U)
  have hp : 1/2 ≤ (gaussianCoordinates (Fin n)).real (localGaussianBall n) :=
    (by norm_num : (1:ℝ)/2 ≤ 3/4).trans (localGaussianBall_probability hn)
  have hc := integral_cond_nonneg_le_two hp hi (ae_of_all _ (fun g => sq_nonneg _))
  have hb : (∫ g,vectorNorm (tapField j J h (y+(σ • U)*ᵥg)-tapField j J h y-
      (fieldJacobian j J y)*ᵥ((σ • U)*ᵥg))^2 ∂gaussianCoordinates (Fin n)) ≤
      C*(3*(n:ℝ)*σ^4/γ^2) := by
    calc
      _ ≤ ∫ g,C*(∑ i,(((σ • U)*ᵥg) i)^4) ∂gaussianCoordinates (Fin n) :=
        integral_mono hi ((matrix_fourth_sum_integrable _).const_mul _)
          (fun g => tap_remainder_sq hn hj hK J hJ h y _)
      _ = C*(∫ g,∑ i,(((σ • U)*ᵥg) i)^4 ∂gaussianCoordinates (Fin n)) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (localGaussian_fourth_moments hU hγ hbound).1 hC
  calc
    _ ≤ 2*(C*(3*(n:ℝ)*σ^4/γ^2)) := hc.trans (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ = _ := by dsimp [C]; ring

lemma vectorNorm_add_sq_young {n : ℕ} (u v : Field n) {η : ℝ} (hη : 0 < η) :
    vectorNorm (u+v)^2 ≤ (1+η)*vectorNorm u^2+(1+η⁻¹)*vectorNorm v^2 := by
  have hh := (sq_le_sq₀ (vectorNorm_nonneg _) (add_nonneg (vectorNorm_nonneg u)
    (vectorNorm_nonneg v))).mpr (vectorNorm_add_le u v)
  have hy : 2*vectorNorm u*vectorNorm v ≤ η*vectorNorm u^2+η⁻¹*vectorNorm v^2 := by
    apply (mul_le_mul_iff_right₀ hη).mp
    have he : η⁻¹*η=1 := inv_mul_cancel₀ hη.ne'
    nlinarith [sq_nonneg (η*vectorNorm u-vectorNorm v)]
  nlinarith

theorem local_energy_pointwise {n : ℕ} (u v R g : Field n) {σ η ρ : ℝ}
    (hσ : 0 < σ) (hη : 0 < η) (hρ : 0 ≤ ρ)
    (hu : vectorNorm u ≤ ρ*sqrt (n:ℝ))
    (hv : vectorNorm v ≤ σ*vectorNorm g) (hg : g ∈ localGaussianBall n) :
    vectorNorm g^2/2-vectorNorm (u+v+R)^2/(2*σ^2) ≥
      -2*η*(n:ℝ)-(1+η⁻¹)*(ρ^2*(n:ℝ)+vectorNorm R^2)/σ^2 := by
  have hsσ : 0 < σ^2 := sq_pos_of_pos hσ
  have hu2 := (sq_le_sq₀ (vectorNorm_nonneg u) (by positivity)).mpr hu
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)] at hu2
  have hv2 := (sq_le_sq₀ (vectorNorm_nonneg v) (mul_nonneg hσ.le (vectorNorm_nonneg g))).mpr hv
  rw [mul_pow] at hv2
  have hUR := vectorNorm_add_sq_young u R (η := 1) (by norm_num)
  norm_num only [inv_one,one_add_one_eq_two] at hUR
  have hh := vectorNorm_add_sq_young v (u+R) hη
  have he : v+(u+R)=u+v+R := by abel
  rw [he] at hh
  have hpos : 0 ≤ 1+η⁻¹ := by positivity
  have hcombine : vectorNorm (u+v+R)^2 ≤ (1+η)*σ^2*vectorNorm g^2+
      2*(1+η⁻¹)*(ρ^2*(n:ℝ)+vectorNorm R^2) := by
    calc
      _ ≤ (1+η)*vectorNorm v^2+(1+η⁻¹)*(2*vectorNorm u^2+2*vectorNorm R^2) :=
        hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hUR hpos))
      _ ≤ (1+η)*(σ^2*vectorNorm g^2)+(1+η⁻¹)*(2*(ρ^2*(n:ℝ))+2*vectorNorm R^2) :=
        add_le_add (mul_le_mul_of_nonneg_left hv2 (by positivity))
          (mul_le_mul_of_nonneg_left (by linarith) hpos)
      _ = _ := by ring
  have hgn : vectorNorm g^2 ≤ 4*(n:ℝ) := by rw [vectorNorm_sq]; exact hg
  apply (mul_le_mul_iff_right₀ hsσ).mp
  have he1 : (-2*η*(n:ℝ)-(1+η⁻¹)*(ρ^2*(n:ℝ)+vectorNorm R^2)/σ^2)*σ^2=
      -2*η*(n:ℝ)*σ^2-(1+η⁻¹)*(ρ^2*(n:ℝ)+vectorNorm R^2) := by
    rw [sub_mul,div_mul_cancel₀ _ hsσ.ne']
  have he2 : (vectorNorm g^2/2-vectorNorm (u+v+R)^2/(2*σ^2))*σ^2=
      (σ^2*vectorNorm g^2-vectorNorm (u+v+R)^2)/2 := by
    field_simp
  rw [mul_comm (σ^2) _,mul_comm (σ^2) _,he1,he2]
  nlinarith [mul_le_mul_of_nonneg_left hgn (mul_nonneg hη.le hsσ.le)]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

lemma localGaussianBall_compact (n : ℕ) : IsCompact (localGaussianBall n) := by
  apply (isCompact_Icc : IsCompact (Icc (fun _ : Fin n => -2*sqrt (n:ℝ)) (fun _ : Fin n => 2*sqrt (n:ℝ)))).of_isClosed_subset
  · apply isClosed_le _ continuous_const
    unfold vectorSqNorm
    fun_prop
  · intro g hg
    have hb := localGaussianBall_norm hg
    have hc (i : Fin n) : |g i| ≤ 2*sqrt (n:ℝ) := by
      have hh := PiLp.norm_apply_le (WithLp.toLp 2 g) i
      exact (show |g i| ≤ vectorNorm g by simpa only [Real.norm_eq_abs,vectorNorm] using hh).trans hb
    exact ⟨fun i => by simpa only [neg_mul] using (abs_le.mp (hc i)).1,fun i => (abs_le.mp (hc i)).2⟩

lemma localGaussian_cond_integrable {n : ℕ} (hn : 0 < n) {f : Field n → ℝ}
    (hf : Continuous f) : Integrable f (cond (gaussianCoordinates (Fin n)) (localGaussianBall n)) := by
  exact (hf.continuousOn.integrableOn_compact (localGaussianBall_compact n)).smul_measure
    (ENNReal.inv_ne_top.mpr (localGaussianBall_ne_zero hn))

def localExponent {n : ℕ} (j σ : ℝ) (J U : Matrix (Fin n) (Fin n) ℝ) (h y g : Field n) : ℝ :=
  vectorNorm g^2/2-vectorNorm (tapField j J h (y+(σ • U)*ᵥg))^2/(2*σ^2)+
    (n:ℝ)*j*varianceAverage (y+(σ • U)*ᵥg)^2/2

lemma localExponent_continuous {n : ℕ} (j σ : ℝ) (J U : Matrix (Fin n) (Fin n) ℝ) (h y : Field n) :
    Continuous (localExponent j σ J U h y) := by
  have hb : Continuous (varianceAverage (n := n)) := by
    unfold varianceAverage
    exact continuous_const.sub (continuous_iff_continuousAt.mpr (fun y => (overlap_hasFDerivAt y).continuousAt))
  exact (((continuous_vectorNorm n).pow 2 |>.div_const 2).sub
    (((continuous_vectorNorm n).comp ((continuous_tapField j J h).comp (by fun_prop))).pow 2 |>.div_const _)).add
      (((hb.comp (by fun_prop)).pow 2 |>.const_mul ((n:ℝ)*j)).div_const 2)

lemma localGaussian_displacement {n : ℕ} {U : Matrix (Fin n) (Fin n) ℝ} {γ σ : ℝ}
    (_hγ : 0 < γ) (hσ : 0 ≤ σ)
    (hbound : ∀ g : Field n, vectorNorm (U*ᵥg) ≤ vectorNorm g/sqrt γ)
    {g : Field n} (hg : g ∈ localGaussianBall n) :
    vectorNorm ((σ • U)*ᵥg) ≤ (2*σ/sqrt γ)*sqrt (n:ℝ) := by
  rw [Matrix.smul_mulVec]
  change vectorNorm (fun i => σ*(U*ᵥg) i) ≤ _
  rw [vectorNorm_smul,abs_of_nonneg hσ]
  calc
    _ ≤ σ*(vectorNorm g/sqrt γ) := mul_le_mul_of_nonneg_left (hbound g) hσ
    _ ≤ σ*((2*sqrt (n:ℝ))/sqrt γ) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (localGaussianBall_norm hg) (sqrt_nonneg _)) hσ
    _ = _ := by ring

lemma localGaussian_variance_change {n : ℕ} (hn : 0 < n) (y : Field n)
    {U : Matrix (Fin n) (Fin n) ℝ} {γ σ : ℝ} (hγ : 0 < γ) (hσ : 0 ≤ σ)
    (hbound : ∀ g : Field n, vectorNorm (U*ᵥg) ≤ vectorNorm g/sqrt γ)
    {g : Field n} (hg : g ∈ localGaussianBall n) :
    |varianceAverage (y+(σ • U)*ᵥg)^2-varianceAverage y^2| ≤ 8*σ/sqrt γ := by
  have hn0 : sqrt (n:ℝ) ≠ 0 := by positivity
  calc
    _ ≤ 4/sqrt (n:ℝ)*vectorNorm ((σ • U)*ᵥg) := varianceAverage_sq_difference hn y _
    _ ≤ 4/sqrt (n:ℝ)*((2*σ/sqrt γ)*sqrt (n:ℝ)) := mul_le_mul_of_nonneg_left
      (localGaussian_displacement hγ hσ hbound hg) (by positivity)
    _ = _ := by field_simp; ring

theorem localGaussian_exponent_bound {n : ℕ} (hn : 0 < n) {j K γ σ η ρ : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (hγ : 0 < γ) (hσ : 0 < σ) (hη : 0 < η) (hρ : 0 ≤ ρ)
    (J U : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (h y : Field n)
    (hU : U.IsHermitian)
    (hbound : ∀ g : Field n, vectorNorm (U*ᵥg) ≤ vectorNorm g/sqrt γ)
    (hlin : ∀ g : Field n, vectorNorm ((fieldJacobian j J y)*ᵥ(U*ᵥg)) ≤ vectorNorm g)
    (hres : vectorNorm (tapField j J h y) ≤ ρ*sqrt (n:ℝ)) :
    (n:ℝ)*(j*varianceAverage y^2/2-2*η-
      (1+η⁻¹)*(ρ^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)-4*j*σ/sqrt γ) ≤
      ∫ g,localExponent j σ J U h y g
        ∂cond (gaussianCoordinates (Fin n)) (localGaussianBall n) := by
  let μ := cond (gaussianCoordinates (Fin n)) (localGaussianBall n)
  let : IsProbabilityMeasure μ := cond_isProbabilityMeasure (localGaussianBall_ne_zero hn)
  let R : Field n → Field n := fun g => tapField j J h (y+(σ • U)*ᵥg)-tapField j J h y-
    (fieldJacobian j J y)*ᵥ((σ • U)*ᵥg)
  have hiR : Integrable (fun g => vectorNorm (R g)^2) μ :=
    integrable_cond_of_integrable (localGaussianBall_ne_zero hn)
      (tap_remainder_sq_integrable hn hj hK J hJ h y _)
  have hR := localGaussian_remainder_cond hn hj hK J hJ h y hU hγ hbound (σ := σ)
  change (∫ g,vectorNorm (R g)^2 ∂μ) ≤ _ at hR
  let f : Field n → ℝ := fun g => (n:ℝ)*j*varianceAverage y^2/2-2*η*(n:ℝ)-
    (1+η⁻¹)*(ρ^2*(n:ℝ)+vectorNorm (R g)^2)/σ^2-4*(n:ℝ)*j*σ/sqrt γ
  have hif : Integrable f μ := by
    exact (((integrable_const _).sub (integrable_const _)).sub
      (((integrable_const _).add hiR).const_mul _ |>.div_const _)).sub (integrable_const _)
  have hmono : (∫ g,f g ∂μ) ≤ ∫ g,localExponent j σ J U h y g ∂μ := by
    apply integral_mono_ae hif (localGaussian_cond_integrable hn (localExponent_continuous _ _ _ _ _ _))
    apply ae_cond_of_forall_mem (localGaussianBall_measurable n)
    intro g hg
    let v := (fieldJacobian j J y)*ᵥ((σ • U)*ᵥg)
    have hv : vectorNorm v ≤ σ*vectorNorm g := by
      dsimp [v]
      rw [Matrix.smul_mulVec,Matrix.mulVec_smul]
      change vectorNorm (fun i => σ*((fieldJacobian j J y)*ᵥ(U*ᵥg)) i) ≤ _
      rw [vectorNorm_smul,abs_of_pos hσ]
      exact mul_le_mul_of_nonneg_left (hlin g) hσ.le
    have hh := local_energy_pointwise (tapField j J h y) v (R g) g hσ hη hρ hres hv hg
    have he : tapField j J h y+v+R g=tapField j J h (y+(σ • U)*ᵥg) := by dsimp [v,R]; abel
    rw [he] at hh
    have hb := (abs_le.mp (localGaussian_variance_change hn y hγ hσ.le hbound hg)).1
    have hbj := mul_le_mul_of_nonneg_left hb (show 0 ≤ (n:ℝ)*j/2 by positivity)
    dsimp [f,localExponent]
    ring_nf at hh hbj ⊢
    linarith only [hh,hbj]
  have he : (∫ g,f g ∂μ)=(n:ℝ)*j*varianceAverage y^2/2-2*η*(n:ℝ)-
      (1+η⁻¹)*(ρ^2*(n:ℝ)+∫ g,vectorNorm (R g)^2 ∂μ)/σ^2-4*(n:ℝ)*j*σ/sqrt γ := by
    have hfEq : f=fun g => ((n:ℝ)*j*varianceAverage y^2/2-2*η*(n:ℝ)-
        (1+η⁻¹)*ρ^2*(n:ℝ)/σ^2-4*(n:ℝ)*j*σ/sqrt γ)-
        ((1+η⁻¹)/σ^2)*vectorNorm (R g)^2 := by
      funext g
      dsimp [f]
      ring
    rw [hfEq,integral_sub (integrable_const _) (hiR.const_mul _),integral_const_mul]
    simp only [integral_const,probReal_univ,one_smul]
    ring
  rw [he] at hmono
  apply le_trans ?_ hmono
  have hh := mul_le_mul_of_nonneg_left hR (show 0 ≤ (1+η⁻¹)/σ^2 by positivity)
  have hsσ : σ ≠ 0 := hσ.ne'
  have heq : (1+η⁻¹)*(ρ^2*(n:ℝ)+6*(8*(j+K)^2+128*j^2)*(n:ℝ)*σ^4/γ^2)/σ^2=
      (n:ℝ)*(1+η⁻¹)*(ρ^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2) := by
    field_simp
  ring_nf at hh heq ⊢
  linarith only [hh,heq]

theorem localGaussian_jensen {n : ℕ} (hn : 0 < n) (j σ : ℝ)
    (J U : Matrix (Fin n) (Fin n) ℝ) (h y : Field n) :
    exp (∫ g,localExponent j σ J U h y g ∂cond (gaussianCoordinates (Fin n)) (localGaussianBall n)) ≤
      ∫ g,exp (localExponent j σ J U h y g) ∂cond (gaussianCoordinates (Fin n)) (localGaussianBall n) := by
  let := cond_isProbabilityMeasure (localGaussianBall_ne_zero hn)
  exact convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => mem_univ _))
    (localGaussian_cond_integrable hn (localExponent_continuous _ _ _ _ _ _))
    (localGaussian_cond_integrable hn (continuous_exp.comp (localExponent_continuous _ _ _ _ _ _)))

end SKGap
end
end

end OAI
