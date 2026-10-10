import Mathlib
import OAI.Probability.SKGap.Localization.ResidualSelection

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal ContDiff
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

def residualScalarCutoff (u : ℝ) : ℝ :=
  Real.smoothTransition ((1-u)*4/3)*Real.smoothTransition ((1+u)*4/3)

lemma residualScalarCutoff_bounds (u : ℝ) :
    0≤residualScalarCutoff u ∧ residualScalarCutoff u≤1 := by
  refine ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),?_⟩
  exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) (by norm_num)).trans_eq (by simp)

lemma residualScalarCutoff_one {u : ℝ} (h0 : 0≤u) (h1 : u≤1/4) :
    residualScalarCutoff u=1 := by
  simp only [residualScalarCutoff,Real.smoothTransition.one_of_one_le (by linarith : 1≤(1-u)*4/3),
    Real.smoothTransition.one_of_one_le (by linarith : 1≤(1+u)*4/3),one_mul]

lemma residualScalarCutoff_zero {u : ℝ} (hu : 1≤u) : residualScalarCutoff u=0 := by
  simp [residualScalarCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : (1-u)*4/3≤0)]

lemma residualScalarCutoff_smooth : ContDiff ℝ ∞ residualScalarCutoff := by
  unfold residualScalarCutoff
  fun_prop

lemma residualScalarCutoff_lipschitz : ∃K,LipschitzWith K residualScalarCutoff := by
  have hc : HasCompactSupport residualScalarCutoff := by
    apply HasCompactSupport.intro' (K:=Set.Icc (-1:ℝ) 1) isCompact_Icc isClosed_Icc
    intro x hx
    simp only [Set.mem_Icc,not_and_or,not_le] at hx
    rcases hx with hx|hx
    · simp [residualScalarCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : (1+x)*4/3≤0)]
    · exact residualScalarCutoff_zero hx.le
  exact ContDiff.lipschitzWith_of_hasCompactSupport hc residualScalarCutoff_smooth (by simp)

lemma norm_derivativeVector_sq (f : Spin n→ℝ) (x : Spin n) :
    ‖derivativeVector f x‖^2=∑i,(halfDiff i f x)^2 := by
  exact vectorNorm_sq (fun i=>halfDiff i f x)

lemma derivativeVector_norm_mono (f g : Spin n→ℝ) (x : Spin n) {C : ℝ} (hC : 0≤C)
    (h : ∀i,|halfDiff i f x|≤C*|halfDiff i g x|) :
    ‖derivativeVector f x‖≤C*‖derivativeVector g x‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simp only [←sq,mul_pow,norm_derivativeVector_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [sq_abs,mul_pow] using pow_le_pow_left₀ (abs_nonneg _) (h i) 2

lemma derivativeVector_comp_lipschitz {φ : ℝ→ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ)
    (f : Spin n→ℝ) (x : Spin n) :
    ‖derivativeVector (fun x=>φ (f x)) x‖≤(K:ℝ)*‖derivativeVector f x‖ := by
  apply derivativeVector_norm_mono _ _ _ K.coe_nonneg
  intro i
  have h:=hφ.dist_le_mul (f (replace x i true)) (f (replace x i false))
  simpa only [halfDiff,abs_div,Real.dist_eq,abs_of_pos (by norm_num : (0:ℝ)<2),mul_div_assoc] using
    div_le_div_of_nonneg_right h (by norm_num : (0:ℝ)≤2)

lemma derivativeVector_scale (c : ℝ) (f : Spin n→ℝ) (x : Spin n) :
    derivativeVector (fun y=>c*f y) x=c • derivativeVector f x := by
  ext i
  simp only [derivativeVector,WithLp.ofLp_toLp,PiLp.smul_apply,smul_eq_mul,halfDiff]
  ring

lemma residualEnergy_as_pair (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    residualEnergy j J h k x =
      (Real.sqrt (n:ℝ))⁻¹*normalizedPair (residual j J h k) (residual j J h k) x := by
  simp only [residualEnergy,vectorNorm_sq,normalizedPair,vectorPair]
  simp only [inv_mul_eq_div,div_div,Real.mul_self_sqrt (Nat.cast_nonneg n),sq]

lemma residualEnergy_gradient (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (k : ℕ) (x : Spin n) {A : ℝ} (hA : 0≤A)
    (hd : SKGap.opNorm (derivativeMatrix (residual j J h k) x)≤A) :
    ‖derivativeVector (residualEnergy j J h k) x‖≤(4*A+2*A^2)/Real.sqrt (n:ℝ) := by
  have he : residualEnergy j J h k=fun y=>(Real.sqrt (n:ℝ))⁻¹*
      normalizedPair (residual j J h k) (residual j J h k) y := funext (residualEnergy_as_pair j J h k)
  rw [he,derivativeVector_scale,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hb:=normalizedPair_derivative_bound hn (residual j J h k) (residual j J h k) x hA hA hd hd
    (residual_vectorNorm j J h k x) (residual_vectorNorm j J h k x)
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans_eq (by ring)

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators NNReal
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

def residualStepCutoff (ρ j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) : ℝ :=
  residualScalarCutoff (residualEnergy j J h k x/ρ^2)

def residualCutoff (ρ j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) : ℝ :=
  residualStepCutoff ρ j J h k x*residualStepCutoff ρ j J h (k+1) x

lemma residualStepCutoff_bounds (ρ j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    0≤residualStepCutoff ρ j J h k x ∧ residualStepCutoff ρ j J h k x≤1 := residualScalarCutoff_bounds _
lemma residualCutoff_bounds (ρ j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    0≤residualCutoff ρ j J h k x ∧ residualCutoff ρ j J h k x≤1 := by
  have h0:=residualStepCutoff_bounds ρ j J h k x
  have h1:=residualStepCutoff_bounds ρ j J h (k+1) x
  exact ⟨mul_nonneg h0.1 h1.1,(mul_le_mul h0.2 h1.2 h1.1 (by norm_num)).trans_eq (by simp)⟩

lemma residualStepCutoff_support (hn : 0<n) {ρ j : ℝ} (hρ : 0<ρ)
    (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n)
    (hc : residualStepCutoff ρ j J h k x≠0) :
    vectorNorm (residual j J h k x)≤ρ*Real.sqrt (n:ℝ) := by
  have hr : residualEnergy j J h k x/ρ^2<1 :=
    lt_of_not_ge (fun hh=>hc (residualScalarCutoff_zero hh))
  have he : residualEnergy j J h k x≤ρ^2 := by
    exact ((div_lt_one (sq_pos_of_pos hρ)).mp hr).le
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simp only [←sq,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
  exact (div_le_iff₀ (Nat.cast_pos.mpr hn)).mp he

lemma residualCutoff_support (hn : 0<n) {ρ j : ℝ} (hρ : 0<ρ)
    (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n)
    (hc : residualCutoff ρ j J h k x≠0) :
    vectorNorm (residual j J h k x)≤ρ*Real.sqrt (n:ℝ) ∧
    vectorNorm (residual j J h (k+1) x)≤ρ*Real.sqrt (n:ℝ) := by
  have H:=mul_ne_zero_iff.mp hc
  exact ⟨residualStepCutoff_support hn hρ J h k x H.1,residualStepCutoff_support hn hρ J h (k+1) x H.2⟩

lemma residualStepCutoff_one (hn : 0<n) {ρ j : ℝ} (hρ : 0<ρ)
    (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n)
    (hk : vectorNorm (residual j J h k x)≤ρ*Real.sqrt (n:ℝ)/2) :
    residualStepCutoff ρ j J h k x=1 := by
  apply residualScalarCutoff_one (div_nonneg (residualEnergy_nonneg j J h k x) (sq_nonneg _))
  rw [residualEnergy,div_div]
  apply (div_le_iff₀ (mul_pos (Nat.cast_pos.mpr hn) (sq_pos_of_pos hρ))).mpr
  have hh:=pow_le_pow_left₀ (vectorNorm_nonneg _) hk 2
  simp only [div_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)] at hh
  nlinarith

lemma residualCutoff_one (hn : 0<n) {ρ j : ℝ} (hρ : 0<ρ)
    (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n)
    (h0 : vectorNorm (residual j J h k x)≤ρ*Real.sqrt (n:ℝ)/2)
    (h1 : vectorNorm (residual j J h (k+1) x)≤ρ*Real.sqrt (n:ℝ)/2) :
    residualCutoff ρ j J h k x=1 := by
  simp only [residualCutoff,residualStepCutoff_one hn hρ J h k x h0,
    residualStepCutoff_one hn hρ J h (k+1) x h1,one_mul]

lemma derivativeVector_mul_bound (f g : Spin n→ℝ) (x : Spin n)
    (hf : ∀x,|f x|≤1) (hg : ∀x,|g x|≤1) {A B : ℝ}
    (hA : 0≤A) (hB : 0≤B)
    (hdF : ‖derivativeVector f x‖≤A) (hdG : ‖derivativeVector g x‖≤B) :
    ‖derivativeVector (fun y=>f y*g y) x‖≤2*(A+B) := by
  have ht (i : Fin n) : (halfDiff i (fun y=>f y*g y) x)^2≤
      2*(halfDiff i f x)^2+2*(halfDiff i g x)^2 := by
    have hf' : (f (flip x i))^2≤1 := by simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hf (flip x i)) 2
    have hg' : (g x)^2≤1 := by simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hg x) 2
    rw [halfDiff_mul_flipped]
    nlinarith [mul_le_mul_of_nonneg_right hf' (sq_nonneg (halfDiff i g x)),
      mul_le_mul_of_nonneg_right hg' (sq_nonneg (halfDiff i f x)),
      sq_nonneg (f (flip x i)*halfDiff i g x-g x*halfDiff i f x)]
  have hb : ‖derivativeVector (fun y=>f y*g y) x‖^2≤2*A^2+2*B^2 := by
    calc
      _ ≤ ∑i,(2*(halfDiff i f x)^2+2*(halfDiff i g x)^2) := by
        rw [norm_derivativeVector_sq]; exact Finset.sum_le_sum (fun i _=>ht i)
      _ = 2*‖derivativeVector f x‖^2+2*‖derivativeVector g x‖^2 := by
        simp only [norm_derivativeVector_sq,Finset.sum_add_distrib,Finset.mul_sum]
      _ ≤ _ := by nlinarith [pow_le_pow_left₀ (norm_nonneg _) hdF 2,pow_le_pow_left₀ (norm_nonneg _) hdG 2]
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simp only [←sq]
  nlinarith [mul_nonneg hA hB,sq_nonneg A,sq_nonneg B]

lemma residualStepCutoff_gradient (hn : 0<n) {j ρ : ℝ} (_ : 0<ρ)
    {K : ℝ≥0} (hK : LipschitzWith K residualScalarCutoff)
    (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) {A : ℝ} (hA : 0≤A)
    (hd : SKGap.opNorm (derivativeMatrix (residual j J h k) x)≤A) :
    ‖derivativeVector (residualStepCutoff ρ j J h k) x‖≤
      (K:ℝ)/ρ^2*(4*A+2*A^2)/Real.sqrt (n:ℝ) := by
  apply (derivativeVector_comp_lipschitz hK (fun y=>residualEnergy j J h k y/ρ^2) x).trans
  have he : (fun y=>residualEnergy j J h k y/ρ^2)=fun y=>(ρ^2)⁻¹*residualEnergy j J h k y := by
    funext y; ring
  rw [he,derivativeVector_scale,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (residualEnergy_gradient hn j J h k x hA hd) (inv_nonneg.mpr (sq_nonneg _))) K.coe_nonneg).trans_eq (by ring)

lemma residualCutoff_gradient (hn : 0<n) {j ρ : ℝ} (hρ : 0<ρ)
    {K : ℝ≥0} (hK : LipschitzWith K residualScalarCutoff)
    (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (h0 : SKGap.opNorm (derivativeMatrix (residual j J h k) x)≤A)
    (h1 : SKGap.opNorm (derivativeMatrix (residual j J h (k+1)) x)≤B) :
    ‖derivativeVector (residualCutoff ρ j J h k) x‖≤
      (2*(K:ℝ)/ρ^2*((4*A+2*A^2)+(4*B+2*B^2)))/Real.sqrt (n:ℝ) := by
  apply (derivativeVector_mul_bound _ _ x
    (fun y=>by rw [abs_of_nonneg (residualStepCutoff_bounds ρ j J h k y).1];exact (residualStepCutoff_bounds ρ j J h k y).2)
    (fun y=>by rw [abs_of_nonneg (residualStepCutoff_bounds ρ j J h (k+1) y).1];exact (residualStepCutoff_bounds ρ j J h (k+1) y).2)
    (by positivity) (by positivity)
    (residualStepCutoff_gradient hn hρ hK J h k x hA h0)
    (residualStepCutoff_gradient hn hρ hK J h (k+1) x hB h1)).trans_eq
  ring

end SKGapCutoff.Recipe

end
end

end OAI
