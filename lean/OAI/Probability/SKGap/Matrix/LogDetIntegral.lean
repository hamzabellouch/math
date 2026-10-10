import Mathlib
import OAI.Probability.SKGap.Localization.Bilinear2
import OAI.Probability.SKGap.Matrix.RegularizedLogDet
import OAI.Probability.SKGap.Brownian.LogDetPath

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def logPathGood (R lo hi q : ℝ) (a : ι → ℝ) : Set (Matrix ι ι ℝ) :=
  {M | opNorm M ≤ R ∧ ∀ z ∈ Icc (0:ℝ) 1,
    lo ≤ ComplexSpectral.lowerRayleigh (liftMatrix (1-pathDiagonal a z*(M-pathShift z q)*pathDiagonal a z)) ∧
    -hi ≤ ComplexSpectral.lowerRayleigh (-liftMatrix (1-pathDiagonal a z*(M-pathShift z q)*pathDiagonal a z))}

lemma logPathGood_isClosed (R lo hi q : ℝ) (a : ι → ℝ) :
    IsClosed (logPathGood R lo hi q a) := by
  have hc (z : ℝ) : Continuous (fun M : Matrix ι ι ℝ => liftMatrix (1-pathDiagonal a z*(M-pathShift z q)*pathDiagonal a z)) := by
    dsimp only [liftMatrix]; fun_prop
  have hl (z : ℝ) := isClosed_le (continuous_const (y := lo)) (ComplexSpectral.continuous_lowerRayleigh.comp (hc z))
  have hu (z : ℝ) := isClosed_le (continuous_const (y := -hi)) (ComplexSpectral.continuous_lowerRayleigh.comp (hc z).neg)
  change IsClosed ({M | opNorm M ≤ R} ∩ {M | ∀ z ∈ Icc (0:ℝ) 1, _})
  apply (isClosed_le continuous_realOpNorm continuous_const).inter
  simp only [ofPred_forall]
  exact isClosed_iInter (fun z => isClosed_iInter (fun _ => (hl z).inter (hu z)))

lemma logPathGood_exponential [Nonempty ι] {j A : ℝ} {a : ι → ℝ}
    (hj : 0 < j) (hA : 0 < A) (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
    (hs : sqrt j*A < 1)
    (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) ≤ (1-sqrt j*A)^2/4) :
    (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      {g | goeMatrix (j/(Fintype.card ι:ℝ)) g ∉
        logPathGood (2*sqrt j+1+1) ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A))
          ((j/(Fintype.card ι:ℝ))*∑ b,a b) a} ≤ 3*Real.exp (-pathRate j A*(Fintype.card ι:ℝ)) := by
  apply (measureReal_mono (s₂ := {g | ∃ z ∈ Icc (0:ℝ) 1, g ∉ truncationGoodSet (j/(Fintype.card ι:ℝ))
        (2*sqrt j+1+1) ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A))
        (pathDiagonal a z) (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b,a b))}) ?_ (measure_ne_top _ _)).trans
    (path_all_good_exponential hj hA ha haA hs herr)
  intro g hg
  by_contra hcontra
  change ¬(∃ z ∈ Icc (0:ℝ) 1, _) at hcontra
  push Not at hcontra
  apply hg
  constructor
  · exact (hcontra 0 (by constructor <;> norm_num)).1.le
  · intro z hz
    exact ⟨(hcontra z hz).2.1.le,(hcontra z hz).2.2.le⟩

lemma logdetPath_integral [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Icc lo hi, f x=(x:ℂ)⁻¹) {R : ℝ} (hR : 0 ≤ R)
    (j : ℝ) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (M : Matrix ι ι ℝ) (hM : Mᵀ=M)
    (hg : M ∈ logPathGood R lo hi ((j/(Fintype.card ι:ℝ))*∑ b,a b) a) :
    (∫ z in (0:ℝ)..1, logPathCutoffDerivative f R hR j a M z)=
      log (logPath ((j/(Fintype.card ι:ℝ))*∑ b,a b) a M 1).det/(Fintype.card ι:ℝ) := by
  have hc : Continuous (fun z => logPathCutoffDerivative f R hR j a M z) :=
    (continuous_logPathCutoffDerivative f hR j a).comp (continuous_id.prodMk continuous_const)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun z => log (logPath ((j/(Fintype.card ι:ℝ))*∑ b,a b) a M z).det/(Fintype.card ι:ℝ))
    (f' := fun z => logPathCutoffDerivative f R hR j a M z)
    (fun z hz => ?_) (hc.intervalIntegrable 0 1)
  · simpa only [logPath,zero_pow (by norm_num : 2 ≠ 0),zero_mul,zero_smul,add_zero,
      sub_zero,Matrix.det_one,log_one,zero_div] using hh
  · have hz' : z ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hz
    obtain ⟨hunit,hagree⟩ := pathK_agrees_at f hlo hf hR j ha hz'.1 M hM hg.1 (hg.2 z hz').1 (hg.2 z hz').2
    have hd := (LogDet.hasDerivAt_logdet (hasDerivAt_logPath ((j/(Fintype.card ι:ℝ))*∑ b,a b) a M z) hunit).div_const (Fintype.card ι:ℝ)
    rw [logPath_trace_derivative,← hagree] at hd
    simpa only [logPathCutoffDerivative,realProject_eq_self hR M hM hg.1] using hd

lemma trace_abs_le_card_opNorm (M : Matrix ι ι ℝ) : |M.trace| ≤ (Fintype.card ι:ℝ)*opNorm M := by
  unfold Matrix.trace Matrix.diag
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => matrix_entry_le_opNorm M i i))

lemma logPathCutoffDerivative_bound [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j : ℝ} (hR : 0 ≤ R) (hj : 0 ≤ j)
    {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ 1) {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1)
    (M : Matrix ι ι ℝ) :
    |logPathCutoffDerivative f R hR j a M z| ≤ (2*j+R)*pathBound f R j 1 := by
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hB := (path_constants_nonneg f hR hj (by norm_num : (0:ℝ)≤1)).1
  have hq := diagonal_mean_bounds hj ha haA
  simp only [mul_one] at hq
  have hK := (pathK_bounds f hR hj (by norm_num : (0:ℝ)≤1) ha haA hz).1 M
  have hD : opNorm (diagonal a) ≤ 1 := opNorm_diagonal_le (by norm_num) (fun i => by rw [abs_of_nonneg (ha i)]; exact haA i)
  have hKD : opNorm (pathK f R hR j a z M*diagonal a) ≤ pathBound f R j 1 :=
    (opNorm_mul _ _).trans (by simpa only [mul_one] using mul_le_mul hK hD (norm_nonneg _) hB)
  have hWKD : opNorm (realProject R hR M*pathK f R hR j a z M*diagonal a) ≤ R*pathBound f R j 1 := by
    rw [mul_assoc]
    exact (opNorm_mul _ _).trans (mul_le_mul (realProject_opNorm hR M) hKD (norm_nonneg _) hR)
  have ht₁ := (trace_abs_le_card_opNorm _).trans (mul_le_mul_of_nonneg_left hKD hn.le)
  have ht₂ := (trace_abs_le_card_opNorm _).trans (mul_le_mul_of_nonneg_left hWKD hn.le)
  have hzq : |2*z*((j/(Fintype.card ι:ℝ))*∑ b,a b)| ≤ 2*j := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hz.1) hq.1)]
    nlinarith [mul_le_mul hz.2 hq.2 hq.1 (by norm_num : (0:ℝ)≤1)]
  unfold logPathCutoffDerivative
  rw [abs_div,abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  have hterm : |(2*z*((j/(Fintype.card ι:ℝ))*∑ b,a b))*(pathK f R hR j a z M*diagonal a).trace| ≤
      2*j*((Fintype.card ι:ℝ)*pathBound f R j 1) := by
    rw [abs_mul]
    exact mul_le_mul hzq ht₁ (abs_nonneg _) (by positivity)
  have hh := (abs_sub (2*z*((j/(Fintype.card ι:ℝ))*∑ b,a b)*(pathK f R hR j a z M*diagonal a).trace)
    (realProject R hR M*pathK f R hR j a z M*diagonal a).trace).trans (add_le_add hterm ht₂)
  exact hh.trans_eq (by ring)
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma frobenius_le_sum_abs (M : Matrix ι ι ℝ) : ‖M‖ ≤ ∑ i,∑ k,|M i k| := by
  apply (sq_le_sq₀ (norm_nonneg M) (by positivity : 0 ≤ ∑ i,∑ k,|M i k|)).mp
  rw [frobenius_sq]
  calc
    _ ≤ ∑ i,(∑ k,|M i k|)^2 := Finset.sum_le_sum (fun i _ => by
      simpa only [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun k _ => abs_nonneg (M i k)))
    _ ≤ (∑ i,∑ k,|M i k|)^2 := Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => by positivity)

lemma frobenius_one : ‖(1:Matrix ι ι ℝ)‖=sqrt (Fintype.card ι:ℝ) := by
  have hs := LogDet.frobenius_sq_trace (1:Matrix ι ι ℝ)
  simp only [transpose_one,one_mul,Matrix.trace_one] at hs
  nlinarith [norm_nonneg (1:Matrix ι ι ℝ),sqrt_nonneg (Fintype.card ι:ℝ),sq_sqrt (Nat.cast_nonneg (Fintype.card ι))]

lemma logPath_one_frobenius [Nonempty ι] {j : ℝ} (hj : 0 ≤ j)
    {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) (M : Matrix ι ι ℝ) :
    ‖logPath ((j/(Fintype.card ι:ℝ))*∑ i,a i) a M 1‖ ≤ sqrt (Fintype.card ι:ℝ)*(1+j)+‖M‖ := by
  have hq := diagonal_mean_bounds hj ha ha1
  simp only [mul_one] at hq
  have hD : opNorm (diagonal a) ≤ 1 := opNorm_diagonal_le (by norm_num) (fun i => by rw [abs_of_nonneg (ha i)]; exact ha1 i)
  have hDn := (LogDet.frobenius_le_sqrt_card_opNorm (diagonal a)).trans
    (mul_le_mul_of_nonneg_left hD (sqrt_nonneg _))
  simp only [mul_one] at hDn
  have hDM := (frobenius_mul_le_opNorm (diagonal a) M).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg M))
  simp only [one_mul] at hDM
  simp only [logPath,one_pow,one_mul,one_smul]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_add_le _ _) hDM).trans
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hq.1,frobenius_one]
  have hh := mul_le_mul hq.2 hDn (norm_nonneg _) hj
  nlinarith

lemma logPath_one_lipschitz {j : ℝ} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) :
    LipschitzWith 1 (fun M : Matrix ι ι ℝ => logPath ((j/(Fintype.card ι:ℝ))*∑ i,a i) a M 1) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  simp only [dist_eq_norm,NNReal.coe_one,one_mul]
  have he : logPath ((j/(Fintype.card ι:ℝ))*∑ i,a i) a M 1-
      logPath ((j/(Fintype.card ι:ℝ))*∑ i,a i) a N 1= -(diagonal a*(M-N)) := by
    simp only [logPath,one_pow,one_mul,one_smul,Matrix.mul_sub]; abel
  rw [he,norm_neg]
  have hD : opNorm (diagonal a) ≤ 1 := opNorm_diagonal_le (by norm_num) (fun i => by rw [abs_of_nonneg (ha i)]; exact ha1 i)
  exact (frobenius_mul_le_opNorm _ _).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hD (norm_nonneg (M-N)))

lemma logPath_regularized_integrable [Nonempty ι] {j γ : ℝ} (hγ : 0 < γ)
    {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) :
    Integrable (fun g => LogDet.regularizedLogDet γ (logPath ((j/(Fintype.card ι:ℝ))*∑ i,a i) a
      (goeMatrix (j/(Fintype.card ι:ℝ)) g) 1))
      (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) := by
  have hF : LipschitzWith ⟨1/sqrt ((Fintype.card ι:ℝ)*γ),by positivity⟩ (LogDet.regularizedLogDet γ : Matrix ι ι ℝ → ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro M N
    change |LogDet.regularizedLogDet γ M-LogDet.regularizedLogDet γ N| ≤ (1/sqrt ((Fintype.card ι:ℝ)*γ))*‖M-N‖
    exact LogDet.regularizedLogDet_lipschitz hγ M N
  exact gaussianProduct_integrable_lipschitz (hF.comp ((logPath_one_lipschitz ha ha1).comp (goeMatrix_L2_lipschitz _)))

lemma logPath_regularized_rare [Nonempty ι] {j γ : ℝ} (hj : 0 ≤ j) (hγ : 0 < γ)
    {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    {s : Set (MatrixCoordinates ι → ℝ)} (hs : MeasurableSet s) :
    (∫ g in s, |LogDet.regularizedLogDet γ (logPath ((j/(Fintype.card ι:ℝ))*∑ i,a i) a
      (goeMatrix (j/(Fintype.card ι:ℝ)) g) 1)|
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) ≤
      (|log γ|+sqrt (Fintype.card ι:ℝ)*(1+j)/sqrt ((Fintype.card ι:ℝ)*γ))*
        (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real s+
      (Fintype.card ι:ℝ)^2*sqrt (2*j/(Fintype.card ι:ℝ))/sqrt ((Fintype.card ι:ℝ)*γ)*
        sqrt ((Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real s) := by
  let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
  let r := j/(Fintype.card ι:ℝ)
  have hentry (i k : ι) : Integrable (fun g => |goeMatrix r g i k|) μ :=
    ((goeEntry_memLp r i k).integrable (by norm_num)).abs
  have hsum : Integrable (fun g => ∑ i,∑ k,|goeMatrix r g i k|) μ :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hentry i k))
  have hpoint (g) : |LogDet.regularizedLogDet γ (logPath ((j/(Fintype.card ι:ℝ))*∑ i,a i) a (goeMatrix r g) 1)| ≤
      (|log γ|+sqrt (Fintype.card ι:ℝ)*(1+j)/sqrt ((Fintype.card ι:ℝ)*γ))+
        (∑ i,∑ k,|goeMatrix r g i k|)/sqrt ((Fintype.card ι:ℝ)*γ) := by
    apply (LogDet.regularizedLogDet_abs hγ _).trans
    have hh := (logPath_one_frobenius hj ha ha1 (goeMatrix r g)).trans (add_le_add_right (frobenius_le_sum_abs _) _)
    have ht := add_le_add_right (div_le_div_of_nonneg_right hh (sqrt_nonneg ((Fintype.card ι:ℝ)*γ))) |log γ|
    exact ht.trans_eq (by ring)
  have hm := integral_mono (μ := μ.restrict s) (logPath_regularized_integrable hγ ha ha1).abs.integrableOn
    ((integrable_const _).add (hsum.div_const _)).integrableOn hpoint
  simp only [Pi.add_apply] at hm
  rw [integral_add (integrable_const (|log γ|+sqrt (Fintype.card ι:ℝ)*(1+j)/sqrt ((Fintype.card ι:ℝ)*γ)))
      (hsum.div_const (sqrt ((Fintype.card ι:ℝ)*γ))).integrableOn,integral_const,smul_eq_mul,
    measureReal_restrict_apply_univ,integral_div] at hm
  have hsumle : (∫ g in s, (∑ i,∑ k,|goeMatrix r g i k|) ∂μ) ≤
      (Fintype.card ι:ℝ)^2*sqrt (2*j/(Fintype.card ι:ℝ))*sqrt (μ.real s) := by
    rw [integral_finsetSum _ (fun i _ => (integrable_finsetSum _ (fun k _ => hentry i k)).integrableOn)]
    simp_rw [integral_finsetSum _ (fun k _ => (hentry _ k).integrableOn)]
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ => Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
      (integral_abs_on_set_le (goeEntry_memLp r i k) hs).trans (mul_le_mul_of_nonneg_right
        (sqrt_le_sqrt (goeEntry_integral_sq_le (by dsimp [r]; positivity) i k)) (sqrt_nonneg _))))
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at ht
    exact ht.trans_eq (by
      dsimp only [r,μ]
      rw [show 2*(j/(Fintype.card ι:ℝ))=2*j/(Fintype.card ι:ℝ) by ring]
      ring)
  apply hm.trans
  have hh := div_le_div_of_nonneg_right hsumle (sqrt_nonneg ((Fintype.card ι:ℝ)*γ))
  exact (add_le_add_right hh (μ.real s*(|log γ|+sqrt (Fintype.card ι:ℝ)*(1+j)/sqrt ((Fintype.card ι:ℝ)*γ)))).trans_eq (by ring)
end SKGap

namespace SKGap
open MeasureTheory Real Set
lemma expectation_upper_good {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F I : Ω → ℝ} {s : Set Ω} (hs : MeasurableSet s) (hF : Integrable F μ) (hI : Integrable I μ)
    {D c : ℝ} (hc : 0 ≤ c) (hD : ∀ x, |I x| ≤ D)
    (hgood : ∀ x ∉ s, F x ≤ 2*I x+c) :
    (∫ x, F x ∂μ) ≤ 2*(∫ x, I x ∂μ)+c+(∫ x in s, |F x| ∂μ)+2*D*μ.real s := by
  have hi : Integrable (fun x => 2*I x+c+s.indicator (fun x => |F x|+2*D) x) μ :=
    ((hI.const_mul 2).add (integrable_const c)).add ((hF.abs.add (integrable_const (2*D))).indicator hs)
  have hp (x) : F x ≤ 2*I x+c+s.indicator (fun x => |F x|+2*D) x := by
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx]
      have hh := (abs_le.mp (hD x)).1
      nlinarith [le_abs_self (F x)]
    · simpa only [Set.indicator_of_notMem hx,add_zero] using hgood x hx
  have hh := integral_mono hF hi hp
  have hi₁ : Integrable (fun x => 2*I x+c) μ := (hI.const_mul 2).add (integrable_const c)
  have hi₂ : Integrable (s.indicator (fun x => |F x|+2*D)) μ := (hF.abs.add (integrable_const (2*D))).indicator hs
  rw [integral_add hi₁ hi₂,integral_add (hI.const_mul 2) (integrable_const c),
    integral_const_mul,integral_indicator hs,integral_add hF.abs.integrableOn (integrable_const (2*D)),
    integral_const,integral_const] at hh
  simpa only [probReal_univ,mul_one,smul_eq_mul,measureReal_restrict_apply_univ,one_mul,mul_comm,add_assoc] using hh
end SKGap
end
end

end OAI
