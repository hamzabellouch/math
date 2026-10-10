import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open InnerProductSpace Laplacian
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma radial_fderiv {f g : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (g t) t) (x : E) :
    fderiv ℝ (fun y : E => f (‖y‖^2)) x = (2*g (‖x‖^2)) • innerSL ℝ x := by
  have h := (hf (‖x‖^2)).comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  apply h.fderiv.trans
  ext v
  simp [two_smul,smul_eq_mul,innerSL_apply_apply]
  ring

lemma radial_second {f g h : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, HasDerivAt g (h t) t)
    (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y : E => f (‖y‖^2))) x v w =
      4*h (‖x‖^2)*⟪x,v⟫*⟪x,w⟫ + 2*g (‖x‖^2)*⟪v,w⟫ := by
  have he : fderiv ℝ (fun y : E => f (‖y‖^2)) =
      (fun y : E => (2*g (‖y‖^2)) • innerSL ℝ y) := funext (radial_fderiv hf)
  rw [he]
  have hd := (((hg (‖x‖^2)).comp_hasFDerivAt x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul 2).smul
      ((innerSL ℝ (E := E)).hasFDerivAt (x := x))
  have he' := congrArg (fun T : E →L[ℝ] E →L[ℝ] ℝ => T v w) hd.fderiv
  dsimp only [Pi.smul_apply,Function.comp_apply] at he'
  apply he'.trans
  simp [two_smul,smul_eq_mul,innerSL]
  ring

lemma radial_laplacian [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {f g h : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, HasDerivAt g (h t) t)
    (x : E) :
    Δ (fun y : E => f (‖y‖^2)) x =
      4*‖x‖^2*h (‖x‖^2) + 2*(Fintype.card ι : ℝ)*g (‖x‖^2) := by
  have hl : Δ (fun y : E => f (‖y‖^2)) x =
      ∑ i, fderiv ℝ (fderiv ℝ (fun y : E => f (‖y‖^2))) x (b i) (b i) := by
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
    apply Finset.sum_congr rfl
    intro i hi
    exact (bilinearIteratedFDerivTwo_eq_iteratedFDeriv (𝕜 := ℝ) _ x (b i) (b i)).symm
  rw [hl]
  simp_rw [radial_second hf hg]
  have hi : ∑ i, ⟪x,b i⟫*⟪x,b i⟫ = ‖x‖^2 := by
    simpa only [real_inner_comm (b _) x,real_inner_self_eq_norm_sq] using b.sum_inner_mul_inner x x
  calc
    _ = 4*h (‖x‖^2)*(∑ i, ⟪x,b i⟫*⟪x,b i⟫) +
        ∑ i, 2*g (‖x‖^2)*⟪b i,b i⟫ := by
      rw [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 4*‖x‖^2*h (‖x‖^2)+2*(Fintype.card ι : ℝ)*g (‖x‖^2) := by
      rw [hi]
      simp only [real_inner_self_eq_norm_sq,b.norm_eq_one,one_pow,mul_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring

end

section
open MeasureTheory Set InnerProductSpace Laplacian
open scoped RealInnerProductSpace

abbrev WeylSpace := EuclideanSpace ℝ (Fin 3)

def radialEta (χ : ℝ → ℝ) (s : ℝ) (x : WeylSpace) : ℝ :=
  χ (‖x‖^2/s^2)/s^3

def radialTheta (Ψ : ℝ → ℝ) (s : ℝ) (x : WeylSpace) : ℝ :=
  Ψ (‖x‖^2/s^2)/(2*s^2)

lemma hasDerivAt_radialEta {χ χ' : ℝ → ℝ} (hχ : ∀ t, HasDerivAt χ (χ' t) t)
    {s : ℝ} (hs : s≠0) (x : WeylSpace) :
    HasDerivAt (fun r => radialEta χ r x)
      (-(3*χ (‖x‖^2/s^2)/s^4+2*‖x‖^2*χ' (‖x‖^2/s^2)/s^6)) s := by
  have hd := ((hχ _).comp s ((hasDerivAt_const s (‖x‖^2)).div ((hasDerivAt_id s).pow 2) (pow_ne_zero _ hs))).div
    ((hasDerivAt_id s).pow 3) (pow_ne_zero _ hs)
  convert hd using 1
  all_goals try dsimp [radialEta,Function.comp_def]
  all_goals try rfl
  all_goals try field_simp [hs]
  all_goals ring

lemma radialTheta_laplacian {χ χ' Ψ : ℝ → ℝ}
    (hΨ : ∀ t, HasDerivAt Ψ (-χ t) t) (hχ : ∀ t, HasDerivAt χ (χ' t) t)
    {s : ℝ} (hs : s≠0) (x : WeylSpace) :
    Δ (radialTheta Ψ s) x = -(3*χ (‖x‖^2/s^2)/s^4+2*‖x‖^2*χ' (‖x‖^2/s^2)/s^6) := by
  have hf (t : ℝ) : HasDerivAt (fun z => Ψ (z/s^2)/(2*s^2))
      (-χ (t/s^2)/(2*s^4)) t := by
    convert ((hΨ _).comp t ((hasDerivAt_id t).div_const (s^2))).div_const (2*s^2) using 1
    all_goals try dsimp [Function.comp_def]
    all_goals try field_simp [hs]
  have hg (t : ℝ) : HasDerivAt (fun z => -χ (z/s^2)/(2*s^4))
      (-χ' (t/s^2)/(2*s^6)) t := by
    convert (((hχ _).comp t ((hasDerivAt_id t).div_const (s^2))).neg).div_const (2*s^4) using 1
    all_goals try dsimp [Function.comp_def]
    all_goals try field_simp [hs]
  have hh := radial_laplacian (EuclideanSpace.basisFun (Fin 3) ℝ) hf hg x
  apply hh.trans
  simp only [Fintype.card_fin,Nat.cast_ofNat]
  field_simp [hs]
  ring

theorem radial_scale_laplacian {χ χ' Ψ : ℝ → ℝ}
    (hΨ : ∀ t, HasDerivAt Ψ (-χ t) t) (hχ : ∀ t, HasDerivAt χ (χ' t) t)
    {s : ℝ} (hs : s≠0) (x : WeylSpace) :
    HasDerivAt (fun r => radialEta χ r x) (Δ (radialTheta Ψ s) x) s := by
  rw [radialTheta_laplacian hΨ hχ hs]
  exact hasDerivAt_radialEta hχ hs x

end

open Set MeasureTheory Filter Topology InnerProductSpace Laplacian
open scoped RealInnerProductSpace

def radialOneBump : ContDiffBump (0:ℝ) :=
  { rIn := 1/2, rOut := 1, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

def radialRaw (x : WeylSpace) : ℝ := radialOneBump (‖x‖^2)

lemma normsq_smooth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : E => ‖x‖^2) := by
  simpa only [id_eq,real_inner_self_eq_norm_sq] using (contDiff_id.inner ℝ contDiff_id :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : E => ⟪x,x⟫))

lemma radialRaw_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) radialRaw :=
  radialOneBump.contDiff.comp normsq_smooth

lemma radialOneBump_zero {t : ℝ} (ht : 1≤t) : radialOneBump t=0 := by
  apply Function.notMem_support.mp
  rw [radialOneBump.support_eq]
  change ¬dist t 0<1
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by linarith)]
  exact not_lt.mpr ht

lemma radialRaw_zero {x : WeylSpace} (hx : 1≤‖x‖) : radialRaw x=0 := by
  apply radialOneBump_zero
  nlinarith [norm_nonneg x]

lemma radialRaw_compact : HasCompactSupport radialRaw := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:WeylSpace) 1)
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  exact le_of_not_gt (fun hn => hx (radialRaw_zero hn.le))

lemma radialRaw_zero_value : radialRaw 0=1 := by
  apply radialOneBump.one_of_mem_closedBall
  norm_num [radialOneBump]

lemma radialRaw_nonneg (x : WeylSpace) : 0≤radialRaw x := radialOneBump.nonneg

def radialMass : ℝ := ∫ x, radialRaw x

lemma radialMass_pos : 0<radialMass := by
  apply (integral_pos_iff_support_of_nonneg radialRaw_nonneg
    (radialRaw_smooth.continuous.integrable_of_hasCompactSupport radialRaw_compact)).2
  exact radialRaw_smooth.continuous.isOpen_support.measure_pos volume
    ⟨0,by rw [Function.mem_support,radialRaw_zero_value]; norm_num⟩

def radialProfile (t : ℝ) : ℝ := radialOneBump t/radialMass

def radialProfilePrimitive (t : ℝ) : ℝ := ∫ r in t..1, radialProfile r

lemma radialProfile_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) radialProfile :=
  radialOneBump.contDiff.div_const _

lemma radialProfile_nonneg (t : ℝ) : 0≤radialProfile t :=
  div_nonneg radialOneBump.nonneg radialMass_pos.le

lemma radialProfile_zero {t : ℝ} (ht : 1≤t) : radialProfile t=0 := by
  simp [radialProfile,radialOneBump_zero ht]

lemma radialProfilePrimitive_deriv (t : ℝ) :
    HasDerivAt radialProfilePrimitive (-radialProfile t) t :=
  intervalIntegral.integral_hasDerivAt_left (radialProfile_smooth.continuous.intervalIntegrable _ _)
    (radialProfile_smooth.continuous.stronglyMeasurableAtFilter _ _) radialProfile_smooth.continuous.continuousAt

lemma radialProfilePrimitive_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) radialProfilePrimitive := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (radialProfilePrimitive_deriv t).differentiableAt,?_⟩
  have he : deriv radialProfilePrimitive = -radialProfile :=
    funext (fun t => (radialProfilePrimitive_deriv t).deriv)
  rw [he]
  exact radialProfile_smooth.neg

lemma radialProfilePrimitive_zero {t : ℝ} (ht : 1≤t) : radialProfilePrimitive t=0 := by
  change (∫ r in t..1, radialProfile r)=0
  rw [←intervalIntegral.integral_zero (a := t) (b := 1) (μ := volume)]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_ge ht] at hr
  exact radialProfile_zero hr.1

lemma radialEta_smooth (s : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (radialEta radialProfile s) :=
  (radialProfile_smooth.comp (normsq_smooth.div_const _)).div_const _

lemma radialTheta_smooth (s : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (radialTheta radialProfilePrimitive s) :=
  (radialProfilePrimitive_smooth.comp (normsq_smooth.div_const _)).div_const _

lemma radialEta_zero {s : ℝ} (hs : 0<s) {x : WeylSpace} (hx : s≤‖x‖) :
    radialEta radialProfile s x=0 := by
  have h : 1≤‖x‖^2/s^2 := (le_div_iff₀ (sq_pos_of_pos hs)).mpr (by nlinarith [norm_nonneg x])
  simp [radialEta,radialProfile_zero h]

lemma radialTheta_zero {s : ℝ} (hs : 0<s) {x : WeylSpace} (hx : s≤‖x‖) :
    radialTheta radialProfilePrimitive s x=0 := by
  have h : 1≤‖x‖^2/s^2 := (le_div_iff₀ (sq_pos_of_pos hs)).mpr (by nlinarith [norm_nonneg x])
  simp [radialTheta,radialProfilePrimitive_zero h]

lemma radialEta_compact {s : ℝ} (hs : 0<s) : HasCompactSupport (radialEta radialProfile s) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:WeylSpace) s)
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  exact le_of_not_gt (fun hn => hx (radialEta_zero hs hn.le))

lemma radialTheta_compact {s : ℝ} (hs : 0<s) : HasCompactSupport (radialTheta radialProfilePrimitive s) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:WeylSpace) s)
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  exact le_of_not_gt (fun hn => hx (radialTheta_zero hs hn.le))

lemma radialEta_nonneg {s : ℝ} (hs : 0<s) (x : WeylSpace) :
    0≤radialEta radialProfile s x := div_nonneg (radialProfile_nonneg _) (by positivity)

lemma radialEta_integral {s : ℝ} (hs : 0<s) : (∫ x, radialEta radialProfile s x)=1 := by
  have he : radialEta radialProfile s = fun x => (radialRaw (s⁻¹ • x)/radialMass)/s^3 := by
    ext x
    simp [radialEta,radialProfile,radialRaw,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,div_eq_mul_inv,mul_comm]
  rw [he,integral_div,integral_div,Measure.integral_comp_smul volume]
  simp only [WeylSpace, finrank_euclideanSpace, Fintype.card_fin,inv_pow,inv_inv,smul_eq_mul]
  rw [abs_of_pos (pow_pos hs 3)]
  change (s^3*radialMass)/radialMass/s^3=1
  field_simp [radialMass_pos.ne',hs.ne']

end ScalarConductivity

end

end OAI
