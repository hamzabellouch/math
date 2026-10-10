import Mathlib

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Set
open scoped ContDiff Topology
namespace EndpointKernel

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def oscillation {n : ℕ} (φ : Space n → ℝ) (lam : ℝ) (x : Space n) : ℂ :=
  Complex.exp (((lam * φ x : ℝ) : ℂ) * Complex.I)

@[simp] lemma norm_oscillation {n : ℕ} (φ : Space n → ℝ) (lam : ℝ) (x : Space n) :
    ‖oscillation φ lam x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma contDiff_oscillation {n : ℕ} {φ : Space n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (lam : ℝ) : ContDiff ℝ ∞ (oscillation φ lam) := by
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hφ)).mul contDiff_const).cexp

lemma fderiv_oscillation {n : ℕ} {φ : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (lam : ℝ) (x v : Space n) :
    fderiv ℝ (oscillation φ lam) x v =
      (lam : ℂ) * Complex.I * (fderiv ℝ φ x v : ℂ) * oscillation φ lam x := by
  have h := ((Complex.ofRealCLM.hasFDerivAt.comp x
    ((hφ x).hasFDerivAt.const_mul lam)).mul_const Complex.I).cexp
  change HasFDerivAt (oscillation φ lam) _ x at h
  rw [h.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, Function.comp_apply,
    Complex.ofReal_mul, smul_eq_mul, oscillation]
  ring

lemma contDiff_mul_of_tsupport {n : ℕ} {u a : Space n → ℂ}
    (hu : ContDiff ℝ ∞ u) (ha : ∀ x ∈ tsupport u, ContDiffAt ℝ ∞ a x) :
    ContDiff ℝ ∞ (fun x => u x * a x) := by
  apply contDiff_iff_contDiffAt.2
  intro x
  by_cases hx : x ∈ tsupport u
  · exact hu.contDiffAt.mul (ha x hx)
  · have hz := (notMem_tsupport_iff_eventuallyEq.1 hx)
    have hm : (fun y => u y * a y) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
      filter_upwards [hz] with y hy
      simp only [hy, Pi.zero_apply, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hm

def weightedDiv {n : ℕ} (A : Fin n → Space n → ℂ) (u : Space n → ℂ)
    (x : Space n) : ℂ :=
  ∑ i, fderiv ℝ (fun y => u y * A i y) x (EuclideanSpace.single i 1)

lemma contDiff_weightedDiv {n : ℕ} {A : Fin n → Space n → ℂ} {u : Space n → ℂ}
    (hA : ∀ i x, x ∈ tsupport u → ContDiffAt ℝ ∞ (A i) x) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (weightedDiv A u) := by
  apply ContDiff.sum
  intro i _
  exact ((contDiff_mul_of_tsupport hu (hA i)).fderiv_right (by simp)).clm_apply contDiff_const

lemma tsupport_weightedDiv_subset {n : ℕ} (A : Fin n → Space n → ℂ)
    (u : Space n → ℂ) : tsupport (weightedDiv A u) ⊆ tsupport u := by
  apply closure_minimal _ (isClosed_tsupport u)
  intro x hx
  by_contra hxu
  have hz : weightedDiv A u x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hn : x ∉ tsupport (fun y => u y * A i y) :=
      fun h => hxu (tsupport_mul_subset_left h)
    rw [fderiv_of_notMem_tsupport ℝ hn]
    rfl
  exact hx hz

lemma compactSupport_weightedDiv {n : ℕ} (A : Fin n → Space n → ℂ)
    {u : Space n → ℂ} (hu : HasCompactSupport u) : HasCompactSupport (weightedDiv A u) :=
  hu.of_isClosed_subset (isClosed_tsupport _) (tsupport_weightedDiv_subset A u)

lemma integration_by_parts {n : ℕ} {A : Fin n → Space n → ℂ}
    {u : Space n → ℂ} {φ : Space n → ℝ}
    (hA : ∀ i x, x ∈ tsupport u → ContDiffAt ℝ ∞ (A i) x) (hu : ContDiff ℝ ∞ u)
    (hcu : HasCompactSupport u) (hφ : ContDiff ℝ ∞ φ) (lam : ℝ)
    (hcancel : ∀ x ∈ tsupport u,
      ∑ i, A i x * (fderiv ℝ φ x (EuclideanSpace.single i 1) : ℂ) = 1) :
    (lam : ℂ) * Complex.I * (∫ x, u x * oscillation φ lam x) =
      -(∫ x, weightedDiv A u x * oscillation φ lam x) := by
  let e := oscillation φ lam
  have he : ContDiff ℝ ∞ e := contDiff_oscillation hφ lam
  have hed : Differentiable ℝ e := he.differentiable (by simp)
  have hprod (i : Fin n) : ContDiff ℝ ∞ (fun x => u x * A i x) := contDiff_mul_of_tsupport hu (hA i)
  have hcp (i : Fin n) : HasCompactSupport (fun x => u x * A i x) := hcu.mul_right
  have hd (i : Fin n) : ContDiff ℝ ∞ (fun x =>
      fderiv ℝ (fun y => u y * A i y) x (EuclideanSpace.single i 1)) :=
    ((hprod i).fderiv_right (by simp)).clm_apply contDiff_const
  have hid (i : Fin n) : Integrable (fun x =>
      fderiv ℝ (fun y => u y * A i y) x (EuclideanSpace.single i 1) * e x) :=
    ((hd i).continuous.mul he.continuous).integrable_of_hasCompactSupport
      ((hcp i).fderiv_apply ℝ _).mul_right
  have hi (i : Fin n) : Integrable (fun x =>
      (u x * A i x) * fderiv ℝ e x (EuclideanSpace.single i 1)) :=
    ((hprod i).continuous.mul
      ((he.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous).integrable_of_hasCompactSupport
      (hcp i).mul_right
  have hip (i : Fin n) : Integrable (fun x => u x * A i x * e x) :=
    ((hprod i).continuous.mul he.continuous).integrable_of_hasCompactSupport (hcp i).mul_right
  have ih (i : Fin n) := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (hid i) (hi i) (hip i)
    (fun x _ => (hprod i).differentiable (by simp) x) (fun x _ => hed x)
  have hc (x : Space n) : (∑ i, u x * A i x * fderiv ℝ e x (EuclideanSpace.single i 1)) =
      (lam : ℂ) * Complex.I * (u x * e x) := by
    by_cases hx : x ∈ tsupport u
    · simp only [e, fderiv_oscillation (hφ.differentiable (by simp))]
      calc
        _ = ((lam : ℂ) * Complex.I * (u x * oscillation φ lam x)) *
          (∑ i, A i x * (fderiv ℝ φ x (EuclideanSpace.single i 1) : ℂ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
        _ = _ := by rw [hcancel x hx, mul_one]
    · have hz : u x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hz]
  calc
    _ = ∫ x, ∑ i, u x * A i x * fderiv ℝ e x (EuclideanSpace.single i 1) := by
      simp only [hc, integral_const_mul, e]
    _ = ∑ i, ∫ x, u x * A i x * fderiv ℝ e x (EuclideanSpace.single i 1) :=
      integral_finsetSum _ (fun i _ => hi i)
    _ = -(∑ i, ∫ x,
        fderiv ℝ (fun y => u y * A i y) x (EuclideanSpace.single i 1) * e x) := by
      simp only [ih, Finset.sum_neg_distrib]
    _ = -(∫ x, weightedDiv A u x * e x) := by
      simp only [weightedDiv, Finset.sum_mul]
      rw [integral_finsetSum _ (fun i _ => hid i)]

def iteratedAmplitude {n : ℕ} (A : Fin n → Space n → ℂ) (u : Space n → ℂ)
    (k : ℕ) : Space n → ℂ := (weightedDiv A)^[k] u

@[simp] lemma iteratedAmplitude_zero {n : ℕ} (A : Fin n → Space n → ℂ) (u : Space n → ℂ) :
    iteratedAmplitude A u 0 = u := rfl

lemma iteratedAmplitude_succ {n : ℕ} (A : Fin n → Space n → ℂ) (u : Space n → ℂ) (k : ℕ) :
    iteratedAmplitude A u (k+1) = weightedDiv A (iteratedAmplitude A u k) :=
  Function.iterate_succ_apply' _ _ _

lemma tsupport_iteratedAmplitude_subset {n : ℕ} (A : Fin n → Space n → ℂ)
    (u : Space n → ℂ) (k : ℕ) : tsupport (iteratedAmplitude A u k) ⊆ tsupport u := by
  induction k with
  | zero => exact Subset.rfl
  | succ k ih =>
    rw [iteratedAmplitude_succ]
    exact (tsupport_weightedDiv_subset A _).trans ih

lemma contDiff_iteratedAmplitude {n : ℕ} {A : Fin n → Space n → ℂ} {u : Space n → ℂ}
    (hA : ∀ i x, x ∈ tsupport u → ContDiffAt ℝ ∞ (A i) x) (hu : ContDiff ℝ ∞ u)
    (k : ℕ) : ContDiff ℝ ∞ (iteratedAmplitude A u k) := by
  induction k with
  | zero => exact hu
  | succ k ih =>
    rw [iteratedAmplitude_succ]
    exact contDiff_weightedDiv (fun i x hx => hA i x (tsupport_iteratedAmplitude_subset A u k hx)) ih

lemma compactSupport_iteratedAmplitude {n : ℕ} (A : Fin n → Space n → ℂ)
    {u : Space n → ℂ} (hu : HasCompactSupport u) (k : ℕ) :
    HasCompactSupport (iteratedAmplitude A u k) :=
  hu.of_isClosed_subset (isClosed_tsupport _) (tsupport_iteratedAmplitude_subset A u k)

lemma iterated_integration_by_parts {n : ℕ} {A : Fin n → Space n → ℂ}
    {u : Space n → ℂ} {φ : Space n → ℝ}
    (hA : ∀ i x, x ∈ tsupport u → ContDiffAt ℝ ∞ (A i) x) (hu : ContDiff ℝ ∞ u)
    (hcu : HasCompactSupport u) (hφ : ContDiff ℝ ∞ φ) (lam : ℝ)
    (hcancel : ∀ x ∈ tsupport u,
      ∑ i, A i x * (fderiv ℝ φ x (EuclideanSpace.single i 1) : ℂ) = 1) (k : ℕ) :
    ((lam : ℂ) * Complex.I) ^ k * (∫ x, u x * oscillation φ lam x) =
      (-1 : ℂ) ^ k * (∫ x, iteratedAmplitude A u k x * oscillation φ lam x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := integration_by_parts
      (fun i x hx => hA i x (tsupport_iteratedAmplitude_subset A u k hx))
      (contDiff_iteratedAmplitude hA hu k) (compactSupport_iteratedAmplitude A hcu k) hφ lam
      (fun x hx => hcancel x (tsupport_iteratedAmplitude_subset A u k hx))
    rw [← iteratedAmplitude_succ] at hk
    calc
      _ = (lam : ℂ) * Complex.I *
          (((lam : ℂ) * Complex.I) ^ k * ∫ x, u x * oscillation φ lam x) := by ring
      _ = (lam : ℂ) * Complex.I *
          ((-1 : ℂ) ^ k * ∫ x, iteratedAmplitude A u k x * oscillation φ lam x) := by rw [ih]
      _ = (-1 : ℂ) ^ k *
          ((lam : ℂ) * Complex.I * ∫ x, iteratedAmplitude A u k x * oscillation φ lam x) := by ring
      _ = _ := by rw [hk]; ring

lemma nonstationary_phase_bound {n : ℕ} {A : Fin n → Space n → ℂ}
    {u : Space n → ℂ} {φ : Space n → ℝ}
    (hA : ∀ i x, x ∈ tsupport u → ContDiffAt ℝ ∞ (A i) x) (hu : ContDiff ℝ ∞ u)
    (hcu : HasCompactSupport u) (hφ : ContDiff ℝ ∞ φ) (lam : ℝ)
    (hcancel : ∀ x ∈ tsupport u,
      ∑ i, A i x * (fderiv ℝ φ x (EuclideanSpace.single i 1) : ℂ) = 1) (k : ℕ) :
    |lam| ^ k * ‖∫ x, u x * oscillation φ lam x‖ ≤ ∫ x, ‖iteratedAmplitude A u k x‖ := by
  have hi := congrArg norm (iterated_integration_by_parts hA hu hcu hφ lam hcancel k)
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one, norm_neg, norm_one, one_pow, one_mul] at hi
  rw [hi]
  convert norm_integral_le_integral_norm (fun x => iteratedAmplitude A u k x * oscillation φ lam x)
    using 1
  simp only [norm_mul, norm_oscillation, mul_one]

section Parameters
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma contDiffAt_partial_fderiv {n : ℕ} {F : P × Space n → ℂ} {p : P} {x : Space n}
    (hF : ContDiffAt ℝ ∞ F (p,x)) (v : Space n) :
    ContDiffAt ℝ ∞ (fun z : P × Space n => fderiv ℝ (fun y => F (z.1,y)) z.2 v) (p,x) := by
  have hh : ContDiffAt ℝ ∞
      (Function.uncurry (fun (z : P × Space n) (y : Space n) => F (z.1,y))) ((p,x),x) :=
    hF.comp ((p,x),x) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact (hh.fderiv contDiffAt_snd (by simp)).clm_apply contDiffAt_const

lemma contDiffAt_iteratedAmplitude_family {n : ℕ} {A : Fin n → P → Space n → ℂ}
    {u : Space n → ℂ} {p : P}
    (hA : ∀ i x, x ∈ tsupport u →
      ContDiffAt ℝ ∞ (fun z : P × Space n => A i z.1 z.2) (p,x))
    (hu : ContDiff ℝ ∞ u) (k : ℕ) (x : Space n) :
    ContDiffAt ℝ ∞ (fun z : P × Space n => iteratedAmplitude (A · z.1) u k z.2) (p,x) := by
  induction k generalizing x with
  | zero => exact hu.contDiffAt.comp (p,x) contDiffAt_snd
  | succ k ih =>
    simp only [iteratedAmplitude_succ, weightedDiv]
    apply ContDiffAt.sum
    intro i _
    have hh : ContDiffAt ℝ ∞
        (fun z : P × Space n => iteratedAmplitude (A · z.1) u k z.2 * A i z.1 z.2) (p,x) := by
      by_cases hx : x ∈ tsupport u
      · exact (ih x).mul (hA i x hx)
      · have hev : ∀ᶠ z : P × Space n in 𝓝 (p,x), z.2 ∉ tsupport u :=
          (continuous_snd.continuousAt : ContinuousAt (Prod.snd : P × Space n → Space n) (p,x)).preimage_mem_nhds
            ((isClosed_tsupport u).isOpen_compl.mem_nhds hx)
        apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        filter_upwards [hev] with z hz
        have hn : z.2 ∉ tsupport (iteratedAmplitude (A · z.1) u k) :=
          fun h => hz (tsupport_iteratedAmplitude_subset _ u k h)
        simp only [image_eq_zero_of_notMem_tsupport hn, zero_mul]
    exact contDiffAt_partial_fderiv hh _

lemma iteratedAmplitude_uniform_integral_bound {n : ℕ}
    {A : Fin n → P → Space n → ℂ} {u : Space n → ℂ} {K : Set P}
    (hK : IsCompact K)
    (hA : ∀ p ∈ K, ∀ i x, x ∈ tsupport u →
      ContDiffAt ℝ ∞ (fun z : P × Space n => A i z.1 z.2) (p,x))
    (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∫ x, ‖iteratedAmplitude (A · p) u k x‖ ≤ C := by
  let F : P × Space n → ℂ := fun z => iteratedAmplitude (A · z.1) u k z.2
  have hF : ContinuousOn F (K ×ˢ tsupport u) := by
    intro z hz
    exact (contDiffAt_iteratedAmplitude_family (hA z.1 hz.1) hu k z.2).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := ((hK.prod hcu).image_of_continuousOn hF).isBounded.exists_norm_le
  let B := max M 0
  refine ⟨volume.real (tsupport u) * B, mul_nonneg ENNReal.toReal_nonneg (le_max_right _ _), ?_⟩
  intro p hp
  have hac (i : Fin n) (x : Space n) (hx : x ∈ tsupport u) : ContDiffAt ℝ ∞ (A i p) x :=
    (hA p hp i x hx).comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hi : Integrable (fun x => ‖iteratedAmplitude (A · p) u k x‖) :=
    ((contDiff_iteratedAmplitude hac hu k).continuous.integrable_of_hasCompactSupport
      (compactSupport_iteratedAmplitude _ hcu k)).norm
  have hib : Integrable ((tsupport u).indicator (fun _ : Space n => B)) :=
    (integrable_indicator_iff hcu.measurableSet).2
      ((continuous_const : Continuous (fun _ : Space n => B)).locallyIntegrable.integrableOn_isCompact hcu)
  calc
    _ ≤ ∫ x, (tsupport u).indicator (fun _ : Space n => B) x := by
      apply integral_mono hi hib
      intro x
      by_cases hx : x ∈ tsupport u
      · rw [indicator_of_mem hx]
        exact (hM (F (p,x)) ⟨(p,x), ⟨hp,hx⟩, rfl⟩).trans (le_max_left _ _)
      · rw [indicator_of_notMem hx]
        have hz : x ∉ tsupport (iteratedAmplitude (A · p) u k) :=
          fun h => hx (tsupport_iteratedAmplitude_subset _ u k h)
        simp [image_eq_zero_of_notMem_tsupport hz]
    _ = _ := by rw [integral_indicator hcu.measurableSet, setIntegral_const, smul_eq_mul]

lemma uniform_nonstationary_phase {n : ℕ} {A : Fin n → P → Space n → ℂ}
    {u : Space n → ℂ} {φ : P → Space n → ℝ} {K : Set P}
    (hK : IsCompact K)
    (hA : ∀ p ∈ K, ∀ i x, x ∈ tsupport u →
      ContDiffAt ℝ ∞ (fun z : P × Space n => A i z.1 z.2) (p,x))
    (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u)
    (hφ : ∀ p ∈ K, ContDiff ℝ ∞ (φ p))
    (hcancel : ∀ p ∈ K, ∀ x ∈ tsupport u,
      ∑ i, A i p x * (fderiv ℝ (φ p) x (EuclideanSpace.single i 1) : ℂ) = 1) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ lam : ℝ,
      |lam| ^ k * ‖∫ x, u x * oscillation (φ p) lam x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := iteratedAmplitude_uniform_integral_bound hK hA hu hcu k
  refine ⟨C, hC, fun p hp lam => ?_⟩
  have hac (i : Fin n) (x : Space n) (hx : x ∈ tsupport u) : ContDiffAt ℝ ∞ (A i p) x :=
    (hA p hp i x hx).comp x (contDiffAt_const.prodMk contDiffAt_id)
  exact (nonstationary_phase_bound hac hu hcu (hφ p hp) lam (hcancel p hp) k).trans (hb p hp)

end Parameters

def quadraticPhase {n : ℕ} (p : Space n × ℝ) (x : Space n) : ℝ :=
  inner ℝ p.1 x - p.2 * ‖x‖ ^ 2

def quadraticGradient {n : ℕ} (p : Space n × ℝ) (x : Space n) : Space n :=
  p.1 - (2*p.2) • x

lemma contDiff_quadraticPhase {n : ℕ} (p : Space n × ℝ) : ContDiff ℝ ∞ (quadraticPhase p) := by
  exact (innerSL ℝ p.1).contDiff.sub (contDiff_const.mul (contDiff_id.norm_sq ℝ))

lemma fderiv_quadraticPhase {n : ℕ} (p : Space n × ℝ) (x v : Space n) :
    fderiv ℝ (quadraticPhase p) x v = inner ℝ (quadraticGradient p x) v := by
  have h := (innerSL ℝ p.1).hasFDerivAt.sub (((hasFDerivAt_id x).norm_sq).const_mul p.2)
  change HasFDerivAt (quadraticPhase p) _ x at h
  rw [h.fderiv]
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, id_eq, smul_eq_mul, quadraticGradient,
    inner_sub_left, real_inner_smul_left]
  ring

lemma fderiv_quadraticPhase_single {n : ℕ} (p : Space n × ℝ) (x : Space n) (i : Fin n) :
    fderiv ℝ (quadraticPhase p) x (EuclideanSpace.single i 1) = quadraticGradient p x i := by
  rw [fderiv_quadraticPhase, EuclideanSpace.inner_single_right]
  simp

def quadraticNormalizer {n : ℕ} (i : Fin n) (p : Space n × ℝ) (x : Space n) : ℂ :=
  ((quadraticGradient p x i / ‖quadraticGradient p x‖ ^ 2 : ℝ) : ℂ)

lemma contDiffAt_quadraticNormalizer {n : ℕ} (i : Fin n) {p : Space n × ℝ} {x : Space n}
    (h : quadraticGradient p x ≠ 0) :
    ContDiffAt ℝ ∞ (fun z : (Space n × ℝ) × Space n => quadraticNormalizer i z.1 z.2) (p,x) := by
  have hg : ContDiffAt ℝ ∞
      (fun z : (Space n × ℝ) × Space n => quadraticGradient z.1 z.2) (p,x) := by
    unfold quadraticGradient
    fun_prop
  have hn : ‖quadraticGradient p x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 h)
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp (p,x)
    (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp (p,x) hg).div (hg.norm_sq ℝ) hn)

lemma quadraticNormalizer_cancels {n : ℕ} {p : Space n × ℝ} {x : Space n}
    (h : quadraticGradient p x ≠ 0) :
    ∑ i, quadraticNormalizer i p x *
      (fderiv ℝ (quadraticPhase p) x (EuclideanSpace.single i 1) : ℂ) = 1 := by
  have hn : ‖quadraticGradient p x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 h)
  simp only [quadraticNormalizer, fderiv_quadraticPhase_single, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  have hl : (∑ i, quadraticGradient p x i / ‖quadraticGradient p x‖ ^ 2 * quadraticGradient p x i) = 1 := by
    simp_rw [div_mul_eq_mul_div, ← sq]
    rw [← Finset.sum_div, ← EuclideanSpace.real_norm_sq_eq, div_self hn]
  rw [hl, Complex.ofReal_one]

lemma uniform_quadratic_nonstationary {n : ℕ} {u : Space n → ℂ} {K : Set (Space n × ℝ)}
    (hK : IsCompact K) (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u)
    (hgrad : ∀ p ∈ K, ∀ x ∈ tsupport u, quadraticGradient p x ≠ 0) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ lam : ℝ,
      |lam| ^ k * ‖∫ x, u x * oscillation (quadraticPhase p) lam x‖ ≤ C := by
  apply uniform_nonstationary_phase hK
    (fun p hp i x hx => contDiffAt_quadraticNormalizer i (hgrad p hp x hx)) hu hcu
    (fun p _ => contDiff_quadraticPhase p)
    (fun p hp x hx => quadraticNormalizer_cancels (hgrad p hp x hx)) k

lemma time_dominated_decay {n : ℕ} {u : Space n → ℂ} {c : ℝ}
    (hc : 0 < c) (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u)
    (hann : ∀ x ∈ tsupport u, c ≤ ‖x‖) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Space n) (t : ℝ),
      ‖z‖ ≤ c * |t| →
      |t| ^ k * ‖∫ x, u x * oscillation (quadraticPhase (z,t)) 1 x‖ ≤ C := by
  let K : Set (Space n × ℝ) := Metric.closedBall 0 c ×ˢ {1}
  have hK : IsCompact K := (isCompact_closedBall 0 c).prod isCompact_singleton
  have hg : ∀ p ∈ K, ∀ x ∈ tsupport u, quadraticGradient p x ≠ 0 := by
    intro p hp x hx hz
    have hv : ‖p.1‖ ≤ c := by simpa using hp.1
    have ht : p.2 = 1 := hp.2
    have he : p.1 = (2 : ℝ) • x := by
      simpa [quadraticGradient, ht] using sub_eq_zero.mp hz
    have hnorm : ‖p.1‖ = 2 * ‖x‖ := by rw [he, norm_smul]; norm_num
    have hr := hann x hx
    nlinarith
  obtain ⟨C, hC, hb⟩ := uniform_quadratic_nonstationary hK hu hcu hg k
  let C₀ := ∫ x, ‖u x‖
  have hC₀ : 0 ≤ C₀ := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨max C C₀, le_max_of_le_left hC, fun z t hzt => ?_⟩
  by_cases ht : t = 0
  · have hz : z = 0 := norm_eq_zero.mp (le_antisymm (by simpa [ht] using hzt) (norm_nonneg _))
    have hi : ‖∫ x, u x * oscillation (quadraticPhase (z,t)) 1 x‖ ≤ C₀ := by
      calc
        _ ≤ ∫ x, ‖u x * oscillation (quadraticPhase (z,t)) 1 x‖ := norm_integral_le_integral_norm _
        _ = C₀ := by simp [C₀]
    calc
      _ ≤ 1 * C₀ := mul_le_mul (by rw [ht, abs_zero]; exact pow_le_one₀ (by norm_num) (by norm_num)) hi
        (norm_nonneg _) (by positivity)
      _ ≤ max C C₀ := by simp
  · have hab : 0 < |t| := abs_pos.mpr ht
    have hp : (t⁻¹ • z, (1 : ℝ)) ∈ K := by
      constructor
      · change dist (t⁻¹ • z) 0 ≤ c
        rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv]
        exact (inv_mul_le_iff₀ hab).mpr (by simpa [mul_comm] using hzt)
      · rfl
    have he : oscillation (quadraticPhase (z,t)) 1 =
        oscillation (quadraticPhase (t⁻¹ • z,1)) t := by
      funext x
      unfold oscillation quadraticPhase
      congr 3
      simp only [one_mul, real_inner_smul_left]
      field_simp
    rw [he]
    exact (hb _ hp t).trans (le_max_left _ _)

lemma spatial_dominated_decay_power {n : ℕ} {u : Space n → ℂ} {R : ℝ}
    (hR : 0 < R) (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u)
    (hsupp : ∀ x ∈ tsupport u, ‖x‖ ≤ R) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Space n) (t : ℝ),
      4 * R * |t| ≤ ‖z‖ →
      ‖z‖ ^ k * ‖∫ x, u x * oscillation (quadraticPhase (z,t)) 1 x‖ ≤ C := by
  let K : Set (Space n × ℝ) := Metric.sphere 0 1 ×ˢ Set.Icc (-(4*R)⁻¹) ((4*R)⁻¹)
  have hr4 : 0 < 4*R := by positivity
  have hK : IsCompact K := (isCompact_sphere 0 1).prod isCompact_Icc
  have hg : ∀ p ∈ K, ∀ x ∈ tsupport u, quadraticGradient p x ≠ 0 := by
    intro p hp x hx hz
    have hv : ‖p.1‖ = 1 := by simpa using hp.1
    have ht : |p.2| ≤ (4*R)⁻¹ := abs_le.mpr hp.2
    have he : p.1 = (2*p.2) • x := sub_eq_zero.mp hz
    have hnorm : 1 = 2 * |p.2| * ‖x‖ := by
      rw [← hv, he, norm_smul, Real.norm_eq_abs, abs_mul]; norm_num
    have hb : |p.2| * (4*R) ≤ 1 := by
      simpa only [inv_mul_cancel₀ hr4.ne'] using mul_le_mul_of_nonneg_right ht hr4.le
    have hh := mul_le_mul_of_nonneg_left (hsupp x hx) (abs_nonneg p.2)
    nlinarith
  obtain ⟨C, hC, hb⟩ := uniform_quadratic_nonstationary hK hu hcu hg k
  let C₀ := ∫ x, ‖u x‖
  have hC₀ : 0 ≤ C₀ := integral_nonneg (fun _ => norm_nonneg _)
  have hi (z : Space n) (t : ℝ) :
      ‖∫ x, u x * oscillation (quadraticPhase (z,t)) 1 x‖ ≤ C₀ := by
    calc
      _ ≤ ∫ x, ‖u x * oscillation (quadraticPhase (z,t)) 1 x‖ := norm_integral_le_integral_norm _
      _ = C₀ := by simp [C₀]
  refine ⟨max C C₀, le_max_of_le_left hC, fun z t hzt => ?_⟩
  by_cases hz : z = 0
  · calc
      _ ≤ 1 * C₀ := mul_le_mul (by rw [hz, norm_zero]; exact pow_le_one₀ (by norm_num) (by norm_num))
        (hi z t) (norm_nonneg _) (by positivity)
      _ ≤ max C C₀ := by simp
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hp : (‖z‖⁻¹ • z, t / ‖z‖) ∈ K := by
      constructor
      · change dist (‖z‖⁻¹ • z) 0 = 1
        rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn, inv_mul_cancel₀ hn.ne']
      · apply abs_le.mp
        rw [abs_div, abs_of_pos hn]
        apply (div_le_iff₀ hn).mpr
        apply (le_inv_mul_iff₀ hr4).mpr
        nlinarith
    have he : oscillation (quadraticPhase (z,t)) 1 =
        oscillation (quadraticPhase (‖z‖⁻¹ • z,t/‖z‖)) ‖z‖ := by
      funext x
      unfold oscillation quadraticPhase
      congr 3
      simp only [one_mul, real_inner_smul_left]
      field_simp
    rw [he]
    simpa only [abs_of_pos hn] using (hb _ hp ‖z‖).trans (le_max_left _ _)

lemma one_add_weight_bound {a b C D : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (k : ℕ) (h : a ^ k * b ≤ C) (h' : b ≤ D) :
    (1+a) ^ k * b ≤ 2 ^ k * max C D := by
  by_cases ha1 : a ≤ 1
  · calc
      (1+a)^k*b ≤ 2^k*D := mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) k) h' hb (by positivity)
      _ ≤ 2^k*max C D := mul_le_mul le_rfl (le_max_right _ _) hD (by positivity)
  · have ha1 : 1 ≤ a := le_of_lt (lt_of_not_ge ha1)
    calc
      (1+a)^k*b ≤ (2*a)^k*b := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by linarith) k) hb
      _ = 2^k*(a^k*b) := by rw [mul_pow, mul_assoc]
      _ ≤ 2^k*C := mul_le_mul_of_nonneg_left h (by positivity)
      _ ≤ 2^k*max C D := mul_le_mul le_rfl (le_max_left _ _) hC (by positivity)

lemma spatial_dominated_decay {n : ℕ} {u : Space n → ℂ} {R : ℝ}
    (hR : 0 < R) (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u)
    (hsupp : ∀ x ∈ tsupport u, ‖x‖ ≤ R) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Space n) (t : ℝ),
      4 * R * |t| ≤ ‖z‖ →
      (1+‖z‖) ^ k * ‖∫ x, u x * oscillation (quadraticPhase (z,t)) 1 x‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := spatial_dominated_decay_power hR hu hcu hsupp k
  let C₀ := ∫ x, ‖u x‖
  have hC₀ : 0 ≤ C₀ := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨2^k * max C C₀, by positivity, fun z t hzt => ?_⟩
  apply one_add_weight_bound (norm_nonneg _) (norm_nonneg _) hC hC₀ k (hb z t hzt)
  calc
    _ ≤ ∫ x, ‖u x * oscillation (quadraticPhase (z,t)) 1 x‖ := norm_integral_le_integral_norm _
    _ = C₀ := by simp [C₀]

def scaledKernel (u : Space 2 → ℂ) (N : ℝ) (z : Space 2) (t : ℝ) : ℂ :=
  ∫ ξ, u (N⁻¹ • ξ) * oscillation (quadraticPhase (z,t)) 1 ξ

lemma scaledKernel_eq (u : Space 2 → ℂ) {N : ℝ} (hN : 0 < N) (z : Space 2) (t : ℝ) :
    scaledKernel u N z t = (N^2 : ℝ) •
      ∫ η, u η * oscillation (quadraticPhase (N • z, N^2*t)) 1 η := by
  let q : Space 2 → ℂ := fun η => u η * oscillation (quadraticPhase (N • z, N^2*t)) 1 η
  have he : (fun ξ => u (N⁻¹ • ξ) * oscillation (quadraticPhase (z,t)) 1 ξ) =
      fun ξ => q (N⁻¹ • ξ) := by
    funext ξ
    dsimp only [q]
    congr 1
    unfold oscillation quadraticPhase
    congr 3
    simp only [real_inner_smul_left, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hN]
    field_simp
  unfold scaledKernel
  rw [he, Measure.integral_comp_inv_smul_of_nonneg volume q hN.le]
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin]
  rfl

lemma scaledKernel_time_decay {u : Space 2 → ℂ} {c : ℝ}
    (hc : 0 < c) (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u)
    (hann : ∀ x ∈ tsupport u, c ≤ ‖x‖) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℝ), 0 < N → ∀ (z : Space 2) (t : ℝ),
      ‖z‖ ≤ c * N * |t| →
      (N^2 * |t|) ^ k * ‖scaledKernel u N z t‖ ≤ C * N^2 := by
  obtain ⟨C,hC,hb⟩ := time_dominated_decay hc hu hcu hann k
  refine ⟨C,hC,fun N hN z t hzt => ?_⟩
  have hz : ‖N • z‖ ≤ c * |N^2*t| := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hN, abs_mul, abs_of_nonneg (sq_nonneg N)]
    nlinarith [mul_le_mul_of_nonneg_left hzt hN.le]
  have hh := hb (N • z) (N^2*t) hz
  rw [scaledKernel_eq u hN, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg N)]
  have hht : |N^2*t| = N^2*|t| := by rw [abs_mul, abs_of_nonneg (sq_nonneg N)]
  rw [hht] at hh
  nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg N)]

lemma scaledKernel_spatial_decay {u : Space 2 → ℂ} {R : ℝ}
    (hR : 0 < R) (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u)
    (hsupp : ∀ x ∈ tsupport u, ‖x‖ ≤ R) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℝ), 0 < N → ∀ (z : Space 2) (t : ℝ),
      4 * R * N * |t| ≤ ‖z‖ →
      ‖scaledKernel u N z t‖ ≤ C * N^2 / (1+N*‖z‖)^k := by
  obtain ⟨C,hC,hb⟩ := spatial_dominated_decay hR hu hcu hsupp k
  refine ⟨C,hC,fun N hN z t hzt => ?_⟩
  have hz : 4*R*|N^2*t| ≤ ‖N • z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hN, abs_mul, abs_of_nonneg (sq_nonneg N)]
    nlinarith [mul_le_mul_of_nonneg_left hzt hN.le]
  have hh := hb (N • z) (N^2*t) hz
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hN] at hh
  rw [le_div_iff₀ (pow_pos (by positivity) k), scaledKernel_eq u hN,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg N)]
  nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg N)]

end EndpointKernel
end

end OAI
