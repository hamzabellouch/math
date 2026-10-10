import Mathlib

namespace OAI

/-! Uniform Fourier decay and localized Taylor amplitudes. -/

open MeasureTheory
open scoped NNReal ENNReal ContDiff
noncomputable section
open Filter
open scoped Topology ContDiff

open MeasureTheory Set
open scoped ContDiff FourierTransform InnerProductSpace ENNReal
namespace DiagonalExtension.UniformFourierDecay
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem weighted_fourier_bound {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (n : ℕ) {M : ℝ} (_hM : 0 ≤ M)
    (hderiv : ∀ j ≤ n, ∫ y, ‖iteratedFDeriv ℝ j f y‖ ≤ M) (x : E) :
    (1 + ‖x‖) ^ n * ‖𝓕 f x‖ ≤ (2 : ℝ) ^ n * (1 + 2 ^ n * (n + 1)) * M := by
  have hint (k j : ℕ) : Integrable (fun y : E => ‖y‖ ^ k * ‖iteratedFDeriv ℝ j f y‖) :=
    (((continuous_norm.pow k).mul (hf.continuous_iteratedFDeriv (by exact WithTop.coe_le_coe.mpr le_top)).norm)).integrable_of_hasCompactSupport
      (((hfc.iteratedFDeriv j).norm).mul_left)
  have h0 : ‖𝓕 f x‖ ≤ M := by
    exact (VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ E) f x).trans
      (by simpa only [norm_iteratedFDeriv_zero] using hderiv 0 (Nat.zero_le n))
  have hw := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := (0 : ℕ∞)) (N := ⊤)
    hf (fun k j _ _ => hint k j) (k := 0) (n := n) (by simp) (by simp) x
  have hw' : ‖x‖ ^ n * ‖𝓕 f x‖ ≤ 2 ^ n * ((n + 1) * M) := by
    simp only [pow_zero, zero_add, one_mul, norm_iteratedFDeriv_zero,
      Nat.cast_zero, Finset.range_one, Finset.singleton_product, Finset.sum_map, Function.Embedding.sectR_apply,
      mul_zero] at hw
    refine hw.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1), M := by
        apply Finset.sum_le_sum
        intro j hj
        exact hderiv j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      _ = _ := by simp
  have hp : (1 + ‖x‖) ^ n ≤ 2 ^ n * (1 + ‖x‖ ^ n) := by
    refine (add_pow_le (a := (1:ℝ)) (b := ‖x‖) (by positivity) (norm_nonneg _) n).trans ?_
    simp only [one_pow]
    gcongr
    · norm_num
    · omega
  calc
    _ ≤ 2 ^ n * (1 + ‖x‖ ^ n) * ‖𝓕 f x‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = 2 ^ n * (‖𝓕 f x‖ + ‖x‖ ^ n * ‖𝓕 f x‖) := by ring
    _ ≤ 2 ^ n * (M + 2 ^ n * ((n + 1) * M)) := by gcongr
    _ = _ := by ring

end DiagonalExtension.UniformFourierDecay

namespace DiagonalExtension.UniformFourierDecay
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma iteratedFDeriv_section {F : P × E → ℂ} (hF : ContDiff ℝ ∞ F)
    (p : P) (z : E) (j : ℕ) :
    iteratedFDeriv ℝ j (fun y => F (p,y)) z =
      (iteratedFDeriv ℝ j F (p,z)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ P E) := by
  let g : P × E → ℂ := fun q => F ((p,0) + q)
  have hg : ContDiff ℝ ∞ g := hF.comp (contDiff_const.add contDiff_id)
  have heq := (ContinuousLinearMap.inr ℝ P E).iteratedFDeriv_comp_right hg z
    (i := j) (by exact WithTop.coe_le_coe.mpr le_top)
  have ht := iteratedFDerivWithin_comp_add_left (𝕜 := ℝ) (f := F) (s := Set.univ)
    j (p, (0:E)) ((0:P),z)
  simp only [Set.vadd_set_univ, iteratedFDerivWithin_univ, Prod.mk_add_mk,
    add_zero, zero_add] at ht
  simp only [Function.comp_def, g, ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk, add_zero, zero_add] at heq
  rw [show iteratedFDeriv ℝ j (fun q : P × E => F ((p,0) + q)) (0,z) =
    iteratedFDeriv ℝ j F (p,z) from ht] at heq
  exact heq

lemma continuous_section_derivative {F : P × E → ℂ} (hF : ContDiff ℝ ∞ F) (j : ℕ) :
    Continuous (fun q : P × E => iteratedFDeriv ℝ j (fun y => F (q.1,y)) q.2) := by
  simp_rw [iteratedFDeriv_section hF]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin j => ContinuousLinearMap.inr ℝ P E)).continuous.comp
    (hF.continuous_iteratedFDeriv (by exact WithTop.coe_le_coe.mpr le_top))

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem compact_uniform_decay {F : P × E → ℂ} (hF : ContDiff ℝ ∞ F)
    {K : Set P} (hK : IsCompact K) {S : Set E} (hS : IsCompact S)
    (hsupp : ∀ p ∈ K, tsupport (fun z => F (p,z)) ⊆ S) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ x : E,
      (1 + ‖x‖) ^ n * ‖𝓕 (fun z => F (p,z)) x‖ ≤ C := by
  have hb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K,
      ∫ z, ‖iteratedFDeriv ℝ j (fun y => F (p,y)) z‖ ≤ C := by
    obtain ⟨B,hB⟩ := (hK.prod hS).exists_bound_of_continuousOn
      (continuous_section_derivative hF j).continuousOn
    refine ⟨max B 0 * (volume S).toReal, by positivity, ?_⟩
    intro p hp
    have hf : ContDiff ℝ ∞ (fun z => F (p,z)) :=
      hF.comp (contDiff_const.prodMk contDiff_id)
    have hfc : HasCompactSupport (fun z => F (p,z)) :=
      hS.of_isClosed_subset isClosed_closure (hsupp p hp)
    have hc : Continuous (fun z => ‖iteratedFDeriv ℝ j (fun y => F (p,y)) z‖) :=
      (hf.continuous_iteratedFDeriv (by exact WithTop.coe_le_coe.mpr le_top)).norm
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S) (fun z hz => ?_)]
    · calc
        _ ≤ ∫ _ in S, max B 0 := by
          apply setIntegral_mono_on (hc.continuousOn.integrableOn_compact hS)
            (integrableOn_const hS.measure_lt_top.ne) hS.measurableSet
          intro z hz
          exact (hB (p,z) ⟨hp,hz⟩).trans (le_max_left _ _)
        _ = _ := by simp [mul_comm, Measure.real_def]
    · exact norm_eq_zero.mpr (Function.notMem_support.mp fun h => hz
        (hsupp p hp (support_iteratedFDeriv_subset j h)))
  choose B hB hbound using hb
  let M := ∑ j ∈ Finset.range (n+1), B j
  have hM : 0 ≤ M := Finset.sum_nonneg fun j _ => hB j
  refine ⟨2 ^ n * (1 + 2 ^ n * (n+1)) * M, by positivity, ?_⟩
  intro p hp x
  apply weighted_fourier_bound (hF.comp (contDiff_const.prodMk contDiff_id))
    (hS.of_isClosed_subset isClosed_closure (hsupp p hp)) n hM _ x
  intro j hj
  exact (hbound j p hp).trans (Finset.single_le_sum (fun i _ => hB i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

end DiagonalExtension.UniformFourierDecay
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
namespace DiagonalExtension.SmoothCompactIntegral
universe u
variable {P A B : Type u}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

def paramDeriv (F : P × A → B) (q : P × A) : P →L[ℝ] B :=
  (fderiv ℝ F q).comp (ContinuousLinearMap.inl ℝ P A)

lemma smooth_partial {F : P × A → B} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (paramDeriv F) :=
  (hF.fderiv_right (by simp)).clm_comp contDiff_const

lemma partial_hasFDerivAt {F : P × A → B} (hF : ContDiff ℝ ∞ F) (p : P) (a : A) :
    HasFDerivAt (fun q => F (q,a)) (paramDeriv F (p,a)) p := by
  convert ((hF.differentiable (by simp)) (p,a)).hasFDerivAt.comp p
    ((hasFDerivAt_id (𝕜 := ℝ) p).prodMk (hasFDerivAt_const (𝕜 := ℝ) a p)) using 1 <;> rfl

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A]
variable {μ : Measure A} [IsFiniteMeasureOnCompacts μ]

lemma hasFDerivAt_integral {K : Set A} (hK : IsCompact K) {F : P × A → B}
    (hF : ContDiff ℝ ∞ F) (p : P) :
    HasFDerivAt (fun q => ∫ a in K, F (q,a) ∂μ)
      (∫ a in K, paramDeriv F (p,a) ∂μ) p := by
  have : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using (hK.measure_lt_top (μ := μ))⟩
  obtain ⟨C,hC⟩ := ((isCompact_closedBall p 1).prod hK).exists_bound_of_continuousOn
    (smooth_partial hF).continuous.continuousOn
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := closedBall p 1) (F' := fun q a => paramDeriv F (q,a)) (bound := fun _ => C)
    (closedBall_mem_nhds p (by norm_num)) ?_ ?_ ?_ ?_ (integrable_const C) ?_
  · exact Filter.Eventually.of_forall fun q =>
      (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hK
  · exact ((smooth_partial hF).continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro q hq
    exact hC (q,a) ⟨hq,ha⟩
  · exact Filter.Eventually.of_forall fun a q _ => partial_hasFDerivAt hF q a

private lemma smooth_integral_nat (n : ℕ) {K : Set A} (hK : IsCompact K)
    {F : P × A → B} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ n (fun q => ∫ a in K, F (q,a) ∂μ) := by
  induction n generalizing B with
  | zero =>
    exact contDiff_zero.mpr (Differentiable.continuous
      (fun p => (hasFDerivAt_integral hK hF p).differentiableAt))
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun p => (hasFDerivAt_integral hK hF p).differentiableAt, by simp, ?_⟩
    have heq : fderiv ℝ (fun q => ∫ a in K, F (q,a) ∂μ) =
        (fun q => ∫ a in K, paramDeriv F (q,a) ∂μ) :=
      funext fun p => (hasFDerivAt_integral hK hF p).fderiv
    rw [heq]
    exact ih (smooth_partial hF)

theorem contDiff_integral {K : Set A} (hK : IsCompact K) {F : P × A → B}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (fun q => ∫ a in K, F (q,a) ∂μ) :=
  contDiff_infty.mpr fun n => smooth_integral_nat n hK hF

end DiagonalExtension.SmoothCompactIntegral

namespace DiagonalExtension.PacketTaylor
open MeasureTheory Set
open scoped ContDiff FourierTransform InnerProductSpace
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def remainder (φ : E → ℝ) (q : (E × ℝ) × E) : ℝ :=
  ∫ s in Set.Icc (0:ℝ) 1, (1-s) *
    (fderiv ℝ (fderiv ℝ φ) (q.1.1 + (s*q.1.2) • q.2) q.2) q.2

lemma smooth_remainder {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (remainder φ) := by
  unfold remainder
  apply SmoothCompactIntegral.contDiff_integral (μ := (volume : Measure ℝ))
    (F := fun q : ((E × ℝ) × E) × ℝ => (1-q.2) *
      (fderiv ℝ (fderiv ℝ φ) (q.1.1.1 + (q.2*q.1.1.2) • q.1.2) q.1.2) q.1.2)
    isCompact_Icc
  have hH : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := ∞) (by simp)).fderiv_right (by simp)
  have hloc : ContDiff ℝ ∞ (fun q : ((E × ℝ) × E) × ℝ =>
      q.1.1.1 + (q.2*q.1.1.2) • q.1.2) := by fun_prop
  exact (contDiff_const.sub contDiff_snd).mul
    (((hH.comp hloc).clm_apply (contDiff_snd.comp contDiff_fst)).clm_apply
      (contDiff_snd.comp contDiff_fst))

omit [FiniteDimensional ℝ E] in
lemma taylor_identity {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (ν z : E) (δ : ℝ) :
    φ (ν + δ • z) = φ ν + δ * (fderiv ℝ φ ν z) + δ^2 * remainder φ ((ν,δ),z) := by
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (f := φ) (x := ν) (y := δ • z)
    (n := 1) (fun _ _ => (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt)
  simp only [Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, pow_one,
    iteratedFDeriv_two_apply] at ht
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at ht
  simp only [smul_smul, map_smul, smul_apply, smul_eq_mul] at ht
  rw [ht, remainder, ← integral_const_mul]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  ring

abbrev Param (E : Type) := (E × ℝ) × (ℝ × (E × ℝ))

def amplitude (φ χ : E → ℝ) (q : Param E × E) : ℂ :=
  (χ q.2 : ℂ) * (χ (q.1.2.2.1 + q.1.2.2.2 • q.2) : ℂ) *
    Complex.exp ((2 * Real.pi * (q.1.2.1 * remainder φ (q.1.1,q.2)) : ℝ) * Complex.I)

lemma smooth_amplitude {φ χ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (amplitude φ χ) := by
  have hr : ContDiff ℝ ∞ (fun q : Param E × E => remainder φ (q.1.1,q.2)) :=
    (smooth_remainder hφ).comp (by fun_prop)
  have h1 : ContDiff ℝ ∞ (fun q : Param E × E => (χ q.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_snd)
  have h2 : ContDiff ℝ ∞ (fun q : Param E × E => (χ (q.1.2.2.1 + q.1.2.2.2 • q.2) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hχ.comp (by fun_prop))
  have ht : ContDiff ℝ ∞ (fun q : Param E × E => q.1.2.1) := by fun_prop
  have h3 : ContDiff ℝ ∞ (fun q : Param E × E => ((2 * Real.pi * (q.1.2.1 * remainder φ (q.1.1,q.2)) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (ht.mul hr))
  exact (h1.mul h2).mul (((Complex.contDiff_exp : ContDiff ℂ ∞ Complex.exp).restrict_scalars ℝ).comp (h3.mul contDiff_const))

variable [MeasurableSpace E] [BorelSpace E]

theorem normalized_locality {φ χ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (R A : ℝ) (L : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν δ τ a ρ,
      ‖ν‖ ≤ R → δ ∈ Icc (0:ℝ) 1 → τ ∈ Icc (0:ℝ) 1 →
      ‖a‖ ≤ A → ρ ∈ Icc (0:ℝ) 1 → ∀ x : E,
      (1 + ‖x‖)^L * ‖𝓕 (fun z => amplitude φ χ (((ν,δ),(τ,(a,ρ))),z)) x‖ ≤ C := by
  let K : Set (Param E) := (Metric.closedBall 0 R ×ˢ Icc 0 1) ×ˢ
    (Icc 0 1 ×ˢ (Metric.closedBall 0 A ×ˢ Icc 0 1))
  have hK : IsCompact K := ((isCompact_closedBall 0 R).prod isCompact_Icc).prod
    (isCompact_Icc.prod ((isCompact_closedBall 0 A).prod isCompact_Icc))
  have hsupp : ∀ p ∈ K, tsupport (fun z => amplitude φ χ (p,z)) ⊆ tsupport χ := by
    intro p hp
    apply closure_mono
    intro z hz
    simp only [Function.mem_support] at *
    intro h
    apply hz
    simp [amplitude,h]
  obtain ⟨C,hC,h⟩ := UniformFourierDecay.compact_uniform_decay (smooth_amplitude hφ hχ)
    hK hχc hsupp L
  refine ⟨C,hC,?_⟩
  intro ν δ τ a ρ hν hδ hτ ha hρ x
  apply h ((ν,δ),(τ,(a,ρ))) _ x
  exact ⟨⟨by simpa using hν,hδ⟩,hτ,by simpa using ha,hρ⟩

end DiagonalExtension.PacketTaylor

end

end OAI
