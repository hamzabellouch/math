import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.HardyMollifier
import OAI.Analysis.CoulombRadii.FieldAnalysis.CubeMeasure

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

theorem realMollify_L2_tendsto {I : Type*} [Fintype I]
    {u : EuclideanSpace ℝ I → ℝ} (hu : MemLp u 2) :
    Tendsto (fun k => ∫ x, (realMollify k u x - u x)^2) atTop (nhds 0) :=
  tendsto_integral_sq_sub_of_ae_of_sq_le hu (fun k => realMollify_memLp k hu)
    (realMollify_ae_tendsto hu) (fun k => realMollify_sq_integral_le k hu)

noncomputable def complexMollify {I : Type*} [Fintype I] (k : ℕ)
    (u : EuclideanSpace ℝ I → ℂ) : EuclideanSpace ℝ I → ℂ :=
  fun x => (realMollify k (fun y => (u y).re) x : ℂ) +
    (realMollify k (fun y => (u y).im) x : ℂ) * Complex.I

lemma complexMollify_contDiff {I : Type*} [Fintype I] (k : ℕ)
    {u : EuclideanSpace ℝ I → ℂ} (hu : MemLp u 2) :
    ContDiff ℝ (⊤ : ℕ∞) (complexMollify k u) := by
  exact (Complex.ofRealCLM.contDiff.comp (realMollify_contDiff k
    (Complex.reCLM.comp_memLp' hu))).add
      ((Complex.ofRealCLM.contDiff.comp (realMollify_contDiff k
        (Complex.imCLM.comp_memLp' hu))).mul contDiff_const)

lemma complexMollify_memLp {I : Type*} [Fintype I] (k : ℕ)
    {u : EuclideanSpace ℝ I → ℂ} (hu : MemLp u 2) :
    MemLp (complexMollify k u) 2 := by
  exact (Complex.ofRealCLM.comp_memLp' (realMollify_memLp k (Complex.reCLM.comp_memLp' hu))).add
    ((Complex.ofRealCLM.comp_memLp' (realMollify_memLp k
      (Complex.imCLM.comp_memLp' hu))).mul_const Complex.I)

lemma complexMollify_sq_sub {I : Type*} [Fintype I] (k : ℕ)
    (u : EuclideanSpace ℝ I → ℂ) (x : EuclideanSpace ℝ I) :
    ‖complexMollify k u x - u x‖^2 =
      (realMollify k (fun y => (u y).re) x - (u x).re)^2 +
      (realMollify k (fun y => (u y).im) x - (u x).im)^2 := by
  simp [complex_norm_sq_components, complexMollify]

theorem complexMollify_L2_tendsto {I : Type*} [Fintype I]
    {u : EuclideanSpace ℝ I → ℂ} (hu : MemLp u 2) :
    Tendsto (fun k => ∫ x, ‖complexMollify k u x - u x‖^2) atTop (nhds 0) := by
  have hr : MemLp (fun x => (u x).re) 2 := Complex.reCLM.comp_memLp' hu
  have hi : MemLp (fun x => (u x).im) 2 := Complex.imCLM.comp_memLp' hu
  have he (k : ℕ) : (∫ x, ‖complexMollify k u x - u x‖^2) =
      (∫ x, (realMollify k (fun y => (u y).re) x - (u x).re)^2) +
      (∫ x, (realMollify k (fun y => (u y).im) x - (u x).im)^2) := by
    simp_rw [complexMollify_sq_sub]
    exact integral_add ((realMollify_memLp k hr).sub hr).integrable_sq
      ((realMollify_memLp k hi).sub hi).integrable_sq
  simp_rw [he]
  simpa using (realMollify_L2_tendsto hr).add (realMollify_L2_tendsto hi)

lemma toLp_tendsto_of_integral_sq_sub {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f : A → ℂ} {F : ℕ → A → ℂ} (hf : MemLp f 2 μ) (hF : ∀ k, MemLp (F k) 2 μ)
    (h : Tendsto (fun k => ∫ x, ‖F k x - f x‖^2 ∂μ) atTop (nhds 0)) :
    Tendsto (fun k => (hF k).toLp (F k)) atTop (nhds (hf.toLp f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have he (k : ℕ) : ‖(hF k).toLp (F k) - hf.toLp f‖^2 =
      ∫ x, ‖F k x - f x‖^2 ∂μ := by
    rw [← MemLp.toLp_sub (hF k) hf, norm_toLp_sq_complex]
    rfl
  have ht := (Real.continuous_sqrt.tendsto 0).comp h
  simp only [Real.sqrt_zero] at ht
  change Tendsto (fun k => Real.sqrt (∫ x, ‖F k x - f x‖^2 ∂μ)) atTop (nhds 0) at ht
  simp_rw [← he, Real.sqrt_sq (norm_nonneg _)] at ht
  exact ht

lemma integral_norm_sq_tendsto_of_L2 {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f : A → ℂ} {F : ℕ → A → ℂ} (hf : MemLp f 2 μ) (hF : ∀ k, MemLp (F k) 2 μ)
    (h : Tendsto (fun k => ∫ x, ‖F k x - f x‖^2 ∂μ) atTop (nhds 0)) :
    Tendsto (fun k => ∫ x, ‖F k x‖^2 ∂μ) atTop (nhds (∫ x, ‖f x‖^2 ∂μ)) := by
  simpa only [norm_toLp_sq_complex] using
    (toLp_tendsto_of_integral_sq_sub hf hF h).norm.pow 2

lemma integral_coefficient_tendsto_of_L2 {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f w : A → ℂ} {F : ℕ → A → ℂ}
    (hf : MemLp f 2 μ) (hw : MemLp w 2 μ) (hF : ∀ k, MemLp (F k) 2 μ)
    (h : Tendsto (fun k => ∫ x, ‖F k x - f x‖^2 ∂μ) atTop (nhds 0)) :
    Tendsto (fun k => ∫ x, star (w x) * F k x ∂μ) atTop
      (nhds (∫ x, star (w x) * f x ∂μ)) := by
  simpa only [inner_toLp_complex] using
    (tendsto_const_nhds (x := hw.toLp w)).inner (𝕜 := ℂ)
      (toLp_tendsto_of_integral_sq_sub hf hF h)

lemma integral_sq_sub_restrict_tendsto {A : Type*} [MeasurableSpace A] {μ ν : Measure A}
    (hμ : ν ≤ μ) {f : A → ℂ} {F : ℕ → A → ℂ}
    (hf : MemLp f 2 μ) (hF : ∀ k, MemLp (F k) 2 μ)
    (h : Tendsto (fun k => ∫ x, ‖F k x - f x‖^2 ∂μ) atTop (nhds 0)) :
    Tendsto (fun k => ∫ x, ‖F k x - f x‖^2 ∂ν) atTop (nhds 0) := by
  apply squeeze_zero (fun k => integral_nonneg fun _ => sq_nonneg _) _ h
  intro k
  exact integral_mono_measure hμ (Eventually.of_forall fun _ => sq_nonneg _)
    ((hF k).sub hf).norm.integrable_sq

lemma mollify_realCLM_mul_ofReal (L : ℂ →L[ℝ] ℝ) (z : ℂ) (t : ℝ) :
    L (z * (t : ℂ)) = L z * t := by
  rw [mul_comm, mul_comm (L z)]
  exact L.map_smul t z

lemma euclidean_weak_complex_component {I : Type*} [Fintype I] (u g : EuclideanSpace ℝ I → ℂ)
    (hu : MemLp u 2) (hg : MemLp g 2) (v : EuclideanSpace ℝ I)
    (hw : ∀ (φ : EuclideanSpace ℝ I → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x v : ℂ)) = -(∫ x, g x * (φ x : ℂ)))
    (L : ℂ →L[ℝ] ℝ) (φ : EuclideanSpace ℝ I → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφC : HasCompactSupport φ) :
    (∫ x, L (u x) * fderiv ℝ φ x v) = -(∫ x, L (g x) * φ x) := by
  have hφL : MemLp (fun x => (φ x : ℂ)) 2 :=
    (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
      (hφC.comp_left (by simp))
  have hdφL : MemLp (fun x => (fderiv ℝ φ x v : ℂ)) 2 :=
    (Complex.continuous_ofReal.comp
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
      ((hφC.fderiv_apply ℝ v).comp_left (by simp))
  have hA := L.integral_comp_comm (hu.integrable_mul hdφL)
  have hB := L.integral_comp_comm (hg.integrable_mul hφL)
  simp only [Pi.mul_apply, mollify_realCLM_mul_ofReal] at hA hB
  rw [hA, hw φ hφ hφC, map_neg, ← hB]

lemma realMollify_fderiv {I : Type*} [Fintype I] (k : ℕ)
    {u g : EuclideanSpace ℝ I → ℝ} (hu : MemLp u 2) (v : EuclideanSpace ℝ I)
    (hw : ∀ φ : EuclideanSpace ℝ I → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * fderiv ℝ φ x v) = -(∫ x, g x * φ x))
    (x : EuclideanSpace ℝ I) :
    fderiv ℝ (realMollify k u) x v = realMollify k g x := by
  exact euclidean_weak_convolution_partial u g ((euclideanMollifier k).normed volume) v
    (hu.locallyIntegrable (by norm_num)) (euclideanMollifier k).contDiff_normed
    (euclideanMollifier k).hasCompactSupport_normed hw x

lemma complexMollify_fderiv {I : Type*} [Fintype I] (k : ℕ)
    {u g : EuclideanSpace ℝ I → ℂ} (hu : MemLp u 2) (hg : MemLp g 2)
    (v : EuclideanSpace ℝ I)
    (hw : ∀ φ : EuclideanSpace ℝ I → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x v : ℂ)) = -(∫ x, g x * (φ x : ℂ)))
    (x : EuclideanSpace ℝ I) :
    fderiv ℝ (complexMollify k u) x v = complexMollify k g x := by
  have hr : MemLp (fun x => (u x).re) 2 := Complex.reCLM.comp_memLp' hu
  have hi : MemLp (fun x => (u x).im) 2 := Complex.imCLM.comp_memLp' hu
  have hwr := euclidean_weak_complex_component u g hu hg v hw Complex.reCLM
  have hwi := euclidean_weak_complex_component u g hu hg v hw Complex.imCLM
  have hfr := (realMollify_contDiff k hr).differentiable (by simp)
  have hfi := (realMollify_contDiff k hi).differentiable (by simp)
  have hR := Complex.ofRealCLM.hasFDerivAt.comp x ((hfr x).hasFDerivAt)
  have hJ := Complex.ofRealCLM.hasFDerivAt.comp x ((hfi x).hasFDerivAt)
  have ht := hR.add (hJ.mul_const Complex.I)
  change HasFDerivAt (complexMollify k u) _ x at ht
  rw [ht.fderiv]
  change ((fderiv ℝ (realMollify k (fun y => (u y).re)) x v : ℝ) : ℂ) +
    Complex.I * ((fderiv ℝ (realMollify k (fun y => (u y).im)) x v : ℝ) : ℂ) = _
  rw [realMollify_fderiv k hr v hwr x, realMollify_fderiv k hi v hwi x]
  simp only [complexMollify, Complex.reCLM_apply, Complex.imCLM_apply, mul_comm]

lemma cubeMeasure_le_volume {b : ℝ} {d : ℕ} :
    cubeMeasure b d ≤ (volume : Measure (Fin d → ℝ)) := by
  unfold cubeMeasure
  rw [← Measure.restrict_pi_pi]
  exact Measure.restrict_le_self

lemma insertNth_path_hasDerivAt {d : ℕ} (i : Fin (d+1)) (x : Fin d → ℝ) (t : ℝ) :
    HasDerivAt (fun t => (WithLp.toLp 2 (Fin.insertNth i t x) : EuclideanSpace ℝ (Fin (d+1))))
      (EuclideanSpace.single i 1) t := by
  classical
  have he : (fun t => (WithLp.toLp 2 (Fin.insertNth i t x) : EuclideanSpace ℝ (Fin (d+1)))) =
      (fun t => t • EuclideanSpace.single i 1 + WithLp.toLp 2 (Fin.insertNth i 0 x)) := by
    funext t
    ext j
    obtain rfl | ⟨j, rfl⟩ := i.eq_self_or_eq_succAbove j
    · simp [EuclideanSpace.single]
    · simp [EuclideanSpace.single, Fin.succAbove_ne]
  rw [he]
  simpa using ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))).add_const
    (WithLp.toLp 2 (Fin.insertNth i 0 x) : EuclideanSpace ℝ (Fin (d+1)))

lemma euclidean_hasDerivAt_insertNth {d : ℕ} (i : Fin (d+1)) (x : Fin d → ℝ) (t : ℝ)
    {f : EuclideanSpace ℝ (Fin (d+1)) → ℂ} (hf : Differentiable ℝ f) :
    HasDerivAt (fun t => f (WithLp.toLp 2 (Fin.insertNth i t x)))
      (fderiv ℝ f (WithLp.toLp 2 (Fin.insertNth i t x)) (EuclideanSpace.single i 1)) t := by
  exact (hf _).hasFDerivAt.comp_hasDerivAt t (insertNth_path_hasDerivAt i x t)

theorem cube_weak_axis_spectral_lower {d : ℕ} {b : ℝ} (hb : 0 < b)
    (i : Fin (d+1)) {u g : EuclideanSpace ℝ (Fin (d+1)) → ℂ}
    (hu : MemLp u 2) (hg : MemLp g 2)
    (hw : ∀ φ : EuclideanSpace ℝ (Fin (d+1)) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x (EuclideanSpace.single i 1) : ℂ)) =
        -(∫ x, g x * (φ x : ℂ)))
    (s : Finset ((Fin d → ℕ) × ℕ)) :
    ∑ q ∈ s, ((((q.2 : ℝ) + 1) * Real.pi / b)^2 *
      ‖∫ x, star (cubeMode b (Fin.insertNth i (q.2+1) q.1) x) * u (WithLp.toLp 2 x)
        ∂(cubeMeasure b (d+1))‖^2) ≤
      ∫ x, ‖g (WithLp.toLp 2 x)‖^2 ∂(cubeMeasure b (d+1)) := by
  classical
  let f : (Fin (d+1) → ℝ) → ℂ := fun x => u (WithLp.toLp 2 x)
  let h : (Fin (d+1) → ℝ) → ℂ := fun x => g (WithLp.toLp 2 x)
  let F : ℕ → (Fin (d+1) → ℝ) → ℂ := fun k x => complexMollify k u (WithLp.toLp 2 x)
  let G : ℕ → (Fin (d+1) → ℝ) → ℂ := fun k x => complexMollify k g (WithLp.toLp 2 x)
  have hp := PiLp.volume_preserving_toLp (Fin (d+1))
  have hf : MemLp f 2 volume := hu.comp_measurePreserving hp
  have hh : MemLp h 2 volume := hg.comp_measurePreserving hp
  have hF : ∀ k, MemLp (F k) 2 volume := fun k => (complexMollify_memLp k hu).comp_measurePreserving hp
  have hG : ∀ k, MemLp (G k) 2 volume := fun k => (complexMollify_memLp k hg).comp_measurePreserving hp
  have hFl : Tendsto (fun k => ∫ x, ‖F k x - f x‖^2) atTop (nhds 0) := by
    have he (k : ℕ) : (∫ x, ‖F k x - f x‖^2) = ∫ x, ‖complexMollify k u x - u x‖^2 :=
      by
        simpa only [F, f] using hp.integral_comp
          ((PiLp.homeomorph 2 (fun _ : Fin (d+1) => ℝ)).symm.measurableEmbedding)
          (fun x => ‖complexMollify k u x - u x‖^2)
    simp_rw [he]
    exact complexMollify_L2_tendsto hu
  have hGl : Tendsto (fun k => ∫ x, ‖G k x - h x‖^2) atTop (nhds 0) := by
    have he (k : ℕ) : (∫ x, ‖G k x - h x‖^2) = ∫ x, ‖complexMollify k g x - g x‖^2 :=
      by
        simpa only [G, h] using hp.integral_comp
          ((PiLp.homeomorph 2 (fun _ : Fin (d+1) => ℝ)).symm.measurableEmbedding)
          (fun x => ‖complexMollify k g x - g x‖^2)
    simp_rw [he]
    exact complexMollify_L2_tendsto hg
  have hFb := integral_sq_sub_restrict_tendsto (cubeMeasure_le_volume (b := b)) hf hF hFl
  have hGb := integral_sq_sub_restrict_tendsto (cubeMeasure_le_volume (b := b)) hh hG hGl
  have hfc := hf.mono_measure (cubeMeasure_le_volume (b := b))
  have hhc := hh.mono_measure (cubeMeasure_le_volume (b := b))
  have hFc := fun k => (hF k).mono_measure (cubeMeasure_le_volume (b := b))
  have hGc := fun k => (hG k).mono_measure (cubeMeasure_le_volume (b := b))
  have hk (k : ℕ) := cube_smooth_axis_spectral_lower hb i (hFc k) (hGc k)
    (Eventually.of_forall (fun x t _ => by
      have H := euclidean_hasDerivAt_insertNth i x t ((complexMollify_contDiff k hu).differentiable (by simp))
      rw [complexMollify_fderiv k hu hg (EuclideanSpace.single i 1) hw] at H
      exact H)) s
  apply le_of_tendsto_of_tendsto _ (integral_norm_sq_tendsto_of_L2 hhc hGc hGb)
    (Eventually.of_forall hk)
  apply tendsto_finsetSum
  intro q hq
  apply Tendsto.const_mul
  apply Tendsto.pow
  apply Tendsto.norm
  exact integral_coefficient_tendsto_of_L2 hfc
    (scalarTensor_memLp (neumannMode b) (neumannMode_memLp b) _) hFc hFb

theorem cube_weak_axis_all_frequencies {d : ℕ} {b : ℝ} (hb : 0 < b)
    (i : Fin (d+1)) {u g : EuclideanSpace ℝ (Fin (d+1)) → ℂ}
    (hu : MemLp u 2) (hg : MemLp g 2)
    (hw : ∀ φ : EuclideanSpace ℝ (Fin (d+1)) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x (EuclideanSpace.single i 1) : ℂ)) =
        -(∫ x, g x * (φ x : ℂ)))
    (s : Finset (Fin (d+1) → ℕ)) :
    ∑ q ∈ s, (((q i : ℝ) * Real.pi / b)^2 *
      ‖∫ x, star (cubeMode b q x) * u (WithLp.toLp 2 x)
        ∂(cubeMeasure b (d+1))‖^2) ≤
      ∫ x, ‖g (WithLp.toLp 2 x)‖^2 ∂(cubeMeasure b (d+1)) := by
  classical
  let p : (Fin (d+1) → ℕ) → ((Fin d → ℕ) × ℕ) :=
    fun q => (i.removeNth q, q i - 1)
  have hrec (q : Fin (d+1) → ℕ) (hq : 0 < q i) :
      Fin.insertNth i ((p q).2 + 1) (p q).1 = q := by
    apply Fin.insertNth_eq_iff.mpr
    exact ⟨Nat.sub_add_cancel (by omega), rfl⟩
  have hinj : Set.InjOn p ↑(s.filter (fun q => 0 < q i)) := by
    intro q hq r hr he
    rw [← hrec q (Finset.mem_filter.mp hq).2, ← hrec r (Finset.mem_filter.mp hr).2, he]
  have H := cube_weak_axis_spectral_lower hb i hu hg hw
    ((s.filter (fun q => 0 < q i)).image p)
  rw [Finset.sum_image hinj] at H
  have he : (∑ q ∈ s.filter (fun q => 0 < q i),
      ((q i : ℝ) * Real.pi / b)^2 *
      ‖∫ x, star (cubeMode b q x) * u (WithLp.toLp 2 x)
        ∂(cubeMeasure b (d+1))‖^2) =
      ∑ q ∈ s, ((q i : ℝ) * Real.pi / b)^2 *
      ‖∫ x, star (cubeMode b q x) * u (WithLp.toLp 2 x)
        ∂(cubeMeasure b (d+1))‖^2 := by
    apply Finset.sum_filter_of_ne
    intro q _ hn
    by_contra hh
    have hz : q i = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_mul, zero_div, zero_pow (by omega : 2 ≠ 0)] at hn
    exact hn rfl
  rw [← he]
  convert H using 1
  apply Finset.sum_congr rfl
  intro q hq
  have hqi : 0 < q i := (Finset.mem_filter.mp hq).2
  have hp : (((p q).2 : ℝ) + 1) = (q i : ℝ) := by
    change ((q i - 1 : ℕ) : ℝ) + 1 = (q i : ℝ)
    exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ q i) : q i - 1 + 1 = q i)
  rw [hrec q (Finset.mem_filter.mp hq).2, hp]

theorem cube_weak_spectral_lower {d : ℕ} {b : ℝ} (hb : 0 < b)
    {u : EuclideanSpace ℝ (Fin (d+1)) → ℂ}
    {g : Fin (d+1) → EuclideanSpace ℝ (Fin (d+1)) → ℂ}
    (hu : MemLp u 2) (hg : ∀ i, MemLp (g i) 2)
    (hw : ∀ i (φ : EuclideanSpace ℝ (Fin (d+1)) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x (EuclideanSpace.single i 1) : ℂ)) =
        -(∫ x, g i x * (φ x : ℂ)))
    (s : Finset (Fin (d+1) → ℕ)) :
    ∑ q ∈ s, ((∑ i, ((q i : ℝ) * Real.pi / b)^2) *
      ‖∫ x, star (cubeMode b q x) * u (WithLp.toLp 2 x)
        ∂(cubeMeasure b (d+1))‖^2) ≤
      ∑ i, ∫ x, ‖g i (WithLp.toLp 2 x)‖^2 ∂(cubeMeasure b (d+1)) := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun i _ => cube_weak_axis_all_frequencies hb i hu (hg i) (hw i) s)

noncomputable def latticeRadius (q : Fin 3 → ℕ) : ℝ :=
  ‖WithLp.toLp 2 (fun i => (q i : ℝ))‖

def integerCell (m : Fin 3 → ℤ) : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ioc (m i : ℝ) ((m i : ℝ) + 1))

lemma integerCell_measurable (m : Fin 3 → ℤ) : MeasurableSet (integerCell m) := by
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

lemma integerCell_volume (m : Fin 3 → ℤ) : volume (integerCell m) = 1 := by
  simp [integerCell, Real.volume_pi_Ioc]

lemma integerCell_disjoint {m n : Fin 3 → ℤ} (hmn : m ≠ n) :
    Disjoint (integerCell m) (integerCell n) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hmn
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hm := hx i (Set.mem_univ i)
  have hn := hy i (Set.mem_univ i)
  rcases lt_or_gt_of_ne hi with h | h
  · have hle : (m i : ℝ) + 1 ≤ (n i : ℝ) := by exact_mod_cast h
    linarith [hm.2, hn.1]
  · have hle : (n i : ℝ) + 1 ≤ (m i : ℝ) := by exact_mod_cast h
    linarith [hn.2, hm.1]

lemma piEuclidean_closedBall_volume (r : ℝ) :
    volume {x : Fin 3 → ℝ | ‖WithLp.toLp 2 x‖ ≤ r} =
      ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  have h := PiLp.volume_preserving_toLp (Fin 3)
  have he : {x : Fin 3 → ℝ | ‖WithLp.toLp 2 x‖ ≤ r} =
      (WithLp.toLp 2) ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) r := by
    ext x
    simp [Metric.mem_closedBall, dist_zero_right]
  rw [he, h.measure_preimage (measurableSet_closedBall.nullMeasurableSet),
    EuclideanSpace.volume_closedBall_fin_three]

lemma integerCell_card_le_ball_volume (s : Finset (Fin 3 → ℤ)) (r : ℝ)
    (hs : ∀ m ∈ s, integerCell m ⊆ {x | ‖WithLp.toLp 2 x‖ ≤ r}) :
    (s.card : ℝ≥0∞) ≤ ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  have hd : Set.PairwiseDisjoint (↑s) integerCell := by
    intro m _ n _ hmn
    exact integerCell_disjoint hmn
  have hv : volume (⋃ m ∈ s, integerCell m) = (s.card : ℝ≥0∞) := by
    rw [measure_biUnion_finset hd (fun m _ => integerCell_measurable m)]
    simp [integerCell_volume]
  rw [← piEuclidean_closedBall_volume r, ← hv]
  apply measure_mono
  exact Set.iUnion₂_subset (fun m hm => hs m hm)

def signedCoordinate (b : Bool) (q : ℕ) : ℤ := if b then q else -(q : ℤ) - 1

lemma signedCoordinate_injective : Function.Injective (fun p : Bool × ℕ => signedCoordinate p.1 p.2) := by
  rintro ⟨a, m⟩ ⟨b, n⟩ h
  cases a <;> cases b <;> simp [signedCoordinate] at h ⊢ <;> omega

def signedLattice (a : (Fin 3 → Bool) × (Fin 3 → ℕ)) : Fin 3 → ℤ :=
  fun i => signedCoordinate (a.1 i) (a.2 i)

lemma signedLattice_injective : Function.Injective signedLattice := by
  intro a b h
  have hi (i : Fin 3) : (a.1 i, a.2 i) = (b.1 i, b.2 i) :=
    signedCoordinate_injective (congrFun h i)
  apply Prod.ext <;> funext i
  · exact congrArg Prod.fst (hi i)
  · exact congrArg Prod.snd (hi i)

lemma signedCell_abs_le {a : (Fin 3 → Bool) × (Fin 3 → ℕ)}
    {x : Fin 3 → ℝ} (hx : x ∈ integerCell (signedLattice a)) (i : Fin 3) :
    |x i| ≤ (a.2 i : ℝ) + 1 := by
  have h := hx i (Set.mem_univ i)
  change (signedCoordinate (a.1 i) (a.2 i) : ℝ) < x i ∧
    x i ≤ (signedCoordinate (a.1 i) (a.2 i) : ℝ) + 1 at h
  cases hd : a.1 i <;> simp [signedCoordinate, hd] at h
  · apply abs_le.mpr
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (a.2 i)]
  · apply abs_le.mpr
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (a.2 i)]

lemma signedCell_radius_le {a : (Fin 3 → Bool) × (Fin 3 → ℕ)}
    {x : Fin 3 → ℝ} (hx : x ∈ integerCell (signedLattice a)) :
    ‖WithLp.toLp 2 x‖ ≤ latticeRadius a.2 + Real.sqrt 3 := by
  let q : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun i => (a.2 i : ℝ))
  let e : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun _ => 1)
  have hle : ‖WithLp.toLp 2 x‖ ^ 2 ≤ ‖q+e‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    change ‖x i‖^2 ≤ ‖(a.2 i : ℝ) + 1‖^2
    simp only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (a.2 i : ℝ) + 1 by positivity)]
    exact pow_le_pow_left₀ (abs_nonneg _) (signedCell_abs_le hx i) 2
  have hnorm : ‖WithLp.toLp 2 x‖ ≤ ‖q+e‖ := by
    nlinarith [norm_nonneg (q+e), norm_nonneg (WithLp.toLp 2 x)]
  have he : ‖e‖ = Real.sqrt 3 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [e, Fin.sum_univ_succ]
  calc
    ‖WithLp.toLp 2 x‖ ≤ ‖q+e‖ := hnorm
    _ ≤ ‖q‖ + ‖e‖ := norm_add_le q e
    _ = latticeRadius a.2 + Real.sqrt 3 := by rw [he]; rfl

theorem spin_two_lattice_count (s : Finset (Fin 3 → ℕ)) {r : ℝ}
    (hr : 0 ≤ r) (hs : ∀ q ∈ s, latticeRadius q ≤ r) :
    2 * (s.card : ℝ) ≤ (Real.pi / 3) * (r + Real.sqrt 3)^3 := by
  classical
  let a : Finset ((Fin 3 → Bool) × (Fin 3 → ℕ)) := Finset.univ ×ˢ s
  let t := a.image signedLattice
  have H := integerCell_card_le_ball_volume t (r + Real.sqrt 3) (by
    intro m hm x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    have h := signedCell_radius_le hx
    exact h.trans (add_le_add (hs p.2 (Finset.mem_product.mp hp).2) le_rfl))
  have ht : t.card = 8 * s.card := by
    rw [Finset.card_image_of_injective _ signedLattice_injective, Finset.card_product]
    simp
  rw [ht] at H
  have hR : 0 ≤ r + Real.sqrt 3 := by positivity
  have hp : 0 ≤ Real.pi * 4 / 3 := by positivity
  rw [← ENNReal.ofReal_pow hR, ← ENNReal.ofReal_mul (pow_nonneg hR 3)] at H
  have hnat : ((8 * s.card : ℕ) : ℝ≥0∞) = ENNReal.ofReal (8 * (s.card : ℝ)) := by
    simp
  rw [hnat] at H
  have HH := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (pow_nonneg hR 3) hp)).mp H
  nlinarith

end Coulomb
end
end

end OAI
