import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.GlobalPrepDualNorm
import OAI.Geometry.SmoothYau.Smoothness.SmDualNorm

namespace OAI

namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance oscDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance oscDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance oscFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance oscFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance

lemma preparationWave_second_translate (τ t v w : ℝ) :
    fderiv ℝ (fderiv ℝ (fun z => preparationWave (z+τ))) t v w =
      preparationWaveSecond (t+τ)*v*w := by
  rw [scalar_second_fderiv (smooth_translate preparationWave_smooth τ)]
  have he : deriv (fun z => preparationWave (z+τ)) = fun z => deriv preparationWave (z+τ) := by
    funext z
    exact deriv_comp_add_const (f:=preparationWave) (a:=τ) (x:=z)
  rw [he,deriv_comp_add_const,preparationWave_second]

lemma preparation_hessian_remainder_eq (g : SmoothMetric E E) (u χ s : E → ℝ)
    (C N τ : ℝ) (hN : N ≠ 0) (x : E) :
    actualCoordinateHessian g (preparationCorrugation u χ preparationWave s C N τ) x-
      (actualCoordinateHessian g u x+
        (C*χ x*preparationWaveSecond (N*s x+τ)) • profileRankOne (fderiv ℝ s x)) =
      corrugationSecondRemainder (metricChristoffel g) u χ (fun z => preparationWave (z+τ)) s
        (C/N) N x := by
  have he : ((C/N)*N*χ x) •
        (fderiv ℝ (fderiv ℝ (fun z => preparationWave (z+τ))) (N • s x)).bilinearComp
          (fderiv ℝ s x) (fderiv ℝ s x) =
      (C*χ x*preparationWaveSecond (N*s x+τ)) • profileRankOne (fderiv ℝ s x) := by
    ext v w
    simp only [smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,
      preparationWave_second_translate,profileRankOne_apply]
    field_simp
  rw [corrugationSecondRemainder,he]
  change coordinateCovariantSecond (metricChristoffel g)
    (fun z => u z+(C/N/N)*(χ z*preparationWave (N • s z+τ))) x-
    (coordinateCovariantSecond (metricChristoffel g) u x+_) = _
  abel

theorem preparation_hessian_uniform (g : SmoothMetric E E)
    {u χ s : E → ℝ} (hu : ContDiff ℝ ∞ u) (hχ : ContDiff ℝ ∞ χ) (hs : ContDiff ℝ ∞ s)
    (K : Set E) (hK : IsCompact K) (C : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℝ, 1 ≤ N → ∀ τ : ℝ, ∀ x ∈ K,
      ‖actualCoordinateHessian g (preparationCorrugation u χ preparationWave s C N τ) x-
        (actualCoordinateHessian g u x+
          (C*χ x*preparationWaveSecond (N*s x+τ)) • profileRankOne (fderiv ℝ s x))‖ ≤ A/N := by
  obtain ⟨A,hA,hbound⟩ := preparation_remainder_uniform_phase
    (metricChristoffel g) (contDiff_metricChristoffel g).continuous hu hχ preparationWave_smooth hs
    K hK C (1/(2*Real.pi^2)) (1/Real.pi) preparationWave_abs_bound preparationWave_deriv_bound
  refine ⟨A,hA,?_⟩
  intro N hN τ x hx
  rw [preparation_hessian_remainder_eq g u χ s C N τ (ne_of_gt (lt_of_lt_of_le zero_lt_one hN)) x]
  exact hbound N hN τ x hx

theorem actual_preparation_on_compact_patch (g : SmoothMetric E E)
    {u χ s : E → ℝ} (hu : ContDiff ℝ ∞ u) (hχ : ContDiff ℝ ∞ χ) (hs : ContDiff ℝ ∞ s)
    {K : Set E} (hK : IsCompact K) (C : ℝ) (hC : 0 < C)
    (hcut : ∀ x ∈ K, 0 ≤ χ x ∧ χ x ≤ 1)
    (hq : ∀ x ∈ K, (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0)
    (hstrict : ∀ x ∈ K, ∀ c ∈ Icc (-2*C) (2*C), quadraticPlaneStrict
      (metricProfileTraceForm (selfMetricFlat g x)
        (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
        (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)))
    (hfull : ∀ x ∈ K, ∀ c ∈ Icc C (2*C), quadraticPlaneFull
      (metricProfileTraceForm (selfMetricFlat g x)
        (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
        (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ τ : ℝ, ∀ x ∈ K,
      let u' := preparationCorrugation u χ preparationWave s C N τ
      coordinateMetricGradient g u' x ≠ 0 ∧ actualProfileStrict g u' x ∧
      (χ x = 1 → 1 < preparationWaveSecond (N*s x+τ) → actualProfileFull g u' x) ∧
      |u' x-u x| < ε ∧ ‖fderiv ℝ u' x-fderiv ℝ u x‖ < ε := by
  let H : E × ℝ → CoordinateForm E := fun z => actualCoordinateHessian g u z.1+
    z.2 • profileRankOne (fderiv ℝ s z.1)
  have hH : Continuous H :=
    ((continuous_coordinateCovariantSecond _ (contDiff_metricChristoffel g).continuous hu).comp
      continuous_fst).add (continuous_snd.smul
        (continuous_profileRankOne ((hs.continuous_fderiv (by simp)).comp continuous_fst)))
  have hl : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
  obtain ⟨δS,hδS,hS⟩ := compact_metricJet_stability g (metricJetStrict g)
    (isOpen_metricJetStrict g) hK (isCompact_Icc (a:=(-2*C)) (b:=2*C)) hH hl
    (fun x hx c hc => ⟨hq x hx,hstrict x hx c hc⟩)
  obtain ⟨δF,hδF,hF⟩ := compact_metricJet_stability g (metricJetFull g)
    (isOpen_metricJetFull g) hK (isCompact_Icc (a:=C) (b:=2*C)) hH hl
    (fun x hx c hc => ⟨hq x hx,hfull x hx c hc⟩)
  let δ := min ε (min δS δF)
  have hδ : 0 < δ := lt_min hε (lt_min hδS hδF)
  obtain ⟨A₁,hA₁,h₁⟩ := preparation_C1_uniform_phase hu hχ preparationWave_smooth hs
    K hK C (1/(2*Real.pi^2)) (1/Real.pi) preparationWave_abs_bound preparationWave_deriv_bound
  obtain ⟨A₂,hA₂,h₂⟩ := preparation_hessian_uniform g hu hχ hs K hK C
  let N₀ := max 1 ((A₁+A₂)/δ+1)
  refine ⟨N₀,le_max_left _ _,?_⟩
  intro N hN τ x hx
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hlarge : (A₁+A₂)/δ < N := by
    have hh := (le_max_right 1 ((A₁+A₂)/δ+1)).trans hN
    linarith
  have hsmall : (A₁+A₂)/N < δ := by
    rw [div_lt_iff₀ hNp]
    have hh := (div_lt_iff₀ hδ).mp hlarge
    linarith
  have hsmall₁ : A₁/N < δ := lt_of_le_of_lt (div_le_div_of_nonneg_right (by linarith) hNp.le) hsmall
  have hsmall₂ : A₂/N < δ := lt_of_le_of_lt (div_le_div_of_nonneg_right (by linarith) hNp.le) hsmall
  obtain ⟨hC0,hC1⟩ := h₁ N hN1 τ x hx
  have hHs := h₂ N hN1 τ x hx
  let c := C*χ x*preparationWaveSecond (N*s x+τ)
  have hcb : |c| ≤ 2*C := by
    dsimp [c]
    rw [abs_mul,abs_mul,abs_of_pos hC,abs_of_nonneg (hcut x hx).1]
    calc
      _ ≤ C*1*2 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hcut x hx).2 hC.le
        · exact preparationWave_second_bound _
        · exact abs_nonneg _
        · positivity
      _ = _ := by ring
  have hc : c ∈ Icc (-2*C) (2*C) := by
    constructor <;> linarith [(abs_le.mp hcb).1,(abs_le.mp hcb).2]
  have hs' := hS x hx c hc _ _
    ((hHs.trans_lt hsmall₂).trans_le (min_le_right _ _ |>.trans (min_le_left _ _)))
    ((hC1.trans_lt hsmall₁).trans_le (min_le_right _ _ |>.trans (min_le_left _ _)))
  have hgood := (metricJetStrict_actual g _ x).mp hs'
  refine ⟨hgood.1,hgood.2,?_,(hC0.trans_lt hsmall₁).trans_le (min_le_left _ _),
    (hC1.trans_lt hsmall₁).trans_le (min_le_left _ _)⟩
  intro hx1 hw
  have hcf : c ∈ Icc C (2*C) := by
    refine ⟨?_,hc.2⟩
    dsimp [c]
    rw [hx1,mul_one]
    nlinarith
  have hf' := hF x hx c hcf _ _
    ((hHs.trans_lt hsmall₂).trans_le (min_le_right _ _ |>.trans (min_le_right _ _)))
    ((hC1.trans_lt hsmall₁).trans_le (min_le_right _ _ |>.trans (min_le_right _ _)))
  exact ((metricJetFull_actual g _ x).mp hf').2

end
end YauCounterexamples

end OAI
