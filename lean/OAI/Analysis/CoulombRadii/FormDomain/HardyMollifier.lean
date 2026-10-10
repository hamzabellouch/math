import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.RegularizedHardyField

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open ContinuousLinearMap
open scoped Convolution

noncomputable def hardyMollifier {n : ℕ} (k : ℕ) : ContDiffBump (0 : Configuration n) where
  rIn := 1 / ((k : ℝ) + 1)
  rOut := 2 / ((k : ℝ) + 1)
  rIn_pos := one_div_pos.mpr (by positivity)
  rIn_lt_rOut := div_lt_div_of_pos_right (by norm_num) (by positivity)

lemma hardyMollifier_tendsto {n : ℕ} :
    Filter.Tendsto (fun k => (hardyMollifier (n := n) k).rOut) Filter.atTop (nhds 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  simpa only [hardyMollifier, mul_one_div, mul_zero] using h

lemma weak_compact_hardy {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (u : Configuration n → ℝ) (g : Fin 3 → Configuration n → ℝ)
    (hu : MemLp u 2) (hg : ∀ b, MemLp (g b) 2)
    (huC : HasCompactSupport u)
    (hw : ∀ b (φ : Configuration n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * fderiv ℝ φ x (EuclideanSpace.single (i,b) 1)) =
        -(∫ x, g b x * φ x)) :
    Integrable (fun x => (blockRadiusSq i R x)⁻¹ * (u x)^2) ∧
    (∫ x, (blockRadiusSq i R x)⁻¹ * (u x)^2) ≤
      4 * ∑ b : Fin 3, ∫ x, (g b x)^2 := by
  let κ : ℕ → Configuration n → ℝ := fun k => (hardyMollifier k).normed volume
  have hκ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (κ k) := fun k =>
    (hardyMollifier k).contDiff_normed
  have hκC : ∀ k, HasCompactSupport (κ k) := fun k =>
    (hardyMollifier k).hasCompactSupport_normed
  have hκn : ∀ k x, 0 ≤ κ k x := fun k x => (hardyMollifier k).nonneg_normed x
  have hκI : ∀ k, (∫ x, κ k x) = 1 := fun k => (hardyMollifier k).integral_normed
  have hul : LocallyIntegrable u := hu.locallyIntegrable (by norm_num)
  have hus : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (κ k ⋆ u) := fun k =>
    (hκC k).contDiff_convolution_left (lsmul ℝ ℝ) (hκ k) hul
  have huc : ∀ k, HasCompactSupport (κ k ⋆ u) := fun k =>
    (hκC k).convolution (lsmul ℝ ℝ) huC
  have hh := fun k => smooth_compact_hardy i R (κ k ⋆ u) (hus k) (huc k)
  have ht : ∀ᵐ x ∂volume,
      Filter.Tendsto (fun k => (κ k ⋆ u) x) Filter.atTop (nhds (u x)) := by
    apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (φ := fun k => hardyMollifier k) (K := 2) hardyMollifier_tendsto _ hul
    apply Filter.Eventually.of_forall
    intro k
    simp only [hardyMollifier]
    simp only [mul_one_div, le_refl]
  apply ae_nonneg_fatou_integrable volume _
    (fun k x => (blockRadiusSq i R x)⁻¹ * ((κ k ⋆ u) x)^2) _
    (fun k => (hh k).1)
    (fun k x => mul_nonneg (inv_nonneg.mpr (blockRadiusSq_nonneg i R x)) (sq_nonneg _))
    (fun x => mul_nonneg (inv_nonneg.mpr (blockRadiusSq_nonneg i R x)) (sq_nonneg _))
  · filter_upwards [ht] with x hx
    exact (hx.pow 2).const_mul _
  · intro k
    apply (hh k).2.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro b _
    have heq : ∀ x, fderiv ℝ (κ k ⋆ u) x (EuclideanSpace.single (i,b) 1) =
        (κ k ⋆ g b) x := by
      intro x
      exact weak_convolution_partial u (g b) (κ k) _ hul (hκ k) (hκC k) (hw b) x
    simp_rw [heq]
    exact (convolution_sq_integral_le (κ k) (g b) (hκ k).continuous (hκC k)
      (hκn k) (hκI k) ((hg b).locallyIntegrable (by norm_num)) (hg b).integrable_sq).2

lemma ae_nonneg_fatou_integrable_of_bound_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (F : ℕ → X → ℝ) (C : ℝ) (B : ℕ → ℝ)
    (hF : ∀ n, Integrable (F n) μ) (hn : ∀ n x, 0 ≤ F n x)
    (hf : ∀ x, 0 ≤ f x)
    (ht : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x)))
    (hC : ∀ n, (∫ x, F n x ∂μ) ≤ B n)
    (hB : Filter.Tendsto B Filter.atTop (nhds C)) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ C := by
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n => (hF n).aestronglyMeasurable)
      ht
  have hb : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (F n x)) Filter.atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ht] with x hx
        exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
      _ ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) Filter.atTop :=
        lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ Filter.liminf (fun n => ENNReal.ofReal (B n)) Filter.atTop := by
        apply Filter.liminf_le_liminf (hv := Filter.isBoundedUnder_of ⟨0, fun _ => bot_le⟩)
          (hu := Filter.isCoboundedUnder_ge_of_le Filter.atTop (fun _ => le_top))
        apply Filter.Eventually.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (Filter.Eventually.of_forall (hn n))]
        exact ENNReal.ofReal_le_ofReal (hC n)
      _ = ENNReal.ofReal C := ((ENNReal.continuous_ofReal.tendsto C).comp hB).liminf_eq
  have hfinite : Integrable f μ := ⟨hfm,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf)).2
      (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)⟩
  refine ⟨hfinite, ?_⟩
  have hCn : 0 ≤ C := ge_of_tendsto hB
    (Filter.Eventually.of_forall (fun n => (integral_nonneg (hn n)).trans (hC n)))
  rw [← ofReal_integral_eq_lintegral_ofReal hfinite (Filter.Eventually.of_forall hf)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hCn).1 hb

lemma realMemLp_bounded_mul {n : ℕ} (u f : Configuration n → ℝ)
    (hu : MemLp u 2) (hf : Continuous f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    MemLp (fun x => f x * u x) 2 := by
  apply hu.of_le_mul (c := B) (hf.aestronglyMeasurable.mul hu.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  change ‖f x * u x‖ ≤ B * ‖u x‖
  rw [norm_mul, Real.norm_eq_abs (f x)]
  exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

lemma weak_partial_bounded_mul {n : ℕ} (u g f : Configuration n → ℝ)
    (v : Configuration n) (hu : MemLp u 2) (hg : MemLp g 2)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {B D : ℝ} (hB : ∀ x, |f x| ≤ B) (hD : ∀ x, |fderiv ℝ f x v| ≤ D)
    (hw : ∀ φ : Configuration n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * fderiv ℝ φ x v) = -(∫ x, g x * φ x))
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφC : HasCompactSupport φ) :
    (∫ x, (f x * u x) * fderiv ℝ φ x v) =
      -(∫ x, (f x * g x + fderiv ℝ f x v * u x) * φ x) := by
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφL : MemLp φ 2 := hφ.continuous.memLp_of_hasCompactSupport hφC
  have hdφL : MemLp (fun x => fderiv ℝ φ x v) 2 :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hφC.fderiv_apply ℝ v)
  have hA : Integrable (fun x => (f x * u x) * fderiv ℝ φ x v) := (realMemLp_bounded_mul u f hu hf.continuous hB).integrable_mul hdφL
  have hB' : Integrable (fun x => (fderiv ℝ f x v * u x) * φ x) := (realMemLp_bounded_mul u _ hu hdf hD).integrable_mul hφL
  have hC : Integrable (fun x => (f x * g x) * φ x) := (realMemLp_bounded_mul g f hg hf.continuous hB).integrable_mul hφL
  have hweak := hw (f * φ) (hf.mul hφ) hφC.mul_left
  have hprod : ∀ x, u x * fderiv ℝ (f * φ) x v =
      (f x * u x) * fderiv ℝ φ x v + (fderiv ℝ f x v * u x) * φ x := by
    intro x
    rw [fderiv_mul (hf.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp_rw [hprod] at hweak
  rw [integral_add hA hB'] at hweak
  have hr : ∀ x, g x * (f * φ) x = (f x * g x) * φ x := by
    intro x
    simp only [Pi.mul_apply]
    ring
  simp_rw [hr] at hweak
  simp_rw [add_mul]
  rw [integral_add hC hB']
  linarith

lemma fderiv_smul_input {n : ℕ} (f : Configuration n → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) (x v : Configuration n) :
    fderiv ℝ (fun z => f (c • z)) x v = c * fderiv ℝ f (c • x) v := by
  have hd := ((hf.differentiable (by simp) (c • x)).hasFDerivAt).comp x
    ((hasFDerivAt_id x).const_smul c)
  change HasFDerivAt (fun z => f (c • z)) _ x at hd
  rw [hd.fderiv]
  simp

lemma exists_hardyCutoffs (n : ℕ) :
    ∃ (χ : ℕ → Configuration n → ℝ) (D : ℝ),
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (χ k)) ∧
      (∀ k, HasCompactSupport (χ k)) ∧
      (∀ k x, |χ k x| ≤ 1) ∧
      (∀ k a x, |fderiv ℝ (χ k) x (EuclideanSpace.single a 1)| ≤ D) ∧
      (∀ x, Filter.Tendsto (fun k => χ k x) Filter.atTop (nhds 1)) ∧
      (∀ a x, Filter.Tendsto (fun k => fderiv ℝ (χ k) x
        (EuclideanSpace.single a 1)) Filter.atTop (nhds 0)) := by
  let β : ContDiffBump (0 : Configuration n) := ⟨1, 2, by norm_num, by norm_num⟩
  let c : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hc : ∀ k, 0 < c k := fun k => one_div_pos.mpr (by positivity)
  have hc1 : ∀ k, c k ≤ 1 := by
    intro k
    simpa only [c, div_one] using
      one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num)
        (show (1 : ℝ) ≤ (k : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) k])
  have hct : Filter.Tendsto c Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hβ : ContDiff ℝ (⊤ : ℕ∞) (β : Configuration n → ℝ) := β.contDiff
  have hβC := β.hasCompactSupport
  have hβ1 : β 0 = 1 := β.one_of_mem_closedBall (by simp [β])
  obtain ⟨D, hD⟩ := ((hβC.fderiv ℝ).isCompact_range
    (hβ.continuous_fderiv (by simp))).exists_bound_of_continuousOn
      (f := fun z => z) continuous_id.continuousOn
  have hD' : ∀ x, ‖fderiv ℝ (β : Configuration n → ℝ) x‖ ≤ D :=
    fun x => hD _ ⟨x, rfl⟩
  have hDn : 0 ≤ D := (norm_nonneg _).trans (hD' 0)
  refine ⟨fun k x => β (c k • x), D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact hβ.comp (contDiff_id.const_smul (c k))
  · intro k
    exact hβC.comp_homeomorph (Homeomorph.smulOfNeZero (c k) (hc k).ne')
  · intro k x
    rw [abs_of_nonneg β.nonneg]
    exact β.le_one
  · intro k a x
    rw [fderiv_smul_input _ hβ, abs_mul, abs_of_pos (hc k)]
    have hnorm : |fderiv ℝ (β : Configuration n → ℝ) (c k • x)
        (EuclideanSpace.single a 1)| ≤ D := by
      calc
        _ = ‖fderiv ℝ (β : Configuration n → ℝ) (c k • x)
          (EuclideanSpace.single a 1)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ (β : Configuration n → ℝ) (c k • x)‖ *
          ‖EuclideanSpace.single (𝕜 := ℝ) a 1‖ := le_opNorm _ _
        _ ≤ D := by simpa using hD' (c k • x)
    exact (mul_le_mul_of_nonneg_left hnorm (hc k).le).trans
      (mul_le_of_le_one_left hDn (hc1 k))
  · intro x
    have ht : Filter.Tendsto (fun k => c k • x) Filter.atTop (nhds 0) := by
      simpa using hct.smul_const x
    simpa only [Function.comp_def, hβ1] using (hβ.continuous.tendsto 0).comp ht
  · intro a x
    have ht : Filter.Tendsto (fun k => c k • x) Filter.atTop (nhds 0) := by
      simpa using hct.smul_const x
    have hdf : Continuous (fun z => fderiv ℝ (β : Configuration n → ℝ) z
        (EuclideanSpace.single a 1)) :=
      (hβ.continuous_fderiv (by simp)).clm_apply continuous_const
    simp_rw [fderiv_smul_input _ hβ]
    simpa only [Function.comp_def, zero_mul] using hct.mul ((hdf.tendsto 0).comp ht)

lemma weak_hardy {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (u : Configuration n → ℝ) (g : Fin 3 → Configuration n → ℝ)
    (hu : MemLp u 2) (hg : ∀ b, MemLp (g b) 2)
    (hw : ∀ b (φ : Configuration n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * fderiv ℝ φ x (EuclideanSpace.single (i,b) 1)) =
        -(∫ x, g b x * φ x)) :
    Integrable (fun x => (blockRadiusSq i R x)⁻¹ * (u x)^2) ∧
    (∫ x, (blockRadiusSq i R x)⁻¹ * (u x)^2) ≤
      4 * ∑ b : Fin 3, ∫ x, (g b x)^2 := by
  obtain ⟨χ, D, hχ, hχC, hχB, hχD, hχt, hχdt⟩ := exists_hardyCutoffs n
  let G : ℕ → Fin 3 → Configuration n → ℝ := fun k b x =>
    χ k x * g b x + fderiv ℝ (χ k) x (EuclideanSpace.single (i,b) 1) * u x
  have hdf : ∀ k b, Continuous (fun x => fderiv ℝ (χ k) x
      (EuclideanSpace.single (i,b) 1)) := fun k b =>
    ((hχ k).continuous_fderiv (by simp)).clm_apply continuous_const
  have hG : ∀ k b, MemLp (G k b) 2 := fun k b =>
    (realMemLp_bounded_mul (g b) (χ k) (hg b) (hχ k).continuous (hχB k)).add
      (realMemLp_bounded_mul u _ hu (hdf k b) (hχD k (i,b)))
  have hU : ∀ k, MemLp (fun x => χ k x * u x) 2 := fun k =>
    realMemLp_bounded_mul u (χ k) hu (hχ k).continuous (hχB k)
  have hUC : ∀ k, HasCompactSupport (fun x => χ k x * u x) := fun k =>
    (hχC k).mul_right
  have hW := fun k => weak_compact_hardy i R (fun x => χ k x * u x) (G k)
    (hU k) (hG k) (hUC k) (fun b φ hφ hφC =>
      weak_partial_bounded_mul u (g b) (χ k) _ hu (hg b) (hχ k) (hχB k)
        (hχD k (i,b)) (hw b) φ hφ hφC)
  have hGt : ∀ b x, Filter.Tendsto (fun k => G k b x) Filter.atTop (nhds (g b x)) := by
    intro b x
    have h := ((hχt x).mul_const (g b x)).add ((hχdt (i,b) x).mul_const (u x))
    simpa only [G, one_mul, zero_mul, add_zero] using h
  have hDnonneg : 0 ≤ D := (abs_nonneg _).trans (hχD 0 (i,0) 0)
  have hbound : ∀ k b x, |(G k b x)^2| ≤ 2 * (g b x)^2 + 2 * D^2 * (u x)^2 := by
    intro k b x
    rw [abs_of_nonneg (sq_nonneg _)]
    have hX : (χ k x)^2 ≤ 1 := by
      nlinarith [(sq_le_sq₀ (abs_nonneg (χ k x)) zero_le_one).mpr (hχB k x), sq_abs (χ k x)]
    have hY : (fderiv ℝ (χ k) x (EuclideanSpace.single (i,b) 1))^2 ≤ D^2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hDnonneg).mpr (hχD k (i,b) x)
    have hx := mul_le_mul_of_nonneg_right hX (sq_nonneg (g b x))
    have hy := mul_le_mul_of_nonneg_right hY (sq_nonneg (u x))
    dsimp only [G]
    nlinarith [sq_nonneg (χ k x * g b x -
      fderiv ℝ (χ k) x (EuclideanSpace.single (i,b) 1) * u x)]
  have hIt : ∀ b, Filter.Tendsto (fun k => ∫ x, (G k b x)^2) Filter.atTop
      (nhds (∫ x, (g b x)^2)) := by
    intro b
    apply tendsto_integral_of_dominated_convergence
      (fun x => 2 * (g b x)^2 + 2 * D^2 * (u x)^2)
    · intro k
      exact ((hG k b).aestronglyMeasurable.pow 2)
    · exact ((hg b).integrable_sq.const_mul 2).add (hu.integrable_sq.const_mul (2 * D^2))
    · intro k
      exact Filter.Eventually.of_forall (fun x => hbound k b x)
    · exact Filter.Eventually.of_forall (fun x => (hGt b x).pow 2)
  apply ae_nonneg_fatou_integrable_of_bound_tendsto volume _
    (fun k x => (blockRadiusSq i R x)⁻¹ * (χ k x * u x)^2) _
    (fun k => 4 * ∑ b : Fin 3, ∫ x, (G k b x)^2)
    (fun k => (hW k).1)
    (fun k x => mul_nonneg (inv_nonneg.mpr (blockRadiusSq_nonneg i R x)) (sq_nonneg _))
    (fun x => mul_nonneg (inv_nonneg.mpr (blockRadiusSq_nonneg i R x)) (sq_nonneg _))
  · apply Filter.Eventually.of_forall
    intro x
    have ht := (((hχt x).mul_const (u x)).pow 2).const_mul ((blockRadiusSq i R x)⁻¹)
    simpa only [one_mul] using ht
  · exact fun k => (hW k).2
  · exact (tendsto_finsetSum _ (fun b _ => hIt b)).const_mul 4

noncomputable def nuclearHardyCoordinates {n : ℕ} (i : Fin n) (R : Space) :
    HardyCoordinates n i where
  coord b x := x (i,b) - R b
  smooth b := (EuclideanSpace.proj (𝕜 := ℝ) (i,b)).contDiff.sub contDiff_const
  directional a b x := by
    have hd := ((EuclideanSpace.proj (𝕜 := ℝ) (i,a)).hasFDerivAt (x := x)).sub_const (R a)
    simp only [EuclideanSpace.coe_proj] at hd
    rw [hd.fderiv]
    by_cases hab : a = b
    · subst a; simp
    · simp [EuclideanSpace.proj, EuclideanSpace.single, hab]

noncomputable def pairHardyCoordinates {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    HardyCoordinates n i where
  coord b x := x (i,b) - x (j,b)
  smooth b := (EuclideanSpace.proj (𝕜 := ℝ) (i,b)).contDiff.sub
    (EuclideanSpace.proj (𝕜 := ℝ) (j,b)).contDiff
  directional a b x := by
    have hd := ((EuclideanSpace.proj (𝕜 := ℝ) (i,a)).hasFDerivAt (x := x)).sub
      ((EuclideanSpace.proj (𝕜 := ℝ) (j,a)).hasFDerivAt (x := x))
    simp only [EuclideanSpace.coe_proj] at hd
    change HasFDerivAt (fun x => x (i,a) - x (j,a)) _ x at hd
    rw [hd.fderiv]
    by_cases hab : a = b
    · subst a; simp [EuclideanSpace.proj, EuclideanSpace.single, hij.symm]
    · simp [EuclideanSpace.proj, EuclideanSpace.single, hab, hij.symm]

lemma realCLM_mul_ofReal (L : ℂ →L[ℝ] ℝ) (z : ℂ) (t : ℝ) :
    L (z * (t : ℂ)) = L z * t := by
  rw [mul_comm, mul_comm (L z)]
  exact L.map_smul t z

lemma weak_complex_component {n : ℕ} (u g : Configuration n → ℂ)
    (hu : MemLp u 2) (hg : MemLp g 2) (v : Configuration n)
    (hw : ∀ (φ : Configuration n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x v : ℂ)) = -(∫ x, g x * (φ x : ℂ)))
    (L : ℂ →L[ℝ] ℝ) (φ : Configuration n → ℝ)
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
  simp only [Pi.mul_apply, realCLM_mul_ofReal] at hA hB
  rw [hA, hw φ hφ hφC, map_neg, ← hB]

lemma complex_norm_sq_components (z : ℂ) : ‖z‖^2 = z.re^2 + z.im^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

lemma complex_weak_hardy {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (u : Configuration n → ℂ) (g : Fin 3 → Configuration n → ℂ)
    (hu : MemLp u 2) (hg : ∀ b, MemLp (g b) 2)
    (hw : ∀ b (φ : Configuration n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x (EuclideanSpace.single (i,b) 1) : ℂ)) =
        -(∫ x, g b x * (φ x : ℂ))) :
    Integrable (fun x => (blockRadiusSq i R x)⁻¹ * ‖u x‖^2) ∧
    (∫ x, (blockRadiusSq i R x)⁻¹ * ‖u x‖^2) ≤
      4 * ∑ b : Fin 3, ∫ x, ‖g b x‖^2 := by
  have huR := Complex.reCLM.comp_memLp' hu
  have huI := Complex.imCLM.comp_memLp' hu
  have hgR := fun b => Complex.reCLM.comp_memLp' (hg b)
  have hgI := fun b => Complex.imCLM.comp_memLp' (hg b)
  have hr := weak_hardy i R (fun x => (u x).re) (fun b x => (g b x).re) huR hgR
    (fun b φ hφ hφC => weak_complex_component u (g b) hu (hg b) _ (hw b)
      Complex.reCLM φ hφ hφC)
  have hi := weak_hardy i R (fun x => (u x).im) (fun b x => (g b x).im) huI hgI
    (fun b φ hφ hφC => weak_complex_component u (g b) hu (hg b) _ (hw b)
      Complex.imCLM φ hφ hφC)
  have hsplit : ∀ x, (blockRadiusSq i R x)⁻¹ * ‖u x‖^2 =
      (blockRadiusSq i R x)⁻¹ * (u x).re^2 + (blockRadiusSq i R x)⁻¹ * (u x).im^2 :=
    fun x => by rw [complex_norm_sq_components, mul_add]
  constructor
  · have hsum : Integrable (fun x => (blockRadiusSq i R x)⁻¹ * (u x).re^2 +
        (blockRadiusSq i R x)⁻¹ * (u x).im^2) := hr.1.add hi.1
    exact hsum.congr (Filter.Eventually.of_forall (fun x => (hsplit x).symm))
  · simp_rw [hsplit]
    rw [integral_add hr.1 hi.1]
    have hb : ∀ b, (∫ x, ‖g b x‖^2) =
        (∫ x, (g b x).re^2) + (∫ x, (g b x).im^2) := by
      intro b
      simp_rw [complex_norm_sq_components]
      exact integral_add (hgR b).integrable_sq (hgI b).integrable_sq
    simp_rw [hb]
    rw [Finset.sum_add_distrib, mul_add]
    exact add_le_add hr.2 hi.2

lemma H1Vector.hardy {n : ℕ} (ψ : H1Vector n) (s : Spins n)
    (i : Fin n) (R : HardyCoordinates n i) :
    Integrable (fun x => (blockRadiusSq i R x)⁻¹ * ‖ψ.value s x‖^2) ∧
    (∫ x, (blockRadiusSq i R x)⁻¹ * ‖ψ.value s x‖^2) ≤
      4 * ∑ b : Fin 3, ∫ x, ‖ψ.gradient s (i,b) x‖^2 :=
  complex_weak_hardy i R (ψ.value s) (fun b => ψ.gradient s (i,b))
    (ψ.value_L2 s) (fun b => ψ.partial_L2 s (i,b)) (fun b => ψ.weak_partial s (i,b))

noncomputable def hardyCoulomb {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (x : Configuration n) : ℝ := (Real.sqrt (blockRadiusSq i R x))⁻¹

lemma hardyCoulomb_nonneg {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (x : Configuration n) : 0 ≤ hardyCoulomb i R x := inv_nonneg.mpr (Real.sqrt_nonneg _)

lemma hardyCoulomb_sq {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (x : Configuration n) : (hardyCoulomb i R x)^2 = (blockRadiusSq i R x)⁻¹ := by
  rw [hardyCoulomb, inv_pow, Real.sq_sqrt (blockRadiusSq_nonneg i R x)]

lemma measurable_hardyCoulomb {n : ℕ} (i : Fin n) (R : HardyCoordinates n i) :
    Measurable (hardyCoulomb i R) :=
  (contDiff_blockRadiusSq i R).continuous.measurable.sqrt.inv

lemma quadratic_young_reciprocal (t : ℝ) {η : ℝ} (hη : 0 < η) :
    t ≤ η * t^2 + 1 / (4 * η) := by
  calc
    t ≤ (4 * η^2 * t^2 + 1) / (4 * η) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * η)).mpr
      nlinarith [sq_nonneg (2 * η * t - 1)]
    _ = η * t^2 + 1 / (4 * η) := by field_simp

lemma H1Vector.coulomb_integrable_bound {n : ℕ} (ψ : H1Vector n) (s : Spins n)
    (i : Fin n) (R : HardyCoordinates n i) {η : ℝ} (hη : 0 < η) :
    Integrable (fun x => hardyCoulomb i R x * ‖ψ.value s x‖^2) ∧
    (∫ x, hardyCoulomb i R x * ‖ψ.value s x‖^2) ≤
      4 * η * (∑ b : Fin 3, ∫ x, ‖ψ.gradient s (i,b) x‖^2) +
      (1 / (4 * η)) * (∫ x, ‖ψ.value s x‖^2) := by
  have hH := ψ.hardy s i R
  have hρ : Integrable (fun x => ‖ψ.value s x‖^2) :=
    (memLp_two_iff_integrable_sq_norm (ψ.value_L2 s).aestronglyMeasurable).mp (ψ.value_L2 s)
  have hB : Integrable (fun x => η * ((blockRadiusSq i R x)⁻¹ * ‖ψ.value s x‖^2) +
      (1 / (4 * η)) * ‖ψ.value s x‖^2) :=
    (hH.1.const_mul η).add (hρ.const_mul (1 / (4 * η)))
  have hpoint : ∀ x, hardyCoulomb i R x * ‖ψ.value s x‖^2 ≤
      η * ((blockRadiusSq i R x)⁻¹ * ‖ψ.value s x‖^2) +
      (1 / (4 * η)) * ‖ψ.value s x‖^2 := by
    intro x
    have ht := mul_le_mul_of_nonneg_right
      (quadratic_young_reciprocal (hardyCoulomb i R x) hη) (sq_nonneg ‖ψ.value s x‖)
    simpa only [hardyCoulomb_sq, add_mul, mul_assoc] using ht
  have hI : Integrable (fun x => hardyCoulomb i R x * ‖ψ.value s x‖^2) := by
    apply hB.mono' ((measurable_hardyCoulomb i R).aestronglyMeasurable.mul
      ((ψ.value_L2 s).aestronglyMeasurable.norm.pow 2))
    apply Filter.Eventually.of_forall
    intro x
    simpa only [Pi.mul_apply, Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (hardyCoulomb_nonneg i R x) (sq_nonneg _))] using hpoint x
  refine ⟨hI, ?_⟩
  have hm := integral_mono hI hB hpoint
  rw [integral_add (hH.1.const_mul η) (hρ.const_mul (1 / (4 * η))),
    integral_const_mul, integral_const_mul] at hm
  have hhard := mul_le_mul_of_nonneg_left hH.2 hη.le
  nlinarith

end Coulomb
end
end

end OAI
