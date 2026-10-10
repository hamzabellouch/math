import Mathlib.Algebra.Module.LinearMap.DivisionRing
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.HausdorffDimension
import OAI.Geometry.StableBernstein.Geometry.Geometry

namespace OAI

noncomputable section

namespace StableBernstein.W30
open Set
open scoped ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem iteratedDeriv_affine_line {f : E → ℝ} (hf : ContDiff ℝ 7 f)
    (x v : E) (t : ℝ) (k : ℕ) (hk : k ≤ 7) :
    iteratedDeriv k (fun s : ℝ => f (x + s • v)) t =
      iteratedFDeriv ℝ k f (x + t • v) (fun _ => v) := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hs : ContDiff ℝ 7 (fun z : E => f (x + z)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have h := L.iteratedFDeriv_comp_right hs t (i := k) (by exact_mod_cast hk)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  simpa [Function.comp_def, L, iteratedFDeriv_comp_add_left,
    ContinuousMultilinearMap.compContinuousLinearMap_apply] using
    congrArg (fun T => T (fun _ : Fin k => (1 : ℝ))) h

theorem taylorWithinEval_eq_of_flat (g : ℝ → ℝ) (s : Set ℝ) (a b : ℝ)
    (n : ℕ) (hflat : ∀ k : ℕ, 1 ≤ k → k ≤ n → iteratedDerivWithin k g s a = 0) :
    taylorWithinEval g n s a b = g a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [taylorWithinEval_succ, ih (fun k hk hkn => hflat k hk (by omega)),
      hflat (n + 1) (by omega) le_rfl]
    simp

theorem flat_taylor_bound_segment {f : E → ℝ} (hf : ContDiff ℝ 7 f)
    (x y : E) (C : ℝ)
    (hflat : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → iteratedFDeriv ℝ k f x = 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ 7 f (x + t • (y - x))‖ ≤ C) :
    |f y - f x| ≤ C * ‖y - x‖ ^ 7 / 720 := by
  let g : ℝ → ℝ := fun t => f (x + t • (y - x))
  have hg : ContDiff ℝ 7 g :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hd (k : ℕ) (hk : k ≤ 7) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      iteratedDerivWithin k g (Icc (0 : ℝ) 1) t =
        iteratedFDeriv ℝ k f (x + t • (y - x)) (fun _ => y - x) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((hg.of_le (by exact_mod_cast hk)).contDiffAt) ht]
    exact iteratedDeriv_affine_line hf x (y - x) t k hk
  have hp : taylorWithinEval g 6 (Icc (0 : ℝ) 1) 0 1 = g 0 := by
    apply taylorWithinEval_eq_of_flat
    intro k hk hk6
    rw [hd k (by omega) 0 (by simp)]
    simpa using congrArg (fun T => T (fun _ : Fin k => y - x)) (hflat k hk hk6)
  have hC : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin 7 g (Icc (0 : ℝ) 1) t‖ ≤ C * ‖y - x‖ ^ 7 := by
    intro t ht
    rw [hd 7 le_rfl t ht]
    calc
      _ ≤ ‖iteratedFDeriv ℝ 7 f (x + t • (y - x))‖ * ‖y - x‖ ^ 7 := by
        simpa using (iteratedFDeriv ℝ 7 f (x + t • (y - x))).le_opNorm
          (fun _ : Fin 7 => y - x)
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound t ht) (pow_nonneg (norm_nonneg _) _)
  have h := taylor_mean_remainder_bound (f := g) (n := 6)
    (a := 0) (b := 1) (x := 1) (C := C * ‖y - x‖ ^ 7)
    zero_le_one hg.contDiffOn (by simp) hC
  rw [hp] at h
  simpa [g, Real.norm_eq_abs, Nat.factorial] using h

theorem flat_taylor_bound_convex {f : E → ℝ} (hf : ContDiff ℝ 7 f)
    {s : Set E} (hs : Convex ℝ s) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    (C : ℝ) (hflat : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → iteratedFDeriv ℝ k f x = 0)
    (hbound : ∀ z ∈ s, ‖iteratedFDeriv ℝ 7 f z‖ ≤ C) :
    |f y - f x| ≤ C * ‖y - x‖ ^ 7 / 720 :=
  flat_taylor_bound_segment hf x y C hflat fun _parameter ht =>
    hbound _ (hs.add_smul_sub_mem hx hy ht)

theorem flat_taylor_bound_ball
    {f : EuclideanSpace ℝ (Fin 6) → ℝ} (hf : ContDiff ℝ 7 f)
    (x : EuclideanSpace ℝ (Fin 6)) {r : ℝ} (hr : 0 < r)
    {y : EuclideanSpace ℝ (Fin 6)} (hy : y ∈ Metric.ball x r) (C : ℝ)
    (hflat : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → iteratedFDeriv ℝ k f x = 0)
    (hbound : ∀ z ∈ Metric.ball x r, ‖iteratedFDeriv ℝ 7 f z‖ ≤ C) :
    |f y - f x| ≤ C * ‖y - x‖ ^ 7 / 720 :=
  flat_taylor_bound_convex hf (convex_ball x r) (Metric.mem_ball_self hr) hy C hflat hbound

end StableBernstein.W30

namespace Bernstein.Sard
open MeasureTheory Manifold Bundle Set Filter
open scoped Topology ContDiff
open StableBernstein.W01

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E6 M]

def chartExceptionalValues (f : M → ℝ) (S : Set M) (c : M) : Set ℝ :=
  (f ∘ (extChartAt I6 c).symm) ''
    {z | z ∈ (extChartAt I6 c).target ∧ (extChartAt I6 c).symm z ∈ S}

theorem chartExceptionalValues_eq (f : M → ℝ) (S : Set M) (c : M) :
    chartExceptionalValues f S c = f '' (S ∩ (extChartAt I6 c).source) := by
  ext t
  constructor
  · rintro ⟨z, ⟨hz, hzS⟩, hzt⟩
    exact ⟨(extChartAt I6 c).symm z,
      ⟨hzS, (extChartAt I6 c).map_target hz⟩, hzt⟩
  · rintro ⟨x, ⟨hxS, hx⟩, hxt⟩
    refine ⟨extChartAt I6 c x, ⟨(extChartAt I6 c).map_source hx, ?_⟩, ?_⟩
    · simpa only [(extChartAt I6 c).left_inv hx] using hxS
    · simpa only [Function.comp_apply, (extChartAt I6 c).left_inv hx] using hxt

theorem exists_countable_chart_exceptional_cover [SecondCountableTopology M]
    (f : M → ℝ) (S : Set M) :
    ∃ C : Set M, C.Countable ∧ f '' S = ⋃ c ∈ C, chartExceptionalValues f S c := by
  obtain ⟨C, hC, hcover⟩ := countable_cover_nhds
    (fun c : M => extChartAt_source_mem_nhds (I := I6) c)
  refine ⟨C, hC, ?_⟩
  ext t
  constructor
  · rintro ⟨x, hxS, hxt⟩
    have hxcover : x ∈ ⋃ c ∈ C, (extChartAt I6 c).source := by
      simpa only [hcover] using (mem_univ x)
    obtain ⟨c, hc⟩ := mem_iUnion.mp hxcover
    obtain ⟨hcC, hxc⟩ := mem_iUnion.mp hc
    refine mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨hcC, ?_⟩⟩
    rw [chartExceptionalValues_eq]
    exact ⟨x, ⟨hxS, hxc⟩, hxt⟩
  · intro ht
    obtain ⟨c, hc⟩ := mem_iUnion.mp ht
    obtain ⟨_, htc⟩ := mem_iUnion.mp hc
    rw [chartExceptionalValues_eq] at htc
    obtain ⟨x, hx, hxt⟩ := htc
    exact ⟨x, hx.1, hxt⟩

theorem exceptionalValues_null_of_chart_null [SecondCountableTopology M]
    (f : M → ℝ) (S : Set M)
    (hlocal : ∀ c : M, volume (chartExceptionalValues f S c) = 0) :
    volume (f '' S) = 0 := by
  obtain ⟨C, hC, hcover⟩ := exists_countable_chart_exceptional_cover f S
  rw [hcover]
  exact (measure_biUnion_null_iff hC).mpr (fun c _ => hlocal c)

variable [IsManifold I6 ∞ M]

theorem chart_fderiv_zero_of_mfderiv_zero (f : M → ℝ)
    (hf : ContMDiff I6 𝓘(ℝ, ℝ) ∞ f) (c : M) {z : E6}
    (hz : z ∈ (extChartAt I6 c).target)
    (hzero : mfderiv I6 𝓘(ℝ, ℝ) f ((extChartAt I6 c).symm z) = 0) :
    fderiv ℝ (f ∘ (extChartAt I6 c).symm) z = 0 := by
  have hinv : MDifferentiableAt I6 I6 (extChartAt I6 c).symm z :=
    (mdifferentiableWithinAt_extChartAt_symm (I := I6) hz).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp z
    (hf.mdifferentiable (by simp) ((extChartAt I6 c).symm z)) hinv
  rw [mfderiv_eq_fderiv, hzero, ContinuousLinearMap.zero_comp] at hchain
  exact hchain

theorem criticalValues_null_of_chart_criticalValues_null [SecondCountableTopology M]
    (f : M → ℝ) (hf : ContMDiff I6 𝓘(ℝ, ℝ) ∞ f)
    (hlocal : ∀ c : M, volume ((f ∘ (extChartAt I6 c).symm) ''
      {z | z ∈ (extChartAt I6 c).target ∧
        fderiv ℝ (f ∘ (extChartAt I6 c).symm) z = 0}) = 0) :
    volume (f '' {x | mfderiv I6 𝓘(ℝ, ℝ) f x = 0}) = 0 := by
  apply exceptionalValues_null_of_chart_null
  intro c
  apply measure_mono_null _ (hlocal c)
  rintro t ⟨z, ⟨hz, hzero⟩, hzt⟩
  exact ⟨z, ⟨hz, chart_fderiv_zero_of_mfderiv_zero f hf c hz hzero⟩, hzt⟩

theorem ae_regularValues_of_chart_criticalValues_null [SecondCountableTopology M]
    (f : M → ℝ) (hf : ContMDiff I6 𝓘(ℝ, ℝ) ∞ f)
    (hlocal : ∀ c : M, volume ((f ∘ (extChartAt I6 c).symm) ''
      {z | z ∈ (extChartAt I6 c).target ∧
        fderiv ℝ (f ∘ (extChartAt I6 c).symm) z = 0}) = 0) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ x : M,
      f x = t → Function.Surjective (mfderiv I6 𝓘(ℝ, ℝ) f x) := by
  have hnull := criticalValues_null_of_chart_criticalValues_null f hf hlocal
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with t ht x hxt
  have hne : mfderiv I6 𝓘(ℝ, ℝ) f x ≠ 0 := by
    intro hzero
    exact ht ⟨x, hzero, hxt⟩
  exact (mfderiv I6 𝓘(ℝ, ℝ) f x).toLinearMap.surjective
    (fun hzero => hne (ContinuousLinearMap.coe_injective hzero))

theorem ae_regularValues_of_scalarSard [SecondCountableTopology M]
    (scalarSard : ∀ (U : Set E6), IsOpen U → ∀ (g : E6 → ℝ),
      ContDiffOn ℝ ∞ g U → volume (g '' {z | z ∈ U ∧ fderiv ℝ g z = 0}) = 0)
    (f : M → ℝ) (hf : ContMDiff I6 𝓘(ℝ, ℝ) ∞ f) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ x : M,
      f x = t → Function.Surjective (mfderiv I6 𝓘(ℝ, ℝ) f x) := by
  apply ae_regularValues_of_chart_criticalValues_null f hf
  intro c
  apply scalarSard (extChartAt I6 c).target (isOpen_extChartAt_target c)
  rw [← contMDiffOn_iff_contDiffOn]
  exact hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm c)

end Bernstein.Sard

namespace StableBernstein.W30
open Set
open scoped ContDiff BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem iteratedDeriv_affine_line_local {f : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 7 f U)
    (x v : E) (t : ℝ) (ht : x + t • v ∈ U) (k : ℕ) (hk : k ≤ 7) :
    iteratedDeriv k (fun s : ℝ => f (x + s • v)) t =
      iteratedFDeriv ℝ k f (x + t • v) (fun _ => v) := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  let S : Set E := (fun z : E => x + z) ⁻¹' U
  have hS : IsOpen S := hU.preimage (continuous_const.add continuous_id)
  have hLS : IsOpen (L ⁻¹' S) := hS.preimage L.continuous
  have hs : ContDiffOn ℝ 7 (fun z : E => f (x + z)) S :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hz => hz)
  have htS : L t ∈ S := ht
  have h := L.iteratedFDerivWithin_comp_right hs hS.uniqueDiffOn
    hLS.uniqueDiffOn htS (i := k) (by exact_mod_cast hk)
  rw [(iteratedFDerivWithin_of_isOpen k hLS) htS,
    (iteratedFDerivWithin_of_isOpen k hS) htS] at h
  rw [iteratedDeriv_eq_iteratedFDeriv]
  simpa [Function.comp_def, L, iteratedFDeriv_comp_add_left,
    ContinuousMultilinearMap.compContinuousLinearMap_apply] using
    congrArg (fun T => T (fun _ : Fin k => (1 : ℝ))) h

theorem flat_taylor_bound_segment_local {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 7 f U)
    (x y : E) (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ U) (C : ℝ)
    (hflat : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → iteratedFDeriv ℝ k f x = 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ 7 f (x + t • (y - x))‖ ≤ C) :
    |f y - f x| ≤ C * ‖y - x‖ ^ 7 / 720 := by
  let g : ℝ → ℝ := fun t => f (x + t • (y - x))
  have hga (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ 7 g t :=
    (hf.contDiffAt (hU.mem_nhds (hseg t ht))).comp t
      ((contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffAt)
  have hg : ContDiffOn ℝ 7 g (Icc (0 : ℝ) 1) :=
    fun t ht => (hga t ht).contDiffWithinAt
  have hd (k : ℕ) (hk : k ≤ 7) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      iteratedDerivWithin k g (Icc (0 : ℝ) 1) t =
        iteratedFDeriv ℝ k f (x + t • (y - x)) (fun _ => y - x) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((hga t ht).of_le (by exact_mod_cast hk)) ht]
    exact iteratedDeriv_affine_line_local hU hf x (y - x) t (hseg t ht) k hk
  have hp : taylorWithinEval g 6 (Icc (0 : ℝ) 1) 0 1 = g 0 := by
    apply taylorWithinEval_eq_of_flat
    intro k hk hk6
    rw [hd k (by omega) 0 (by simp)]
    simpa using congrArg (fun T => T (fun _ : Fin k => y - x)) (hflat k hk hk6)
  have hC : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin 7 g (Icc (0 : ℝ) 1) t‖ ≤ C * ‖y - x‖ ^ 7 := by
    intro t ht
    rw [hd 7 le_rfl t ht]
    calc
      _ ≤ ‖iteratedFDeriv ℝ 7 f (x + t • (y - x))‖ * ‖y - x‖ ^ 7 := by
        simpa using (iteratedFDeriv ℝ 7 f (x + t • (y - x))).le_opNorm
          (fun _ : Fin 7 => y - x)
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound t ht) (pow_nonneg (norm_nonneg _) _)
  have h := taylor_mean_remainder_bound (f := g) (n := 6)
    (a := 0) (b := 1) (x := 1) (C := C * ‖y - x‖ ^ 7)
    zero_le_one hg (by simp) hC
  rw [hp] at h
  simpa [g, Real.norm_eq_abs, Nat.factorial] using h

theorem flat_taylor_bound_convex_local {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 7 f U)
    {s : Set E} (hs : Convex ℝ s) (hsU : s ⊆ U) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    (C : ℝ) (hflat : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → iteratedFDeriv ℝ k f x = 0)
    (hbound : ∀ z ∈ s, ‖iteratedFDeriv ℝ 7 f z‖ ≤ C) :
    |f y - f x| ≤ C * ‖y - x‖ ^ 7 / 720 :=
  flat_taylor_bound_segment_local hU hf x y
    (fun _parameter ht => hsU (hs.add_smul_sub_mem hx hy ht)) C hflat fun _parameter ht =>
      hbound _ (hs.add_smul_sub_mem hx hy ht)

end StableBernstein.W30

namespace Bernstein.Sard
open Set Filter MeasureTheory
open scoped ContDiff

theorem scalar_sard_one_dimensional (U : Set ℝ) (hU : IsOpen U)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f U) :
    volume (f '' {x | x ∈ U ∧ fderiv ℝ f x = 0}) = 0 := by
  apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (f' := fderiv ℝ f) volume
  · intro x hx
    exact ((hf.differentiableOn_one.differentiableAt
      (hU.mem_nhds hx.1)).hasFDerivAt).hasFDerivWithinAt
  · intro x hx
    rw [hx.2]
    simp

theorem scalar_sard_one_dimensional_deriv (U : Set ℝ) (hU : IsOpen U)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f U) :
    volume (f '' {x | x ∈ U ∧ deriv f x = 0}) = 0 := by
  have heq : {x | x ∈ U ∧ deriv f x = 0} =
      {x | x ∈ U ∧ fderiv ℝ f x = 0} := by
    ext x
    constructor
    · rintro ⟨hx, hd⟩
      refine ⟨hx, ?_⟩
      apply ContinuousLinearMap.ext
      intro v
      rw [fderiv_eq_smul_deriv, hd]
      simp
    · rintro ⟨hx, hd⟩
      refine ⟨hx, ?_⟩
      rw [← fderiv_apply_one_eq_deriv, hd]
      rfl
  rw [heq]
  exact scalar_sard_one_dimensional U hU f hf

end Bernstein.Sard

namespace StableBernstein.W30
open Set MeasureTheory
open scoped ContDiff NNReal ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sixFlat_holderOn_local {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 7 f U)
    {s K : Set E} (hs : Convex ℝ s) (hsU : s ⊆ U) (hKs : K ⊆ s)
    (hflat : ∀ x ∈ K, ∀ k : ℕ, 1 ≤ k → k ≤ 6 → iteratedFDeriv ℝ k f x = 0) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z ∈ s, ‖iteratedFDeriv ℝ 7 f z‖ ≤ C) :
    HolderOnWith ⟨C / 720, div_nonneg hC (by norm_num)⟩ 7 f K := by
  intro x hx y hy
  have h := flat_taylor_bound_convex_local hU hf hs hsU (hKs hx) (hKs hy) C (hflat x hx) hbound
  have hd : dist (f x) (f y) ≤ (C / 720) * dist x y ^ 7 := by
    simpa [Real.dist_eq, dist_eq_norm, abs_sub_comm, norm_sub_rev,
      div_mul_eq_mul_div] using h
  have he := ENNReal.ofReal_le_ofReal hd
  have hc720 : 0 ≤ C / 720 := div_nonneg hC (by norm_num)
  rw [ENNReal.ofReal_mul hc720, ENNReal.ofReal_pow dist_nonneg,
    ENNReal.ofReal_eq_coe_nnreal hc720] at he
  simpa only [edist_dist, NNReal.coe_ofNat, ENNReal.rpow_natCast, ENNReal.rpow_ofNat,
    NNReal.mk] using he

theorem volume_image_sixFlat_local_eq_zero [FiniteDimensional ℝ E]
    (hdim : (Module.finrank ℝ E : ℝ) < 7) {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 7 f U)
    {s K : Set E} (hs : Convex ℝ s) (hsU : s ⊆ U) (hKs : K ⊆ s)
    (hflat : ∀ x ∈ K, ∀ k : ℕ, 1 ≤ k → k ≤ 6 → iteratedFDeriv ℝ k f x = 0) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z ∈ s, ‖iteratedFDeriv ℝ 7 f z‖ ≤ C) :
    volume (f '' K) = 0 := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  have hH := (sixFlat_holderOn_local hU hf hs hsU hKs hflat C hC hbound).hausdorffMeasure_image_le
    (by norm_num : (0 : ℝ≥0) < 7) (d := 1) (by norm_num)
  have hzero : (Measure.hausdorffMeasure 7 : Measure E) = 0 :=
    Real.hausdorffMeasure_of_finrank_lt (E := E) (d := 7)
      hdim
  have hz : volume (f '' K) ≤ 0 := by
    simpa [MeasureTheory.hausdorffMeasure_real, hzero] using hH
  exact le_antisymm hz zero_le

theorem exists_ball_sixFlat_image_null [FiniteDimensional ℝ E]
    (hdim : (Module.finrank ℝ E : ℝ) < 7)
    {f : E → ℝ} {U K : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 7 f U)
    (hKU : K ⊆ U)
    (hflat : ∀ x ∈ K, ∀ k : ℕ, 1 ≤ k → k ≤ 6 → iteratedFDeriv ℝ k f x = 0)
    {x : E} (hx : x ∈ K) :
    ∃ r : ℝ, 0 < r ∧ volume (f '' (K ∩ Metric.ball x r)) = 0 := by
  let C : ℝ := ‖iteratedFDeriv ℝ 7 f x‖ + 1
  have hC : 0 ≤ C := add_nonneg (norm_nonneg _) zero_le_one
  have hc : ContinuousAt (fun z => ‖iteratedFDeriv ℝ 7 f z‖) x :=
    ((hf.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt_iteratedFDeriv
      (by norm_num)).norm
  have he : {z : E | ‖iteratedFDeriv ℝ 7 f z‖ < C} ∈ 𝓝 x :=
    hc.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hU.mem_nhds (hKU hx)) he)
  refine ⟨r, hr, ?_⟩
  apply volume_image_sixFlat_local_eq_zero hdim hU hf (convex_ball x r)
    (fun _ hz => (hball hz).1) inter_subset_right
    (fun z hz => hflat z hz.1) C hC
  intro z hz
  exact (hball hz).2.le

end StableBernstein.W30

namespace Bernstein.Sard

section
open Set Filter MeasureTheory
open scoped Topology ContDiff

section FiniteDimensional
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem regular_scalar_range [FiniteDimensional ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0) : L.range = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  exact L.toLinearMap.surjective (fun h => hL (ContinuousLinearMap.coe_injective h))

theorem regular_scalar_kernel_dimension (L : E →L[ℝ] ℝ) (hL : L ≠ 0) :
    Module.finrank ℝ L.ker + 1 = Module.finrank ℝ E := by
  have hd := L.toLinearMap.finrank_range_add_finrank_ker
  have hr := regular_scalar_range L hL
  change L.toLinearMap.range = ⊤ at hr
  rw [hr] at hd
  simpa only [finrank_top, Module.finrank_self, Nat.add_comm] using hd

theorem exists_smooth_regular_stratum_chart (U : Set E) (hU : IsOpen U)
    (h : E → ℝ) (hh : ContDiffOn ℝ ∞ h U) (a : E) (ha : a ∈ U)
    (_ha0 : h a = 0) (hreg : fderiv ℝ h a ≠ 0) :
    ∃ (V : Set E) (W : Set (fderiv ℝ h a).ker)
      (ψ : (fderiv ℝ h a).ker → E) (q : E → (fderiv ℝ h a).ker),
      IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧ IsOpen W ∧
      ContDiffOn ℝ ∞ ψ W ∧ MapsTo ψ W U ∧
      (∀ t ∈ W, h (ψ t) = 0 ∧ q (ψ t) = t) ∧
      (∀ x ∈ V, h x = 0 → q x ∈ W ∧ ψ (q x) = x) := by
  let L := fderiv ℝ h a
  have hr : L.range = ⊤ := regular_scalar_range L hreg
  have hs : HasStrictFDerivAt h L a :=
    (hh.contDiffAt (hU.mem_nhds ha)).hasStrictFDerivAt (by simp)
  let hker := L.ker_closedComplemented_of_finiteDimensional_range
  let P : E →L[ℝ] L.ker := Classical.choose hker
  let φ := hs.implicitFunctionDataOfComplemented h L hr hker
  let e := φ.toOpenPartialHomeomorph
  have hae : a ∈ e.source := φ.pt_mem_toOpenPartialHomeomorph_source
  have hg : ContDiffOn ℝ ∞ φ.prodFun U := by
    change ContDiffOn ℝ ∞ (fun x => (h x, P (x - a))) U
    exact hh.prodMk
      ((P.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn)
  have hcg : ContinuousAt (fderiv ℝ φ.prodFun) a :=
    (hg.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt (hU.mem_nhds ha)
  obtain ⟨e₀, he₀⟩ := φ.isInvertible_fderiv_prodFun
  have hpoint : φ.pt = a := rfl
  have hnear : {x : E | ∃ A : E ≃L[ℝ] (ℝ × L.ker),
      (A : E →L[ℝ] (ℝ × L.ker)) = fderiv ℝ φ.prodFun x} ∈ 𝓝 a := by
    have H : Set.range ((↑) : (E ≃L[ℝ] (ℝ × L.ker)) →
        E →L[ℝ] (ℝ × L.ker)) ∈ 𝓝 (fderiv ℝ φ.prodFun a) := by
      simpa only [he₀, hpoint] using e₀.nhds
    exact hcg.preimage_mem_nhds H
  have hnbhd : {x : E | x ∈ U ∧ x ∈ e.source ∧
      ∃ A : E ≃L[ℝ] (ℝ × L.ker),
        (A : E →L[ℝ] (ℝ × L.ker)) = fderiv ℝ φ.prodFun x} ∈ 𝓝 a :=
    inter_mem (hU.mem_nhds ha) (inter_mem (e.open_source.mem_nhds hae) hnear)
  obtain ⟨V, hVs, hV, haV⟩ := mem_nhds_iff.mp hnbhd
  have hVU : V ⊆ U := fun x hx => (hVs hx).1
  have hVe : V ⊆ e.source := fun x hx => (hVs hx).2.1
  let T := e.target ∩ e.symm ⁻¹' V
  have hT : IsOpen T := e.isOpen_inter_preimage_symm hV
  have hTsm : ContDiffOn ℝ ∞ e.symm T := by
    intro p hp
    obtain ⟨A, hA⟩ := (hVs hp.2).2.2
    have hd : HasFDerivAt e (A : E →L[ℝ] (ℝ × L.ker)) (e.symm p) := by
      rw [hA]
      exact ((hg.differentiableOn (by simp)).differentiableAt
        (hU.mem_nhds (hVU hp.2))).hasFDerivAt
    have hc : ContDiffAt ℝ ∞ e (e.symm p) :=
      hg.contDiffAt (hU.mem_nhds (hVU hp.2))
    exact (e.contDiffAt_symm hp.1 hd hc).contDiffWithinAt
  let W : Set L.ker := (fun t : L.ker => ((0 : ℝ), t)) ⁻¹' T
  let ψ : L.ker → E := fun t => e.symm (0, t)
  let q : E → L.ker := fun x => (e x).2
  have hW : IsOpen W := hT.preimage (continuous_const.prodMk continuous_id)
  have hψ : ContDiffOn ℝ ∞ ψ W :=
    hTsm.comp ((contDiff_const.prodMk contDiff_id).contDiffOn) (fun _ ht => ht)
  refine ⟨V, W, ψ, q, hV, haV, hVU, hW, hψ, ?_, ?_, ?_⟩
  · intro t ht
    exact hVU ht.2
  · intro t ht
    have hi := e.right_inv ht.1
    constructor
    · have hfirst := congrArg Prod.fst hi
      change h (ψ t) = 0 at hfirst
      exact hfirst
    · change (e (e.symm (0, t))).2 = t
      rw [hi]
  · intro x hx hx0
    have hcoords : e x = (0, (e x).2) := by
      apply Prod.ext
      · change h x = 0
        exact hx0
      · rfl
    have ht : (0, (e x).2) ∈ T := by
      rw [← hcoords]
      refine ⟨e.map_source (hVe hx), ?_⟩
      change e.symm (e x) ∈ V
      rw [e.left_inv (hVe hx)]
      exact hx
    refine ⟨ht, ?_⟩
    change e.symm (0, (e x).2) = x
    rw [← hcoords, e.left_inv (hVe hx)]

end FiniteDimensional

theorem restricted_fderiv_zero {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (U : Set E) (hU : IsOpen U) (W : Set K) (hW : IsOpen W)
    (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U)
    (ψ : K → E) (hψ : ContDiffOn ℝ ∞ ψ W) (hmap : MapsTo ψ W U)
    {t : K} (ht : t ∈ W) (hzero : fderiv ℝ f (ψ t) = 0) :
    fderiv ℝ (f ∘ ψ) t = 0 := by
  have hdf := (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds (hmap ht))
  have hdψ := (hψ.differentiableOn (by simp)).differentiableAt (hW.mem_nhds ht)
  rw [fderiv_comp t hdf hdψ, hzero, ContinuousLinearMap.zero_comp]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem regular_stratum_local_image_null
    (U : Set E) (hU : IsOpen U) (f h : E → ℝ)
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U)
    (S : Set E) (hcrit : ∀ x ∈ S, fderiv ℝ f x = 0)
    (hlevel : ∀ x ∈ S, h x = 0) (a : E) (haU : a ∈ U) (haS : a ∈ S)
    (hreg : fderiv ℝ h a ≠ 0)
    (lowerSard : ∀ W : Set (fderiv ℝ h a).ker, IsOpen W →
      ∀ g : (fderiv ℝ h a).ker → ℝ, ContDiffOn ℝ ∞ g W →
        volume (g '' {t | t ∈ W ∧ fderiv ℝ g t = 0}) = 0) :
    ∃ V : Set E, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧ volume (f '' (S ∩ V)) = 0 := by
  obtain ⟨V, W, ψ, q, hV, haV, hVU, hW, hψ, hmap, _, hrep⟩ :=
    exists_smooth_regular_stratum_chart U hU h hh a haU (hlevel a haS) hreg
  refine ⟨V, hV, haV, hVU, ?_⟩
  have hsm : ContDiffOn ℝ ∞ (f ∘ ψ) W := hf.comp hψ hmap
  have hnull := lowerSard W hW (f ∘ ψ) hsm
  apply measure_mono_null _ hnull
  rintro r ⟨x, ⟨hxS, hxV⟩, hxr⟩
  obtain ⟨hqx, hψqx⟩ := hrep x hxV (hlevel x hxS)
  refine ⟨q x, ⟨hqx, ?_⟩, ?_⟩
  · apply restricted_fderiv_zero U hU W hW f hf ψ hψ hmap hqx
    simpa only [hψqx] using hcrit x hxS
  · simpa only [Function.comp_apply, hψqx] using hxr

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem contDiffOn_iteratedFDeriv_component [FiniteDimensional ℝ E] [CompleteSpace E]
    (U : Set E) (hU : IsOpen U) (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U)
    (k : ℕ) (v : Fin k → E) :
    ContDiffOn ℝ ∞ (fun x => iteratedFDeriv ℝ k f x v) U := by
  let ev : (E [×k]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℝ v
  intro x hx
  have hd : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ k f) x :=
    (hf.contDiffAt (hU.mem_nhds hx)).iteratedFDeriv_right
      (WithTop.coe_le_coe.mpr (show (⊤ : ℕ∞) + (k : ℕ∞) ≤ ⊤ from le_top))
  exact (ev.contDiff.contDiffAt.comp x hd).contDiffWithinAt

theorem derivative_component_stratum_local_image_null
    (U : Set E) (hU : IsOpen U) (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U)
    (k : ℕ) (v : Fin k → E) (S : Set E)
    (hcrit : ∀ x ∈ S, fderiv ℝ f x = 0)
    (hflat : ∀ x ∈ S, iteratedFDeriv ℝ k f x = 0)
    (a : E) (haU : a ∈ U) (haS : a ∈ S)
    (hreg : fderiv ℝ (fun x => iteratedFDeriv ℝ k f x v) a ≠ 0)
    (lowerSard : ∀ W : Set (fderiv ℝ (fun x => iteratedFDeriv ℝ k f x v) a).ker,
      IsOpen W → ∀ g : (fderiv ℝ (fun x => iteratedFDeriv ℝ k f x v) a).ker → ℝ,
      ContDiffOn ℝ ∞ g W → volume (g '' {t | t ∈ W ∧ fderiv ℝ g t = 0}) = 0) :
    ∃ V : Set E, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧ volume (f '' (S ∩ V)) = 0 := by
  apply regular_stratum_local_image_null U hU f
    (fun x => iteratedFDeriv ℝ k f x v) hf
    (contDiffOn_iteratedFDeriv_component U hU f hf k v) S hcrit
    (fun x hx => by rw [hflat x hx]; rfl) a haU haS hreg lowerSard

end

section
open Set MeasureTheory
open scoped ContDiff

theorem scalar_sard_finrank_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 1) (U : Set E) (hU : IsOpen U)
    (f : E → ℝ) (hf : ContDiffOn ℝ 1 f U) :
    volume (f '' {x | x ∈ U ∧ fderiv ℝ f x = 0}) = 0 := by
  let e : E ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim)
  let W : Set ℝ := e.symm ⁻¹' U
  have hW : IsOpen W := hU.preimage e.symm.continuous
  have hsm : ContDiffOn ℝ 1 (f ∘ e.symm) W :=
    hf.comp e.symm.contDiff.contDiffOn (fun _ ht => ht)
  have hnull := scalar_sard_one_dimensional W hW (f ∘ e.symm) hsm
  apply measure_mono_null _ hnull
  rintro r ⟨x, ⟨hx, hdx⟩, hxr⟩
  refine ⟨e x, ⟨?_, ?_⟩, ?_⟩
  · change e.symm (e x) ∈ U
    simpa only [e.symm_apply_apply] using hx
  · have hdf := hf.differentiableOn_one.differentiableAt (hU.mem_nhds hx)
    have hdf' : DifferentiableAt ℝ f (e.symm (e x)) := by
      simpa only [e.symm_apply_apply] using hdf
    rw [fderiv_comp (e x) hdf' e.symm.differentiableAt,
      e.symm_apply_apply, hdx, ContinuousLinearMap.zero_comp]
  · simpa only [Function.comp_apply, e.symm_apply_apply] using hxr

theorem exists_regular_iteratedFDeriv_component
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hU : IsOpen U) (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U)
    (a : E) (ha : a ∈ U) (k : ℕ)
    (hne : iteratedFDeriv ℝ (k + 1) f a ≠ 0) :
    ∃ v : Fin k → E, fderiv ℝ (fun x => iteratedFDeriv ℝ k f x v) a ≠ 0 := by
  by_contra hnone
  push Not at hnone
  apply hne
  have hD : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) a :=
    ((hf.contDiffAt (hU.mem_nhds ha)).iteratedFDeriv_right
      (m := ∞)
      (WithTop.coe_le_coe.mpr (show (⊤ : ℕ∞) + (k : ℕ∞) ≤ ⊤ from le_top))).differentiableAt (by simp)
  apply ContinuousMultilinearMap.ext
  intro m
  rw [iteratedFDeriv_succ_apply_left]
  let ev : (E [×k]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℝ (Fin.tail m)
  have heval : fderiv ℝ (fun x => iteratedFDeriv ℝ k f x (Fin.tail m)) a =
      ev.comp (fderiv ℝ (iteratedFDeriv ℝ k f) a) :=
    (ev.hasFDerivAt.comp a hD.hasFDerivAt).fderiv
  have hz := congrArg (fun L : E →L[ℝ] ℝ => L (m 0)) (hnone (Fin.tail m))
  rw [heval] at hz
  exact hz

theorem image_null_of_locally_image_null
    {E : Type*} [TopologicalSpace E] [SecondCountableTopology E]
    (f : E → ℝ) (S : Set E)
    (hlocal : ∀ a ∈ S, ∃ V : Set E, IsOpen V ∧ a ∈ V ∧
      volume (f '' (S ∩ V)) = 0) : volume (f '' S) = 0 := by
  choose V hV haV hnull using fun a : S => hlocal a a.property
  obtain ⟨C, hC, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable V hV
  have hsub : f '' S ⊆ ⋃ a ∈ C, f '' (S ∩ V a) := by
    rintro r ⟨x, hx, hxr⟩
    have hxV : x ∈ ⋃ a : S, V a := mem_iUnion.mpr ⟨⟨x, hx⟩, haV ⟨x, hx⟩⟩
    rw [← hcover] at hxV
    obtain ⟨a, ha⟩ := mem_iUnion.mp hxV
    obtain ⟨haC, hxa⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨haC, ⟨x, ⟨hx, hxa⟩, hxr⟩⟩⟩
  exact measure_mono_null hsub ((measure_biUnion_null_iff hC).mpr (fun a _ => hnull a))

theorem nonflat_stratum_image_null
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    (U : Set E) (hU : IsOpen U) (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U)
    (k : ℕ) (S : Set E) (hSU : S ⊆ U)
    (hcrit : ∀ x ∈ S, fderiv ℝ f x = 0)
    (hflat : ∀ x ∈ S, iteratedFDeriv ℝ k f x = 0)
    (hnext : ∀ x ∈ S, iteratedFDeriv ℝ (k + 1) f x ≠ 0)
    (lowerSard : ∀ L : E →L[ℝ] ℝ, L ≠ 0 →
      ∀ W : Set L.ker, IsOpen W → ∀ g : L.ker → ℝ,
      ContDiffOn ℝ ∞ g W → volume (g '' {t | t ∈ W ∧ fderiv ℝ g t = 0}) = 0) :
    volume (f '' S) = 0 := by
  apply image_null_of_locally_image_null f S
  intro a ha
  obtain ⟨v, hv⟩ := exists_regular_iteratedFDeriv_component U hU f hf a (hSU ha) k
    (hnext a ha)
  obtain ⟨V, hV, haV, _, hnull⟩ := derivative_component_stratum_local_image_null
    U hU f hf k v S hcrit hflat a (hSU ha) ha hv (lowerSard _ hv)
  exact ⟨V, hV, haV, hnull⟩

end

open Set MeasureTheory Manifold
open scoped ContDiff Topology
universe u

section Strata
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sixFlatSet (U : Set E) (f : E → ℝ) : Set E :=
  {x | x ∈ U ∧ ∀ k : ℕ, 1 ≤ k → k ≤ 6 → iteratedFDeriv ℝ k f x = 0}

def nonflatCriticalStratum (U : Set E) (f : E → ℝ) (k : ℕ) : Set E :=
  {x | x ∈ U ∧ fderiv ℝ f x = 0 ∧ iteratedFDeriv ℝ k f x = 0 ∧
    iteratedFDeriv ℝ (k + 1) f x ≠ 0}

theorem criticalSet_subset_sixFlat_union_strata (U : Set E) (f : E → ℝ) :
    {x | x ∈ U ∧ fderiv ℝ f x = 0} ⊆
      sixFlatSet U f ∪ ⋃ i : Fin 5, nonflatCriticalStratum U f (i.val + 1) := by
  intro x hx
  have h1 : iteratedFDeriv ℝ 1 f x = 0 := by
    apply ContinuousMultilinearMap.ext
    intro v
    rw [iteratedFDeriv_one_apply, hx.2]
    rfl
  by_cases h2 : iteratedFDeriv ℝ 2 f x = 0
  · by_cases h3 : iteratedFDeriv ℝ 3 f x = 0
    · by_cases h4 : iteratedFDeriv ℝ 4 f x = 0
      · by_cases h5 : iteratedFDeriv ℝ 5 f x = 0
        · by_cases h6 : iteratedFDeriv ℝ 6 f x = 0
          · left
            refine ⟨hx.1, ?_⟩
            intro k hk1 hk6
            interval_cases k <;> assumption
          · right
            exact mem_iUnion.mpr ⟨⟨4, by decide⟩, hx.1, hx.2, h5, h6⟩
        · right
          exact mem_iUnion.mpr ⟨⟨3, by decide⟩, hx.1, hx.2, h4, h5⟩
      · right
        exact mem_iUnion.mpr ⟨⟨2, by decide⟩, hx.1, hx.2, h3, h4⟩
    · right
      exact mem_iUnion.mpr ⟨⟨1, by decide⟩, hx.1, hx.2, h2, h3⟩
  · right
    exact mem_iUnion.mpr ⟨⟨0, by decide⟩, hx.1, hx.2, h1, h2⟩

theorem sixFlatSet_image_null [FiniteDimensional ℝ E] [SecondCountableTopology E]
    (hdim : (Module.finrank ℝ E : ℝ) < 7)
    (U : Set E) (hU : IsOpen U) (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U) :
    volume (f '' sixFlatSet U f) = 0 := by
  apply image_null_of_locally_image_null f (sixFlatSet U f)
  intro x hx
  have hf7 : ContDiffOn ℝ 7 f U := hf.of_le
    (WithTop.coe_le_coe.mpr (show (7 : ℕ∞) ≤ ⊤ from le_top))
  obtain ⟨r, hr, hnull⟩ := StableBernstein.W30.exists_ball_sixFlat_image_null
    hdim hU hf7 (fun _ hz => hz.1) (fun z hz => hz.2) hx
  exact ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr, hnull⟩
end Strata

theorem scalar_sard_finrank_eq (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E],
      Module.finrank ℝ E = n → n ≤ 6 →
      ∀ (U : Set E), IsOpen U → ∀ (f : E → ℝ), ContDiffOn ℝ ∞ f U →
        volume (f '' {x | x ∈ U ∧ fderiv ℝ f x = 0}) = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E instN instS instF instC inst2 hdim hn U hU f hf
    by_cases hn0 : n = 0
    · have : Subsingleton E := Module.finrank_zero_iff.mp (hdim.trans hn0)
      have hz : volume ({f 0} : Set ℝ) = 0 := measure_singleton _
      apply measure_mono_null _ hz
      rintro t ⟨x, _, hxt⟩
      simpa only [mem_singleton_iff, Subsingleton.elim x 0] using hxt.symm
    · have hlower : ∀ L : E →L[ℝ] ℝ, L ≠ 0 →
          ∀ W : Set L.ker, IsOpen W → ∀ g : L.ker → ℝ,
          ContDiffOn ℝ ∞ g W → volume (g '' {t | t ∈ W ∧ fderiv ℝ g t = 0}) = 0 := by
        intro L hL W hW g hg
        have hk := regular_scalar_kernel_dimension L hL
        rw [hdim] at hk
        have hkn : Module.finrank ℝ L.ker < n := by omega
        have hk6 : Module.finrank ℝ L.ker ≤ 6 := by omega
        exact ih (Module.finrank ℝ L.ker) hkn L.ker rfl hk6 W hW g hg
      have hflat : volume (f '' sixFlatSet U f) = 0 := by
        apply sixFlatSet_image_null _ U hU f hf
        have : Module.finrank ℝ E ≤ 6 := by simpa only [hdim] using hn
        exact lt_of_le_of_lt (Nat.cast_le.mpr this) (by norm_num)
      have hstrata : ∀ i : Fin 5,
          volume (f '' nonflatCriticalStratum U f (i.val + 1)) = 0 := by
        intro i
        apply nonflat_stratum_image_null U hU f hf (i.val + 1)
          (nonflatCriticalStratum U f (i.val + 1))
          (fun _ hx => hx.1) (fun _ hx => hx.2.1)
          (fun _ hx => hx.2.2.1) (fun _ hx => hx.2.2.2) hlower
      have hnull : volume (f '' sixFlatSet U f ∪
          ⋃ i : Fin 5, f '' nonflatCriticalStratum U f (i.val + 1)) = 0 :=
        measure_union_null hflat (measure_iUnion_null_iff.mpr hstrata)
      apply measure_mono_null _ hnull
      rintro t ⟨x, hx, hxt⟩
      rcases criticalSet_subset_sixFlat_union_strata U f hx with hxf | hxs
      · exact Or.inl ⟨x, hxf, hxt⟩
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxs
        exact Or.inr (mem_iUnion.mpr ⟨i, x, hxi, hxt⟩)

theorem scalar_sard_finrank_le_six
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    (hdim : Module.finrank ℝ E ≤ 6)
    (U : Set E) (hU : IsOpen U) (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U) :
    volume (f '' {x | x ∈ U ∧ fderiv ℝ f x = 0}) = 0 :=
  scalar_sard_finrank_eq (Module.finrank ℝ E) E rfl hdim U hU f hf

theorem scalar_sard_E6 (U : Set StableBernstein.W01.E6) (hU : IsOpen U)
    (f : StableBernstein.W01.E6 → ℝ) (hf : ContDiffOn ℝ ∞ f U) :
    volume (f '' {x | x ∈ U ∧ fderiv ℝ f x = 0}) = 0 :=
  scalar_sard_finrank_le_six (by simp only [StableBernstein.W01.source_dimension, le_refl]) U hU f hf

open StableBernstein.W01

theorem manifold_ae_regularValues
    {M : Type*} [TopologicalSpace M] [ChartedSpace E6 M]
    [IsManifold I6 ∞ M] [SecondCountableTopology M]
    (f : M → ℝ) (hf : ContMDiff I6 𝓘(ℝ, ℝ) ∞ f) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ x : M,
      f x = t → Function.Surjective (mfderiv I6 𝓘(ℝ, ℝ) f x) :=
  ae_regularValues_of_scalarSard scalar_sard_E6 f hf

theorem manifold_ae_noncritical_values
    {M : Type*} [TopologicalSpace M] [ChartedSpace E6 M]
    [IsManifold I6 ∞ M] [SecondCountableTopology M]
    (f : M → ℝ) (hf : ContMDiff I6 𝓘(ℝ, ℝ) ∞ f) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ x : M,
      f x = t → mfderiv I6 𝓘(ℝ, ℝ) f x ≠ 0 := by
  filter_upwards [manifold_ae_regularValues f hf] with t ht x hxt hzero
  obtain ⟨v, hv⟩ := ht x hxt (1 : ℝ)
  rw [hzero] at hv
  change (0 : ℝ) = 1 at hv
  exact zero_ne_one hv

end Bernstein.Sard

open MeasureTheory Manifold Set Filter
open scoped Topology ContDiff
namespace StableBernstein.W26
open W01

universe u
variable {M : Type u} [TopologicalSpace M] [T1Space M]
  [ChartedSpace E6 M] [IsManifold I6 ∞ M]

def puncturedCriticalSet (o : M) (f : M → ℝ) : Set M :=
  {x | x ≠ o ∧ mfderiv I6 𝓘(ℝ, ℝ) f x = 0}

def poleCriticalSet (o : M) (f : M → ℝ) : Set M :=
  {o} ∪ puncturedCriticalSet o f

theorem chart_fderiv_zero_of_punctured (o : M) (f : M → ℝ)
    (hf : ContMDiffOn I6 𝓘(ℝ, ℝ) ∞ f ({o}ᶜ : Set M)) (c : M) {z : E6}
    (hz : z ∈ (extChartAt I6 c).target) (hne : (extChartAt I6 c).symm z ≠ o)
    (hzero : mfderiv I6 𝓘(ℝ, ℝ) f ((extChartAt I6 c).symm z) = 0) :
    fderiv ℝ (f ∘ (extChartAt I6 c).symm) z = 0 := by
  have hinv : MDifferentiableAt I6 I6 (extChartAt I6 c).symm z :=
    (mdifferentiableWithinAt_extChartAt_symm (I := I6) hz).mdifferentiableAt (by simp)
  have hdf : MDifferentiableAt I6 𝓘(ℝ, ℝ) f ((extChartAt I6 c).symm z) :=
    (hf.mdifferentiableOn (by simp)).mdifferentiableAt
      (isOpen_compl_singleton.mem_nhds (by simpa using hne))
  have hchain := mfderiv_comp z hdf hinv
  rw [mfderiv_eq_fderiv, hzero, ContinuousLinearMap.zero_comp] at hchain
  exact hchain

variable [SecondCountableTopology M]

theorem punctured_critical_values_null (o : M) (f : M → ℝ)
    (hf : ContMDiffOn I6 𝓘(ℝ, ℝ) ∞ f ({o}ᶜ : Set M)) :
    volume (f '' puncturedCriticalSet o f) = 0 := by
  apply Bernstein.Sard.exceptionalValues_null_of_chart_null
  intro c
  let U : Set E6 := (extChartAt I6 c).target ∩ (extChartAt I6 c).symm ⁻¹' ({o}ᶜ : Set M)
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    exact inter_mem ((isOpen_extChartAt_target (I := I6) c).mem_nhds hz.1)
      ((continuousAt_extChartAt_symm'' hz.1).preimage_mem_nhds
        (isOpen_compl_singleton.mem_nhds hz.2))
  have hcomp : ContDiffOn ℝ ∞ (f ∘ (extChartAt I6 c).symm) U := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact hf.comp ((contMDiffOn_extChartAt_symm c).mono inter_subset_left) inter_subset_right
  have hnull := Bernstein.Sard.scalar_sard_E6 U hU (f ∘ (extChartAt I6 c).symm) hcomp
  apply measure_mono_null _ hnull
  rintro t ⟨z, ⟨hz, hcrit⟩, hzt⟩
  refine ⟨z, ⟨⟨hz, hcrit.1⟩, ?_⟩, hzt⟩
  exact chart_fderiv_zero_of_punctured o f hf c hz hcrit.1 hcrit.2

theorem pole_critical_values_null (o : M) (f : M → ℝ)
    (hf : ContMDiffOn I6 𝓘(ℝ, ℝ) ∞ f ({o}ᶜ : Set M)) :
    volume (f '' poleCriticalSet o f) = 0 := by
  rw [poleCriticalSet, image_union, image_singleton]
  exact measure_union_null (measure_singleton _) (punctured_critical_values_null o f hf)

def poleCriticalCarrier (o : M) (f : M → ℝ) : Set ℝ :=
  toMeasurable volume (f '' poleCriticalSet o f)

omit [T1Space M] [IsManifold I6 ∞ M] [SecondCountableTopology M] in
theorem measurableSet_poleCriticalCarrier
    [T1Space M] [IsManifold I6 ∞ M] [SecondCountableTopology M] (o : M) (f : M → ℝ) :
    MeasurableSet (poleCriticalCarrier o f) := measurableSet_toMeasurable _ _

theorem poleCriticalCarrier_null (o : M) (f : M → ℝ)
    (hf : ContMDiffOn I6 𝓘(ℝ, ℝ) ∞ f ({o}ᶜ : Set M)) :
    volume (poleCriticalCarrier o f) = 0 := by
  rw [poleCriticalCarrier, measure_toMeasurable]
  exact pole_critical_values_null o f hf

omit [T1Space M] [IsManifold I6 ∞ M] [SecondCountableTopology M] in
theorem mapsTo_poleCriticalCarrier
    [T1Space M] [IsManifold I6 ∞ M] [SecondCountableTopology M] (o : M) (f : M → ℝ) :
    MapsTo f (poleCriticalSet o f) (poleCriticalCarrier o f) := by
  intro x hx
  exact subset_toMeasurable volume _ ⟨x, hx, rfl⟩

end StableBernstein.W26

end

end OAI
