import Mathlib
import OAI.Geometry.SmoothYau.Geometry.LocalizeRepresentative
import OAI.Geometry.SmoothYau.Smoothness.TotallyBoundedCauchySubsequence

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal BoundedContinuousFunction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma boundedDistribution_memLp (f : E →ᵇ ℂ) (hf : MemLp (f : E → ℂ) 2 volume) :
    boundedDistribution f = Lp.toTemperedDistribution (hf.toLp f) := by
  ext φ
  rw [boundedDistribution_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

lemma sobolev_zero_distribution (u : FourierSobolevSpace E ℂ 0) :
    fourierSobolevDistribution E ℂ 0 u = Lp.toTemperedDistribution (𝓕⁻ u) := by
  rw [fourierSobolevDistribution_apply]
  simp only [neg_zero, zero_div, Real.rpow_zero, Complex.ofReal_one,
    smulLeftCLM_const, one_smul]
  exact Lp.fourierInv_toTemperedDistribution_eq u

lemma sobolev_norm_zero_repr {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (u : FourierSobolevSpace E ℂ s) (hu : MemLp (sobolevRepresentative hs u : E → ℂ) 2 volume) :
    ‖sobolevInclusion s 0 (by have _hn : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _; linarith) u‖ =
    ‖hu.toLp (sobolevRepresentative hs u)‖ := by
  let v := sobolevInclusion s 0 (by have _hn : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _; linarith) u
  have he : Lp.toTemperedDistribution (𝓕⁻ v) = Lp.toTemperedDistribution (hu.toLp _) := by
    rw [← sobolev_zero_distribution, sobolevInclusion_distribution,
      ← sobolevRepresentative_distribution hs, boundedDistribution_memLp _ hu]
  have hi : Function.Injective (Lp.toTemperedDistribution (F := ℂ) (p := 2) (μ := (volume : Measure E))) :=
    LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot
  have hh := congrArg norm (hi he)
  have hn := Lp.norm_fourier_eq (𝓕⁻ v)
  rw [fourier_fourierInv_eq] at hn
  exact hn.trans hh

lemma compact_L2_bound (f : E →ᵇ ℂ) (K : Set E) (hK : IsCompact K)
    (hsupp : tsupport f ⊆ K) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) :
    ∃ hf : MemLp (f : E → ℂ) 2 volume,
      ‖hf.toLp f‖ ≤ C * (volume K).toReal ^ (1 / 2 : ℝ) := by
  have hc : HasCompactSupport (f : E → ℂ) := hK.of_isClosed_subset (isClosed_tsupport _) hsupp
  have hf : MemLp (f : E → ℂ) 2 volume :=
    hc.memLp_of_bound f.continuous.aestronglyMeasurable C (Filter.Eventually.of_forall hb)
  refine ⟨hf, ?_⟩
  have he : eLpNorm f 2 volume ≤ ENNReal.ofReal C * volume K ^ (1 / 2 : ℝ) := by
    calc
      eLpNorm f 2 volume ≤ eLpNorm (K.indicator (fun _ : E => (C : ℂ))) 2 volume := by
        apply eLpNorm_mono hf.aestronglyMeasurable
        intro x
        by_cases hx : x ∈ K
        · simpa only [Set.indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hC] using hb x
        · have hz : f x = 0 := by
            by_contra hn
            exact hx (hsupp (subset_tsupport _ hn))
          simp only [Set.indicator_of_notMem hx, hz, norm_zero, le_refl]
      _ = ENNReal.ofReal C * volume K ^ (1 / 2 : ℝ) := by
        rw [eLpNorm_indicator_const hK.measurableSet.nullMeasurableSet (by norm_num) (by norm_num)]
        simp only [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hC, ENNReal.toReal_ofNat]
  rw [Lp.norm_toLp]
  have hfinite : ENNReal.ofReal C * volume K ^ (1 / 2 : ℝ) ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hK.measure_lt_top.ne)
  have ht := ENNReal.toReal_mono hfinite he
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, ENNReal.toReal_rpow] using ht

lemma sobolev_zero_compact_bound {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (u : FourierSobolevSpace E ℂ s) (K : Set E) (hK : IsCompact K)
    (hsupp : tsupport (sobolevRepresentative hs u) ⊆ K) :
    ‖sobolevInclusion s 0 (by have _hn : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _; linarith) u‖ ≤
      ‖sobolevRepresentative hs u‖ * (volume K).toReal ^ (1 / 2 : ℝ) := by
  obtain ⟨hf, hh⟩ := compact_L2_bound (sobolevRepresentative hs u) K hK hsupp
    ‖sobolevRepresentative hs u‖ (norm_nonneg _) (fun x => BoundedContinuousFunction.norm_coe_le_norm _ x)
  rw [sobolev_norm_zero_repr hs u hf]
  exact hh

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Metric
open scoped Topology BoundedContinuousFunction
variable {E : Type*} [NormedAddCommGroup E]

lemma supported_bcf_dist_le (K : Set E) (f g : E →ᵇ ℂ)
    (hf : tsupport f ⊆ K) (hg : tsupport g ⊆ K) :
    dist f g ≤ dist (f.domRestrict K) (g.domRestrict K) := by
  apply (BoundedContinuousFunction.dist_le (dist_nonneg)).2
  intro x
  by_cases hx : x ∈ K
  · exact BoundedContinuousFunction.dist_coe_le_dist (f := f.domRestrict K) (g := g.domRestrict K) (⟨x, hx⟩ : K)
  · have hfx : f x = 0 := by
      by_contra hn
      exact hx (hf (subset_tsupport _ hn))
    have hgx : g x = 0 := by
      by_contra hn
      exact hx (hg (subset_tsupport _ hn))
    rw [hfx, hgx, dist_self]
    exact dist_nonneg

theorem supported_bcf_subsequence (K : Set E) (hK : IsCompact K)
    (f : ℕ → E →ᵇ ℂ) (C D : ℝ)
    (hb : ∀ n, ‖f n‖ ≤ C) (hsupp : ∀ n, tsupport (f n) ⊆ K)
    (hlip : ∀ n x y, dist (f n x) (f n y) ≤ D * dist x y) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ CauchySeq (f ∘ ψ) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : ℕ → K →ᵇ ℂ := fun n => (f n).domRestrict K
  have hcomp : IsCompact (closure (Set.range F)) := by
    apply BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) C) (isCompact_closedBall _ _)
    · rintro g x ⟨n, rfl⟩
      rw [mem_closedBall, dist_zero_right]
      exact (BoundedContinuousFunction.norm_coe_le_norm (f n) x).trans (hb n)
    · apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => D * t)
        (by
          have hc : Continuous (fun t : ℝ => D * t) := by fun_prop
          simpa only [mul_zero] using hc.tendsto 0)
      rintro x y ⟨g, n, rfl⟩
      exact hlip n x y
  obtain ⟨g, _, ψ, hψ, hg⟩ := hcomp.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  refine ⟨ψ, hψ, Metric.cauchySeq_iff.mpr ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hg.cauchySeq ε hε
  exact ⟨N, fun n hn m hm => (supported_bcf_dist_le K (f (ψ n)) (f (ψ m))
    (hsupp _) (hsupp _)).trans_lt (hN n hn m hm)⟩

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal BoundedContinuousFunction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sobolev_repr_dist_bound {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (ht : Module.finrank ℝ E < 2 * (s - 1))
    (u : FourierSobolevSpace E ℂ s) (x y : E) :
    dist (sobolevRepresentative hs u x) (sobolevRepresentative hs u y) ≤
      ((2 * Real.pi * ‖innerSL ℝ (E := E)‖) * ‖momentBesselLp (E := E) (s := s) 1 (by simpa only [Nat.cast_one] using ht)‖ * ‖u‖) * dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  apply (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => ((contDiff_sobolevRepresentative 1 (by simpa only [Nat.cast_one] using ht) hs u).differentiable (by norm_num)) z)
      (fun z _ => ?_) (mem_univ y) (mem_univ x)
  have hh := sobolevRepresentative_jet_bound hs 1 (by simpa only [Nat.cast_one] using ht) u z
  rwa [norm_iteratedFDeriv_one, pow_one] at hh

theorem sobolev_rellich_subsequence (k : ℕ)
    (ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ) - 1))
    (K : Set E) (hK : IsCompact K)
    (u : ℕ → FourierSobolevSpace E ℂ (2 * ((k + 1 : ℕ) : ℝ)))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ‖u n‖ ≤ C)
    (hsupp : ∀ n, tsupport (sobolevRepresentative (by linarith) (u n)) ⊆ K) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ CauchySeq (fun n =>
      sobolevInclusion _ (2 * (k : ℝ)) (by push_cast; linarith) (u (ψ n))) := by
  have hs : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)) := by linarith
  let f : ℕ → E →ᵇ ℂ := fun n => sobolevRepresentative hs (u n)
  let D := (2 * Real.pi * ‖innerSL ℝ (E := E)‖) * ‖momentBesselLp (E := E) (s := 2 * ((k + 1 : ℕ) : ℝ)) 1 (by simpa only [Nat.cast_one] using ht)‖
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨ψ, hψ, hf⟩ := supported_bcf_subsequence K hK f
    (‖sobolevRepresentative hs‖ * C) (D * C)
    (fun n => ((sobolevRepresentative hs).le_opNorm (u n)).trans
      (mul_le_mul_of_nonneg_left (hb n) (norm_nonneg _))) hsupp
    (fun n x y => (sobolev_repr_dist_bound hs ht (u n) x y).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hb n) hD) dist_nonneg))
  refine ⟨ψ, hψ, ?_⟩
  have hlow : CauchySeq (fun n => sobolevInclusion _ 0 (by positivity) (u (ψ n))) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    let V := (volume K).toReal ^ (1 / 2 : ℝ)
    have hV : 0 ≤ V := by positivity
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hf (ε / (V + 1)) (div_pos hε (by positivity))
    refine ⟨N, fun n hn m hm => ?_⟩
    have hh := sobolev_zero_compact_bound hs (u (ψ n) - u (ψ m)) K hK (by
      rw [map_sub]
      exact (tsupport_sub _ _).trans (union_subset (hsupp _) (hsupp _)))
    rw [map_sub, map_sub, ← dist_eq_norm, ← dist_eq_norm] at hh
    have hn' := hN n hn m hm
    have hv := (lt_div_iff₀ (by positivity : 0 < V + 1)).mp hn'
    change dist (f (ψ n)) (f (ψ m)) * (V + 1) < ε at hv
    have hz : 0 ≤ dist (f (ψ n)) (f (ψ m)) := dist_nonneg
    change dist _ _ ≤ dist (f (ψ n)) (f (ψ m)) * V at hh
    nlinarith
  exact interpolation_cauchy
    ((sobolevInclusion _ (2 * (k : ℝ)) (by push_cast; linarith)).restrictScalars ℝ)
    ((sobolevInclusion _ 0 (by positivity)).restrictScalars ℝ)
    (fun ε hε => ⟨(ε⁻¹)^k, by positivity, sobolev_interpolation k hε⟩)
    (fun n => u (ψ n)) hC (fun n => hb (ψ n)) hlow

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter
open scoped Topology Manifold BoundedContinuousFunction ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] {ι : Type*} [Fintype ι]
variable (p : ι → M) (η : ι → M → ℂ)
    (hηc : ∀ i, HasCompactSupport (η i))
    (hηs : ∀ i, tsupport (η i) ⊆ (chartAt E (p i)).source)
    (hηm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i))

omit [CompactSpace M] in
lemma manifoldSobolevInclusion_coordinate (s t : ℝ) (h : t ≤ s)
    (u : ManifoldSobolev p η hηc hηs hηm s) (i : ι) :
    (manifoldSobolevInclusion p η hηc hηs hηm s t u).val i =
      sobolevInclusion s t h (u.val i) := by
  refine (denseRange_smoothToManifoldSobolev p η hηc hηs hηm s).induction_on u ?_ ?_
  · apply isClosed_eq
    · exact (continuous_apply i).comp (continuous_subtype_val.comp
        (manifoldSobolevInclusion p η hηc hηs hηm s t).continuous)
    · exact (sobolevInclusion s t h).continuous.comp
        ((continuous_apply i).comp continuous_subtype_val)
  · intro f
    rw [manifoldSobolevInclusion_smooth p η hηc hηs hηm s t h]
    exact (sobolevInclusion_schwartz s t h _).symm

theorem manifoldSobolevInclusion_compact (hηone : ∀ x, ∑ i, η i x = 1) (k : ℕ)
    (ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ) - 1)) :
    IsCompactOperator (manifoldSobolevInclusion p η hηc hηs hηm
      (2 * ((k + 1 : ℕ) : ℝ)) (2 * (k : ℝ))) := by
  classical
  let s : ℝ := 2 * ((k + 1 : ℕ) : ℝ)
  let t : ℝ := 2 * (k : ℝ)
  have hts : t ≤ s := by dsimp [s, t]; push_cast; linarith
  have hs : Module.finrank ℝ E < 2 * s := by dsimp [s]; linarith
  let I := manifoldSobolevInclusion p η hηc hηs hηm s t
  let K : ι → Set E := fun i => (chartAt E (p i)) '' tsupport (η i)
  have hK : ∀ i, IsCompact (K i) := fun i => isCompact_chartSupport (p i) (η i) (hηc i) (hηs i)
  let S : ι → Set (FourierSobolevSpace E ℂ t) := fun i =>
    sobolevInclusion s t hts '' {v : FourierSobolevSpace E ℂ s |
      ‖v‖ ≤ 1 ∧ tsupport (sobolevRepresentative hs v) ⊆ K i}
  have hS : ∀ i, TotallyBounded (S i) := by
    intro i
    apply totallyBounded_of_cauchy_subsequence
    intro x hx
    choose u hu he using hx
    obtain ⟨ψ, hψ, hc⟩ := sobolev_rellich_subsequence k ht (K i) (hK i) u 1
      zero_le_one (fun n => (hu n).1) (fun n => (hu n).2)
    refine ⟨ψ, hψ, ?_⟩
    change CauchySeq (fun n => sobolevInclusion s t hts (u (ψ n))) at hc
    simp_rw [he] at hc
    exact hc
  have hc : IsCompact {v : ι → FourierSobolevSpace E ℂ t | ∀ i, v i ∈ closure (S i)} :=
    isCompact_pi_infinite fun i => (hS i).closure.isCompact_of_isClosed isClosed_closure
  have himg : TotallyBounded (Subtype.val '' (I '' Metric.closedBall 0 1)) := by
    apply hc.totallyBounded.subset
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩ i
    apply subset_closure
    refine ⟨u.val i, ⟨?_, ?_⟩, ?_⟩
    · apply (norm_le_pi_norm u.val i).trans
      have hh : ‖u‖ ≤ (1 : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hu
      convert hh using 1; rfl
    · have he : (sobolevRepresentative hs (u.val i) : E → ℂ) =
          chartLocalize (E := E) (p i) (η i)
            (manifoldSobolevRepresentative p η hηc hηs hηm s u) := by
        funext y
        exact manifoldSobolevRepresentative_localize p η hηc hηs hηm hηone hs u i y
      rw [he]
      exact closure_minimal (support_chartLocalize (p i) (η i) _) (hK i).isClosed
    · exact (manifoldSobolevInclusion_coordinate p η hηc hηs hηm s t hts u i).symm
  have himg' : TotallyBounded (I '' Metric.closedBall 0 1) :=
    (totallyBounded_image_iff isUniformEmbedding_subtype_val.isUniformInducing).mp himg
  exact (isCompactOperator_iff_isCompact_closure_image_closedBall I.toLinearMap
    (by norm_num : (0 : ℝ) < 1)).mpr (himg'.closure.isCompact_of_isClosed isClosed_closure)


end YauCounterexamples
end

end OAI
