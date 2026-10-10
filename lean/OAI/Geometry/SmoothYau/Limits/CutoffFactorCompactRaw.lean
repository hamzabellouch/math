import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.CutoffExactificationSmoothNeighborhood

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Manifold
open scoped Topology ContDiff InnerProductSpace

lemma inverse_gram_differential_norm {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (L : E →L[ℝ] ℝ) :
    (∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j*L (b i)*L (b j))=‖L‖^2 := by
  let v := (InnerProductSpace.toDual ℝ E).symm L
  have hh := inverse_gram_contraction b v v
  have hv (i : ι) : inner ℝ (b i) v=L (b i) := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  simp only [hv,real_inner_self_eq_norm_sq] at hh
  have hn : ‖v‖=‖L‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map L
  rw [hn] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma round_centered_gradient_norm (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (q : Sphere 3) (U : Sphere 3 → ℝ)
    (hg : ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=inner ℝ
        (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4) (fun p : Sphere 3 => (p:Euclidean 4)) q v)
        (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4) (fun p : Sphere 3 => (p:Euclidean 4)) q w)) :
    Real.sqrt (coordinateGradientPair g U U q)=
      ‖fderiv ℝ (U ∘ (chartAt (Euclidean 3) q).symm) 0‖ := by
  rw [coordinateGradientPair,sphere_chart_center,round_metricCoefficients_at g q hg,
    inverse_gram_differential_norm,Real.sqrt_sq (norm_nonneg _)]

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def chartInverseDifferentialBound (g : SmoothMetric E M) (p : M) (y : E) : ℝ :=
  ∑ i, ∑ j, |(metricCoefficients g p y)⁻¹ i j| *
    ‖Module.finBasis ℝ E i‖*‖Module.finBasis ℝ E j‖

lemma chart_inverse_differential_bound (g : SmoothMetric E M) (p : M) (y : E)
    (L : E →L[ℝ] ℝ) :
    (∑ i, ∑ j, (metricCoefficients g p y)⁻¹ i j*L (Module.finBasis ℝ E i)*L (Module.finBasis ℝ E j)) ≤
      chartInverseDifferentialBound g p y*‖L‖^2 := by
  unfold chartInverseDifferentialBound
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  have hi : |L (Module.finBasis ℝ E i)| ≤ ‖L‖*‖Module.finBasis ℝ E i‖ := L.le_opNorm _
  have hj : |L (Module.finBasis ℝ E j)| ≤ ‖L‖*‖Module.finBasis ℝ E j‖ := L.le_opNorm _
  calc
    _ ≤ |(metricCoefficients g p y)⁻¹ i j*L (Module.finBasis ℝ E i)*L (Module.finBasis ℝ E j)| :=
      le_abs_self _
    _ = |(metricCoefficients g p y)⁻¹ i j| *|L (Module.finBasis ℝ E i)| *|L (Module.finBasis ℝ E j)| := by
      rw [abs_mul,abs_mul]
    _ ≤ |(metricCoefficients g p y)⁻¹ i j| *(‖L‖*‖Module.finBasis ℝ E i‖)*
        (‖L‖*‖Module.finBasis ℝ E j‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hi (abs_nonneg _)) hj
        (abs_nonneg _) (mul_nonneg (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ = _ := by ring

lemma chartInverseDifferentialBound_continuous (g : SmoothMetric E M) (p : M) :
    ContinuousOn (chartInverseDifferentialBound g p) (chartAt E p).target := by
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  exact (((contDiffOn_metricInverse g p i j).continuousOn.abs).mul continuousOn_const).mul continuousOn_const

theorem compact_chart_intrinsic_gradient_bound (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target) :
    ∃ C > 0, ∀ (U : M → ℝ), ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ U → ∀ y ∈ K,
      Real.sqrt (coordinateGradientPair g U U ((chartAt E p).symm y)) ≤
        C*‖fderiv ℝ (U ∘ (chartAt E p).symm) y‖ := by
  obtain ⟨T,hT⟩ := hK.exists_bound_of_continuousOn
    ((chartInverseDifferentialBound_continuous g p).mono hKt)
  let C := Real.sqrt (max 1 T)
  have hC : 0 < C := Real.sqrt_pos.mpr (zero_lt_one.trans_le (le_max_left _ _))
  refine ⟨C,hC,?_⟩
  intro U hU y hy
  have hbound := chart_inverse_differential_bound g p y (fderiv ℝ (U ∘ (chartAt E p).symm) y)
  have hG : coordinateGradientPair g U U ((chartAt E p).symm y) ≤
      chartInverseDifferentialBound g p y*‖fderiv ℝ (U ∘ (chartAt E p).symm) y‖^2 := by
    rw [←localGradientPair_eq_global hU g p (hKt hy)]
    convert hbound using 1
    simp only [localGradientPair,dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hTb : chartInverseDifferentialBound g p y ≤ max 1 T :=
    (le_abs_self _).trans ((hT y hy).trans (le_max_right _ _))
  have hG' := hG.trans (mul_le_mul_of_nonneg_right hTb (sq_nonneg _))
  have hG0 := coordinateGradientPair_nonneg g U ((chartAt E p).symm y)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hC.le (norm_nonneg _))).mp
  have hCsq : (C:ℝ)^2 = max 1 T := Real.sq_sqrt (zero_le_one.trans (le_max_left _ _))
  rw [Real.sq_sqrt hG0,mul_pow,hCsq]
  exact hG'

end



open Set Filter Function Manifold
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]

omit [MeasurableSpace E] [BorelSpace E] [T2Space M] [CompactSpace M] in
theorem cutoffFactor_compact_raw (χ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ) (p : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target) (m : ℕ) :
    ∃ C > 0, ∀ (v : M → ℝ), ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
      ∀ y ∈ K, ∀ ε : ℝ, 0 ≤ ε →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt E p).symm) y‖ ≤ ε) →
      ∀ j ≤ m, ‖iteratedFDeriv ℝ j
        ((fun x => cutoffFactor χ v x-1) ∘ (chartAt E p).symm) y‖ ≤ C*ε := by
  let O := (chartAt E p).target
  have hO : IsOpen O := (chartAt E p).open_target
  have hχ' : ContDiffOn ℝ ∞ (χ ∘ (chartAt E p).symm) O :=
    fun y hy => (contDiffAt_inChart hχ p hy).contDiffWithinAt
  obtain ⟨A,hA,hAj⟩ := compact_raw_jet_bound hO hK hKt hχ' m
  refine ⟨2^m*A,by positivity,?_⟩
  intro v hv y hy ε hε hvJ j hj
  have hv' : ContDiffOn ℝ ∞ ((fun x => v x-1) ∘ (chartAt E p).symm) O :=
    fun y hy => (contDiffAt_inChart (hv.sub contMDiff_const) p hy).contDiffWithinAt
  have hp := constant_product_jet_bound_on hO (hKt hy) hχ' hv' m
    (zero_le_one.trans hA) hε (fun k hk => hAj k hk y hy) hvJ j hj
  simpa only [Function.comp_def,cutoffFactor,add_sub_cancel_left] using hp

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
  (A : CompactMetricAtlas g k hs)

def coveringRawTest (i₀ : CoordIndex E) (i : A.t) : CoordinateTest E M where
  center := A.p i
  compactSet := A.scalarChartSupport i
  isCompact := A.scalarChartSupport_compact i
  inTarget := A.scalarChartSupport_target i
  order := 0
  row := i₀
  column := i₀

noncomputable def coveringRawTests (i₀ : CoordIndex E) : List (CoordinateTest E M) :=
  (Finset.univ : Finset A.t).toList.map (A.coveringRawTest i₀)

omit [T2Space M] in
lemma coveringRawTest_mem (i₀ : CoordIndex E) (i : A.t) :
    A.coveringRawTest i₀ i ∈ A.coveringRawTests i₀ := by
  classical
  exact List.mem_map.mpr ⟨i,Finset.mem_toList.mpr (Finset.mem_univ _),rfl⟩

omit [T2Space M] in
lemma coveringRawTests_cover (i₀ : CoordIndex E) (x : M) :
    ∃ t ∈ A.coveringRawTests i₀, ∃ y ∈ t.compactSet, (chartAt E t.center).symm y=x := by
  classical
  have hex : ∃ i : A.t, A.η i x ≠ 0 := by
    by_contra h
    push Not at h
    have hh := A.sum_η x
    simp only [h,Finset.sum_const_zero] at hh
    exact zero_ne_one hh
  obtain ⟨i,hi⟩ := hex
  have hx : x ∈ tsupport (A.η i) := subset_tsupport _ hi
  refine ⟨A.coveringRawTest i₀ i,A.coveringRawTest_mem i₀ i,
    chartAt E (A.p i) x,⟨x,hx,rfl⟩,?_⟩
  exact (chartAt E (A.p i)).left_inv (A.chart_η i hx)

omit [T2Space M] in
theorem global_cutoff_raw_controls (i₀ : CoordIndex E) (χ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ) :
    ∃ C > 0, ∀ (b v : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      (∀ t ∈ A.coveringRawTests i₀, ∀ y ∈ t.compactSet, ∀ j ≤ 1,
        ‖iteratedFDeriv ℝ j ((fun x => b x-1) ∘ (chartAt E t.center).symm) y‖ ≤ ε) →
      (∀ t ∈ A.coveringRawTests i₀, ∀ y ∈ t.compactSet, ∀ j ≤ 2,
        ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt E t.center).symm) y‖ ≤ ε) →
      ∀ x : M,
        |weightedLaplacian g b (cutoffFactor χ v) x| ≤ C*ε ∧
        Real.sqrt (coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) x) ≤ C*ε := by
  classical
  choose D hD hDj using fun t : CoordinateTest E M =>
    cutoffFactor_compact_raw χ hχ t.center t.isCompact t.inTarget 2
  choose L hL hLj using fun t : CoordinateTest E M =>
    weightedLaplacian_small_jets_on_compact g t.center t.isCompact t.inTarget 0
  choose G hG hGj using fun t : CoordinateTest E M =>
    compact_chart_intrinsic_gradient_bound g t.center t.isCompact t.inTarget
  let cs (t : CoordinateTest E M) := L t*2*D t+G t*D t
  let C := 1+∑ t ∈ (A.coveringRawTests i₀).toFinset, cs t
  have hcs (t : CoordinateTest E M) : 0 ≤ cs t := by dsimp [cs]; exact add_nonneg (mul_nonneg (mul_nonneg (hL t).le (by norm_num)) (hD t).le) (mul_nonneg (hG t).le (hD t).le)
  have hC : 0 < C := by
    have hsum := Finset.sum_nonneg (fun t (_ : t ∈ (A.coveringRawTests i₀).toFinset) => hcs t)
    exact add_pos_of_pos_of_nonneg zero_lt_one hsum
  have hcsC (t : CoordinateTest E M) (ht : t ∈ A.coveringRawTests i₀) : cs t ≤ C := by
    have hh := Finset.single_le_sum (fun t (_ : t ∈ (A.coveringRawTests i₀).toFinset) => hcs t)
      (List.mem_toFinset.mpr ht)
    dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro b v hb hv ε hε hε1 hbJ hvJ x
  obtain ⟨t,ht,y,hy,hxy⟩ := A.coveringRawTests_cover i₀ x
  let w := cutoffFactor χ v
  have hw : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ w :=
    contMDiff_const.add (hχ.mul (hv.sub contMDiff_const))
  have hwJ := hDj t v hv y hy ε hε (hvJ t ht y hy)
  have hb' : ContDiffOn ℝ ∞ (b ∘ (chartAt E t.center).symm) (chartAt E t.center).target :=
    fun z hz => (contDiffAt_inChart hb t.center hz).contDiffWithinAt
  have hbraw := raw_jets_of_near_one (chartAt E t.center).open_target
    (t.inTarget hy) hb' 1 hε (hbJ t ht y hy)
  have hb2 : ∀ j ≤ 1, ‖iteratedFDeriv ℝ j (b ∘ (chartAt E t.center).symm) y‖ ≤ (2:ℝ) := by
    intro j hj
    exact (hbraw j hj).trans (by linarith)
  have hlap := hLj t b w hb hw y hy 2 (D t*ε) (by norm_num) (mul_nonneg (hD t).le hε)
    hb2 hwJ 0 (by omega)
  simp only [norm_iteratedFDeriv_zero,Function.comp_apply,hxy,Real.norm_eq_abs] at hlap
  have hgrad := hGj t w hw y hy
  have hfd : ‖fderiv ℝ (w ∘ (chartAt E t.center).symm) y‖ ≤ D t*ε := by
    have hh := hwJ 1 (by omega)
    simpa only [norm_iteratedFDeriv_one,Function.comp_def,fderiv_sub_const] using hh
  rw [hxy] at hgrad
  constructor
  · calc
      _ ≤ L t*2*(D t*ε) := hlap
      _ = (L t*2*D t)*ε := by ring
      _ ≤ C*ε := mul_le_mul_of_nonneg_right
        ((le_add_of_nonneg_right (mul_nonneg (hG t).le (hD t).le)).trans (hcsC t ht)) hε
  · calc
      _ ≤ G t*(D t*ε) := hgrad.trans (mul_le_mul_of_nonneg_left hfd (hG t).le)
      _ = (G t*D t)*ε := by ring
      _ ≤ C*ε := mul_le_mul_of_nonneg_right
        ((le_add_of_nonneg_left (mul_nonneg (mul_nonneg (hL t).le (by norm_num)) (hD t).le)).trans (hcsC t ht)) hε
end CompactMetricAtlas

end YauCounterexamples
end

end OAI
