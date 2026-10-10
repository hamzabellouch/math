import OAI.Probability.FreeIsing.Brownian.ArrayFiltrationIntegral
import OAI.Probability.FreeIsing.Stochastic.IntegralAssociativityLimit

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367

namespace BrownianGrid

theorem uniformSum_sub_coeff {Ω : Type*} (B H K : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    uniformSum B (fun t ω => H t ω - K t ω) T n ω =
      uniformSum B H T n ω - uniformSum B K T n ω := by
  simp only [uniformSum, integralSum, sub_mul, Finset.sum_sub_distrib]

end BrownianGrid

namespace SimpleIntegral

theorem meanSquare_limit_sub {Ω α : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {l : Filter α} {X Y : α → Ω → ℝ} {I J : Ω → ℝ}
    (hX : ∀ a, MemLp (X a) 2 P) (hY : ∀ a, MemLp (Y a) 2 P)
    (hI : MemLp I 2 P) (hJ : MemLp J 2 P)
    (hx : Tendsto (fun a => ∫ ω, (X a ω - I ω) ^ 2 ∂P) l (𝓝 0))
    (hy : Tendsto (fun a => ∫ ω, (Y a ω - J ω) ^ 2 ∂P) l (𝓝 0)) :
    Tendsto (fun a => ∫ ω, ((X a ω - Y a ω) - (I ω - J ω)) ^ 2 ∂P)
      l (𝓝 0) := by
  apply (tendsto_toLp_iff_meanSquare (fun a => (hX a).sub (hY a)) (hI.sub hJ)).mp
  change Tendsto (fun a => (hX a).toLp (X a) - (hY a).toLp (Y a)) l
    (𝓝 (hI.toLp I - hJ.toLp J))
  exact ((tendsto_toLp_iff_meanSquare hX hI).mpr hx).sub
    ((tendsto_toLp_iff_meanSquare hY hJ).mpr hy)

end SimpleIntegral

namespace BrownianFiltrationGrid

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem uniform_meanSquare_limit_isometry
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (H : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted F H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (T : ℝ≥0) {I : Ω → ℝ} (hI : MemLp I 2 P)
    (happrox : Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum B H T n ω - I ω) ^ 2 ∂P) atTop (𝓝 0)) :
    (∫ ω, I ω ^ 2 ∂P) =
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, H t.toNNReal ω ^ 2 ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P := by
    apply MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hlim := (SimpleIntegral.tendsto_toLp_iff_meanSquare
    (uniformSum_memLp hB hAd hind H hH hH2 T) hI).mpr happrox
  have hiso := uniformSumLp_limit_isometry hB hAd hind H hH hH2 hc hC hb T hlim
  calc
    (∫ ω, I ω ^ 2 ∂P) = ∫ ω, (hI.toLp I ω) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [hI.coeFn_toLp] with ω hω
      rw [hω]
    _ = _ := hiso

theorem uniform_meanSquare_difference_isometry
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (H K : ℝ≥0 → Ω → ℝ) (hH : StronglyAdapted F H) (hK : StronglyAdapted F K)
    (hcH : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (T : ℝ≥0) {I J : Ω → ℝ} (hI : MemLp I 2 P) (hJ : MemLp J 2 P)
    (haI : Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum B H T n ω - I ω) ^ 2 ∂P) atTop (𝓝 0))
    (haJ : Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum B K T n ω - J ω) ^ 2 ∂P) atTop (𝓝 0)) :
    (∫ ω, (I ω - J ω) ^ 2 ∂P) =
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, (H t.toNNReal ω - K t.toNNReal ω) ^ 2 ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P := by
    apply MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
    filter_upwards [hbH] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hK2 (t : ℝ≥0) : MemLp (K t) 2 P := by
    apply MemLp.of_bound ((hK t).mono (F.le t)).aestronglyMeasurable D
    filter_upwards [hbK] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  refine uniform_meanSquare_limit_isometry hB hAd hind (fun t ω => H t ω - K t ω)
    (fun t => (hH t).sub (hK t)) ?_ (add_nonneg hC hD) ?_ T (hI.sub hJ) ?_
  · filter_upwards [hcH, hcK] with ω hωH hωK
    exact hωH.sub hωK
  · filter_upwards [hbH, hbK] with ω hωH hωK
    intro t
    exact (abs_sub _ _).trans (add_le_add (hωH t) (hωK t))
  · simpa only [BrownianGrid.uniformSum_sub_coeff, Pi.sub_apply] using
      SimpleIntegral.meanSquare_limit_sub
        (uniformSum_memLp hB hAd hind H hH hH2 T)
        (uniformSum_memLp hB hAd hind K hK hK2 T) hI hJ haI haJ

end BrownianFiltrationGrid

namespace BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ι → ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem uniform_meanSquare_limits_orthogonal [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (H : ι → ℝ≥0 → Ω → ℝ) (hH : ∀ a, StronglyAdapted F (H a))
    (hH2 : ∀ a t, MemLp (H a t) 2 P) (T : ℝ≥0)
    {I : ι → Ω → ℝ} (hI : ∀ a, MemLp (I a) 2 P)
    (ha : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (H a) T n ω - I a ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Pairwise fun a b => ∫ ω, I a ω * I b ω ∂P = 0 := by
  have hi (a : ι) (s t : ℝ≥0) (hst : s ≤ t) :=
    coordinate_increment_indep_past (hind s t hst) a
  have hS (a : ι) := BrownianFiltrationGrid.uniformSum_memLp
    (hB a) (hAd a) (hi a) (H a) (hH a) (hH2 a) T
  have hlim (a : ι) := (SimpleIntegral.tendsto_toLp_iff_meanSquare (hS a) (hI a)).mpr (ha a)
  intro a b hab
  have hliminner := (hlim a).inner (𝕜 := ℝ) (hlim b)
  have hz (n : ℕ) : inner ℝ
      ((hS a n).toLp (BrownianGrid.uniformSum (B a) (H a) T n))
      ((hS b n).toLp (BrownianGrid.uniformSum (B b) (H b) T n)) = 0 := by
    rw [PredictableL2.inner_toLp]
    exact grid_sums_orthogonal hB hAd hind hcross
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun a k => H a (BrownianGrid.uniformGrid T n k))
      (fun a k => hH a _) (fun a k => hH2 a _) hab (Finset.range n) (Finset.range n)
  have heq : inner ℝ ((hI a).toLp (I a)) ((hI b).toLp (I b)) = 0 :=
    tendsto_nhds_unique hliminner (by simpa only [hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  exact (PredictableL2.inner_toLp (hI a) (hI b)).symm.trans heq

theorem uniform_meanSquare_differences_orthogonal [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (H K : ι → ℝ≥0 → Ω → ℝ)
    (hH : ∀ a, StronglyAdapted F (H a)) (hK : ∀ a, StronglyAdapted F (K a))
    (hH2 : ∀ a t, MemLp (H a t) 2 P) (hK2 : ∀ a t, MemLp (K a t) 2 P)
    (T : ℝ≥0) {I J : ι → Ω → ℝ}
    (hI : ∀ a, MemLp (I a) 2 P) (hJ : ∀ a, MemLp (J a) 2 P)
    (haI : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (H a) T n ω - I a ω) ^ 2 ∂P) atTop (𝓝 0))
    (haJ : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (K a) T n ω - J a ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Pairwise fun a b => ∫ ω, (I a ω - J a ω) * (I b ω - J b ω) ∂P = 0 := by
  apply uniform_meanSquare_limits_orthogonal hB hAd hind hcross
    (fun a t ω => H a t ω - K a t ω)
    (fun a t => (hH a t).sub (hK a t)) (fun a t => (hH2 a t).sub (hK2 a t)) T
    (fun a => (hI a).sub (hJ a))
  intro a
  have hi (s t : ℝ≥0) (hst : s ≤ t) :=
    coordinate_increment_indep_past (hind s t hst) a
  simpa only [BrownianGrid.uniformSum_sub_coeff, Pi.sub_apply] using
    SimpleIntegral.meanSquare_limit_sub
      (BrownianFiltrationGrid.uniformSum_memLp (hB a) (hAd a) hi (H a) (hH a) (hH2 a) T)
      (BrownianFiltrationGrid.uniformSum_memLp (hB a) (hAd a) hi (K a) (hK a) (hK2 a) T)
      (hI a) (hJ a) (haI a) (haJ a)

section RowComparison

variable [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (H K : ι → ℝ≥0 → Ω → ℝ)
    (hH : ∀ a, StronglyAdapted F (H a)) (hK : ∀ a, StronglyAdapted F (K a))
    (hcH : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (hcK : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => K a t ω))
    (C D : ι → ℝ) (hC : ∀ a, 0 ≤ C a) (hD : ∀ a, 0 ≤ D a)
    (hbH : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a)
    (hbK : ∀ a, ∀ᵐ ω ∂P, ∀ t, |K a t ω| ≤ D a)
    (T : ℝ≥0) {I J : ι → Ω → ℝ}
    (hI : ∀ a, MemLp (I a) 2 P) (hJ : ∀ a, MemLp (J a) 2 P)
    (haI : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (H a) T n ω - I a ω) ^ 2 ∂P) atTop (𝓝 0))
    (haJ : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (K a) T n ω - J a ω) ^ 2 ∂P) atTop (𝓝 0))

include hB hAd hind hcross hH hK hcH hcK hC hD hbH hbK hI hJ haI haJ in

theorem finite_row_difference_isometry (s : Finset ι) :
    (∫ ω, ((∑ a ∈ s, I a ω) - ∑ a ∈ s, J a ω) ^ 2 ∂P) =
      ∑ a ∈ s, ∫ t in (0 : ℝ)..(T : ℝ),
        ∫ ω, (H a t.toNNReal ω - K a t.toNNReal ω) ^ 2 ∂P := by
  have hH2 (a : ι) (t : ℝ≥0) : MemLp (H a t) 2 P := by
    apply MemLp.of_bound ((hH a t).mono (F.le t)).aestronglyMeasurable (C a)
    filter_upwards [hbH a] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hK2 (a : ι) (t : ℝ≥0) : MemLp (K a t) 2 P := by
    apply MemLp.of_bound ((hK a t).mono (F.le t)).aestronglyMeasurable (D a)
    filter_upwards [hbK a] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have horth := uniform_meanSquare_differences_orthogonal hB hAd hind hcross H K hH hK
    hH2 hK2 T hI hJ haI haJ
  simp_rw [← Finset.sum_sub_distrib]
  rw [SimpleIntegral.integral_sq_sum_of_orthogonal s
    (fun a ω => I a ω - J a ω)
    (fun a _ b _ => ((hI a).sub (hJ a)).integrable_mul ((hI b).sub (hJ b)))
    (fun a _ b _ hab => horth hab)]
  apply Finset.sum_congr rfl
  intro a ha
  exact BrownianFiltrationGrid.uniform_meanSquare_difference_isometry
    (hB a) (hAd a) (fun s t hst => coordinate_increment_indep_past (hind s t hst) a)
    (H a) (K a) (hH a) (hK a) (hcH a) (hcK a) (hC a) (hD a)
    (hbH a) (hbK a) T (hI a) (hJ a) (haI a) (haJ a)

include hB hAd hind hcross hH hK hcH hcK hC hD hbH hbK hI hJ haI haJ in

theorem infinite_row_difference_isometry
    {Y Z : Ω → ℝ} (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P)
    (hsY : Tendsto (fun s : Finset ι => ∫ ω,
      ((∑ a ∈ s, I a ω) - Y ω) ^ 2 ∂P) atTop (𝓝 0))
    (hsZ : Tendsto (fun s : Finset ι => ∫ ω,
      ((∑ a ∈ s, J a ω) - Z ω) ^ 2 ∂P) atTop (𝓝 0))
    (henergy : Summable fun a => ∫ t in (0 : ℝ)..(T : ℝ),
      ∫ ω, (H a t.toNNReal ω - K a t.toNNReal ω) ^ 2 ∂P) :
    (∫ ω, (Y ω - Z ω) ^ 2 ∂P) =
      ∑' a, ∫ t in (0 : ℝ)..(T : ℝ),
        ∫ ω, (H a t.toNNReal ω - K a t.toNNReal ω) ^ 2 ∂P := by
  have hIs (s : Finset ι) : MemLp (fun ω => ∑ a ∈ s, I a ω) 2 P :=
    memLp_finsetSum s (fun a _ => hI a)
  have hJs (s : Finset ι) : MemLp (fun ω => ∑ a ∈ s, J a ω) 2 P :=
    memLp_finsetSum s (fun a _ => hJ a)
  have hd := SimpleIntegral.meanSquare_limit_sub hIs hJs hY hZ hsY hsZ
  have hlp := (SimpleIntegral.tendsto_toLp_iff_meanSquare
    (fun s => (hIs s).sub (hJs s)) (hY.sub hZ)).mpr hd
  have hnorm : Tendsto (fun s : Finset ι => ∫ ω,
      ((∑ a ∈ s, I a ω) - ∑ a ∈ s, J a ω) ^ 2 ∂P) atTop
      (𝓝 (∫ ω, (Y ω - Z ω) ^ 2 ∂P)) := by
    simpa only [PredictableL2.norm_toLp_sq, Pi.sub_apply] using hlp.norm.pow 2
  have heq (s : Finset ι) := finite_row_difference_isometry hB hAd hind hcross
    H K hH hK hcH hcK C D hC hD hbH hbK T hI hJ haI haJ s
  apply tendsto_nhds_unique hnorm
  simpa only [HasSum, SummationFilter.unconditional, heq] using henergy.hasSum

end RowComparison
end BrownianArrayFiltration
end Problem367

end

end OAI
