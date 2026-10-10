import OAI.Probability.FreeIsing.Brownian.ArrayCrossIsometry

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.SimpleIntegral

theorem summable_integral_sq_sub {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {I J : ι → Ω → ℝ}
    (hI : ∀ a, MemLp (I a) 2 P) (hJ : ∀ a, MemLp (J a) 2 P)
    (hsI : Summable fun a => ∫ ω, I a ω ^ 2 ∂P)
    (hsJ : Summable fun a => ∫ ω, J a ω ^ 2 ∂P) :
    Summable fun a => ∫ ω, (I a ω - J a ω) ^ 2 ∂P := by
  apply Summable.of_nonneg_of_le
    (fun a => integral_nonneg fun ω => sq_nonneg _) _
    ((hsI.mul_left 2).add (hsJ.mul_left 2))
  intro a
  simpa using BrownianGrid.integral_sq_sub_le_two (hI a) (hJ a)
    (MemLp.zero' : MemLp (fun _ : Ω => (0 : ℝ)) 2 P)

end Problem367.SimpleIntegral

namespace Problem367.BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ι → ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (H K : ι → ℝ≥0 → Ω → ℝ)
    (hH : ∀ a, StronglyAdapted F (H a)) (hK : ∀ a, StronglyAdapted F (K a))
    (hcH : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (hcK : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => K a t ω))
    (C D : ι → ℝ) (hC : ∀ a, 0 ≤ C a) (hD : ∀ a, 0 ≤ D a)
    (hbH : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a)
    (hbK : ∀ a, ∀ᵐ ω ∂P, ∀ t, |K a t ω| ≤ D a)
    (T : ℝ≥0)
    (heH : Summable fun a =>
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, H a t.toNNReal ω ^ 2 ∂P)
    (heK : Summable fun a =>
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, K a t.toNNReal ω ^ 2 ∂P)

include hB hAd hind hH hK hcH hcK hC hD hbH hbK heH heK in

theorem summable_difference_energy_of_row_energies
    {I J : ι → Ω → ℝ}
    (hI : ∀ a, MemLp (I a) 2 P) (hJ : ∀ a, MemLp (J a) 2 P)
    (haI : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (H a) T n ω - I a ω) ^ 2 ∂P) atTop (𝓝 0))
    (haJ : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (K a) T n ω - J a ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Summable fun a => ∫ t in (0 : ℝ)..(T : ℝ),
      ∫ ω, (H a t.toNNReal ω - K a t.toNNReal ω) ^ 2 ∂P := by
  have hi (a : ι) (s t : ℝ≥0) (hst : s ≤ t) :=
    coordinate_increment_indep_past (hind s t hst) a
  have hIE (a : ι) := BrownianFiltrationGrid.uniform_meanSquare_limit_isometry
    (hB a) (hAd a) (hi a) (H a) (hH a) (hcH a) (hC a) (hbH a) T (hI a) (haI a)
  have hJE (a : ι) := BrownianFiltrationGrid.uniform_meanSquare_limit_isometry
    (hB a) (hAd a) (hi a) (K a) (hK a) (hcK a) (hD a) (hbK a) T (hJ a) (haJ a)
  have hs := SimpleIntegral.summable_integral_sq_sub hI hJ
    (by simpa only [hIE] using heH) (by simpa only [hJE] using heK)
  have hDE (a : ι) := BrownianFiltrationGrid.uniform_meanSquare_difference_isometry
    (hB a) (hAd a) (hi a) (H a) (K a) (hH a) (hK a) (hcH a) (hcK a)
    (hC a) (hD a) (hbH a) (hbK a) T (hI a) (hJ a) (haI a) (haJ a)
  simpa only [hDE] using hs

variable [IsProbabilityMeasure P]
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)

include hB hAd hind hcross hH hK hcH hcK hC hD hbH hbK heH heK in

theorem infinite_row_difference_isometry_of_row_energies
    {I J : ι → Ω → ℝ}
    (hI : ∀ a, MemLp (I a) 2 P) (hJ : ∀ a, MemLp (J a) 2 P)
    (haI : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (H a) T n ω - I a ω) ^ 2 ∂P) atTop (𝓝 0))
    (haJ : ∀ a, Tendsto (fun n => ∫ ω,
      (BrownianGrid.uniformSum (B a) (K a) T n ω - J a ω) ^ 2 ∂P) atTop (𝓝 0))
    {Y Z : Ω → ℝ} (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P)
    (hsY : Tendsto (fun s : Finset ι => ∫ ω,
      ((∑ a ∈ s, I a ω) - Y ω) ^ 2 ∂P) atTop (𝓝 0))
    (hsZ : Tendsto (fun s : Finset ι => ∫ ω,
      ((∑ a ∈ s, J a ω) - Z ω) ^ 2 ∂P) atTop (𝓝 0)) :
    (∫ ω, (Y ω - Z ω) ^ 2 ∂P) =
      ∑' a, ∫ t in (0 : ℝ)..(T : ℝ),
        ∫ ω, (H a t.toNNReal ω - K a t.toNNReal ω) ^ 2 ∂P := by
  exact infinite_row_difference_isometry hB hAd hind hcross
    H K hH hK hcH hcK C D hC hD hbH hbK T hI hJ haI haJ hY hZ hsY hsZ
    (summable_difference_energy_of_row_energies hB hAd hind
      H K hH hK hcH hcK C D hC hD hbH hbK T heH heK hI hJ haI haJ)

include hB hAd hind hcross hH hK hcH hcK hC hD hbH hbK heH heK in

theorem exists_paired_infinite_integrals :
    ∃ (I J : ι → Ω → ℝ) (Y Z : Ω → ℝ),
      (∀ a, MemLp (I a) 2 P) ∧ (∀ a, MemLp (J a) 2 P) ∧
      (∀ a, Tendsto (fun n => ∫ ω,
        (BrownianGrid.uniformSum (B a) (H a) T n ω - I a ω) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ a, Tendsto (fun n => ∫ ω,
        (BrownianGrid.uniformSum (B a) (K a) T n ω - J a ω) ^ 2 ∂P) atTop (𝓝 0)) ∧
      Measurable Y ∧ Measurable Z ∧
      AEStronglyMeasurable[F T] Y P ∧ AEStronglyMeasurable[F T] Z P ∧
      MemLp Y 2 P ∧ MemLp Z 2 P ∧
      (∫ ω, Y ω ∂P) = 0 ∧ (∫ ω, Z ω ∂P) = 0 ∧
      (∫ ω, Y ω ^ 2 ∂P) =
        (∑' a, ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, H a t.toNNReal ω ^ 2 ∂P) ∧
      (∫ ω, Z ω ^ 2 ∂P) =
        (∑' a, ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, K a t.toNNReal ω ^ 2 ∂P) ∧
      Tendsto (fun s : Finset ι => ∫ ω,
        ((∑ a ∈ s, I a ω) - Y ω) ^ 2 ∂P) atTop (𝓝 0) ∧
      Tendsto (fun s : Finset ι => ∫ ω,
        ((∑ a ∈ s, J a ω) - Z ω) ^ 2 ∂P) atTop (𝓝 0) ∧
      Summable (fun a => ∫ t in (0 : ℝ)..(T : ℝ),
        ∫ ω, (H a t.toNNReal ω - K a t.toNNReal ω) ^ 2 ∂P) ∧
      (∫ ω, (Y ω - Z ω) ^ 2 ∂P) =
        (∑' a, ∫ t in (0 : ℝ)..(T : ℝ),
          ∫ ω, (H a t.toNNReal ω - K a t.toNNReal ω) ^ 2 ∂P) ∧
      (∫ ω, (Y ω - Z ω) ^ 2 ∂P) ≤
        2 * (∑' a, ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, H a t.toNNReal ω ^ 2 ∂P) +
        2 * (∑' a, ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, K a t.toNNReal ω ^ 2 ∂P) := by
  obtain ⟨I, Y, hI, haI, hmY, htY, hY, hzY, heY, hsY⟩ :=
    exists_infinite_integral hB hAd hind hcross H hH hcH C hC hbH T heH
  obtain ⟨J, Z, hJ, haJ, hmZ, htZ, hZ, hzZ, heZ, hsZ⟩ :=
    exists_infinite_integral hB hAd hind hcross K hK hcK D hD hbK T heK
  have heD := summable_difference_energy_of_row_energies hB hAd hind
    H K hH hK hcH hcK C D hC hD hbH hbK T heH heK hI hJ haI haJ
  refine ⟨I, J, Y, Z, hI, hJ, haI, haJ, hmY, hmZ, htY, htZ,
    hY, hZ, hzY, hzZ, heY, heZ, hsY, hsZ, heD, ?_, ?_⟩
  · exact infinite_row_difference_isometry hB hAd hind hcross
      H K hH hK hcH hcK C D hC hD hbH hbK T hI hJ haI haJ hY hZ hsY hsZ heD
  · rw [← heY, ← heZ]
    simpa using BrownianGrid.integral_sq_sub_le_two hY hZ
      (MemLp.zero' : MemLp (fun _ : Ω => (0 : ℝ)) 2 P)

end Problem367.BrownianArrayFiltration

end

end OAI
