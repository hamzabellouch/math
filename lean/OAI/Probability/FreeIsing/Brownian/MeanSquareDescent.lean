import OAI.Probability.FreeIsing.Brownian.IntegralTransport
import OAI.Probability.FreeIsing.Posterior.FilteringRepresentationClosure

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Problem367.BrownianGrid

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}

theorem meanSquare_limit_comp_iff
    {α : Type*} {l : Filter α}
    (hφ : MeasurePreserving φ Q P) {X : α → Ω → ℝ} {I : Ω → ℝ}
    (hX : ∀ a, AEStronglyMeasurable (X a) P)
    (hI : AEStronglyMeasurable I P) :
    Tendsto (fun a => ∫ ω, (X a (φ ω) - I (φ ω)) ^ 2 ∂Q) l (𝓝 0) ↔
      Tendsto (fun a => ∫ ω, (X a ω - I ω) ^ 2 ∂P) l (𝓝 0) := by
  have heq : (fun a => ∫ ω, (X a (φ ω) - I (φ ω)) ^ 2 ∂Q) =
      (fun a => ∫ ω, (X a ω - I ω) ^ 2 ∂P) :=
    funext (fun a => integral_sq_sub_comp hφ (hX a) hI)
  rw [heq]

theorem meanSquare_limit_iff_of_comp_ae
    {α : Type*} {l : Filter α}
    (hφ : MeasurePreserving φ Q P)
    {X : α → Ω → ℝ} {I : Ω → ℝ}
    {Y : α → Ω' → ℝ} {J : Ω' → ℝ}
    (hX : ∀ a, AEStronglyMeasurable (X a) P)
    (hI : AEStronglyMeasurable I P)
    (hY : ∀ a, Y a =ᵐ[Q] X a ∘ φ) (hJ : J =ᵐ[Q] I ∘ φ) :
    Tendsto (fun a => ∫ ω, (Y a ω - J ω) ^ 2 ∂Q) l (𝓝 0) ↔
      Tendsto (fun a => ∫ ω, (X a ω - I ω) ^ 2 ∂P) l (𝓝 0) := by
  have heq : (fun a => ∫ ω, (Y a ω - J ω) ^ 2 ∂Q) =
      (fun a => ∫ ω, (X a (φ ω) - I (φ ω)) ^ 2 ∂Q) := by
    funext a
    apply integral_congr_ae
    filter_upwards [hY a, hJ] with ω hω hωJ
    simp only [hω, hωJ, Function.comp_apply]
  rw [heq]
  exact meanSquare_limit_comp_iff hφ hX hI

end Problem367.BrownianGrid

namespace Problem367.PredictableL2

theorem hasSum_toLp_iff_meanSquare
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 P)
    {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    HasSum (fun i => (hf i).toLp (f i)) (hY.toLp Y) ↔
      Tendsto (fun s : Finset ι => ∫ ω,
        ((∑ i ∈ s, f i ω) - Y ω) ^ 2 ∂P) atTop (𝓝 0) := by
  constructor
  · exact tendsto_integral_sq_error_of_hasSum f hf hY
  · intro hlim
    have h := FilteringRepresentationClosure.tendsto_toLp_of_integral_sq_error
      (fun s : Finset ι => memLp_finsetSum s (fun i _ => hf i)) hY hlim
    change Tendsto (fun s : Finset ι => ∑ i ∈ s, (hf i).toLp (f i))
      atTop (𝓝 (hY.toLp Y))
    convert h using 1
    funext s
    exact (toLp_finsetSum f hf s).symm

theorem hasSum_toLp_descend_of_comp_ae
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {φ : Ω' → Ω}
    (hφ : MeasurePreserving φ Q P)
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 P)
    {Y : Ω → ℝ} (hY : MemLp Y 2 P)
    (g : ι → Ω' → ℝ) (hg : ∀ i, MemLp (g i) 2 Q)
    {Z : Ω' → ℝ} (hZ : MemLp Z 2 Q)
    (hfg : ∀ i, g i =ᵐ[Q] f i ∘ φ) (hYZ : Z =ᵐ[Q] Y ∘ φ)
    (hsum : HasSum (fun i => (hg i).toLp (g i)) (hZ.toLp Z)) :
    HasSum (fun i => (hf i).toLp (f i)) (hY.toLp Y) := by
  apply (hasSum_toLp_iff_meanSquare f hf hY).mpr
  apply (BrownianGrid.meanSquare_limit_iff_of_comp_ae hφ
    (fun s : Finset ι => (memLp_finsetSum s (fun i _ => hf i)).aestronglyMeasurable)
    hY.aestronglyMeasurable (Y := fun s ω => ∑ i ∈ s, g i ω)
    (J := Z) ?_ hYZ).mp
  · exact tendsto_integral_sq_error_of_hasSum g hg hZ hsum
  · intro s
    have hall : ∀ᵐ ω ∂Q, ∀ i ∈ s, g i ω = f i (φ ω) :=
      (Filter.eventually_all_finite s.finite_toSet).mpr (fun i _ => hfg i)
    filter_upwards [hall] with ω hω
    exact Finset.sum_congr rfl (fun i hi => hω i hi)

end Problem367.PredictableL2

end

end OAI
