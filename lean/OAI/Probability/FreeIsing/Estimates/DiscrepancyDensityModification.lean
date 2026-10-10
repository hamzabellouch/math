import OAI.Probability.FreeIsing.Energy.DiscrepancyRowEnergy
import OAI.Probability.FreeIsing.Estimates.ProgressivePrimitiveFubini

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.DiscrepancyEnergy

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]

theorem density_congr_ae {μ : Measure Ω}
    {c c' b b' : ι → Ω → ℝ} {X Y m m' k k' : Ω → ℝ}
    (hc : ∀ i, c i =ᵐ[μ] b i) (hc' : ∀ i, c' i =ᵐ[μ] b' i)
    (hX : X =ᵐ[μ] Y) (hm : m =ᵐ[μ] k) (hm' : m' =ᵐ[μ] k') :
    density c c' X m m' =ᵐ[μ] density b b' Y k k' := by
  filter_upwards [ae_all_iff.mpr hc, ae_all_iff.mpr hc', hX, hm, hm']
    with ω hω hω' hXω hmω hmω'
  simp only [density, hω, hω', hXω, hmω, hmω']

theorem isStronglyProgressive_density
    {F : Filtration ℝ≥0 mΩ}
    {c c' : ι → ℝ≥0 → Ω → ℝ} {X m m' : ℝ≥0 → Ω → ℝ}
    (hc : ∀ i, IsStronglyProgressive F (c i))
    (hc' : ∀ i, IsStronglyProgressive F (c' i))
    (hX : IsStronglyProgressive F X)
    (hm : IsStronglyProgressive F m) (hm' : IsStronglyProgressive F m') :
    IsStronglyProgressive F (fun t =>
      density (fun i => c i t) (fun i => c' i t) (X t) (m t) (m' t)) := by
  intro T
  let : MeasurableSpace Ω := F T
  have hnoise : StronglyMeasurable (fun p : Set.Iic T × Ω =>
      ∑' i : ι, (c i p.1 p.2 - c' i p.1 p.2) ^ 2) := StronglyMeasurable.tsum
    (fun i => ((hc i T).sub (hc' i T)).pow 2)
  have hleft : StronglyMeasurable (fun p : Set.Iic T × Ω =>
      ∑' i : ι, c i p.1 p.2 ^ 2) := StronglyMeasurable.tsum (fun i => (hc i T).pow 2)
  have hright : StronglyMeasurable (fun p : Set.Iic T × Ω =>
      ∑' i : ι, c' i p.1 p.2 ^ 2) := StronglyMeasurable.tsum (fun i => (hc' i T).pow 2)
  exact hnoise.add (((stronglyMeasurable_const.mul (hX T)).mul
    (((hm T).mul hleft).sub ((hm' T).mul hright))))

theorem ae_all_primitive_density_eq_of_modification {μ : Measure Ω} [SFinite μ]
    {F G : Filtration ℝ≥0 mΩ}
    {c c' b b' : ι → ℝ≥0 → Ω → ℝ}
    {X Y m m' k k' : ℝ≥0 → Ω → ℝ}
    (hc : ∀ i, IsStronglyProgressive F (c i))
    (hc' : ∀ i, IsStronglyProgressive F (c' i))
    (hX : IsStronglyProgressive F X)
    (hm : IsStronglyProgressive F m) (hm' : IsStronglyProgressive F m')
    (hb : ∀ i, IsStronglyProgressive G (b i))
    (hb' : ∀ i, IsStronglyProgressive G (b' i))
    (hY : IsStronglyProgressive G Y)
    (hk : IsStronglyProgressive G k) (hk' : IsStronglyProgressive G k')
    (hcb : ∀ i t, c i t =ᵐ[μ] b i t)
    (hcb' : ∀ i t, c' i t =ᵐ[μ] b' i t)
    (hXY : ∀ t, X t =ᵐ[μ] Y t)
    (hmk : ∀ t, m t =ᵐ[μ] k t) (hmk' : ∀ t, m' t =ᵐ[μ] k' t) :
    ∀ᵐ ω ∂μ, ∀ t,
      nnrealTimePrimitive (fun s => density (fun i => c i s)
        (fun i => c' i s) (X s) (m s) (m' s)) t ω =
      nnrealTimePrimitive (fun s => density (fun i => b i s)
        (fun i => b' i s) (Y s) (k s) (k' s)) t ω := by
  apply ae_all_nnrealTimePrimitive_eq_of_modification
    (isStronglyProgressive_density hc hc' hX hm hm')
    (isStronglyProgressive_density hb hb' hY hk hk')
  intro t
  exact density_congr_ae (fun i => hcb i t) (fun i => hcb' i t)
    (hXY t) (hmk t) (hmk' t)

end Problem367.DiscrepancyEnergy

end

end OAI
