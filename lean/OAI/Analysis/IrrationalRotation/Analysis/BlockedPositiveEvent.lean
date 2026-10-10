import OAI.Analysis.IrrationalRotation.Couplings.BlockedProductCoupling
import OAI.Analysis.IrrationalRotation.Couplings.BlockedCouplingDensity
import OAI.Analysis.IrrationalRotation.Analysis.EndpointLoss
import OAI.Analysis.IrrationalRotation.Analysis.ParameterTails

namespace OAI

open Filter MeasureTheory Set
open scoped Topology

namespace Invariant233.BlockedProductCoupling

variable {m : ℕ → ℕ} {κ : ℕ → ℝ}
  {a b : (s : ℕ) → Fin (m s) → ℝ}
  (hm : ∀ s, 100 ≤ m s) (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
  (ha : ∀ s i, 1 / (m s : ℝ) ≤ a s i) (ha' : ∀ s i, a s i ≤ 1 / 4)
  (hb : ∀ s i, 1 / (m s : ℝ) ≤ b s i) (hb' : ∀ s i, b s i ≤ 1 / 4)

include hm hκ0 hκ ha ha' hb hb'

theorem futureBad_mass_le_ratio {K : ℕ → ℝ} (hK : ∀ s, 0 < K s)
    (hd : ∀ s, 2 * K s ≤ K (s + 1)) (j : ℕ) :
    (law m κ a b j).real (futureBad m K j) ≤ 80 * (K j / K (j + 1)) := by
  have hs : Summable (fun n : ℕ => 1 / K (j + 1 + n)) := by
    simpa only [Function.comp_def, Nat.add_comm] using
      (ParameterTails.summable_reciprocal hK hd).comp_injective
        (show Function.Injective (fun n : ℕ => n + (j + 1)) from
          fun _ _ h => Nat.add_right_cancel h)
  calc
    _ ≤ 40 * K j * ∑' n : ℕ, 1 / K (j + 1 + n) :=
      futureBad_mass_le hm hκ0 hκ ha ha' hb hb' hK j hs
    _ ≤ 40 * K j * (2 / K (j + 1)) :=
      mul_le_mul_of_nonneg_left (ParameterTails.reciprocal_tail_bound hK hd j)
        (mul_nonneg (by norm_num) (hK j).le)
    _ = 80 * (K j / K (j + 1)) := by ring

theorem tendsto_futureBad_mass_zero {K : ℕ → ℝ} (hK : ∀ s, 0 < K s)
    (hd : ∀ s, 2 * K s ≤ K (s + 1))
    (hratio : Tendsto (fun j => K j / K (j + 1)) atTop (𝓝 0)) :
    Tendsto (fun j => (law m κ a b j).real (futureBad m K j)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (futureBad_mass_le_ratio hm hκ0 hκ ha ha' hb hb' hK hd)
  simpa using tendsto_const_nhds.mul hratio

theorem eventually_retainedEvent_mass
    {K : ℕ → ℝ} (hK : ∀ s, 0 < K s)
    (hd : ∀ s, 2 * K s ≤ K (s + 1))
    (hratio : Tendsto (fun j => K j / K (j + 1)) atTop (𝓝 0))
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {r : X → ℝ} (hr : Measurable r) (hi : ∀ᵐ x ∂μ, 0 < r x ∧ r x < 1)
    (x y : Sample m → X) (hx : Measurable x) (hy : Measurable y)
    (h₁ h₂ : ℕ → X → ℝ)
    (hh₁ : ∀ j, MemLp (h₁ j) 2 μ) (hh₂ : ∀ j, MemLp (h₂ j) 2 μ)
    (hn₁ : ∀ j, 0 ≤ᵐ[μ] h₁ j) (hn₂ : ∀ j, 0 ≤ᵐ[μ] h₂ j)
    (H₁ H₂ : ℝ)
    (hH₁ : ∀ j, Real.sqrt (∫ z, h₁ j z ^ 2 ∂μ) ≤ H₁)
    (hH₂ : ∀ j, Real.sqrt (∫ z, h₂ j z ^ 2 ∂μ) ≤ H₂)
    (hmap₁ : ∀ j, (law m κ a b j).map x =
      μ.withDensity (fun z => ENNReal.ofReal (h₁ j z)))
    (hmap₂ : ∀ j, (law m κ a b j).map y =
      μ.withDensity (fun z => ENNReal.ofReal (h₂ j z))) :
    ∀ᶠ j in atTop, Real.exp (-82) / 2 ≤
      (law m κ a b j).real (retainedEvent m K r x y j) := by
  have := law_isProbabilityMeasure hm hκ0 hκ ha ha' hb hb'
  have hdiag := EndpointLoss.tendsto_endpoint_bad_union_zero μ hr hi
    (law m κ a b) (fun _ => x) (fun _ => y) (fun _ => hx) (fun _ => hy)
    h₁ h₂ hh₁ hh₂ hn₁ hn₂ H₁ H₂ hH₁ hH₂ hmap₁ hmap₂
  have hfuture := tendsto_futureBad_mass_zero hm hκ0 hκ ha ha' hb hb' hK hd hratio
  have hloss : Tendsto (fun j => (law m κ a b j).real
      (futureBad m K j ∪ ({z | r (x z) < 1 / (j : ℝ)} ∪
        {z | 1 - r (y z) < 1 / (j : ℝ)}))) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) (fun _ => measureReal_union_le _ _)
    simpa only [zero_add] using hfuture.add hdiag
  exact InvariantRotation.TaggedEventBounds.eventually_half_le_measureReal_sdiff
    (law m κ a b) (currentEvent m) _ (Real.exp_pos _)
    (Eventually.of_forall (currentEvent_mass hm hκ0 hκ ha ha' hb hb')) hloss

theorem eventually_actual_retainedEvent_mass
    (hsq : Summable (fun s => κ s ^ 2))
    (e : ℕ ≃ Σ s, Fin (m s))
    {K : ℕ → ℝ} (hK : ∀ s, 0 < K s)
    (hd : ∀ s, 2 * K s ≤ K (s + 1))
    (hratio : Tendsto (fun j => K j / K (j + 1)) atTop (𝓝 0))
    {r : OrderedProductCoupling.Endpoint → ℝ} (hr : Measurable r)
    (hi : ∀ᵐ x ∂OrderedProductCoupling.baseMeasure, 0 < r x ∧ r x < 1) :
    ∀ᶠ j in atTop, Real.exp (-82) / 2 ≤
      (law m κ a b j).real
        (retainedEvent m K r (leftEndpoint e) (rightEndpoint e) j) := by
  choose h₁ hh₁ hn₁ hH₁ hmap₁ using
    exists_left_density_of_blocks hm hκ0 hκ ha ha' hb hb' hsq e
  choose h₂ hh₂ hn₂ hH₂ hmap₂ using
    exists_right_density_of_blocks hm hκ0 hκ ha ha' hb hb' hsq e
  apply eventually_retainedEvent_mass hm hκ0 hκ ha ha' hb hb' hK hd hratio
    OrderedProductCoupling.baseMeasure hr hi (leftEndpoint e) (rightEndpoint e)
    (by unfold leftEndpoint flatten OrderedProductCoupling.leftEndpoint; fun_prop)
    (by unfold rightEndpoint flatten OrderedProductCoupling.rightEndpoint; fun_prop)
    h₁ h₂ hh₁ hh₂ hn₁ hn₂ _ _ hH₁ hH₂ hmap₁ hmap₂

end Invariant233.BlockedProductCoupling

end OAI
