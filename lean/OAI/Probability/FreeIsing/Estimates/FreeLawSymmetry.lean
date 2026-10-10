import OAI.Probability.FreeIsing.Estimates.FreeLawUnique
import OAI.Probability.FreeIsing.Spins.Flip

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.flip_invariant {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu) :
    mu.map flipConfig = mu :=
  hmu.map_flipConfig.unique hmu

theorem HasFreeIsingLaw.measurePreserving_flipConfig {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu) :
    MeasurePreserving flipConfig mu mu :=
  ⟨measurable_flipConfig, hmu.flip_invariant⟩

theorem HasFreeIsingLaw.integral_odd {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (f : (TreeVertex d → IsingSpin) → ℝ) (hf : ∀ x, f (flipConfig x) = -f x) :
    ∫ x, f x ∂mu = 0 :=
  integral_eq_zero_of_flipConfig_odd hmu.flip_invariant f hf

theorem HasFreeIsingLaw.measure_even_event_inter_spin {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    {A : Set (TreeVertex d → IsingSpin)} (hA : MeasurableSet A)
    (hAflip : flipConfig ⁻¹' A = A) (v : TreeVertex d) (s : IsingSpin) :
    mu (A ∩ {x | x v = s}) = mu (A ∩ {x | x v = s.flip}) :=
  Problem367.measure_even_event_inter_spin hmu.flip_invariant hA hAflip v s

theorem HasFreeIsingLaw.setIntegral_spin_even {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    {f : (TreeVertex d → IsingSpin) → ℝ} (hf : Integrable f mu)
    (heven : ∀ x, f (flipConfig x) = f x) (v : TreeVertex d) (s : IsingSpin) :
    ∫ x in {x | x v = s}, f x ∂mu = (1 / 2 : ℝ) * ∫ x, f x ∂mu :=
  setIntegral_spin_eq_half_of_flipConfig_even hmu.flip_invariant hf heven v s

end Problem367

end

end OAI
