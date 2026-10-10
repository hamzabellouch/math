import OAI.Probability.FreeIsing.Conditioning.PlantedInformation
import OAI.Probability.FreeIsing.Energy.ComponentCovariance

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal

namespace Problem367

abbrev ComponentIndex {d : ℕ} (c : Fin d) := Σ n : ℕ, ReducedTail c n

def componentIndexVertex {d : ℕ} {c : Fin d} (u : ComponentIndex c) : TreeVertex d :=
  componentVertex u.2

theorem componentIndexVertex_injective {d : ℕ} (c : Fin d) :
    Function.Injective (componentIndexVertex (c := c)) := by
  rintro ⟨k, u⟩ ⟨l, v⟩ h
  have hw : u.1 = v.1 := (List.cons.inj (congrArg Subtype.val h)).2
  have hkl : k = l := by
    simpa only [u.2.1, v.2.1] using congrArg List.length hw
  subst l
  have huv : u = v := Subtype.ext hw
  subst v
  rfl

theorem HasFreeIsingLaw.component_critical_information_lower {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (c : Fin d) (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) :
    min (Real.sqrt (t : ℝ)) 1 / 5 ≤
      ∫ p, (condExp
        (PlantedInformation.observationSigma (componentIndexVertex (c := c)) t)
        (mu.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
        (fun q => spinSign (q.1 ⟨[c], List.IsChain.singleton c⟩)) p) ^ 2
          ∂mu.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t) := by
  classical
  let := hmu.isProbabilityMeasure
  apply PlantedInformation.critical_information_of_spin_sums mu
    (componentIndexVertex (c := c)) (componentIndexVertex_injective c)
    ⟨[c], List.IsChain.singleton c⟩ ht
    (componentIndexFinset c) (fun _ u => theta ^ u.1)
  · intro n
    simp only [componentIndexFinset, Finset.sum_sigma]
    have hlen (k : ℕ) (u : ReducedTail c k) : u.1.length = k := u.2.1
    simpa only [hlen] using sum_component_radial_sq_levels_critical theta c hcritical n
  · intro n
    simp only [componentIndexFinset, Finset.sum_sigma, componentIndexVertex]
    exact hmu.component_signal_critical hlo hhi c hcritical n
  · intro n
    simp only [componentIndexFinset, Finset.sum_sigma, componentIndexVertex]
    calc
      _ = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          ∑ u : ReducedTail c k, ∑ v : ReducedTail c l,
          theta ^ k * theta ^ l *
            (∫ σ, spinSign (σ (componentVertex u)) * spinSign (σ (componentVertex v)) ∂mu) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_comm]
      _ ≤ _ := hmu.component_covariance_sum_critical_le hlo hhi c hcritical n

theorem HasFreeIsingLaw.component_critical_information_lower_of_le
    {d : ℕ} {theta : ℝ} {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (c : Fin d) (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t)
    (m' : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)))
    (hm' : m' ≤ MeasurableSpace.prod inferInstance inferInstance)
    (hobs : PlantedInformation.observationSigma (componentIndexVertex (c := c)) t ≤ m') :
    min (Real.sqrt (t : ℝ)) 1 / 5 ≤
      ∫ p, (condExp m'
        (mu.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
        (fun q => spinSign (q.1 ⟨[c], List.IsChain.singleton c⟩)) p) ^ 2
          ∂mu.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t) := by
  let := hmu.isProbabilityMeasure
  apply (hmu.component_critical_information_lower hlo hhi c hcritical ht).trans
  apply posterior_information_mono hobs hm'
  exact (PlantedInformation.spinSign_memLp mu ⟨[c], List.IsChain.singleton c⟩).comp_measurePreserving
    measurePreserving_fst

end Problem367

end

end OAI
