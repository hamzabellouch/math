import OAI.Analysis.FiniteFactor.Coupling.Law

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace CouplingParameters
variable (p : CouplingParameters)

/-- Conditioning on y uses a bottom label; conditioning on x uses a top label. -/
def crossingLabel (right : Bool) (w : Fin 2) : Fin 5 :=
  if right then ![1,3] w else ![0,2] w

theorem crossingLabel_mass (right : Bool) (w : Fin 2) :
    p.replacementMass (crossingLabel right w) = p.rho w := by
  cases right <;> fin_cases w <;> simp [crossingLabel, replacementMass]

theorem crossingLabel_length (right : Bool) (w : Fin 2) :
    p.endpointLength right (crossingLabel right w) = 1-p.width w/2 := by
  cases right <;> fin_cases w <;>
    simp [crossingLabel, endpointLength, leftLength, rightLength]

theorem crossingLabel_interval (right : Bool) (w : Fin 2) :
    p.endpointInterval right (crossingLabel right w) =
      if right then Set.Ico (p.width w/2) 1 else Set.Ico 0 (1-p.width w/2) := by
  cases right <;> fin_cases w <;>
    simp [crossingLabel, endpointInterval, leftLength, rightLength]

theorem crossingLabel_opposite_interval (right : Bool) (w : Fin 2) :
    p.endpointInterval (!right) (crossingLabel right w) =
      if right then Set.Ico 0 (p.width w/2) else Set.Ico (1-p.width w/2) 1 := by
  cases right <;> fin_cases w <;>
    simp [crossingLabel, endpointInterval, leftLength, rightLength]

/-- This is the conditional label weight from conditional-kernel. -/
def posteriorMass (right : Bool) (t : ℝ) (i : Fin 5) : ℝ :=
  p.replacementMass i * p.endpointComponentDensity right i t / p.endpointDensity right t

theorem posteriorMass_nonneg (right : Bool) (t : ℝ) (i : Fin 5) :
    0 ≤ p.posteriorMass right t i := by
  apply div_nonneg
  · exact mul_nonneg (p.replacementMass_nonneg i)
      (intervalDensity_nonneg (p.endpointLength_pos right i).le t)
  · exact (p.diagonalMass_pos.trans_le (p.endpointDensity_lower right t)).le

theorem posteriorMass_sum (right : Bool) (t : ℝ) :
    p.diagonalMass / p.endpointDensity right t + ∑ i, p.posteriorMass right t i = 1 := by
  simp only [posteriorMass]
  rw [← Finset.sum_div, ← add_div]
  change p.endpointDensity right t / p.endpointDensity right t = 1
  exact div_self (ne_of_gt (p.diagonalMass_pos.trans_le (p.endpointDensity_lower right t)))

theorem crossing_component_density_ge_one (right : Bool) (w : Fin 2)
    {t u : ℝ} (ht : t ∈ Set.Ico 0 1) (hu : p.width w ≤ u ∧ u ≤ 1-p.width w)
    (heligible : if right then u ≤ t else t < u) :
    1 ≤ p.endpointComponentDensity right (crossingLabel right w) t := by
  have hw := p.width_pos w
  have hupp := p.width_upper w
  have hmem : t ∈ p.endpointInterval right (crossingLabel right w) := by
    rw [p.crossingLabel_interval]
    cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at *
    · exact ⟨ht.1, by linarith [hu.2]⟩
    · exact ⟨by linarith [hu.1], ht.2⟩
  unfold endpointComponentDensity intervalDensity
  rw [Set.indicator_of_mem hmem, p.crossingLabel_length]
  exact (one_le_inv₀ (by linarith : 0 < 1-p.width w/2)).2 (by linarith)

theorem crossing_posterior_lower (right : Bool) (w : Fin 2)
    {t u : ℝ} (ht : t ∈ Set.Ico 0 1) (hu : p.width w ≤ u ∧ u ≤ 1-p.width w)
    (heligible : if right then u ≤ t else t < u) :
    p.rho w / 10 ≤ p.posteriorMass right t (crossingLabel right w) := by
  have hh := p.diagonalMass_pos.trans_le (p.endpointDensity_lower right t)
  have hd := p.crossing_component_density_ge_one right w ht hu heligible
  unfold posteriorMass
  rw [p.crossingLabel_mass]
  calc
    p.rho w / 10 ≤ p.rho w / p.endpointDensity right t :=
      div_le_div_of_nonneg_left (p.rho_nonneg w) hh (p.endpointDensity_lt_ten right t).le
    _ ≤ _ := div_le_div_of_nonneg_right
      (by simpa using mul_le_mul_of_nonneg_left hd (p.rho_nonneg w)) hh.le

/-- The opposite endpoint of the selected label crosses the threshold surely. -/
theorem crossing_partner_interval (right : Bool) (w : Fin 2) {u : ℝ}
    (hu : p.width w ≤ u ∧ u ≤ 1-p.width w) :
    p.endpointInterval (!right) (crossingLabel right w) ⊆
      if right then Set.Iio u else Set.Ici u := by
  rw [p.crossingLabel_opposite_interval]
  have hw := p.width_pos w
  cases right <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · intro z hz
    exact (by linarith [hz.1, hu.2] : u ≤ z)
  · intro z hz
    exact (by linarith [hz.2, hu.1] : z < u)

/-- The actual probability measure in the displayed conditional-kernel formula.
The disintegration identities are proved separately. -/
def posteriorLaw (right : Bool) (t : ℝ) : Measure ℝ :=
  ENNReal.ofReal (p.diagonalMass / p.endpointDensity right t) • Measure.dirac t +
    ∑ i, ENNReal.ofReal (p.posteriorMass right t i) • p.endpointComponentLaw (!right) i

instance posteriorLaw_probability (right : Bool) (t : ℝ) :
    IsProbabilityMeasure (p.posteriorLaw right t) := by
  constructor
  simp only [posteriorLaw, Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => p.posteriorMass_nonneg right t i),
    ← ENNReal.ofReal_add (div_nonneg p.diagonalMass_pos.le
      (p.diagonalMass_pos.trans_le (p.endpointDensity_lower right t)).le)
      (Finset.sum_nonneg (fun i _ => p.posteriorMass_nonneg right t i)),
    p.posteriorMass_sum]
  simp

theorem posteriorLaw_component_le (right : Bool) (t : ℝ) (i : Fin 5) (S : Set ℝ) :
    ENNReal.ofReal (p.posteriorMass right t i) * p.endpointComponentLaw (!right) i S ≤
      p.posteriorLaw right t S := by
  rw [posteriorLaw, Measure.add_apply, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  apply le_trans _ (le_add_left le_rfl)
  exact Finset.single_le_sum (f := fun j => ENNReal.ofReal (p.posteriorMass right t j) *
    p.endpointComponentLaw (!right) j S) (fun j _ => zero_le) (Finset.mem_univ i)

/-- Both orientations of the actual posterior crossing estimate, with the
source constant 1/10 and no assumptions on a candidate projection. -/
theorem posteriorLaw_crossing_lower (right : Bool) (w : Fin 2)
    {t u : ℝ} (ht : t ∈ Set.Ico 0 1) (hu : p.width w ≤ u ∧ u ≤ 1-p.width w)
    (heligible : if right then u ≤ t else t < u) :
    ENNReal.ofReal (p.rho w / 10) ≤
      p.posteriorLaw right t (if right then Set.Iio u else Set.Ici u) := by
  have hcomp := p.endpointComponentLaw_of_contains (!right) (crossingLabel right w)
    (p.crossing_partner_interval right w hu)
  have hterm := p.posteriorLaw_component_le right t (crossingLabel right w)
    (if right then Set.Iio u else Set.Ici u)
  rw [hcomp, mul_one] at hterm
  exact (ENNReal.ofReal_le_ofReal (p.crossing_posterior_lower right w ht hu heligible)).trans hterm

end CouplingParameters
end
end FiniteFactor

end OAI
