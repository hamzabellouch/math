import OAI.Analysis.FiniteFactor.Coupling.Density
import OAI.Analysis.FiniteFactor.Coupling.Parameters
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

namespace FiniteFactor
open MeasureTheory
noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {ι : Type*} [Fintype ι]

def mixtureDensity (q : ℝ) (π : ι → ℝ) (d : ι → X → ℝ) (x : X) : ℝ :=
  q + ∑ i, π i * d i x

theorem mixtureDensity_memLp (q : ℝ) (π : ι → ℝ) (d : ι → X → ℝ)
    (hd : ∀ i, MemLp (d i) 2 μ) : MemLp (mixtureDensity q π d) 2 μ :=
  (memLp_const q).add (memLp_finsetSum Finset.univ (fun i _ => (hd i).const_mul (π i)))

theorem mixtureDensity_integral (q : ℝ) (π : ι → ℝ) (d : ι → X → ℝ)
    (hd : ∀ i, Integrable (d i) μ) (hm : ∀ i, ∫ x, d i x ∂μ = 1)
    (hπ : q + ∑ i, π i = 1) : ∫ x, mixtureDensity q π d x ∂μ = 1 := by
  have hi := integral_add (integrable_const q)
    (integrable_finsetSum Finset.univ (fun i _ => (hd i).const_mul (π i)))
  unfold mixtureDensity
  rw [hi, integral_finsetSum Finset.univ (fun i _ => (hd i).const_mul (π i))]
  simp_rw [integral_const_mul, hm, mul_one]
  simpa using hπ

theorem mixtureDensity_energy_le (q : ℝ) (π : ι → ℝ) (d : ι → X → ℝ)
    (hd : ∀ i, MemLp (d i) 2 μ) (hm : ∀ i, ∫ x, d i x ∂μ = 1)
    (hπ : q + ∑ i, π i = 1) (E : ι → ℝ)
    (hE : ∀ i, (∫ x, (d i x - 1)^2 ∂μ) ≤ E i) :
    (∫ x, mixtureDensity q π d x ^ 2 ∂μ) ≤
      1 + (Fintype.card ι : ℝ) * ∑ i, (π i)^2 * E i := by
  classical
  have hd1 (i) : Integrable (d i) μ := (hd i).integrable (by norm_num)
  have hh := mixtureDensity_memLp q π d hd
  have hm' := mixtureDensity_integral q π d hd1 hm hπ
  have heq (x : X) : mixtureDensity q π d x - 1 = ∑ i, π i * (d i x - 1) := by
    simp only [mixtureDensity, mul_sub, mul_one, Finset.sum_sub_distrib]
    linarith
  have hbound (x : X) : (mixtureDensity q π d x - 1)^2 ≤
      (Fintype.card ι : ℝ) * ∑ i, (π i)^2 * (d i x - 1)^2 := by
    rw [heq]
    simpa [mul_pow] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => π i * (d i x - 1)))
  have hsub (i) : MemLp (fun x => d i x - 1) 2 μ := (hd i).sub (memLp_const 1)
  have his (i) : Integrable (fun x => (π i)^2 * (d i x - 1)^2) μ :=
    (hsub i).integrable_sq.const_mul _
  have hi := integral_mono ((hh.sub (memLp_const 1)).integrable_sq)
    ((integrable_finsetSum Finset.univ (fun i _ => his i)).const_mul (Fintype.card ι : ℝ)) hbound
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => his i)] at hi
  simp_rw [integral_const_mul] at hi
  have hsum : (∑ i, (π i)^2 * ∫ x, (d i x - 1)^2 ∂μ) ≤ ∑ i, (π i)^2 * E i := by
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hE i) (sq_nonneg _)
  have he := density_energy_identity (hh.integrable (by norm_num)) hh.integrable_sq hm'
  have hc := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _)
  dsimp only [Pi.sub_apply] at hi
  linarith

def unitIntervalMeasure : Measure ℝ := volume.restrict (Set.Ico 0 1)

instance : IsProbabilityMeasure unitIntervalMeasure := by
  constructor
  simp [unitIntervalMeasure, Real.volume_Ico]

theorem unitIntervalMeasure_interval {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    unitIntervalMeasure.real (Set.Ico a b) = b-a := by
  rw [unitIntervalMeasure, measureReal_restrict_apply measurableSet_Ico,
    Set.inter_eq_left.mpr (Set.Ico_subset_Ico ha hb), Real.volume_real_Ico_of_le hab]

namespace CouplingParameters
variable (p : CouplingParameters)

def endpointLength (right : Bool) (i : Fin 5) : ℝ :=
  if right then p.rightLength i else p.leftLength i

def endpointInterval (right : Bool) (i : Fin 5) : Set ℝ :=
  if right then Set.Ico (1-p.rightLength i) 1 else Set.Ico 0 (p.leftLength i)

def endpointComponentDensity (right : Bool) (i : Fin 5) : ℝ → ℝ :=
  intervalDensity (p.endpointInterval right i) (p.endpointLength right i)

def endpointDensity (right : Bool) : ℝ → ℝ :=
  mixtureDensity p.diagonalMass p.replacementMass (p.endpointComponentDensity right)

theorem endpointLength_pos (right : Bool) (i : Fin 5) : 0 < p.endpointLength right i := by
  cases right <;> simp [endpointLength, leftLength_pos, rightLength_pos]

theorem endpointLength_le (right : Bool) (i : Fin 5) : p.endpointLength right i ≤ 1 := by
  have := p.lengths_sum_le i
  have := p.leftLength_pos i
  have := p.rightLength_pos i
  cases right <;> simp [endpointLength] <;> linarith

theorem endpointInterval_measurable (right : Bool) (i : Fin 5) :
    MeasurableSet (p.endpointInterval right i) := by
  cases right <;> exact measurableSet_Ico

theorem endpointInterval_mass (right : Bool) (i : Fin 5) :
    unitIntervalMeasure.real (p.endpointInterval right i) = p.endpointLength right i := by
  have hpos := p.endpointLength_pos right i
  have hle := p.endpointLength_le right i
  cases right
  · simpa [endpointInterval, endpointLength] using
      unitIntervalMeasure_interval (a := 0) (by norm_num) hpos.le hle
  · have h₀ : 0 ≤ 1-p.rightLength i := by simpa [endpointLength] using sub_nonneg.mpr hle
    have h₁ : 1-p.rightLength i ≤ 1 := by have := p.rightLength_pos i; linarith
    simpa [endpointInterval, endpointLength] using
      unitIntervalMeasure_interval h₀ h₁ le_rfl

theorem endpointDensity_memLp (right : Bool) : MemLp (p.endpointDensity right) 2 unitIntervalMeasure := by
  apply mixtureDensity_memLp
  intro i
  exact (memLp_const _).indicator (p.endpointInterval_measurable right i)

theorem endpointDensity_integral (right : Bool) :
    ∫ t, p.endpointDensity right t ∂unitIntervalMeasure = 1 := by
  apply mixtureDensity_integral
  · intro i
    exact intervalDensity_integrable (p.endpointInterval_measurable right i) _
  · intro i
    exact intervalDensity_integral (p.endpointInterval_measurable right i)
      (p.endpointLength_pos right i) (p.endpointInterval_mass right i)
  · exact p.mass_sum

theorem endpointDensity_lower (right : Bool) (t : ℝ) :
    p.diagonalMass ≤ p.endpointDensity right t := by
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun i _ => mul_nonneg (p.replacementMass_nonneg i)
    (intervalDensity_nonneg (p.endpointLength_pos right i).le t)

end CouplingParameters
end
end FiniteFactor

end OAI
