import OAI.NumberTheory.Jacobsthal.Estimates.ReferenceSourceDecomposition

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceHighIntervals

attribute [local instance] Classical.propDecidable
open _root_.Finset _root_.Set _root_.MeasureTheory
open FinitePathGeometry PrimeTiltGeometry ReferenceSourcePrimeSets ReferenceMertens
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimeEndpoints

noncomputable def highInterval (b : ℝ) (closed : Bool) : Set ℝ :=
  {x | 2<x ∧ capGuard closed b x}

theorem highInterval_measurable (b : ℝ) (closed : Bool) : MeasurableSet (highInterval b closed) := by
  cases closed <;> simp only [highInterval,capGuard,Bool.false_eq_true,ite_false,ite_true] <;> measurability

theorem highInterval_orderConnected (b : ℝ) (closed : Bool) : (highInterval b closed).OrdConnected := by
  cases closed
  · exact ordConnected_Ioo
  · exact ordConnected_Ioc

theorem highInterval_subset (b : ℝ) (closed : Bool) : highInterval b closed ⊆ Icc 2 b := by
  intro x hx
  refine ⟨hx.1.le,?_⟩
  cases closed
  · exact hx.2.le
  · exact hx.2

theorem highPrimes_eq_filter {w : ℝ} (hw : 1 < w) (b : ℝ) (closed : Bool) :
    highPrimes w b closed=(Nat.primesLE ⌊w^b⌋₊).filter (fun p => primeExponent w p ∈ highInterval b closed) := by
  ext p
  rw [highPrimes_membership hw,Finset.mem_filter]
  constructor
  · rintro ⟨hp,hlo,hcap⟩
    have hup : primeExponent w p ≤ b := by
      cases closed
      · exact hcap.le
      · exact hcap
    have hpx := (exponent_le_iff hw (by exact_mod_cast hp.pos)).mp hup
    have hfloor := (Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) b).le).mpr hpx
    exact ⟨Nat.mem_primesLE.mpr ⟨hfloor,hp⟩,hlo,hcap⟩
  · rintro ⟨hp,hlo,hcap⟩
    exact ⟨(Nat.mem_primesLE.mp hp).2,hlo,hcap⟩

theorem highPrime_sum {w : ℝ} (hw : 1 < w) (b : ℝ) (closed : Bool) (F : ℕ → ℝ) :
    (∑ p ∈ highPrimes w b closed,F p)=
      ∑ p ∈ Nat.primesLE ⌊w^b⌋₊,if primeExponent w p ∈ highInterval b closed then F p else 0 := by
  rw [highPrimes_eq_filter hw,Finset.sum_filter]

theorem highPrime_mass_eq {w : ℝ} (hw : 1 < w) (b : ℝ) (closed : Bool) :
    (∑ p ∈ highPrimes w b closed,(p:ℝ)⁻¹)=harmonicMass w false closed 2 b := by
  rw [highPrime_sum hw,harmonicMass]
  apply Finset.sum_congr rfl
  intro p _hp
  simp only [highInterval,capGuard,intervalGuard,Bool.false_eq_true,ite_false,Set.mem_ofPred_eq]
  split_ifs <;> rfl

theorem highInterval_integral {b : ℝ} (hb : 2 ≤ b) (closed : Bool) (F : ℝ → ℝ) :
    (∫ x in highInterval b closed,F x)=∫ x in (2:ℝ)..b,F x := by
  cases closed
  · change (∫ x in Ioo 2 b,F x)=_
    rw [← integral_Ioc_eq_integral_Ioo,intervalIntegral.integral_of_le hb]
  · exact (intervalIntegral.integral_of_le hb).symm

theorem highPrime_mass_bound : ∃ C w₀ : ℝ,0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ b : ℝ,2 ≤ b → ∀ closed : Bool,
      (∑ p ∈ highPrimes w b closed,(p:ℝ)⁻¹) ≤ C*(1+Real.log b) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := harmonic_prime_measure
  refine ⟨C+1,w₀,by positivity,hw₀,?_⟩
  intro w hw b hb closed
  have hw1 : 1 < w := hw₀.trans_le hw
  rw [highPrime_mass_eq hw1]
  have hh := h w hw 2 b (by norm_num) hb false closed
  have he : Real.exp (-c*Real.sqrt (2*Real.log w)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Real.sqrt_nonneg _))
  have hu := (abs_le.mp hh).2
  have hlog : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hl2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left he hC.le]

end NumberTheoryLean.ReferenceHighIntervals

end

end Erdos970

end OAI
