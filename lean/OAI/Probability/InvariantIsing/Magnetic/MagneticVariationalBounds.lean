import OAI.Probability.InvariantIsing.Magnetic.MagneticVariational
import OAI.Probability.InvariantIsing.Core.FiniteVariationalBounds

namespace OAI

/-! Finiteness of the magnetic variational value, with the original
cube-mass entropy lower bound. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace InvariantIsing

lemma magneticEntropyFunctional_lower {A : Type*} [Fintype A]
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hmag : ∀ a, |mag a| ≤ 1) (p : OverlapPath) :
    ((-Real.log 2 : ℝ) : EReal) ≤ magneticEntropyFunctional γ mag p := by
  have hg : -Real.log 2 ≤ magneticGroupValue γ mag zeroField := by
    calc
      _ = ∑ a, γ a * (-Real.log 2) := by rw [← Finset.sum_mul, hγsum, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
        (by simpa only [zeroField, sub_zero, zero_div] using
          (constrainedFieldValue_bounds zeroField (hmag a)).1) (hγ a)
  have hh := le_iSup (fun h : FieldStep =>
    ((magneticGroupValue γ mag h + fieldPairing p h / 2 : ℝ) : EReal)) zeroField
  simp only [fieldPairing_zero, zero_div, add_zero] at hh
  exact (EReal.coe_le_coe hg).trans hh

theorem finiteMagneticVariational_mem_interval {A ι : Type*} [Fintype A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hmag : ∀ a, |mag a| ≤ 1) (K : ℝ) (heig : ∀ a, |eig a| ≤ K) :
    ((-Real.log 2-K/2 : ℝ) : EReal) ≤ magneticVariationalFunctional (finiteR ρ eig hρ hρsum) γ mag ∧
      magneticVariationalFunctional (finiteR ρ eig hρ hρsum) γ mag ≤ ((K/2 : ℝ) : EReal) := by
  constructor
  · apply le_iInf
    intro p
    have hs := (abs_le.mp (finiteSpectralFunctional_abs_le ρ eig hρ hρsum K heig p)).1
    have hh := add_le_add (magneticEntropyFunctional_lower γ mag hγ hγsum hmag p)
      (EReal.coe_le_coe hs)
    simpa only [← EReal.coe_add, sub_eq_add_neg, neg_div] using hh
  · exact (magneticVariationalFunctional_le (finiteR ρ eig hρ hρsum) γ mag hγ hγsum hmag).trans
      (finiteVariational_mem_interval ρ eig hρ hρsum K heig).2

theorem finiteMagneticVariational_ne_top_bot {A ι : Type*} [Fintype A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hmag : ∀ a, |mag a| ≤ 1) :
    magneticVariationalFunctional (finiteR ρ eig hρ hρsum) γ mag ≠ ⊤ ∧
      magneticVariationalFunctional (finiteR ρ eig hρ hρsum) γ mag ≠ ⊥ := by
  let K := ∑ a, |eig a|
  have heig a : |eig a| ≤ K := Finset.single_le_sum
    (fun a _ => abs_nonneg (eig a)) (Finset.mem_univ a)
  have hb := finiteMagneticVariational_mem_interval ρ eig hρ hρsum γ mag hγ hγsum hmag K heig
  exact ⟨ne_top_of_le_ne_top (EReal.coe_ne_top _) hb.2,
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hb.1⟩

end InvariantIsing

end

end OAI
