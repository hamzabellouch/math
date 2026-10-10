import OAI.NumberTheory.JointDickman.Probability.HistogramProductError
import OAI.NumberTheory.JointDickman.Probability.ResidueFourierProjection

namespace OAI

/-! # Identifying the residue projection of the actual histogram -/

namespace JointDickman
open Finset MeasureTheory

noncomputable def manuscriptProjectedValue (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ) : ℂ :=
  ∑ i ∈ J, (channelMesh (channelFineCount m B) : ℂ)*
    (finiteResidueAverage (fun r => manuscriptChannel m B q g (i,r)) : ℂ)*
      complexCellAverage (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i) F

noncomputable def manuscriptProjectedFourier (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ) (h : ZMod q) : ℂ :=
  unitResidueFourier (fun _ => complexResidueMean
    (fun r => ∑ i ∈ J, manuscriptCellApprox m B q g F i r)) h

theorem manuscriptProjectedValue_eq_sum (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ) :
    manuscriptProjectedValue m B q J g F =
      ∑ r : (ZMod q)ˣ, ∑ i ∈ J, manuscriptCellApprox m B q g F i r := by
  unfold manuscriptProjectedValue manuscriptCellApprox finiteResidueAverage
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp only [ZMod.card_units_eq_totient,Complex.ofReal_div,Complex.ofReal_sum,
    Complex.ofReal_natCast,Complex.ofReal_mul]
  rw [← sum_mul,← mul_sum]
  ring

theorem manuscriptProjectedFourier_eq (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ) (h : ZMod q) :
    manuscriptProjectedFourier m B q J g F h =
      (ramanujanSum q h/(q.totient : ℂ))*manuscriptProjectedValue m B q J g F := by
  rw [manuscriptProjectedFourier,unitResidueFourier_projected,manuscriptProjectedValue_eq_sum]

theorem manuscriptProjectedFourier_square_le (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ) :
    (∑ h : ZMod q, ‖manuscriptProjectedFourier m B q J g F h‖^2) ≤
      ∑ h : ZMod q, ‖manuscriptApproxFourier m B q J g F h‖^2 :=
  unitResidueFourier_projection_contract _

theorem manuscriptHistogram_centered_identity (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ) (h : ZMod q) :
    manuscriptApproxFourier m B q J g F h-manuscriptProjectedFourier m B q J g F h =
      unitResidueFourier (fun r => ∑ i ∈ J,
        (channelMesh (channelFineCount m B) : ℂ)*
          ((manuscriptChannel m B q g (i,r)-
            finiteResidueAverage (fun s => manuscriptChannel m B q g (i,s))) : ℝ)*
          complexCellAverage (channelLower (channelFineCount m B) i)
            (channelUpper (channelFineCount m B) i) F) h/(q.totient : ℂ) := by
  rw [manuscriptApproxFourier,manuscriptProjectedFourier,unitResidueFourier_centered]
  have hmean : complexResidueMean (fun r => ∑ i ∈ J, manuscriptCellApprox m B q g F i r) =
      manuscriptProjectedValue m B q J g F/(q.totient : ℂ) := by
    rw [complexResidueMean,manuscriptProjectedValue_eq_sum]
  simp only [unitResidueFourier]
  rw [sum_div]
  apply sum_congr rfl
  intro r _
  rw [hmean]
  unfold manuscriptProjectedValue manuscriptCellApprox
  simp only [sum_div,← sum_sub_distrib,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_sub]
  simp only [mul_sum,sum_div]
  apply sum_congr rfl
  intro i _
  push_cast
  ring

end JointDickman

end OAI
