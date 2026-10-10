import OAI.NumberTheory.JointDickman.Counting.HistogramCellCoefficients
import OAI.NumberTheory.JointDickman.Probability.ProjectedHistogram

namespace OAI

/-! # Residue projection of the sampled endpoint histogram -/

namespace JointDickman
open Finset MeasureTheory

theorem unitResidueFourier_projected_sub_contract {q : ℕ} [NeZero q]
    (v w : (ZMod q)ˣ → ℂ) :
    (∑ h : ZMod q, ‖unitResidueFourier (fun _ => complexResidueMean v) h-
      unitResidueFourier (fun _ => complexResidueMean w) h‖^2) ≤
      ∑ h : ZMod q, ‖unitResidueFourier v h-unitResidueFourier w h‖^2 := by
  have hh := unitResidueFourier_projection_contract (fun r => v r-w r)
  simpa only [complexResidueMean,sum_sub_distrib,sub_div,unitResidueFourier,
    sub_mul,mul_sub] using hh

noncomputable def sampledProjectedValue (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ)
    (F : Fin (channelFineCount m B) → ℂ) : ℂ :=
  ∑ i ∈ J, (channelMesh (channelFineCount m B) : ℂ)*
    (finiteResidueAverage (fun r => manuscriptChannel m B q g (i,r)) : ℂ)*F i

noncomputable def sampledProjectedFourier (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ)
    (F : Fin (channelFineCount m B) → ℂ) (h : ZMod q) : ℂ :=
  unitResidueFourier (fun _ => complexResidueMean (fun r => ∑ i ∈ J,
    (((channelMesh (channelFineCount m B)/(q.totient : ℝ))*
      manuscriptChannel m B q g (i,r) : ℝ) : ℂ)*F i)) h

theorem sampledProjectedValue_eq_sum (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ)
    (F : Fin (channelFineCount m B) → ℂ) :
    sampledProjectedValue m B q J g F =
      ∑ r : (ZMod q)ˣ, ∑ i ∈ J,
        (((channelMesh (channelFineCount m B)/(q.totient : ℝ))*
          manuscriptChannel m B q g (i,r) : ℝ) : ℂ)*F i := by
  unfold sampledProjectedValue finiteResidueAverage
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp only [ZMod.card_units_eq_totient,Complex.ofReal_div,Complex.ofReal_sum,
    Complex.ofReal_natCast,Complex.ofReal_mul]
  rw [← sum_mul,← mul_sum]
  ring

theorem sampledProjectedFourier_eq (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ)
    (F : Fin (channelFineCount m B) → ℂ) (h : ZMod q) :
    sampledProjectedFourier m B q J g F h =
      (ramanujanSum q h/(q.totient : ℂ))*sampledProjectedValue m B q J g F := by
  rw [sampledProjectedFourier,unitResidueFourier_projected,sampledProjectedValue_eq_sum]

theorem sampledProjectedFourier_square_le {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (F : Fin (channelFineCount m B) → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ i ∈ J, ‖F i‖ ≤ M) :
    (∑ h : ZMod q, ‖sampledProjectedFourier m B q J g F h‖^2) ≤
      manuscriptAmplitudeEnergy m B q J*M^2 :=
  (unitResidueFourier_projection_contract _).trans
    (cellCoefficientFourier_square_le hm hB J g hg F hM hF)

theorem projected_averaged_to_sampled_square_error {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (F : ℝ → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hI : ∀ i ∈ J, IntervalIntegrable F volume
      (channelLower (channelFineCount m B) i) (channelUpper (channelFineCount m B) i))
    (hLip : ∀ i ∈ J, ∀ u ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i),
      ∀ v ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i), ‖F u-F v‖ ≤ L*|u-v|) :
    (∑ h : ZMod q, ‖manuscriptProjectedFourier m B q J g F h-
      sampledProjectedFourier m B q J g (fun i => F (channelLower (channelFineCount m B) i)) h‖^2) ≤
      manuscriptAmplitudeEnergy m B q J*(L*channelMesh (channelFineCount m B))^2 :=
  (unitResidueFourier_projected_sub_contract _ _).trans
    (averaged_to_sampled_square_error hm hB J g hg F hL hI hLip)

end JointDickman

end OAI
