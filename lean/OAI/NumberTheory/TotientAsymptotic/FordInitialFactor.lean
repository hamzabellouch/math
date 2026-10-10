import OAI.NumberTheory.TotientAsymptotic.FordBandWitness
import OAI.NumberTheory.TotientAsymptotic.BandStateMass
import OAI.NumberTheory.TotientAsymptotic.InitialRoughEncoding

namespace OAI

/-! The first common rough factor of an actual Ford tuple. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma partBetween_eq_partAbove {n : ℕ} {U V : ℝ}
    (hV : (largestPrimeFactor n:ℝ) ≤ V) : partBetween n U V=partAbove n U := by
  unfold partBetween partAbove
  congr 1
  apply List.filter_congr
  intro p hp
  have hpV : (p:ℝ) ≤ V := (show (p:ℝ) ≤ largestPrimeFactor n by
    exact_mod_cast primeFactor_le_largest hp).trans hV
  simp only [hpV,and_true]

def fordInitialFactor {b : ℕ} (hb : 1 ≤ b) (t : ShiftedPair b) (Y : ℕ → ℝ) : ℕ :=
  partAbove (t.left ⟨0,by omega⟩-1) (Y 1)

lemma ford_initial_band {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hp : FordComparisonParameters b y S D r Y U)
    (h : FordComparisonConditions b y S D r Y U t) :
    pairedProduct (fordBand hp.1 t Y)=fordInitialFactor hp.1 t Y := by
  have hh := (h.2.1 ⟨0,by have := hp.1; omega⟩).2.2.2.2.1
  change (∏ j : Fin 1,partBetween (t.left (Fin.castLE hp.1 j)-1) (Y 1) (Y 0))=fordInitialFactor hp.1 t Y
  simp only [Fin.prod_univ_one]
  exact partBetween_eq_partAbove hh

lemma ford_initial_decomposition {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hp : FordComparisonParameters b y S D r Y U)
    (h : FordComparisonConditions b y S D r Y U t) :
    factorProduct (fordFactorState t (Y 1))*fordInitialFactor hp.1 t Y=shiftedProduct t.left := by
  have hU : Y 1 ≤ Y 0 := ford_cutoff_antitone hp (by omega) hp.1
  have hsplit := factorProduct_band_split hp.1 (fordFactorState t (Y 0)) hU
    (fun j => partBelow_nested _ le_rfl)
    (fun j hj => by
      rw [show partBetween ((fordFactorState t (Y 0)).left j) (Y 1) (Y 0)=
        partBetween (t.left j-1) (Y 1) (Y 0) from partBetween_below _ le_rfl]
      exact (ford_band_tail hp h j hj).1)
  rw [lower_fordFactorState t hU] at hsplit
  have hband : stateBand hp.1 (fordFactorState t (Y 0)) (Y 1) (Y 0)=fordBand hp.1 t Y :=
    stateBand_fordFactorState hp.1 t le_rfl
  rw [hband,ford_initial_band hp h] at hsplit
  rw [← hsplit]
  apply Finset.prod_congr rfl
  intro j hj
  exact partBelow_all_of_largest_le (ford_shift_pos h j).1.ne'
    (((h.2.1 j).2.2.2.2.1).trans (ford_cutoff_antitone hp (Nat.zero_le _) j.isLt.le))

end TotientAsymptotic

end

end OAI
