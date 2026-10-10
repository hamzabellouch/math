import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageHaarBasic
import OAI.NumberTheory.Ostmann.Characters.BinaryExposure

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairedFrequencyAverageHaar
open Characters

theorem bulkLeaves_surjective (G : Type*) [CommGroup G] (m l : ℕ) (hm : 0 < m) :
    Function.Surjective (bulkLeaves (G:=G) m l) :=
  (orderedLeavesEquiv G l).surjective.comp (blockProductHom_surjective G m l hm)

theorem bulkLeaves_average {G : Type*} [CommGroup G] [Fintype G]
    (m l : ℕ) (hm : 0 < m) (test : BinaryHaar.Leaves G l → ℂ) :
    ResidueHaar.average (fun x : (Fin (2^l) × Fin m) → G => test (bulkLeaves m l x)) =
      ResidueHaar.average test := by
  have hh := GroupHaarImage.average_surjective (blockProductHom G m l)
    (blockProductHom_surjective G m l hm) (fun y => test (orderedLeavesEquiv G l y))
  exact hh.trans (ResidueHaar.average_equiv (orderedLeavesEquiv G l) test)

theorem bulkLeaves_avg {G : Type*} [CommGroup G] [Fintype G]
    (m l : ℕ) (hm : 0 < m) (test : BinaryHaar.Leaves G l → ℝ) :
    BinaryExposure.avg (fun x : (Fin (2^l) × Fin m) → G => test (bulkLeaves m l x)) =
      BinaryExposure.avg test := by
  have hh := bulkLeaves_average m l hm (fun y => (test y : ℂ))
  apply Complex.ofReal_injective
  simpa only [BinaryExposure.avg, ResidueHaar.average, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_sum] using hh

theorem bulkLeaves_proportion {G : Type*} [CommGroup G] [Fintype G]
    (m l : ℕ) (hm : 0 < m) (P : BinaryHaar.Leaves G l → Prop) :
    (Nat.card {x : (Fin (2^l) × Fin m) → G // P (bulkLeaves m l x)} : ℝ) /
        Nat.card ((Fin (2^l) × Fin m) → G) =
      (Nat.card {z : BinaryHaar.Leaves G l // P z} : ℝ) / Nat.card (BinaryHaar.Leaves G l) := by
  classical
  rw [← BinaryExposure.avg_indicator, ← BinaryExposure.avg_indicator]
  exact bulkLeaves_avg m l hm (fun z => if P z then 1 else 0)

end Ostmann.Arithmetic.HistoryPairedFrequencyAverageHaar

end

end OAI
