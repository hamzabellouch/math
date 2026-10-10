import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBAverageDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryPairVariableBAverage
open Construction HistoryPairPattern HistoryPairRows HistoryPairRepresentatives
open HistoryPairSquareProbability HistoryCRTIntegration HistoryBulkReferenceTests
open HistorySignedResidueFactorization ResidueHaar
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

theorem finiteBAt_intCast_iff_fiber_good (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ) (X Y : ℤ) :
    finiteOwnPrimeLinesAt h k hs ks v (X,Y) ↔ ∀r : Representative h k,
      Good (prime h k r) Finset.univ (actualLeftAt h k hs ks v r) (actualRightAt h k hs ks v r) X Y := by
  rw [finiteOwnPrimeLinesAt_intCast_iff]
  constructor
  · intro hh r
    constructor
    · intro i _
      have hp : (slot h k i.val).value=prime h k r := by
        rw [← prime_label h k i.val,i.property]
      simpa only [actualLeftAt,actualRightAt,hp] using (hh i.val).1
    · intro i _
      have hp : (slot h k i.val).value=prime h k r := by
        rw [← prime_label h k i.val,i.property]
      simpa only [actualLeftAt,actualRightAt,hp] using (hh i.val).2
  · intro hh i
    exact ⟨(hh (label h k i)).1 ⟨i,rfl⟩ (Finset.mem_univ _),
      (hh (label h k i)).2 ⟨i,rfl⟩ (Finset.mem_univ _)⟩

theorem finiteBAt_iff_projected_fiber_good (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (z : ZMod (representativeModulus h k)×ZMod (representativeModulus h k)) :
    finiteOwnPrimeLinesAt h k hs ks v z ↔ ∀r : Representative h k,
      Good (prime h k r) Finset.univ (actualLeftAt h k hs ks v r) (actualRightAt h k hs ks v r)
        ((representativeSquareProjectionB h k r z.1).val:ℤ)
        ((representativeSquareProjectionB h k r z.2).val:ℤ) := by
  let : NeZero (representativeModulus h k) := ⟨(representativeModulus_pos h k hs ks).ne'⟩
  have hz : (((z.1.val:ℤ):ZMod (representativeModulus h k)),
      ((z.2.val:ℤ):ZMod (representativeModulus h k)))=z := by
    simp only [Int.cast_natCast,ZMod.natCast_zmod_val]
  rw [← hz,finiteBAt_intCast_iff_fiber_good]
  apply forall_congr'
  intro r
  let : NeZero ((prime h k r)^2) := ⟨pow_ne_zero _ (representative_prime h k hs ks r).ne_zero⟩
  apply good_congr_square
  · simp only [Int.cast_natCast,ZMod.natCast_zmod_val]
    simpa only [ZMod.natCast_zmod_val] using
      (map_natCast (representativeSquareProjectionB h k r) z.1.val).symm
  · simp only [Int.cast_natCast,ZMod.natCast_zmod_val]
    simpa only [ZMod.natCast_zmod_val] using
      (map_natCast (representativeSquareProjectionB h k r) z.2.val).symm

theorem primeResidueIndicatorAt_eq_projected_product (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (z : ZMod (representativeModulus h k)×ZMod (representativeModulus h k)) :
    primeResidueIndicatorAt h k hs ks v z=∏r : Representative h k,
      actualSquareIndicatorAt h k hs ks v r
        (representativeSquareProjectionB h k r z.1,representativeSquareProjectionB h k r z.2) := by
  unfold primeResidueIndicatorAt actualSquareIndicatorAt
  rw [propext (finiteBAt_iff_projected_fiber_good h k hs ks v z),guardIndicator_forall]

end Ostmann.Arithmetic.HistoryPairVariableBAverage

end

end OAI
