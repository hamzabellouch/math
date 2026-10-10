import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSquareProbabilityActual
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationB

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryPairSquareProbability
open Construction Characters.RationalHistory HistoryPairPattern HistoryPairRows
open HistoryPairRepresentatives HistoryCRTIntegration HistorySignedResidueFactorization
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

lemma linear_dvd_congr {n : ℕ} (A B X Y X' Y' : ℤ)
    (hx : (X : ZMod n)=(X' : ZMod n)) (hy : (Y : ZMod n)=(Y' : ZMod n)) :
    (n:ℤ) ∣ A*X+B*Y ↔ (n:ℤ) ∣ A*X'+B*Y' := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_add,Int.cast_mul,hx,hy]

lemma good_congr_square {ι : Type*} (p : ℕ) (s : Finset ι) (A B : ι→ℤ)
    (X Y X' Y' : ℤ) (hx : (X:ZMod (p^2))=(X':ZMod (p^2)))
    (hy : (Y:ZMod (p^2))=(Y':ZMod (p^2))) :
    Good p s A B X Y ↔ Good p s A B X' Y' := by
  let red : ZMod (p^2)→+*ZMod p := ZMod.castHom (dvd_pow_self p (by decide : 2≠0)) _
  have hx₁ : (X:ZMod p)=(X':ZMod p) := by simpa only [map_intCast] using congrArg red hx
  have hy₁ : (Y:ZMod p)=(Y':ZMod p) := by simpa only [map_intCast] using congrArg red hy
  have hbase : Base p s A B X Y ↔ Base p s A B X' Y' := by
    unfold Base
    exact forall_congr' fun i => forall_congr' fun _ => linear_dvd_congr (A i) (B i) X Y X' Y' hx₁ hy₁
  rw [Good,Good,hbase]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  apply forall_congr'
  intro _
  apply not_congr
  simpa only [Nat.cast_pow] using linear_dvd_congr (A i) (B i) X Y X' Y' hx hy

def representativeSquareProjectionB (h k : History l) (r : Representative h k) :
    ZMod (representativeModulus h k)→+*ZMod ((prime h k r)^2) :=
  ZMod.castHom (Finset.dvd_prod_of_mem (fun r : Representative h k => (prime h k r)^2)
    (Finset.mem_univ r)) _

theorem finiteB_intCast_iff_fiber_good (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (X Y : ℤ) :
    finiteOwnPrimeLinesB h k hs ks (X,Y) ↔ ∀r : Representative h k,
      Good (prime h k r) Finset.univ (actualLeft h k hs ks r) (actualRight h k hs ks r) X Y := by
  rw [← ownPrimeLines_and_squareLines_iff_finiteB]
  constructor
  · rintro ⟨hline,hsquare⟩ r
    constructor
    · intro i _
      have hp : (slot h k i.val).value=prime h k r := by
        rw [← prime_label h k i.val,i.property]
      simpa only [actualLeft,actualRight,hp] using hline i.val
    · intro i _
      have hp : (slot h k i.val).value=prime h k r := by
        rw [← prime_label h k i.val,i.property]
      simpa only [actualLeft,actualRight,hp] using hsquare i.val
  · intro hh
    constructor
    · intro i
      exact (hh (label h k i)).1 ⟨i,rfl⟩ (Finset.mem_univ _)
    · intro i
      exact (hh (label h k i)).2 ⟨i,rfl⟩ (Finset.mem_univ _)

theorem finiteB_iff_projected_fiber_good (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (z : ZMod (representativeModulus h k)×ZMod (representativeModulus h k)) :
    finiteOwnPrimeLinesB h k hs ks z ↔ ∀r : Representative h k,
      Good (prime h k r) Finset.univ (actualLeft h k hs ks r) (actualRight h k hs ks r)
        ((representativeSquareProjectionB h k r z.1).val : ℤ)
        ((representativeSquareProjectionB h k r z.2).val : ℤ) := by
  let : NeZero (representativeModulus h k) := ⟨(representativeModulus_pos h k hs ks).ne'⟩
  have hz : (((z.1.val:ℤ):ZMod (representativeModulus h k)),
      ((z.2.val:ℤ):ZMod (representativeModulus h k)))=z := by
    simp only [Int.cast_natCast,ZMod.natCast_zmod_val]
  rw [← hz,finiteB_intCast_iff_fiber_good]
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

end Ostmann.Arithmetic.HistoryPairSquareProbability

end

end OAI
