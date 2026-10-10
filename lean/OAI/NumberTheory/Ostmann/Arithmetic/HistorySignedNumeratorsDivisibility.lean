import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedNumeratorsPair

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedNumerators
open Construction Characters.RationalHistory HistoryOccurrenceVariables HistorySignedDecode
open HistoryPairPattern HistoryPairRows MvPolynomial

theorem actual_divisible {l : ℕ} (h : History l) (Xp Xm : ℤ)
    (hi : (rebuild h Xp Xm).IntegralGuard) (i : InternalKey h) :
    ((internalSlot h i).value:ℤ) ∣ actual h Xp Xm i := by
  induction h generalizing Xp Xm with
  | leaf a => exact isEmptyElim i
  | @node l a p u hp hm left right ihl ihr =>
    have hguard := hi
    simp only [rebuild,SignedHistory.IntegralGuard,rebuild_root] at hguard
    rcases i with i | i
    · have hd : (u.get i).value ∣ (u.map SmallSlot.value).prod :=
        List.dvd_prod (List.mem_map.mpr ⟨u.get i,List.get_mem _ _,rfl⟩)
      have hd' : ((u.get i).value:ℤ) ∣ ((u.map SmallSlot.value).prod:ℤ) := by
        exact_mod_cast hd
      simpa only [actual_node,internalSlot,Sum.elim_inl] using
        dvd_trans (dvd_mul_of_dvd_right hd' a.frequency) hguard.2.1
    · rcases i with i | i
      · exact ihl _ _ hguard.2.2.1 i
      · exact ihr _ _ hguard.2.2.2 i

theorem pairActual_divisible {l : ℕ} (h k : History l) (Xp Xm : ℤ)
    (hi : (rebuild h Xp Xm).IntegralGuard) (ki : (rebuild k Xp Xm).IntegralGuard)
    (i : Occurrences h k) : ((slot h k i).value:ℤ) ∣ pairActual h k Xp Xm i := by
  rcases i with i | i
  · exact actual_divisible h Xp Xm hi i
  · exact actual_divisible k Xp Xm ki i

theorem pairActual_line_zero {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hroot : RootGiantsAgree h k) (Xp Xm : ℤ)
    (hi : (rebuild h Xp Xm).IntegralGuard) (ki : (rebuild k Xp Xm).IntegralGuard)
    (i : Occurrences h k) :
    let p := (slot h k i).value
    (eval (pairSample h k) (leftFlag h k hs ks i):ZMod p)*(Xp:ZMod p)+
      (eval (pairSample h k) (rightFlag h k hs ks i):ZMod p)*(Xm:ZMod p)=0 := by
  dsimp only
  have he := congrArg (fun z : ℤ => (z:ZMod (slot h k i).value))
    (pairActual_integer_linear_cleared h k hs ks hroot Xp Xm hi ki i)
  have hz : (pairActual h k Xp Xm i:ZMod (slot h k i).value)=0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (pairActual_divisible h k Xp Xm hi ki i)
  simp only [Int.cast_mul,Int.cast_add,hz,mul_zero] at he
  exact he.symm

end Ostmann.Arithmetic.HistorySignedNumerators

end

end OAI
