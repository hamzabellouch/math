import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairFlags

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairRepresentativeVariables
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairFlagScope HistoryPairFlags
open HistoryRepeatedRenaming MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def representativeMap (h k : History l) (r : Representative h k) : PairKey h k :=
  ⟨Sum.inr (r.val.1,(r.val.2:ℤ)),by
    obtain ⟨i,rfl⟩ := label_surjective h k r
    rcases i with i | i
    · exact (leftMap h k (Sum.inr (Sum.inr i))).property
    · exact (rightMap h k (Sum.inr (Sum.inr i))).property⟩

@[simp] theorem representativeMap_level (h k : History l) (r : Representative h k) :
    pairLevel h k (representativeMap h k r)=r.val.1 := rfl

@[simp] theorem representativeMap_sample (h k : History l) (r : Representative h k) :
    pairSample h k (representativeMap h k r)=(prime h k r:ℤ) := rfl

theorem representativeMap_injective (h k : History l) : Function.Injective (representativeMap h k) := by
  intro a b hab
  have he : Sum.inr (a.val.1,(a.val.2:ℤ)) = (Sum.inr (b.val.1,(b.val.2:ℤ)) : Bool ⊕ (ℕ × ℤ)) :=
    congrArg Subtype.val hab
  obtain ⟨hlevel,hvalue⟩ := Prod.mk.inj (Sum.inr.inj he)
  apply Subtype.ext
  apply Prod.ext hlevel
  exact_mod_cast hvalue

theorem eval_update_representative (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r s : Representative h k) (hlevel : s.val.1≤r.val.1) (j : Index h k r)
    {R : Type*} [CommRing R] (x : PairKey h k → R) (b : R) :
    eval₂ (Int.castRingHom R) (Function.update x (representativeMap h k s) b) (polynomial h k hs ks r j) =
      eval₂ (Int.castRingHom R) x (polynomial h k hs ks r j) := by
  classical
  apply HistoryPairFlagScope.eval_congr h k r.val.1 _ (polynomial_scope h k hs ks r j)
  intro a _ ha
  apply Function.update_of_ne
  intro he
  subst a
  rw [representativeMap_level] at ha
  omega

theorem divisibility_update_iff (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (j : Index h k r) (x : PairKey h k → ℤ) (b : ℕ) :
    (b:ℤ) ∣ eval (Function.update x (representativeMap h k r) (b:ℤ)) (polynomial h k hs ks r j) ↔
      (b:ℤ) ∣ eval x (polynomial h k hs ks r j) := by
  have he := eval_update_representative h k hs ks r r le_rfl j x (b:ℤ)
  change eval (Function.update x (representativeMap h k r) (b:ℤ)) (polynomial h k hs ks r j) =
    eval x (polynomial h k hs ks r j) at he
  rw [he]

end Ostmann.Arithmetic.HistoryPairRepresentativeVariables

end

end OAI
