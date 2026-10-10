import OAI.Combinatorics.ContingencyTables.Transport.RationalMapProducts

namespace OAI

/-! # Reserving a common word length for adaptive bounded draws -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture FairBits

noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]

lemma mapLaw_product_fst (p : RationalLaw A) (q : RationalLaw B) :
    mapLaw (productLaw p q) Prod.fst=p := by
  apply RationalLaw.ext
  funext x
  simp only [mapLaw, productLaw, Fintype.sum_prod_type]
  change (∑ a,∑ b,if a=x then p.mass a*q.mass b else 0)=p.mass x
  have hs (a : A) : (∑ b,if a=x then p.mass a*q.mass b else 0)=if a=x then p.mass a else 0 := by
    by_cases ha : a=x
    · simp only [ha,ite_true,←Finset.mul_sum,q.total,mul_one]
    · simp only [ha,ite_false,Finset.sum_const_zero]
  simp_rw [hs]
  simp

def prefixWord {k N : ℕ} (hk : k ≤ N) (bits : Fin N → Bool) : Fin k → Bool :=
  fun i => bits (Fin.castLE hk i)

def paddingWordEquiv {k N : ℕ} (hk : k ≤ N) :
    (Fin N → Bool) ≃ ((Fin k → Bool) × (Fin (N-k) → Bool)) :=
  (Equiv.arrowCongr (finCongr (Nat.add_sub_of_le hk)).symm (Equiv.refl Bool)).trans
    (splitWordEquiv k (N-k))

lemma paddingWordEquiv_fst {k N : ℕ} (hk : k ≤ N) (bits : Fin N → Bool) :
    (paddingWordEquiv hk bits).1=prefixWord hk bits := by
  funext i
  change bits _=bits _
  apply congrArg bits
  apply Fin.ext
  rfl

/-- Taking the needed prefix of a larger uniform word preserves the exact
law, so unused bits can be reserved even after the current state is known. -/
theorem prefixWord_uniform {k N : ℕ} (hk : k ≤ N) :
    mapLaw (uniformLaw (α := Fin N → Bool)) (prefixWord hk)=uniformLaw (α := Fin k → Bool) := by
  have hf : prefixWord hk=fun bits => (paddingWordEquiv hk bits).1 := by
    funext bits
    exact (paddingWordEquiv_fst hk bits).symm
  rw [hf,←map_equiv (paddingWordEquiv hk),uniform_equiv,←uniform_product,mapLaw_product_fst]

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- An arbitrary finite draw keeps its law when padded to the common
bound; this applies separately at every state of an adaptive walk. -/
theorem padded_draw_law {k N : ℕ} (hk : k ≤ N) (draw : (Fin k → Bool) → Y) :
    mapLaw (uniformLaw (α := Fin N → Bool)) (fun bits => draw (prefixWord hk bits))=
      mapLaw (uniformLaw (α := Fin k → Bool)) draw := by
  rw [←mapLaw_comp,prefixWord_uniform]

end
end ContingencyTables.FirstSuccess

end OAI
