import OAI.MathematicalPhysics.Heisenberg.OnsiteSwaps

namespace OAI

section
noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface
open MeshPair
variable {V X : Type} [Fintype V] [Nonempty V]

lemma list_completion (loc : V → X) (L : List (V×V))
    (hL : ∀ e∈L,loc e.1=loc e.2) :
    ∃ (c : ℕ) (u v : ℕ → V),(∀ j,loc (u j)=loc (v j)) ∧
      prefixMatrix (fun j=>SlotColor.matrix (Equiv.swap (u j) (v j))) c=
        SlotColor.matrix ((L.map (fun e=>Equiv.swap e.1 e.2)).prod) := by
  classical
  induction L with
  | nil=>
    refine ⟨0,fun _=>Classical.arbitrary V,fun _=>Classical.arbitrary V,fun _=>rfl,?_⟩
    simp only [prefixMatrix,List.map_nil,List.prod_nil,SlotColor.matrix_one]
  | cons e L ih=>
    obtain ⟨c,u,v,huv,hprod⟩:=ih (fun f hf=>hL f (List.mem_cons_of_mem e hf))
    let u' : ℕ → V:=fun j=>if j=c then e.1 else u j
    let v' : ℕ → V:=fun j=>if j=c then e.2 else v j
    refine ⟨c+1,u',v',?_,?_⟩
    · intro j
      by_cases hj : j=c
      · simpa only [u',v',ite_eq_left hj] using hL e (List.mem_cons_self ..)
      · simpa only [u',v',ite_eq_right hj] using huv j
    · rw [prefixMatrix]
      have hp : prefixMatrix (fun j=>SlotColor.matrix (Equiv.swap (u' j) (v' j))) c=
          prefixMatrix (fun j=>SlotColor.matrix (Equiv.swap (u j) (v j))) c := by
        apply Serial.prefix_congr
        intro j hj
        simp only [u',v',ite_eq_right (show j≠c by omega)]
      rw [hp,hprod]
      simp only [u',v',ite_eq_left rfl,List.map_cons,List.prod_cons,SlotColor.matrix_mul]

theorem completion_factorization (loc : V → X) (π : Equiv.Perm V)
    (hπ : ∀ v,loc (π v)=loc v) :
    ∃ (c : ℕ) (u v : ℕ → V),(∀ j,loc (u j)=loc (v j)) ∧
      prefixMatrix (fun j=>SlotColor.matrix (Equiv.swap (u j) (v j))) c=SlotColor.matrix π := by
  obtain ⟨L,hL,he⟩:=Onsite.swap_factorization loc π hπ
  obtain ⟨c,u,v,h,hp⟩:=list_completion loc L hL
  exact ⟨c,u,v,h,by simpa only [he] using hp⟩

end Heisenberg.Surface
end
end

end OAI
