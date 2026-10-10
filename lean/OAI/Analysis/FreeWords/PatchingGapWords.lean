import Mathlib
import OAI.Analysis.FreeWords.PatchingWordFamilies

namespace OAI

noncomputable section

namespace KKLocalPatching.PatchingWord

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKProjectionSupport KKMatrixQuantization

noncomputable section

variable {A : Type*} [Ring A]

def raw (w : PatchingWord A) : List (A × ℤ) := (w.left,w.first)::w.middle

omit [Ring A] in
@[simp] theorem raw_length (w : PatchingWord A) : w.raw.length=w.length := by
  simp only [raw,List.length_cons,length,Nat.add_comm]

theorem value_raw (w : PatchingWord A) (u : ℤ → A) : w.value u=tailValue u w.raw*w.right := rfl

omit [Ring A] in
theorem middle_of_raw_split (w : PatchingWord A) (p g r : List (A × ℤ)) (z y : A × ℤ)
    (he : w.raw=p++z::(g++y::r)) :
    (∀ a∈g, a∈w.middle) ∧ y∈w.middle ∧ g.length+2≤w.length := by
  have hlen := congrArg List.length he
  rw [raw_length] at hlen
  simp only [List.length_append,List.length_cons] at hlen
  have hglen : g.length+2≤w.length := by omega
  refine ⟨?_,?_,hglen⟩
  · cases p with
    | nil =>
      have h := (List.cons.inj he).2
      rw [h]
      intro a ha
      exact List.mem_append_left _ ha
    | cons b p =>
      have h := (List.cons.inj he).2
      rw [h]
      intro a ha
      exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ ha))
  · cases p with
    | nil =>
      have h := (List.cons.inj he).2
      rw [h]
      exact List.mem_append_right _ List.mem_cons_self
    | cons b p =>
      have h := (List.cons.inj he).2
      rw [h]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

theorem gap_and_endpoint_bounds {X : Set (ConcreteAlgebra M)} {K : Set ℤ} {N : ℕ}
    (hX : ∀ x∈X, τ.map x=0) (hK1 : 1∈K) (hKm1 : -1∈K)
    (v : PartialUnitary (ConcreteAlgebra M)) {b : ℝ} (hb : 0≤b)
    (hv : ∀ a, Admissible X K N a → ‖τ.map (a.value v.power)‖≤b)
    {w : PatchingWord (ConcreteAlgebra M)} (hw : Admissible X K N w)
    (p g r : List (ConcreteAlgebra M × ℤ)) (z y : ConcreteAlgebra M × ℤ)
    (he : w.raw=p++z::(g++y::r)) :
    ‖τ.map (tailValue v.power g*y.1)‖≤b ∧
      ‖τ.map (v.support*(tailValue v.power g*y.1))‖≤b := by
  obtain ⟨hg,hy,hlen⟩ := middle_of_raw_split w p g r z y he
  have hgX : ∀ a∈g, a.1∈X ∧ a.2∈K := fun a ha => hw.2.2.2.1 a (hg a ha)
  have hyX := (hw.2.2.2.1 y hy).1
  constructor
  · cases g with
    | nil => simpa only [tailValue_nil,one_mul,hX y.1 hyX,norm_zero] using hb
    | cons a s =>
      let W : PatchingWord (ConcreteAlgebra M) := ⟨a.1,a.2,s,y.1⟩
      have hW : Admissible X K N W := by
        refine ⟨Set.mem_insert_of_mem _ (hgX a List.mem_cons_self).1,
          (hgX a List.mem_cons_self).2,Set.mem_insert_of_mem _ hyX,?_,?_⟩
        · intro d hd
          exact hgX d (List.mem_cons_of_mem _ hd)
        · change 1+s.length≤N
          have hn := hlen.trans hw.2.2.2.2
          simp only [List.length_cons] at hn
          omega
      simpa only [W,value,tailValue_cons] using hv W hW
  · let W : PatchingWord (ConcreteAlgebra M) := ⟨1,1,g++[(y.1,-1)],1⟩
    have hW : Admissible X K N W := by
      refine ⟨Set.mem_insert _ _,hK1,Set.mem_insert _ _,?_,?_⟩
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hgX a ha
        · have he : a=(y.1,-1) := List.mem_singleton.mp ha
          simpa only [he] using And.intro hyX hKm1
      · change 1+(g++[(y.1,-1)]).length≤N
        simp only [List.length_append,List.length_cons,List.length_nil]
        have hn := hlen.trans hw.2.2.2.2
        omega
    have htrace : τ.map (W.value v.power)=τ.map (v.support*(tailValue v.power g*y.1)) := by
      simp only [W,value,tailValue_append,tailValue_cons,tailValue_nil,mul_one,one_mul]
      rw [show v.power 1*(tailValue v.power g*(y.1*v.power (-1)))=
        (v.power 1*(tailValue v.power g*y.1))*v.power (-1) by noncomm_ring]
      rw [τ.tracial,← mul_assoc,← v.add]
      norm_num
      rfl
    simpa only [htrace] using hv W hW

end

end KKLocalPatching.PatchingWord
end

end OAI
