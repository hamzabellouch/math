import Mathlib
import OAI.Analysis.FreeWords.PatchingWordFamilies

namespace OAI

noncomputable section

namespace KKLocalPatching.PatchingWord

variable {A : Type*} [Ring A]

def ofMixedHead (k : ℤ) (x : A) : List (ℤ × A) → PatchingWord A
  | [] => ⟨1,k,[],x⟩
  | (l,y)::s => let w := ofMixedHead l y s; ⟨1,k,(x,l)::w.middle,w.right⟩

@[simp] theorem ofMixedHead_left (k : ℤ) (x : A) (s : List (ℤ × A)) :
    (ofMixedHead k x s).left=1 := by cases s <;> rfl

@[simp] theorem ofMixedHead_first (k : ℤ) (x : A) (s : List (ℤ × A)) :
    (ofMixedHead k x s).first=k := by cases s <;> rfl

@[simp] theorem ofMixedHead_length (k : ℤ) (x : A) (s : List (ℤ × A)) :
    (ofMixedHead k x s).length=s.length+1 := by
  induction s generalizing k x with
  | nil => rfl
  | cons z s ih =>
    have h := ih z.1 z.2
    change 1+(ofMixedHead z.1 z.2 s).middle.length=s.length+1 at h
    change 1+((x,z.1)::(ofMixedHead z.1 z.2 s).middle).length=(z::s).length+1
    simp only [List.length_cons]
    omega

theorem ofMixedHead_value (u : ℤ → A) (k : ℤ) (x : A) (s : List (ℤ × A)) :
    (ofMixedHead k x s).value u=(u k*x)*(s.map (fun z => u z.1*z.2)).prod := by
  induction s generalizing k x with
  | nil => simp [ofMixedHead,value]
  | cons z s ih =>
    have h := ih z.1 z.2
    simp only [value,ofMixedHead_left,ofMixedHead_first,one_mul] at h
    simp only [ofMixedHead,value,one_mul,tailValue_cons,List.map_cons,List.prod_cons]
    rw [show u k*(x*u z.1*tailValue u (ofMixedHead z.1 z.2 s).middle)*
      (ofMixedHead z.1 z.2 s).right=
        (u k*x)*(u z.1*tailValue u (ofMixedHead z.1 z.2 s).middle*(ofMixedHead z.1 z.2 s).right) by noncomm_ring,h]

theorem ofMixedHead_admissible {X : Set A} {K : Set ℤ} {N : ℕ}
    (k : ℤ) (x : A) (s : List (ℤ × A))
    (hk : k∈K) (hx : x∈X) (hs : ∀ z∈s, z.1∈K ∧ z.2∈X)
    (hn : s.length+1≤N) : Admissible X K N (ofMixedHead k x s) := by
  induction s generalizing k x with
  | nil => exact ⟨Set.mem_insert _ _,hk,Set.mem_insert_of_mem _ hx,by simp [ofMixedHead],hn⟩
  | cons z s ih =>
    have hz := hs z List.mem_cons_self
    have ht := ih z.1 z.2 hz.1 hz.2 (fun a ha => hs a (List.mem_cons_of_mem _ ha)) (by simp only [List.length_cons] at hn; omega)
    refine ⟨Set.mem_insert _ _,hk,ht.2.2.1,?_,?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨hx,hz.1⟩
      · exact ht.2.2.2.1 a ha
    · simpa only [ofMixedHead_length] using hn

end KKLocalPatching.PatchingWord
end

end OAI
