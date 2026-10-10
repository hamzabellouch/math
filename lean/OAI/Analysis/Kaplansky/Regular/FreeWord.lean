import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Regular.FreeNormal

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

attribute [local instance] Classical.decEq Classical.propDecidable

lemma toWord_translate (n : ℤ) (v : FZ) :
    (translate n v).toWord = v.toWord.map (fun x => (x.1+n,x.2)) := by
  have hr : FreeGroup.IsReduced (v.toWord.map (fun x => (x.1+n,x.2))) := by
    rw [FreeGroup.IsReduced,List.isChain_map]
    apply List.IsChain.imp (p:=FreeGroup.isReduced_toWord)
    intro x y h hxy
    exact h (add_right_cancel hxy)
  conv_lhs => rw [←FreeGroup.mk_toWord (x:=v)]
  change ((FreeGroup.map (fun i : ℤ => i+n)) (FreeGroup.mk v.toWord)).toWord = _
  rw [FreeGroup.map.mk,FreeGroup.toWord_mk,hr.reduce_eq]

lemma toWord_mul_of_boundary (v w : FZ)
    (hb : ∀ x ∈ v.toWord.getLast?, ∀ y ∈ w.toWord.head?, x.1 ≠ y.1) :
    (v*w).toWord = v.toWord ++ w.toWord := by
  rw [FreeGroup.toWord_mul]
  apply FreeGroup.IsReduced.reduce_eq
  exact List.IsChain.append FreeGroup.isReduced_toWord FreeGroup.isReduced_toWord
    (fun x hx y hy hxy => (hb x hx y hy hxy).elim)

lemma toWord_inv_of (n : ℤ) : (FreeGroup.of n : FZ)⁻¹.toWord = [(n,false)] := by
  simp [FreeGroup.toWord_inv,FreeGroup.toWord_of,FreeGroup.invRev]

def Starts (n : ℤ) (v : FZ) : Prop := ∃ s, Prefix n s v

lemma starts_iff_head (n : ℤ) (v : FZ) : Starts n v ↔ ∃ s, (n,s) ∈ v.toWord.head? := by
  simp only [Starts,Prefix,Option.mem_def,List.head?_eq_some_iff]
lemma not_starts_head {n : ℤ} {v : FZ} (h : ¬ Starts n v) {x : ℤ × Bool}
    (hx : x ∈ v.toWord.head?) : x.1 ≠ n := by
  intro he
  apply h
  apply (starts_iff_head _ _).2
  exact ⟨x.2,by simpa [←he] using hx⟩

lemma starts_translate (n k : ℤ) (v : FZ) :
    Starts (n+k) (translate k v) ↔ Starts n v := by
  rw [starts_iff_head,starts_iff_head,toWord_translate]
  simp only [List.head?_map,Option.mem_map]
  constructor
  · rintro ⟨s,x,hx,he⟩
    have hx1 : x.1=n := add_right_cancel (congrArg Prod.fst he)
    have hx2 : x.2=s := congrArg Prod.snd he
    have hx' : x = (n,s) := Prod.ext hx1 hx2
    exact ⟨s,by simpa [hx'] using hx⟩
  · rintro ⟨s,hs⟩
    exact ⟨s,(n,s),hs,rfl⟩

lemma prefix_multiply_of_not_starts (n : ℤ) (v : FZ) (h : ¬ Starts n v) :
    Prefix n true (FreeGroup.of n*v) :=
  prefix_mul_of_not_negative n v (fun hp => h ⟨false,hp⟩)

lemma word_sandwich (n k : ℤ) (v : FZ)
    (h1 : ∀ x ∈ v.toWord, x.1 ≠ n)
    (h2 : ∀ x ∈ v.toWord, x.1 ≠ n+k)
    (hne : v ≠ 1 ∨ k ≠ 0) :
    (FreeGroup.of n*v*(FreeGroup.of (n+k))⁻¹).toWord =
      [(n,true)] ++ v.toWord ++ [(n+k,false)] := by
  have hleft : (FreeGroup.of n*v).toWord = [(n,true)] ++ v.toWord := by
    rw [toWord_mul_of_boundary,FreeGroup.toWord_of]
    intro x hx y hy
    simp only [FreeGroup.toWord_of,List.getLast?_singleton,Option.mem_some_iff] at hx
    subst x
    exact (h1 y (List.mem_of_mem_head? hy)).symm
  rw [toWord_mul_of_boundary,hleft,toWord_inv_of]
  intro x hx y hy
  simp only [toWord_inv_of,List.head?_cons,Option.mem_some_iff] at hy
  subst y
  rw [hleft,List.getLast?_append] at hx
  by_cases hv : v=1
  · subst v
    simp only [FreeGroup.toWord_one,List.getLast?_nil,Option.none_or,List.getLast?_singleton,
      Option.mem_some_iff] at hx
    subst x
    intro he
    have hk : k=0 := by omega
    exact hne.elim (fun h => h rfl) (fun h => h hk)
  · have ht : v.toWord.getLast? ≠ none := by
      simpa only [ne_eq,List.getLast?_eq_none_iff,FreeGroup.toWord_eq_nil_iff] using hv
    cases hvw : v.toWord.getLast? with
    | none => exact (ht hvw).elim
    | some z =>
      rw [hvw,Option.some_or] at hx
      exact h2 x (List.mem_of_mem_getLast? (by simpa [hvw] using hx))

lemma sandwich_multiply_starts (n k : ℤ) (v w : FZ)
    (h1 : ∀ x ∈ v.toWord, x.1 ≠ n)
    (h2 : ∀ x ∈ v.toWord, x.1 ≠ n+k)
    (hne : v ≠ 1 ∨ k ≠ 0) (hw : ¬ Starts n w) :
    Starts n ((FreeGroup.of n*v*(FreeGroup.of (n+k))⁻¹)*translate k w) := by
  have hs := word_sandwich n k v h1 h2 hne
  have ht : ¬ Starts (n+k) (translate k w) := by rwa [starts_translate]
  have he : ((FreeGroup.of n*v*(FreeGroup.of (n+k))⁻¹)*translate k w).toWord =
      (FreeGroup.of n*v*(FreeGroup.of (n+k))⁻¹).toWord ++ (translate k w).toWord := by
    apply toWord_mul_of_boundary
    intro x hx y hy
    simp only [hs,List.getLast?_append,List.getLast?_singleton,Option.some_or,
      Option.mem_some_iff] at hx
    subst x
    exact (not_starts_head ht hy).symm
  refine ⟨true,?_⟩
  unfold Prefix
  rw [he,hs]
  exact ⟨v.toWord ++ [(n+k,false)] ++ (translate k w).toWord,by simp [List.append_assoc]⟩


end KaplanskyConsequences.Regular

end

end OAI
