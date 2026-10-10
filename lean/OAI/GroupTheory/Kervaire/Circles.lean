import OAI.GroupTheory.Kervaire.VertexJoin

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [DecidableEq D] [Finite D]

def Circle (σ : Perm D) (o : D) (l : List D) : Prop :=
  (o :: (l ++ [o])).IsChain (fun x y ↦ σ x = y)

omit [Finite D] [DecidableEq D] in
lemma chain_mem_next (σ : Perm D) (o x : D) (l : List D)
    (hc : (x :: (l ++ [o])).IsChain (fun x y ↦ σ x = y)) {d : D} (hd : d ∈ x::l) :
    σ d ∈ l ++ [o] := by
  induction l generalizing x with
  | nil =>
    have hd' : d = x := by simpa using hd
    have hh : σ x = o := by simpa using hc
    simp [hd',hh]
  | cons y l ih =>
    have hh := List.isChain_cons_cons.mp hc
    rcases List.mem_cons.mp hd with rfl | hd
    · simp only [hh.1,List.cons_append,List.mem_cons,true_or]
    · exact List.mem_cons_of_mem _ (ih y hh.2 hd)

omit [DecidableEq D] in
lemma circle_cycles (σ : Perm D) (o : D) (l : List D) (hc : Circle σ o l) (d : D) :
    σ.SameCycle o d ↔ d ∈ o::l := by
  have hm : ∀ d ∈ o::l, σ d ∈ o::l := by
    intro d hd
    have hh := chain_mem_next σ o o l hc hd
    simpa [or_comm] using hh
  constructor
  · intro hd
    obtain ⟨n,hn⟩ := hd.exists_nat_pow_eq
    have hi : ∀ n : ℕ, (σ^n) o ∈ o::l := by
      intro n; induction n with
      | zero => exact List.mem_cons_self
      | succ n ih => rw [pow_succ',mul_apply]; exact hm _ ih
    exact hn ▸ hi n
  · intro hd
    let : Trans σ.SameCycle σ.SameCycle σ.SameCycle := ⟨fun h₁ h₂ ↦ h₁.trans h₂⟩
    have hcc : (o :: (l++[o])).IsChain σ.SameCycle :=
      List.IsChain.imp (R := fun x y ↦ σ x = y) (fun x y h ↦ h ▸ SameCycle.rfl.apply_right) hc
    rcases List.mem_cons.mp hd with rfl | hd
    · exact SameCycle.rfl
    · exact hcc.rel_cons (List.mem_append.mpr (Or.inl hd))

omit [DecidableEq D] in
lemma circle_mem_apply (σ : Perm D) (o : D) (l : List D) (hc : Circle σ o l) {d : D}
    (hd : d ∈ o::l) : σ d ∈ o::l :=
  (circle_cycles σ o l hc _).mp (((circle_cycles σ o l hc _).mpr hd).apply_right)

omit [DecidableEq D] in
lemma sameCycle_two (σ : Perm D) {x y z : D} (hx : σ x = y) (hy : σ y = x)
    (hz : σ.SameCycle x z) : z = x ∨ z = y := by
  obtain ⟨n,hn⟩ := hz.exists_nat_pow_eq
  have hi : ∀ n : ℕ, (σ^n) x = x ∨ (σ^n) x = y := by
    intro n; induction n with
    | zero => exact Or.inl rfl
    | succ n ih => rw [pow_succ',mul_apply]; rcases ih with h | h <;> simp only [h,hx,hy,true_or,or_true]
  simpa only [hn] using hi n

omit [Finite D] in
lemma chain_cap (σ : Perm D) (pre post : List D) {d x y : D}
    (hc : (pre ++ d::x::y::post).IsChain (fun x y ↦ σ x = y))
    (hxy : x ≠ y) (hno : ∀ z ∈ pre ++ d::post, z ≠ x ∧ z ≠ y) :
    (pre ++ d::post).IsChain (fun a b ↦ erase (erase σ x) y a = b) := by
  obtain ⟨hpre,hd,hxy',hpost⟩ := by
    simpa only [List.isChain_append_cons_cons,List.isChain_cons_cons] using hc
  apply List.isChain_split.mpr
  constructor
  · apply hpre.imp_of_mem_imp
    intro a b ha hb hab
    have hma : a ∈ pre ++ d::post := by
      simpa only [List.mem_append,List.mem_singleton,List.mem_cons] using
        (List.mem_append.mp ha).imp_right (fun h ↦ Or.inl (List.mem_singleton.mp h))
    have hmb : b ∈ pre ++ d::post := by
      simpa only [List.mem_append,List.mem_singleton,List.mem_cons] using
        (List.mem_append.mp hb).imp_right (fun h ↦ Or.inl (List.mem_singleton.mp h))
    rw [cap_vertex_other σ hxy hxy' (hno a hma).1 (hno a hma).2,hab,ite_eq_right (hno b hmb).1]
  · cases post with
    | nil => exact List.IsChain.singleton _
    | cons z post =>
      obtain ⟨hyz,htail⟩ := List.isChain_cons_cons.mp hpost
      apply List.isChain_cons_cons.mpr
      constructor
      · rw [cap_vertex_other σ hxy hxy' (hno d (by simp)).1 (hno d (by simp)).2,hd,ite_eq_left rfl,hyz]
      · apply htail.imp_of_mem_imp
        intro a b ha hb hab
        have hma : a ∈ pre ++ d::z::post := by simp only [List.mem_append,List.mem_cons]; exact Or.inr (Or.inr (List.mem_cons.mp ha))
        have hmb : b ∈ pre ++ d::z::post := by simp only [List.mem_append,List.mem_cons]; exact Or.inr (Or.inr (List.mem_cons.mp hb))
        rw [cap_vertex_other σ hxy hxy' (hno a hma).1 (hno a hma).2,hab,ite_eq_right (hno b hmb).1]
end
open Monoid Multiplicative
open scoped Classical
variable {D A : Type*} [Group A]
abbrev FreeProd (A : Type*) [Group A] := Coprod A (Multiplicative ℤ)
def dartLetter (t : D → ℤ) (c : D → A) (d : D) : FreeProd A :=
  Coprod.inr (ofAdd (t d)) * Coprod.inl (c d)
def dartEval (t : D → ℤ) (c : D → A) (l : List D) : FreeProd A := (l.map (dartLetter t c)).prod

lemma dartEval_append (t : D → ℤ) (c : D → A) (l r : List D) :
    dartEval t c (l++r) = dartEval t c l * dartEval t c r := by
  simp only [dartEval,List.map_append,List.prod_append]
lemma dartEval_cons (t : D → ℤ) (c : D → A) (d : D) (l : List D) :
    dartEval t c (d::l) = dartLetter t c d * dartEval t c l := rfl

/-- An actual adjacent cancellable unit pair in a coefficient-valued outside
word. Nothing about coefficients being finite or torsion-free is used. -/
lemma dart_pinch (t : D → ℤ) (c : D → A) (l : List D) (hl : l ≠ [])
    (ht : ∀ d ∈ l, t d = 1 ∨ t d = -1) (g : A)
    (he : dartEval t c l = Coprod.inl g) :
    ∃ pre post x y, l = pre ++ x::y::post ∧ c x = 1 ∧ t y = -t x := by
  let U : D → ℤˣ := fun d ↦ if t d = 1 then 1 else -1
  have hU (d) (hd : d ∈ l) : ((U d : ℤˣ) : ℤ) = t d := by
    rcases ht d hd with h | h <;> simp [U,h]
  have hn : ¬ l.IsChain (fun x y ↦ c x = 1 → t x = t y) := by
    intro hc
    let L := l.map (fun d ↦ (U d,c d))
    have hLc : L.IsChain (fun x y : ℤˣ × A ↦ x.2 = 1 → x.1 = y.1) := by
      change (l.map _).IsChain _
      rw [List.isChain_map]
      exact hc.imp (fun x y hh hh' ↦ by simp only [U,hh hh'])
    let w : HNNExtension.NormalWord.ReducedWord A ⊥ ⊥ :=
      ⟨1,L,by simpa only [HNNExtension.toSubgroup,ite_self,Subgroup.mem_bot] using hLc⟩
    have hL : L = [] := by
      apply HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range w
        (φ := MulEquiv.refl (⊥ : Subgroup A))
      refine ⟨g,?_⟩
      let q : FreeProd A →* HNNExtension A ⊥ ⊥ (MulEquiv.refl (⊥ : Subgroup A)) :=
        Coprod.lift HNNExtension.of (zpowersHom _ HNNExtension.t)
      have hh := congrArg q he
      have hmap : (l.map (fun d ↦ HNNExtension.t ^ (U d : ℤ) * HNNExtension.of (c d))) =
          (l.map (fun d ↦ q (dartLetter t c d))) := by
        apply List.map_congr_left
        intro d hd
        simp [q,dartLetter,hU d hd]
      have hh' := hh.symm
      rw [show q (Coprod.inl g) = HNNExtension.of g by simp [q],dartEval,map_list_prod,List.map_map,Function.comp_def,← hmap] at hh'
      simpa [HNNExtension.NormalWord.ReducedWord.prod,w,L,Function.comp_def] using hh'
    exact hl (List.map_eq_nil_iff.mp hL)
  rw [List.isChain_iff_forall_rel_of_append_cons_cons] at hn
  push Not at hn
  obtain ⟨x,y,pre,post,hl',hc,hne⟩ := hn
  have hx : x ∈ l := by rw [hl']; simp
  have hy : y ∈ l := by rw [hl']; simp
  refine ⟨pre,post,x,y,hl',hc,?_⟩
  rcases ht x hx with ha | ha <;> rcases ht y hy with hb | hb <;> omega
end KervaireRibbon

end

end OAI
