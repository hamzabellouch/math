import OAI.GroupTheory.Kervaire.Circles

namespace OAI

section
noncomputable section

namespace KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D E B : Type*} [DecidableEq D] [DecidableEq E]

def splice (σ : Perm D) (τ : Perm E) (o : D) (p : E) : Perm (D ⊕ E) :=
  erase (swap (Sum.inl o) (Sum.inr p) * (σ.sumCongr τ)) (Sum.inr p)

lemma splice_inl (σ : Perm D) (τ : Perm E) (o : D) (p : E) (d : D) :
    splice σ τ o p (Sum.inl d) =
      if σ d = o then (if τ p = p then Sum.inl o else Sum.inr (τ p)) else Sum.inl (σ d) := by
  rw [splice,erase_apply _ _ _ (by simp)]
  simp only [mul_apply,Equiv.Perm.sumCongr_apply,Sum.map_inl,Sum.map_inr]
  by_cases hd : σ d = o
  · rw [hd,swap_apply_left,ite_eq_left rfl,ite_eq_left rfl]
    by_cases hp : τ p = p
    · rw [hp,swap_apply_right,ite_eq_left rfl]
    · rw [swap_apply_of_ne_of_ne (by simp) (by simpa using hp),ite_eq_right hp]
  · rw [swap_apply_of_ne_of_ne (by simpa using hd) (by simp),ite_eq_right (by simp),ite_eq_right hd]

lemma splice_inr (σ : Perm D) (τ : Perm E) (o : D) (p d : E) (hd : d ≠ p) :
    splice σ τ o p (Sum.inr d) = if τ d = p then Sum.inl o else Sum.inr (τ d) := by
  rw [splice,erase_apply _ _ _ (by simpa using hd)]
  simp only [mul_apply,Equiv.Perm.sumCongr_apply,Sum.map_inr]
  by_cases hp : τ d = p
  · rw [hp,swap_apply_right,ite_eq_right (by simp),ite_eq_left rfl]
  · rw [swap_apply_of_ne_of_ne (by simp) (by simpa using hp),ite_eq_right (by simpa using hp),ite_eq_right hp]

lemma splice_marker (σ : Perm D) (τ : Perm E) (o : D) (p : E) :
    splice σ τ o p (Sum.inr p) = Sum.inr p := erase_fixed _ _

omit [DecidableEq E] in
lemma chain_redirect (σ : Perm D) (F : B → B) (f : D → B) (o : D) (q : B)
    (x : D) (l : List D) (hc : (x::(l++[o])).IsChain (fun a b ↦ σ a = b))
    (hno : o ∉ l) (hf : ∀ d ∈ x::l, F (f d) = if σ d = o then q else f (σ d)) :
    (f x :: (l.map f ++ [q])).IsChain (fun a b ↦ F a = b) := by
  induction l generalizing x with
  | nil =>
    have hh : σ x = o := by simpa using hc
    simp only [List.map_nil,List.nil_append,List.isChain_cons_cons,List.isChain_singleton,and_true,
      hf x (by simp),hh,ite_true]
  | cons d l ih =>
    obtain ⟨hxd,ht⟩ := List.isChain_cons_cons.mp hc
    have hd : d ≠ o := fun h ↦ hno (by simp [h])
    apply List.isChain_cons_cons.mpr
    constructor
    · rw [hf x (by simp),hxd,ite_eq_right hd]
    · exact ih d ht (fun h ↦ hno (by simp [h])) (fun z hz ↦ hf z (by simp only [List.mem_cons] at hz ⊢; tauto))

lemma circle_splice [Finite D] [Finite E] (σ : Perm D) (τ : Perm E) (o : D) (p : E)
    (l : List D) (m : List E) (hc : Circle σ o l) (hd : Circle τ p m)
    (hno : o ∉ l) (hnp : p ∉ m) :
    Circle (splice σ τ o p) (Sum.inl o) (l.map Sum.inl ++ m.map Sum.inr) := by
  have hl := chain_redirect σ (splice σ τ o p) Sum.inl o
    (if τ p = p then Sum.inl o else Sum.inr (τ p)) o l hc hno
    (fun d _ ↦ splice_inl σ τ o p d)
  cases m with
  | nil =>
    have hp : τ p = p := by simpa only [Circle,List.nil_append,List.isChain_cons_cons,List.isChain_singleton,and_true] using hd
    simpa only [Circle,List.map_nil,List.append_nil,hp,ite_true] using hl
  | cons d m =>
    have hpd : τ p = d := (List.isChain_cons_cons.mp hd).1
    have hdm := (List.isChain_cons_cons.mp hd).2
    have hdp : d ≠ p := fun h ↦ hnp (by simp [h])
    have hl' : (Sum.inl o :: (l.map Sum.inl ++ [Sum.inr d])).IsChain (fun a b ↦ splice σ τ o p a = b) := by
      simpa only [hpd,ite_eq_right hdp] using hl
    have hm := chain_redirect τ (splice σ τ o p) Sum.inr p (Sum.inl o) d m hdm
      (fun h ↦ hnp (by simp [h])) (fun z hz ↦ splice_inr σ τ o p z (fun h ↦ hnp (h ▸ hz)))
    change (Sum.inl o :: ((l.map Sum.inl ++ Sum.inr d :: m.map Sum.inr) ++ [Sum.inl o])).IsChain _
    have hx : ((Sum.inl o :: l.map Sum.inl) ++ Sum.inr d :: (m.map Sum.inr ++ [Sum.inl o])).IsChain
        (fun a b ↦ splice σ τ o p a = b) :=
      List.isChain_split.mpr ⟨by simpa only [List.cons_append] using hl',hm⟩
    simpa only [List.cons_append,List.append_assoc] using hx

lemma planar_splice [Fintype D] [Fintype E] (σ θ : Perm D) (τ η : Perm E)
    (o : D) (p : E) (h₁ : planar σ θ) (h₂ : planar τ η) :
    planar (splice σ τ o p) (θ.sumCongr η) := by
  have hc : ¬ components (σ.sumCongr τ) (θ.sumCongr η) (Sum.inl o) (Sum.inr p) := by
    rw [components_sumPerm]
    change ¬ Sum.inl (Quotient.mk (components σ θ) o) = Sum.inr (Quotient.mk (components τ η) p)
    simp
  have hp := planar_vertex_join (σ.sumCongr τ) (θ.sumCongr η) hc (planar_sumPerm σ θ τ η h₁ h₂)
  let μ := swap (Sum.inl o) (Sum.inr p) * (σ.sumCongr τ)
  by_cases he : μ (Sum.inr p) = Sum.inr p
  · have hh : erase μ (Sum.inr p) = μ := by ext d; simp [erase,he]
    change planar (erase μ (Sum.inr p)) _
    rw [hh]
    exact hp
  · exact planar_vertex_split μ (θ.sumCongr η) (Ne.symm he) SameCycle.rfl.apply_right hp
end KervaireRibbon

end
end

section
namespace KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma planar_vertex_join_face (σ θ : Perm D) {x y : D}
    (hv : ¬ σ.SameCycle x y) (hf : (σ*θ).SameCycle x y) (hp : planar σ θ) :
    planar (swap x y*σ) θ := by
  have hne : x ≠ y := fun h ↦ hv (h ▸ SameCycle.rfl)
  have hn := numCycles_swap_merge σ hv
  have hm := numCycles_swap_split (σ*θ) hne hf
  have hc : components (swap x y*σ) θ x y :=
    (le_sup_left : SameCycle.setoid (swap x y*σ) ≤ components (swap x y*σ) θ) (sameCycle_swap_merges σ hv)
  have hd : components σ θ x y := cycles_mul_le σ θ _ le_sup_left le_sup_right hf
  have hr := components_swap_sup σ θ x y
  rw [joinPair_eq _ hc,joinPair_eq _ hd] at hr
  unfold planar at hp ⊢
  rw [hr,mul_assoc]
  omega

omit [DecidableEq D] in
lemma planar_one_left (θ : Perm D) : planar 1 θ := by
  have h := planar_one_right θ
  unfold planar components at h ⊢
  simpa only [one_mul,mul_one,sup_comm,Nat.add_comm (numCycles (1:Perm D))] using h

def whisker (σ : Perm D) (o : D) : Perm (D ⊕ Bool) :=
  swap (Sum.inl o) (Sum.inr true) *
    (swap (Sum.inl (σ o)) (Sum.inr false) * (σ.sumCongr 1))

omit [Fintype D] in
lemma whisker_o (σ : Perm D) (o : D) : whisker σ o (Sum.inl o) = Sum.inr false := by
  simp [whisker,swap_apply_def]
omit [Fintype D] in
lemma whisker_y (σ : Perm D) (o : D) : whisker σ o (Sum.inr true) = Sum.inl o := by
  simp [whisker,swap_apply_def]
omit [Fintype D] in
lemma whisker_x (σ : Perm D) (o : D) : whisker σ o (Sum.inr false) =
    if σ o = o then Sum.inr true else Sum.inl (σ o) := by
  simp only [whisker,mul_apply,Equiv.Perm.sumCongr_apply,Sum.map_inr,one_apply,swap_apply_right]
  by_cases he : σ o = o
  · simp only [he,ite_true,swap_apply_left]
  · rw [swap_apply_of_ne_of_ne (by simpa using he) (by simp),ite_eq_right he]
omit [Fintype D] in
lemma whisker_inl (σ : Perm D) (o d : D) (hd : d ≠ o) : whisker σ o (Sum.inl d) =
    if σ d = o then Sum.inr true else Sum.inl (σ d) := by
  simp only [whisker,mul_apply,Equiv.Perm.sumCongr_apply,Sum.map_inl]
  rw [swap_apply_of_ne_of_ne (fun h ↦ hd (σ.injective (Sum.inl.inj h))) (by simp)]
  by_cases he : σ d = o
  · simp only [he,ite_true,swap_apply_left]
  · rw [swap_apply_of_ne_of_ne (by simpa using he) (by simp),ite_eq_right he]

lemma planar_whisker (σ θ : Perm D) (o : D) (ho : θ o = o) (hp : planar σ θ) :
    planar (whisker σ o) (θ.sumCongr (swap false true)) := by
  let τ := σ.sumCongr (1 : Perm Bool)
  let η := θ.sumCongr (swap false true)
  let α := swap (Sum.inl (σ o)) (Sum.inr false) * τ
  have hc : ¬ components τ η (Sum.inl (σ o)) (Sum.inr false) := by
    rw [components_sumPerm]
    change ¬ Sum.inl _ = Sum.inr _
    simp
  have hα := planar_vertex_join τ η hc (planar_sumPerm σ θ 1 (swap false true) hp (planar_one_left _))
  have hy : α (Sum.inr true) = Sum.inr true := by simp [α,τ,swap_apply_def]
  have hv : ¬ α.SameCycle (Sum.inl o) (Sum.inr true) := fun h ↦ Sum.inl_ne_inr (h.eq_of_right hy)
  have hf : (α*η).SameCycle (Sum.inl o) (Sum.inr true) := by
    have he : ((α*η)^2) (Sum.inl o) = Sum.inr true := by
      simp [pow_two,α,τ,η,ho,swap_apply_def]
    exact ⟨(2:ℤ),by simpa only [zpow_ofNat] using he⟩
  exact planar_vertex_join_face α η hv hf hα

omit [Fintype D] in
lemma circle_whisker (σ : Perm D) (o : D) (l : List D) (hc : Circle σ o l) (hn : o ∉ l) :
    Circle (whisker σ o) (Sum.inl o) (Sum.inr false :: l.map Sum.inl ++ [Sum.inr true]) := by
  cases l with
  | nil =>
    have he : σ o = o := by simpa only [Circle,List.nil_append,List.isChain_cons_cons,List.isChain_singleton,and_true] using hc
    simp only [Circle,List.map_nil,List.cons_append,List.nil_append,List.isChain_cons_cons,
      List.isChain_singleton,and_true,whisker_o,whisker_x,he,ite_true,whisker_y]
  | cons d l =>
    have hod : σ o = d := (List.isChain_cons_cons.mp hc).1
    have hdl := (List.isChain_cons_cons.mp hc).2
    have hdo : d ≠ o := fun he ↦ hn (by simp [he])
    have hh := chain_redirect σ (whisker σ o) Sum.inl o (Sum.inr true) d l hdl
      (fun h ↦ hn (by simp [h])) (fun z hz ↦ whisker_inl σ o z (fun he ↦ hn (he ▸ hz)))
    change (Sum.inl o :: Sum.inr false :: ((Sum.inl d :: l.map Sum.inl) ++ [Sum.inr true] ++ [Sum.inl o])).IsChain _
    apply List.isChain_cons_cons.mpr
    refine ⟨whisker_o _ _,?_⟩
    apply List.isChain_cons_cons.mpr
    refine ⟨?_,?_⟩
    · rw [whisker_x,hod,ite_eq_right hdo]
    · have hb : (Sum.inr true :: [Sum.inl o]).IsChain (fun x y ↦ whisker σ o x = y) := by
        simpa only [List.isChain_cons_cons,List.isChain_singleton,and_true] using whisker_y σ o
      have hg : ((Sum.inl d :: l.map Sum.inl) ++ Sum.inr true :: [Sum.inl o]).IsChain
          (fun x y ↦ whisker σ o x = y) :=
        List.isChain_split.mpr ⟨by simpa only [List.cons_append] using hh,hb⟩
      simpa only [List.append_eq,List.cons_append,List.append_assoc,List.singleton_append,List.nil_append] using hg

end KervaireRibbon

end

end OAI
