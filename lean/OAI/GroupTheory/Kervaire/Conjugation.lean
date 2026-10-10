import OAI.GroupTheory.Kervaire.RibbonProducts

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

def OuterRibbon.conjLetter {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) (n : ℤ) (hn : n=1 ∨ n = -1) :
    OuterRibbon (V := V) ρ a s (Sum.inl o) (Sum.inr false :: l.map Sum.inl ++ [Sum.inr true]) := by
  let σ := whisker r.σ o
  let θ := r.θ.sumCongr (swap false true)
  let t : D ⊕ Bool → ℤ := Sum.elim r.t (fun b ↦ if b then -n else n)
  let u : D ⊕ Bool → A := Sum.elim r.u (fun _ ↦ r.u o)
  have hd (vi : V × I) : r.atlas.disk vi ≠ o := fun he ↦ r.disjoint vi (by simp [he])
  have hs (v : V) (i : I) : r.σ (r.atlas.disk (v,i)) ≠ o := by rw [r.atlas.next]; exact hd _
  let b : DiskAtlas (V := V) ρ a s σ t := {
    disk := r.atlas.disk.trans ⟨Sum.inl,Sum.inl_injective⟩
    ε := r.atlas.ε
    polarity := r.atlas.polarity
    next := by intro v i; change whisker r.σ o (Sum.inl (r.atlas.disk (v,i))) = _
               rw [whisker_inl _ _ _ (hd _),ite_eq_right (hs _ _)]; exact congrArg Sum.inl (r.atlas.next v i)
    sign := r.atlas.sign }
  refine {
    σ := σ, θ := θ, t := t, u := u, atlas := b
    involutive := ?_, planar' := planar_whisker _ _ _ r.marker r.planar'
    opposite := ?_, marker := congrArg Sum.inl r.marker, marker_sign := r.marker_sign
    circle := circle_whisker _ _ _ r.circle (List.nodup_cons.mp r.nodup).1
    nodup := ?_, unit := ?_, disjoint := ?_, cover := ?_, corners := ?_ }
  · rintro (d|d)
    · exact congrArg Sum.inl (r.involutive d)
    · simp only [θ,Equiv.Perm.sumCongr_apply,Sum.map_inr,swap_apply_self]
  · rintro (d|d)
    · exact r.opposite d
    · cases d <;> simp [θ,t]
  · have hl : (l.map (Sum.inl : D → D ⊕ Bool) ++ [Sum.inr true]).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨r.nodup.of_cons.map Sum.inl_injective,by simp,?_⟩
      intro d hd e he hde
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hd
      have he' : e = Sum.inr true := List.mem_singleton.mp he
      exact Sum.inl_ne_inr (hde.trans he')
    apply List.nodup_cons.mpr
    constructor
    · simpa only [List.mem_cons,List.mem_append,List.mem_map,List.mem_singleton,
        Sum.inl_ne_inr,List.not_mem_nil,or_false,false_or,Sum.inl.injEq,exists_eq_right] using
        (List.nodup_cons.mp r.nodup).1
    · apply List.nodup_cons.mpr
      exact ⟨by simp [List.mem_map],hl⟩
  · intro d hd'
    simp only [List.cons_append,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hd'
    rcases hd' with rfl | hd' | rfl
    · exact hn
    · obtain ⟨d,hmem,rfl⟩ := List.mem_map.mp hd'
      exact r.unit d hmem
    · rcases hn with h|h <;> simp [t,h]
  · intro vi he
    have hh : r.atlas.disk vi ∈ o::l := by simpa [b,List.mem_map] using he
    exact r.disjoint vi hh
  · rintro (d|d)
    · obtain ⟨vi,hi⟩ | hi | ⟨hs',hθ⟩ := r.cover d
      · exact Or.inl ⟨vi,congrArg Sum.inl hi⟩
      · exact Or.inr (Or.inl (by simpa [List.mem_map] using hi))
      · by_cases he : d=o
        · subst d; exact Or.inr (Or.inl (by simp))
        · refine Or.inr (Or.inr ⟨?_,congrArg Sum.inl hθ⟩)
          change whisker r.σ o (Sum.inl d) = Sum.inl d
          rw [whisker_inl _ _ _ he,hs',ite_eq_right he]
    · cases d <;> exact Or.inr (Or.inl (by simp))
  · intro v i
    rw [r.corners]
    change corner r.σ r.θ r.u (r.atlas.disk (v,i)) = corner σ θ u (Sum.inl (r.atlas.disk (v,i)))
    simp only [corner,σ,whisker_inl _ _ _ (hd _),hs,ite_false,θ,Equiv.Perm.sumCongr_apply,Sum.map_inl,u,Sum.elim_inl]

omit [Fintype V] [Fintype I] in
lemma OuterRibbon.value_conjLetter {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) (n : ℤ) (hn : n=1 ∨ n = -1) :
    (r.conjLetter n hn).value = Coprod.inr (ofAdd n)*r.value*(Coprod.inr (ofAdd n))⁻¹ := by
  rw [OuterRibbon.value_formula,OuterRibbon.value_formula]
  change Coprod.inl (r.u o) *
    transportEval (r.θ.sumCongr (swap false true)) (Sum.elim r.t (fun b ↦ if b then -n else n))
      (Sum.elim r.u (fun _ ↦ r.u o)) (Sum.inr false :: l.map Sum.inl ++ [Sum.inr true]) *
    (Coprod.inl (r.u o))⁻¹ = _
  have he := transportEval_map_gauge r.θ (r.θ.sumCongr (swap false true)) r.t
    (Sum.elim r.t (fun b ↦ if b then -n else n)) r.u (Sum.elim r.u (fun _ ↦ r.u o))
    Sum.inl 1 (fun _ ↦ rfl) (fun _ ↦ rfl) (fun d ↦ (mul_one _).symm) l
  simp only [map_one,inv_one,one_mul,mul_one] at he
  rw [show Sum.inr false :: l.map Sum.inl ++ [Sum.inr true] =
      [Sum.inr false] ++ l.map Sum.inl ++ [Sum.inr true] from rfl,
    transportEval_append,transportEval_append,he]
  simp only [transportEval,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
    transportLetter,Equiv.Perm.sumCongr_apply,Sum.map_inr,swap_apply_left,swap_apply_right,
    Sum.elim_inr,Bool.false_eq_true,ite_false,ite_true,ofAdd_neg,map_inv]
  group
end

open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

omit [Fintype V] [Fintype I] [DecidableEq D] in
lemma OuterRibbon.theta_ne_marker {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) {d : D} (hd : d ≠ o) : r.θ d ≠ o :=
  fun he ↦ hd (r.θ.injective (he.trans r.marker.symm))

def OuterRibbon.conjCoefficient {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) (g : A) : OuterRibbon (V := V) ρ a s o l := by
  refine { r with u := Function.update r.u o (g*r.u o), corners := ?_ }
  intro v i
  have hn (vi : V × I) : r.atlas.disk vi ≠ o := fun he ↦ r.disjoint vi (by simp [he])
  have hs : r.σ (r.atlas.disk (v,i)) ≠ o := by rw [r.atlas.next]; exact hn _
  rw [r.corners]
  simp only [corner,Function.update_of_ne (r.theta_ne_marker (hn _)),Function.update_of_ne hs]

omit [Fintype V] [Fintype I] in
lemma OuterRibbon.value_conjCoefficient {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) (g : A) :
    (r.conjCoefficient g).value = Coprod.inl g*r.value*(Coprod.inl g)⁻¹ := by
  have ht : transportEval r.θ r.t (Function.update r.u o (g*r.u o)) l = transportEval r.θ r.t r.u l := by
    apply congrArg List.prod
    apply List.map_congr_left
    intro d hd
    have hn : d ≠ o := fun he ↦ (List.nodup_cons.mp r.nodup).1 (he ▸ hd)
    simp only [transportLetter,Function.update_of_ne hn,Function.update_of_ne (r.theta_ne_marker hn)]
  rw [OuterRibbon.value_formula,OuterRibbon.value_formula]
  change Coprod.inl (Function.update r.u o (g*r.u o) o) *
    transportEval r.θ r.t (Function.update r.u o (g*r.u o)) l *
    (Coprod.inl (Function.update r.u o (g*r.u o) o))⁻¹ = _
  rw [Function.update_self,ht,map_mul]
  group
end KervaireRibbon

end

end OAI
