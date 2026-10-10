import OAI.Combinatorics.PolynomialVacuum.Cylinder.BoundaryDecomposition
import OAI.Combinatorics.PolynomialVacuum.Cylinder.IceCurrent

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

@[simp] theorem turnVisit_append (g : Germ M) (u w : List Bool) :
    turnVisit g (u++w)=turnVisit g u+turnVisit (terminalGerm g u) w := by
  induction u generalizing g with
  | nil => simp [turnVisit,terminalGerm]
  | cons b u ih => simp [turnVisit,terminalGerm,ih,add_assoc]

theorem simple_turnVisit_split (g : Germ M) (u : List Bool) (b : Bool) (w : List Bool)
    (hN : (traced g (u++b::w)).Nodup) (k : Fin 3) :
    turnVisit g (u++b::w) ((terminalGerm g u).1,k)=
      (if k=outgoingSlot (terminalGerm g u) b then 1 else 0)-
      (if k=(terminalGerm g u).2 then 1 else 0) := by
  rw [traced_append] at hN
  have hu : (terminalGerm g u).1∉traced g u := by
    intro hh
    exact (List.nodup_append.mp hN).2.2 _ hh _ (by simp [traced]) rfl
  have hw : (terminalGerm g u).1∉traced (advance (terminalGerm g u) b) w :=
    (List.nodup_cons.mp (List.nodup_append.mp hN).2.1).1
  rw [turnVisit_append,Finsupp.add_apply,turnVisit_eq_zero_of_not_mem _ _ _ _ hu,zero_add]
  simp [turnVisit,turnVisit_eq_zero_of_not_mem _ _ _ _ hw,Finsupp.single_apply,Prod.ext_iff,eq_comm]

namespace BoundaryArc
variable {D : Finset (Vertex M)} (A : BoundaryArc D)

theorem vertices_subset : A.vertices⊆D := fun v hv => A.inside v (List.mem_toFinset.mp hv)

theorem current_on_domain (v : Vertex M) (hv : v∈D) (k : Fin 3) :
    orientedFlow A.current (v,k)=turnVisit A.start A.word (v,k) := by
  have hs : reverseGerm A.start≠(v,k) := by
    intro he
    exact A.startOutside ((congrArg Prod.fst he).symm ▸ hv)
  have ht : terminalGerm A.start A.word≠(v,k) := by
    intro he
    exact A.endOutside ((congrArg Prod.fst he).symm ▸ hv)
  simp [current,orientedFlow_arc,hs,ht]

theorem contour : WordContour A.current A.start A.word := by
  apply wordContour_of_splits
  intro u b w he
  have hm : (terminalGerm A.start u).1∈traced A.start A.word := by
    rw [he,traced_append]
    simp [traced]
  intro k
  rw [A.current_on_domain _ (A.inside _ hm),he]
  exact simple_turnVisit_split A.start u b w (he ▸ A.distinct) k

theorem current_zero (v : Vertex M) (hv : v∈D) (ha : v∉A.vertices) (k : Fin 3) :
    orientedFlow A.current (v,k)=0 := by
  rw [A.current_on_domain v hv k]
  exact turnVisit_eq_zero_of_not_mem _ _ _ _ (by simpa [vertices] using ha)

theorem local_ice (v : Vertex M) (hv : v∈D) : LocalIce A.current v := by
  by_cases hA : v∈A.vertices
  · exact wordContour_localIce _ _ _ A.contour v (List.mem_toFinset.mp hA)
  · exact Or.inl (A.current_zero v hv hA)

theorem supported : SupportedAt D A.current := by
  intro g hg hr
  have hs : reverseGerm A.start≠g := by
    intro hh
    apply hr
    rw [← hh,reverseGerm_reverseGerm]
    exact A.startInside
  have ht : terminalGerm A.start A.word≠g := by
    intro hh
    exact hr (hh ▸ A.endInside)
  have hz : turnVisit A.start A.word g=0 := turnVisit_eq_zero_of_not_mem _ _ _ _
    (fun hv => hg (A.inside _ hv))
  simpa [current,orientedFlow_arc,Finsupp.single_apply,hs,ht] using hz
end BoundaryArc

 

theorem localContour_turn_unique (q : Edge M →₀ ℤ) (g : Germ M) (a b : Bool)
    (ha : LocalContour q g a) (hb : LocalContour q g b) : a=b := by
  have he : (if outgoingSlot g a=outgoingSlot g b then (1 : ℤ) else 0)=1 := by
    have h:= (ha (outgoingSlot g a)).symm.trans (hb (outgoingSlot g a))
    simp only [ite_true,outgoingSlot_ne,ite_false,sub_zero] at h
    exact h.symm
  have hh : outgoingSlot g a=outgoingSlot g b := by split_ifs at he <;> omega
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases a <;> cases b <;> simp_all [outgoingSlot,Fin.ext_iff]

 

theorem contour_open_word_unique (D : Finset (Vertex M)) (q : Edge M →₀ ℤ)
    (g : Germ M) (w u : List Bool)
    (hw : WordContour q g w) (hu : WordContour q g u)
    (iw : ∀v∈traced g w,v∈D) (iu : ∀v∈traced g u,v∈D)
    (ew : (terminalGerm g w).1∉D) (eu : (terminalGerm g u).1∉D) : w=u := by
  induction w generalizing g u with
  | nil =>
    cases u with
    | nil => rfl
    | cons b u => exact False.elim (ew (iu g.1 (by simp [traced])))
  | cons a w ih =>
    cases u with
    | nil => exact False.elim (eu (iw g.1 (by simp [traced])))
    | cons b u =>
      have hab:=localContour_turn_unique q g a b hw.1 hu.1
      subst b
      congr 1
      exact ih (advance g a) u hw.2 hu.2
        (fun v hv => iw v (by simp [traced,hv]))
        (fun v hv => iu v (by simp [traced,hv])) ew eu

end PolynomialVacuumCylinder

end OAI
