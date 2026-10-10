import OAI.Combinatorics.PolynomialVacuum.Cylinder.HalfArcs

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

theorem columnTotal_sub (q r : Edge M →₀ ℤ) (i : ZMod M) :
    columnTotal (q-r) i=columnTotal q i-columnTotal r i := by
  have he : column (q-r) i 2=column q i 2-column r i 2 := by ext; rfl
  unfold columnTotal
  rw [he,Finsupp.sum_sub_index]; simp

@[simp] theorem columnTotal_neg (q : Edge M →₀ ℤ) (i : ZMod M) : columnTotal (-q) i= -columnTotal q i := by
  have he : column (-q) i 2= -column q i 2 := by ext; rfl
  unfold columnTotal
  rw [he,Finsupp.sum_neg_index] <;> simp

theorem columnTotal_single (e : Edge M) (a : ℤ) (i : ZMod M) :
    columnTotal (Finsupp.single e a) i=if e.1.1=i ∧ e.2=2 then a else 0 := by
  have he : column (Finsupp.single e a) i 2=
      if e.1.1=i ∧ e.2=2 then Finsupp.single e.1.2 a else 0 := by
    rcases e with ⟨⟨x,y⟩,k⟩
    by_cases hx : x=i <;> by_cases hk : k=2 <;> ext j <;>
      simp_all [column_apply,Finsupp.single_apply,Prod.mk.injEq,eq_comm]
  unfold columnTotal
  rw [he]
  split_ifs <;> simp

theorem columnTotal_dart_vertical (g : Germ M) (y : ℤ) (i : ZMod M) :
    columnTotal (dartFlow (mapGerm (translate 0 y) g)) i=columnTotal (dartFlow g) i := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> simp [dartFlow,columnTotal_single,mapGerm,translate,edgeOf,dartSign]

theorem columnTotal_word_vertical (g : Germ M) (w : List Bool) (y : ℤ) (i : ZMod M) :
    columnTotal (wordFlow (mapGerm (translate 0 y) g) w) i=columnTotal (wordFlow g w) i := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
    simp only [wordFlow,columnTotal_add]
    rw [← map_advance _ (translate_neighbor_cyl 0 y),ih]
    congr 1
    have he : ((mapGerm (translate 0 y) g).1,outgoingSlot (mapGerm (translate 0 y) g) b)=
        mapGerm (translate 0 y) (g.1,outgoingSlot g b) := rfl
    rw [he,columnTotal_dart_vertical]

theorem columnTotal_arc_vertical (g : Germ M) (w : List Bool) (y : ℤ) (i : ZMod M) :
    columnTotal (arcFlow (mapGerm (translate 0 y) g) w) i=columnTotal (arcFlow g w) i := by
  simp only [arcFlow,columnTotal_sub,columnTotal_word_vertical,columnTotal_dart_vertical]

variable {H J : ℕ} [NeZero M]

theorem atPort_start_vertical (A : PolynomialVacuumBridge.Corridor.ArchWord.CylinderArch M)
    (hH : A.val.height≤H) (hJ : A.val.height≤J) (p : Bool × ZMod M) :
    (atPort A hJ p).start=mapGerm (translate 0 (if p.1 then (J : ℤ)-H else 0)) (atPort A hH p).start := by
  simp only [atPort_start]
  cases p with
  | mk b i => cases b <;> simp [mapGerm,translate]

theorem atPort_weight (A : PolynomialVacuumBridge.Corridor.ArchWord.CylinderArch M)
    (hH : A.val.height≤H) (hJ : A.val.height≤J) (p : Bool × ZMod M) :
    (atPort A hJ p).weight=(atPort A hH p).weight := by
  simp only [BoundaryArc.weight,BoundaryArc.current,atPort_word]
  rw [atPort_start_vertical A hH hJ p,columnTotal_arc_vertical]

theorem atPort_vertices (A : PolynomialVacuumBridge.Corridor.ArchWord.CylinderArch M)
    (hH : A.val.height≤H) (hJ : A.val.height≤J) (p : Bool × ZMod M) :
    (atPort A hJ p).vertices=(atPort A hH p).vertices.image (translate 0 (if p.1 then (J : ℤ)-H else 0)) := by
  simp only [BoundaryArc.vertices,atPort_word,atPort_start_vertical A hH hJ p,← map_traced _ (translate_neighbor_cyl _ _)]
  ext v
  simp
end PolynomialVacuumCylinder

end OAI
