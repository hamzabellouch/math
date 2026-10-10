import Mathlib
import OAI.Algebra.GroupRing.Path

namespace OAI



section
namespace TorsionFreeZeroDivisors.GraphConePresentation
open PortSubdivision GraphPresentation
open scoped Classical
noncomputable section
variable {V D S : Type} (Γ : PortGraph V D)
/-- Physical unoriented edges, retaining loops and parallel edges. -/
def edgeSetoid : Setoid D where
  r d e := d=e ∨ d=Γ.reverse e
  iseqv := ⟨fun _=>Or.inl rfl, by
    intro d e h
    rcases h with rfl|h
    · exact Or.inl rfl
    · exact Or.inr (by rw [h,Γ.reverse_reverse_apply]), by
    intro d e f h k
    rcases h with rfl|h
    · exact k
    · rcases k with rfl|k
      · exact Or.inr h
      · exact Or.inl (by rw [h,k,Γ.reverse_reverse_apply])⟩
abbrev Edge := Quotient (edgeSetoid Γ)
def edge (d : D) : Edge Γ := Quotient.mk _ d
def representative (e : Edge Γ) : D := e.out
lemma representative_cases (d : D) :
    d=representative Γ (edge Γ d) ∨ d=Γ.reverse (representative Γ (edge Γ d)) :=
  Quotient.exact (Quotient.out_eq (edge Γ d)).symm

variable (letters : D→FreeGroup S) (R : Routes Γ)
/-- Radial edges except for the one edge collapsed at the root of each component. -/
abbrev Generator := S ⊕ {v : V // v≠R.base v}
def old : FreeGroup S →* FreeGroup (Generator (S:=S) Γ R) := FreeGroup.map Sum.inl
def radial (v : V) : FreeGroup (Generator (S:=S) Γ R) :=
  if h : v=R.base v then 1 else FreeGroup.of (Sum.inr ⟨v,h⟩)
def triangle (d : D) : FreeGroup (Generator (S:=S) Γ R) :=
  radial Γ R (Γ.origin d)*old Γ R (letters d)*(radial Γ R (Γ.origin (Γ.reverse d)))⁻¹
/-- There is one two-cell per physical edge, NOT one per directed dart. -/
def attachment (e : Edge Γ) : FreeGroup (Generator (S:=S) Γ R) := triangle Γ letters R (representative Γ e)
def relations : Set (FreeGroup (Generator (S:=S) Γ R)) := Set.range (attachment Γ letters R)
abbrev Group := PresentedGroup (relations Γ letters R)
def radialValue (v : V) : Group Γ letters R := PresentedGroup.mk _ (radial Γ R v)
def oldMap : FreeGroup S →* Group Γ letters R := (PresentedGroup.mk _).comp (old Γ R)
lemma triangle_reverse (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹) (d : D) :
    triangle Γ letters R (Γ.reverse d)=(triangle Γ letters R d)⁻¹ := by
  simp only [triangle,Γ.reverse_reverse_apply,hl,map_inv,mul_inv_rev,inv_inv]
  group
lemma triangle_trivial (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹) (d : D) :
    PresentedGroup.mk (relations Γ letters R) (triangle Γ letters R d)=1 := by
  have h := PresentedGroup.one_of_mem (show attachment Γ letters R (edge Γ d)∈relations Γ letters R from ⟨_,rfl⟩)
  change PresentedGroup.mk _ (triangle Γ letters R (representative Γ (edge Γ d)))=1 at h
  rcases representative_cases Γ d with hd|hd
  · rw [hd]; exact h
  · rw [hd,triangle_reverse Γ letters R hl,map_inv,h,inv_one]
lemma edge_value (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹) (d : D) :
    radialValue Γ letters R (Γ.origin (Γ.reverse d))=
      radialValue Γ letters R (Γ.origin d)*oldMap Γ letters R (letters d) := by
  have h := triangle_trivial Γ letters R hl d
  simp only [triangle,map_mul,map_inv] at h
  exact (mul_inv_eq_one.mp h).symm
lemma path_value (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹)
    {a b : V} (p : Path Γ a b) :
    p.eval (fun d=>oldMap Γ letters R (letters d))=
      (radialValue Γ letters R a)⁻¹*radialValue Γ letters R b := by
  induction p with
  | nil v => simp
  | cons d p ih =>
    rw [Path.eval_cons,ih,edge_value Γ letters R hl]
    group
lemma radial_base (hbase : ∀v,R.base (R.base v)=R.base v) (v : V) :
    radial (S:=S) Γ R (R.base v)=1 := by simp [radial,hbase]
lemma old_word (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹)
    (hbase : ∀v,R.base (R.base v)=R.base v) (v : V) :
    oldMap Γ letters R (word Γ letters R v)=radialValue Γ letters R v := by
  rw [word,←Path.eval_map,path_value Γ letters R hl]
  simp [radialValue,radial_base Γ R hbase]

/-- The original graph-loop group maps to the nonredundant cone group. -/
def fromGraph (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹)
    (hbase : ∀v,R.base (R.base v)=R.base v) :
    GraphPresentation.Group Γ letters R →* Group Γ letters R :=
  PresentedGroup.toGroup (f:=fun s=>oldMap Γ letters R (FreeGroup.of s)) (by
    have hf : FreeGroup.lift (fun s=>oldMap Γ letters R (FreeGroup.of s))=oldMap Γ letters R := by
      ext s; simp
    rintro w ⟨d,rfl⟩
    rw [hf,relator,map_mul,map_mul,map_inv,old_word Γ letters R hl hbase,
      old_word Γ letters R hl hbase,←edge_value Γ letters R hl]
    simp)

lemma graph_value_base (hbase : ∀v,R.base (R.base v)=R.base v) (v : V) :
    value Γ letters R (R.base v)=1 := by
  have h := closed_value Γ letters R (R.base v)
    ((R.path (R.base v)).cast (hbase v) rfl)
  rw [Path.eval_cast] at h
  change (R.path (R.base v)).eval (fun d=>PresentedGroup.mk _ (letters d))=1 at h
  rw [Path.eval_map] at h
  exact h

def toGraphGenerator : Generator (S:=S) Γ R → GraphPresentation.Group Γ letters R
  | .inl s => PresentedGroup.of s
  | .inr v => value Γ letters R v
lemma lift_old : (FreeGroup.lift (toGraphGenerator Γ letters R)).comp (old Γ R)=
    PresentedGroup.mk (GraphPresentation.relations Γ letters R) := by
  ext s
  simp [old,toGraphGenerator,PresentedGroup.of]
lemma lift_radial (hbase : ∀v,R.base (R.base v)=R.base v) (v : V) :
    FreeGroup.lift (toGraphGenerator Γ letters R) (radial Γ R v)=value Γ letters R v := by
  by_cases h : v=R.base v
  · simp only [radial,dite_eq_left h,map_one]
    rw [h,graph_value_base Γ letters R hbase]
  · simp [radial,h,toGraphGenerator]
/-- The precise reverse Tietze map, keeping each new radial generator's value. -/
def toGraph (hbase : ∀v,R.base (R.base v)=R.base v) :
    Group Γ letters R →* GraphPresentation.Group Γ letters R :=
  PresentedGroup.toGroup (f:=toGraphGenerator Γ letters R) (by
    rintro _ ⟨e,rfl⟩
    simp only [attachment,triangle,map_mul,map_inv,lift_radial Γ letters R hbase]
    rw [←MonoidHom.comp_apply,lift_old]
    change value Γ letters R _*letter Γ letters R _*(value Γ letters R _)⁻¹=1
    rw [←GraphPresentation.edge]
    simp)
lemma fromGraph_mk (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹)
    (hbase : ∀v,R.base (R.base v)=R.base v) (w : FreeGroup S) :
    fromGraph Γ letters R hl hbase (PresentedGroup.mk _ w)=oldMap Γ letters R w := by
  have h : (fromGraph Γ letters R hl hbase).comp (PresentedGroup.mk _)=oldMap Γ letters R := by
    ext s
    change fromGraph Γ letters R hl hbase (PresentedGroup.of s)=_
    simp [fromGraph]
  exact DFunLike.congr_fun h w
lemma fromGraph_value (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹)
    (hbase : ∀v,R.base (R.base v)=R.base v) (v : V) :
    fromGraph Γ letters R hl hbase (value Γ letters R v)=radialValue Γ letters R v := by
  rw [value,fromGraph_mk,old_word Γ letters R hl hbase]

def equivalence (hl : ∀ d,letters (Γ.reverse d)=(letters d)⁻¹)
    (hbase : ∀v,R.base (R.base v)=R.base v) :
    GraphPresentation.Group Γ letters R ≃* Group Γ letters R :=
  MonoidHom.toMulEquiv (fromGraph Γ letters R hl hbase) (toGraph Γ letters R hbase) (by
    apply PresentedGroup.ext
    intro s
    change toGraph Γ letters R hbase (oldMap Γ letters R (FreeGroup.of s))=PresentedGroup.of s
    change toGraph Γ letters R hbase (PresentedGroup.of (Sum.inl s))=_
    simp [toGraph,toGraphGenerator]) (by
    apply PresentedGroup.ext
    intro s
    cases s with
    | inl s =>
      simp only [MonoidHom.comp_apply,MonoidHom.id_apply,toGraph,PresentedGroup.toGroup.of,toGraphGenerator]
      change fromGraph Γ letters R hl hbase (PresentedGroup.of s)=PresentedGroup.of (Sum.inl s)
      rw [PresentedGroup.of,fromGraph_mk]
      rfl
    | inr v =>
      simp only [MonoidHom.comp_apply,MonoidHom.id_apply,toGraph,PresentedGroup.toGroup.of,toGraphGenerator]
      change fromGraph Γ letters R hl hbase (value Γ letters R v)=PresentedGroup.of (Sum.inr v)
      rw [fromGraph_value]
      simp [radialValue,radial,v.property,PresentedGroup.of])

lemma canonical_base (v : V) : (routes Γ).base ((routes Γ).base v)=(routes Γ).base v := by
  exact congrArg (fun q : Quot (ShortClosure.simpleGraph Γ).Reachable=>q.out)
    ((ShortClosure.simpleGraph Γ).connectedComponentMk v).out_eq

instance [Finite S] [Finite V] [Finite D] : _root_.Group.IsFinitelyPresented (Group Γ letters R) := by
  have : Finite (relations Γ letters R) := Set.finite_range (attachment Γ letters R) |>.to_subtype
  infer_instance
end
end TorsionFreeZeroDivisors.GraphConePresentation

end


end OAI
