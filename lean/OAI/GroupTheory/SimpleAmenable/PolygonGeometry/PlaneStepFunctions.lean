import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FiniteArrangementGerms

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PlaneStepFunctions

def GenericPlane (a : ℕ) := {p : ℝ × ℝ // AvoidsCuts a p}

namespace GenericPlane
noncomputable def shift {a : ℕ} (u : CutRing × CutRing) (p : GenericPlane a) :
    GenericPlane a := ⟨p.val+(ordinary u.1,ordinary u.2),avoidsCuts_translate p.property u⟩
@[simp] theorem shift_zero {a : ℕ} (p : GenericPlane a) : shift 0 p=p := by
  apply Subtype.ext
  simp [shift]
@[simp] theorem shift_add {a : ℕ} (u v : CutRing × CutRing) (p : GenericPlane a) :
    shift u (shift v p)=shift (u+v) p := by
  apply Subtype.ext
  simp only [shift,Prod.fst_add,Prod.snd_add,map_add]
  ext <;> simp only [Prod.fst_add,Prod.snd_add] <;> ring
end GenericPlane

abbrev PlaneCut := Fin 4 × CutRing

noncomputable def planeSign {a : ℕ} (l : PlaneCut) (p : GenericPlane a) : Bool :=
  decide (cutForm a l.1 p.val < ordinary l.2)

def HasPlaneArrangement {a : ℕ} (f : GenericPlane a → ℤ) : Prop :=
  ∃ S : Finset PlaneCut, ∀ p q, (∀ l∈S, planeSign l p=planeSign l q) → f p=f q

def PlaneCompactSupport {a : ℕ} (f : GenericPlane a → ℤ) : Prop :=
  ∃ R : ℝ, ∀ p, R < |p.val.1| ∨ R < |p.val.2| → f p=0

noncomputable def planeStepSubmodule (a : ℕ) : Submodule ℤ (GenericPlane a → ℤ) where
  carrier := {f | HasPlaneArrangement f ∧ PlaneCompactSupport f}
  zero_mem' := by
    refine ⟨⟨∅,fun _ _ _ => rfl⟩,⟨0,fun _ _ => rfl⟩⟩
  add_mem' := by
    classical
    rintro f g ⟨⟨S,hS⟩,⟨R,hR⟩⟩ ⟨⟨T,hT⟩,⟨Q,hQ⟩⟩
    constructor
    · refine ⟨S∪T,fun p q hpq => ?_⟩
      exact congrArg₂ (·+·) (hS p q (fun l hl => hpq l (Finset.mem_union_left T hl)))
        (hT p q (fun l hl => hpq l (Finset.mem_union_right S hl)))
    · refine ⟨max R Q,fun p hp => ?_⟩
      have h₁ : R < |p.val.1| ∨ R < |p.val.2| := hp.imp
        (lt_of_le_of_lt (le_max_left _ _)) (lt_of_le_of_lt (le_max_left _ _))
      have h₂ : Q < |p.val.1| ∨ Q < |p.val.2| := hp.imp
        (lt_of_le_of_lt (le_max_right _ _)) (lt_of_le_of_lt (le_max_right _ _))
      change f p+g p=0
      rw [hR p h₁,hQ p h₂,add_zero]
  smul_mem' := by
    rintro c f ⟨⟨S,hS⟩,⟨R,hR⟩⟩
    refine ⟨⟨S,fun p q hpq => congrArg (c • ·) (hS p q hpq)⟩,⟨R,fun p hp => ?_⟩⟩
    change c • f p=0
    rw [hR p hp,smul_zero]

noncomputable abbrev PlaneStep (a : ℕ) : Type := ↥(planeStepSubmodule a)

namespace PlaneStep
variable {a : ℕ}

theorem hasArrangement (f : PlaneStep a) : HasPlaneArrangement f.val := f.property.1
theorem compactSupport (f : PlaneStep a) : PlaneCompactSupport f.val := f.property.2

@[simp] theorem translated_sign (l : PlaneCut) (u : CutRing × CutRing)
    (p : GenericPlane a) : planeSign l (GenericPlane.shift (-u) p)=
      planeSign (l.1,l.2+integralCutForm a l.1 u) p := by
  unfold planeSign
  apply decide_eq_decide.mpr
  have he : integralCutForm a l.1 (-u) = -integralCutForm a l.1 u := by
    rcases l with ⟨j,c⟩
    fin_cases j <;> simp [integralCutForm] <;> ring
  simp only [GenericPlane.shift,cutForm_add,cutForm_ordinary,he,map_neg,map_add]
  constructor <;> intro h <;> linarith

theorem translated_arrangement (f : PlaneStep a) (u : CutRing × CutRing) :
    HasPlaneArrangement (fun p => f.val (GenericPlane.shift (-u) p)) := by
  classical
  obtain ⟨S,hS⟩ := hasArrangement f
  refine ⟨S.image (fun l => (l.1,l.2+integralCutForm a l.1 u)),fun p q hpq => ?_⟩
  apply hS
  intro l hl
  rw [translated_sign,translated_sign]
  exact hpq _ (Finset.mem_image_of_mem _ hl)

theorem translated_compact (f : PlaneStep a) (u : CutRing × CutRing) :
    PlaneCompactSupport (fun p => f.val (GenericPlane.shift (-u) p)) := by
  obtain ⟨R,hR⟩ := compactSupport f
  refine ⟨R + |ordinary u.1|+|ordinary u.2|,fun p hp => ?_⟩
  apply hR
  have h₁ : |p.val.1| ≤ |p.val.1-ordinary u.1|+|ordinary u.1| := by
    simpa using abs_add_le (p.val.1-ordinary u.1) (ordinary u.1)
  have h₂ : |p.val.2| ≤ |p.val.2-ordinary u.2|+|ordinary u.2| := by
    simpa using abs_add_le (p.val.2-ordinary u.2) (ordinary u.2)
  change R < |p.val.1+ordinary (-u).1| ∨ R < |p.val.2+ordinary (-u).2|
  simp only [Prod.fst_neg,Prod.snd_neg,map_neg,← sub_eq_add_neg]
  rcases hp with hp|hp
  · left; linarith [abs_nonneg (ordinary u.2)]
  · right; linarith [abs_nonneg (ordinary u.1)]

noncomputable def translate (u : CutRing × CutRing) : PlaneStep a →ₗ[ℤ] PlaneStep a where
  toFun f := ⟨fun p => f.val (GenericPlane.shift (-u) p),
    translated_arrangement f u,translated_compact f u⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem translate_apply (u : CutRing × CutRing) (f : PlaneStep a) (p : GenericPlane a) :
    (translate u f).val p=f.val (GenericPlane.shift (-u) p) := rfl

noncomputable def representation (a : ℕ) :
    Representation ℤ (Multiplicative (CutRing × CutRing)) (PlaneStep a) where
  toFun u := translate u.toAdd
  map_one' := by
    ext f p
    simp [translate]
  map_mul' u v := by
    ext f p
    change f.val (GenericPlane.shift (-(u.toAdd+v.toAdd)) p)=
      f.val (GenericPlane.shift (-v.toAdd) (GenericPlane.shift (-u.toAdd) p))
    rw [GenericPlane.shift_add]
    abel_nf

end PlaneStep

abbrev PolygonGroupRing := MonoidAlgebra ℤ (Multiplicative (CutRing × CutRing))

noncomputable def PolygonCoefficientModule (a : ℕ) := (PlaneStep.representation a).asModule

instance : AddGroup.FG CutRing := by
  apply Module.Finite.iff_addGroup_fg.mp
  infer_instance

instance : IsNoetherianRing PolygonGroupRing := by
  let : Algebra.FiniteType ℤ PolygonGroupRing :=
    MonoidAlgebra.finiteType_iff_group_fg.mpr inferInstance
  exact Algebra.FiniteType.isNoetherianRing ℤ PolygonGroupRing

end PlaneStepFunctions

section PlaneArrangementGerms

open Classical

def TransverseDirection (a : ℕ) (v : ℝ × ℝ) : Prop :=
  ∀ j : Fin 4, cutForm a j v ≠ 0

noncomputable def planeSector (a : ℕ) (z v : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | ∀ j : Fin 4, if cutForm a j v < 0 then cutForm a j p < cutForm a j z
      else cutForm a j z < cutForm a j p}

theorem planeSector_open (a : ℕ) (z v : ℝ × ℝ) : IsOpen (planeSector a z v) := by
  have he : planeSector a z v = ⋂ j : Fin 4,
      {p | if cutForm a j v < 0 then cutForm a j p < cutForm a j z
        else cutForm a j z < cutForm a j p} := by ext; simp [planeSector]
  rw [he]
  apply isOpen_iInter_of_finite
  intro j
  split_ifs
  · exact isOpen_lt (cutForm_continuous a j) continuous_const
  · exact isOpen_lt continuous_const (cutForm_continuous a j)

theorem planeSector_generic {a : ℕ} {z v : ℝ × ℝ} (hv : TransverseDirection a v)
    {N : Set (ℝ × ℝ)} (hN : IsOpen N) (hz : z∈N) :
    ∃ p : GenericPlane a, p.val∈N ∧ p.val∈planeSector a z v := by
  let σ : Fin 4 → Bool := fun j => decide (cutForm a j v < 0)
  have hactive (j : Fin 4) (_ : cutForm a j z=cutForm a j z) :
      if σ j then cutForm a j (z+v)<cutForm a j z
      else cutForm a j z<cutForm a j (z+v) := by
    simp only [σ,cutForm_add]
    split_ifs with h
    · have : cutForm a j v<0 := of_decide_eq_true h
      linarith
    · have hh : 0<cutForm a j v := lt_of_le_of_ne
        (le_of_not_gt (of_decide_eq_false (Bool.eq_false_iff.mpr h))) (hv j).symm
      linarith
  obtain ⟨p,hp,hσ,hpg⟩ := finite_arrangement_germ a id (fun j => cutForm a j z)
    z (z+v) σ hactive (fun _ hh => (hh rfl).elim) N hN hz
  refine ⟨⟨p,hpg⟩,hp,?_⟩
  intro j
  have hh := hσ j
  simpa [σ] using hh

noncomputable def arrangementNeighborhood (a : ℕ) (S : Finset PlaneCut) (z : ℝ × ℝ) :
    Set (ℝ × ℝ) := ⋂ l∈S, if cutForm a l.1 z=ordinary l.2 then Set.univ
      else if cutForm a l.1 z<ordinary l.2 then {p | cutForm a l.1 p<ordinary l.2}
      else {p | ordinary l.2<cutForm a l.1 p}

theorem arrangementNeighborhood_open (a : ℕ) (S : Finset PlaneCut) (z : ℝ × ℝ) :
    IsOpen (arrangementNeighborhood a S z) := by
  apply isOpen_biInter_finset
  intro l hl
  split_ifs
  · exact isOpen_univ
  · exact isOpen_lt (cutForm_continuous a l.1) continuous_const
  · exact isOpen_lt continuous_const (cutForm_continuous a l.1)

theorem self_mem_arrangementNeighborhood (a : ℕ) (S : Finset PlaneCut) (z : ℝ × ℝ) :
    z∈arrangementNeighborhood a S z := by
  apply Set.mem_iInter₂.mpr
  intro l hl
  split_ifs with he ht
  · trivial
  · exact ht
  · exact lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm he)

theorem planeSign_neighborhood {a : ℕ} {S : Finset PlaneCut} {z v : ℝ × ℝ}
    {p : GenericPlane a} (hN : p.val∈arrangementNeighborhood a S z)
    (hv : p.val∈planeSector a z v) {l : PlaneCut} (hl : l∈S) :
    planeSign l p=decide (if cutForm a l.1 z=ordinary l.2 then cutForm a l.1 v<0
      else cutForm a l.1 z<ordinary l.2) := by
  unfold planeSign
  apply decide_eq_decide.mpr
  by_cases he : cutForm a l.1 z=ordinary l.2
  · rw [ite_eq_left he]
    have hh := hv l.1
    rw [he] at hh
    by_cases ht : cutForm a l.1 v<0
    · rw [ite_eq_left ht] at hh
      exact iff_of_true hh ht
    · rw [ite_eq_right ht] at hh
      exact iff_of_false (not_lt_of_gt hh) ht
  · rw [ite_eq_right he]
    have hh := Set.mem_iInter₂.mp hN l hl
    rw [ite_eq_right he] at hh
    by_cases ht : cutForm a l.1 z<ordinary l.2
    · rw [ite_eq_left ht] at hh
      exact iff_of_true hh ht
    · rw [ite_eq_right ht] at hh
      exact iff_of_false (not_lt_of_gt hh) ht

def IsPlaneGerm {a : ℕ} (f : PlaneStep a) (z v : ℝ × ℝ) (n : ℤ) : Prop :=
  ∃ N : Set (ℝ × ℝ), IsOpen N ∧ z∈N ∧
    ∀ p : GenericPlane a, p.val∈N → p.val∈planeSector a z v → f.val p=n

theorem exists_planeGerm {a : ℕ} (f : PlaneStep a) (z v : ℝ × ℝ)
    (hv : TransverseDirection a v) : ∃ n : ℤ, IsPlaneGerm f z v n := by
  obtain ⟨S,hS⟩ := PlaneStep.hasArrangement f
  obtain ⟨p,hp,hpv⟩ := planeSector_generic hv (arrangementNeighborhood_open a S z)
    (self_mem_arrangementNeighborhood a S z)
  refine ⟨f.val p,arrangementNeighborhood a S z,arrangementNeighborhood_open a S z,
    self_mem_arrangementNeighborhood a S z,fun q hq hqv => ?_⟩
  apply hS
  intro l hl
  rw [planeSign_neighborhood hq hqv hl,planeSign_neighborhood hp hpv hl]

theorem IsPlaneGerm.unique {a : ℕ} {f : PlaneStep a} {z v : ℝ × ℝ} {m n : ℤ}
    (hv : TransverseDirection a v) (hm : IsPlaneGerm f z v m) (hn : IsPlaneGerm f z v n) :
    m=n := by
  obtain ⟨N,hN,hz,hf⟩ := hm
  obtain ⟨M,hM,hz',hg⟩ := hn
  obtain ⟨p,hp,hpv⟩ := planeSector_generic hv (hN.inter hM) ⟨hz,hz'⟩
  exact (hf p hp.1 hpv).symm.trans (hg p hp.2 hpv)

noncomputable def planeGerm {a : ℕ} (f : PlaneStep a) (z v : ℝ × ℝ) : ℤ :=
  if hv : TransverseDirection a v then Classical.choose (exists_planeGerm f z v hv) else 0

theorem planeGerm_spec {a : ℕ} (f : PlaneStep a) (z v : ℝ × ℝ)
    (hv : TransverseDirection a v) : IsPlaneGerm f z v (planeGerm f z v) := by
  rw [planeGerm,dite_eq_left hv]
  exact Classical.choose_spec (exists_planeGerm f z v hv)

theorem planeGerm_eq {a : ℕ} {f : PlaneStep a} {z v : ℝ × ℝ} {n : ℤ}
    (hv : TransverseDirection a v) (hn : IsPlaneGerm f z v n) : planeGerm f z v=n :=
  (planeGerm_spec f z v hv).unique hv hn

@[simp] theorem planeGerm_zero {a : ℕ} (z v : ℝ × ℝ) :
    planeGerm (0 : PlaneStep a) z v=0 := by
  by_cases hv : TransverseDirection a v
  · exact planeGerm_eq hv ⟨Set.univ,isOpen_univ,Set.mem_univ z,fun _ _ _ => rfl⟩
  · simp [planeGerm,hv]

@[simp] theorem planeGerm_add {a : ℕ} (f g : PlaneStep a) (z v : ℝ × ℝ) :
    planeGerm (f+g) z v=planeGerm f z v+planeGerm g z v := by
  by_cases hv : TransverseDirection a v
  · obtain ⟨N,hN,hz,hf⟩ := planeGerm_spec f z v hv
    obtain ⟨M,hM,hz',hg⟩ := planeGerm_spec g z v hv
    apply planeGerm_eq hv
    refine ⟨N∩M,hN.inter hM,⟨hz,hz'⟩,fun p hp hpv => ?_⟩
    exact congrArg₂ (·+·) (hf p hp.1 hpv) (hg p hp.2 hpv)
  · simp [planeGerm,hv]

@[simp] theorem planeGerm_smul {a : ℕ} (c : ℤ) (f : PlaneStep a) (z v : ℝ × ℝ) :
    planeGerm (c • f) z v=c • planeGerm f z v := by
  by_cases hv : TransverseDirection a v
  · obtain ⟨N,hN,hz,hf⟩ := planeGerm_spec f z v hv
    apply planeGerm_eq hv
    exact ⟨N,hN,hz,fun p hp hpv => congrArg (c • ·) (hf p hp hpv)⟩
  · simp [planeGerm,hv]

theorem planeGerm_evaluate {a : ℕ} (f : PlaneStep a) {S : Finset PlaneCut}
    (hS : ∀ p q, (∀ l∈S, planeSign l p=planeSign l q) → f.val p=f.val q)
    {z v : ℝ × ℝ} (hv : TransverseDirection a v) {p : GenericPlane a}
    (hp : p.val∈arrangementNeighborhood a S z) (hpv : p.val∈planeSector a z v) :
    f.val p=planeGerm f z v := by
  obtain ⟨N,hN,hz,hf⟩ := planeGerm_spec f z v hv
  obtain ⟨q,hq,hqv⟩ := planeSector_generic hv
    ((arrangementNeighborhood_open a S z).inter hN)
    ⟨self_mem_arrangementNeighborhood a S z,hz⟩
  have hpq : f.val p=f.val q := hS p q (fun l hl =>
    (planeSign_neighborhood hp hpv hl).trans (planeSign_neighborhood hq.1 hqv hl).symm)
  exact hpq.trans (hf q hq.2 hqv)

theorem planeGerm_congr_direction {a : ℕ} (f : PlaneStep a) (z : ℝ × ℝ)
    {v w : ℝ × ℝ} (hv : TransverseDirection a v) (hw : TransverseDirection a w)
    (hvw : ∀ j, (cutForm a j v<0 ↔ cutForm a j w<0)) :
    planeGerm f z v=planeGerm f z w := by
  apply planeGerm_eq hv
  obtain ⟨N,hN,hz,hf⟩ := planeGerm_spec f z w hw
  refine ⟨N,hN,hz,fun p hp hpv => hf p hp ?_⟩
  intro j
  have hh := hpv j
  simpa only [hvw j] using hh

end PlaneArrangementGerms

end SimpleAmenable
end
end

end OAI
