import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.CoordinateWindowTarget
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveTable

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ResolvedBoolean

variable {X ι : Type*}

def ResolvedBy (U : ι → Set X) (V : Set X) : Prop :=
  ∀ x y, (∀ i, x ∈ U i ↔ y ∈ U i) → (x ∈ V ↔ y ∈ V)

def resolvedAlgebra (U : ι → Set X) : BooleanSubalgebra (Set X) where
  carrier := {V | ResolvedBy U V}
  supClosed' := by
    intro V hV W hW x y h
    exact or_congr (hV x y h) (hW x y h)
  infClosed' := by
    intro V hV W hW x y h
    exact and_congr (hV x y h) (hW x y h)
  compl_mem' := by
    intro V hV x y h
    exact not_congr (hV x y h)
  bot_mem' := by intro x y h; rfl

theorem resolved_test (U : ι → Set X) (i : ι) : U i ∈ resolvedAlgebra U := by
  intro x y h
  exact h i

theorem resolved_mono {κ : Type*} (U : ι → Set X) (V : κ → Set X)
    (h : ∀ i, U i ∈ resolvedAlgebra V) : resolvedAlgebra U ≤ resolvedAlgebra V := by
  intro S hS x y he
  apply hS x y
  intro i
  exact h i x y he

variable {a : ℕ}

noncomputable def resolvedPolygonMask (U : ι → polygonAlgebra a)
    (V : Set (GenericSquare a)) : Set (Set.range (polygonAssignment U)) :=
  {ω | ∃ x, polygonAssignment U x = ω.val ∧ x ∈ V}

theorem polygonAssignment_eq_iff (U : ι → polygonAlgebra a) (x y : GenericSquare a) :
    polygonAssignment U x = polygonAssignment U y ↔
      ∀ i, x ∈ (U i).val ↔ y ∈ (U i).val := by
  classical
  constructor
  · intro h i
    have hi := congrFun h i
    simpa only [polygonAssignment,decide_eq_decide] using hi
  · intro h
    funext i
    exact decide_eq_decide.mpr (h i)

theorem resolvedPolygonMask_mem (U : ι → polygonAlgebra a)
    (V : Set (GenericSquare a)) (hV : ResolvedBy (fun i => (U i).val) V)
    (x : GenericSquare a) :
    (⟨polygonAssignment U x,⟨x,rfl⟩⟩ : Set.range (polygonAssignment U)) ∈
       resolvedPolygonMask U V ↔ x ∈ V := by
  constructor
  · rintro ⟨y,he,hy⟩
    exact (hV y x ((polygonAssignment_eq_iff U y x).mp he)).mp hy
  · intro hx
    exact ⟨x,rfl,hx⟩

theorem resolvedPolygonMask_mono (U : ι → polygonAlgebra a)
    {V W : Set (GenericSquare a)} (h : V ⊆ W) :
    resolvedPolygonMask U V ⊆ resolvedPolygonMask U W := by
  rintro ω ⟨x,he,hx⟩
  exact ⟨x,he,h hx⟩

theorem resolvedPolygonMask_disjoint (U : ι → polygonAlgebra a)
    {V W : Set (GenericSquare a)} (hV : ResolvedBy (fun i => (U i).val) V)
    (h : Disjoint V W) : Disjoint (resolvedPolygonMask U V) (resolvedPolygonMask U W) := by
  apply Set.disjoint_left.mpr
  rintro ω ⟨x,hx,hxV⟩ ⟨y,hy,hyW⟩
  have hyV := (hV x y ((polygonAssignment_eq_iff U x y).mp (hx.trans hy.symm))).mp hxV
  exact Set.disjoint_left.mp h hyV hyW

theorem resolvedPolygonMask_union (U : ι → polygonAlgebra a)
    (V W : Set (GenericSquare a)) :
    resolvedPolygonMask U (V ∪ W) = resolvedPolygonMask U V ∪ resolvedPolygonMask U W := by
  ext ω
  constructor
  · rintro ⟨x,he,hx | hx⟩
    · exact Or.inl ⟨x,he,hx⟩
    · exact Or.inr ⟨x,he,hx⟩
  · rintro (⟨x,he,hx⟩ | ⟨x,he,hx⟩)
    · exact ⟨x,he,Or.inl hx⟩
    · exact ⟨x,he,Or.inr hx⟩

end ResolvedBoolean

section FiniteCoordinateAlgebra

@[simp] theorem coordinateShift_add (j : Fin 2) (u v : CutRing) :
    coordinateShift j (u+v) = coordinateShift j u + coordinateShift j v := by
  fin_cases j <;> simp [coordinateShift]

@[simp] theorem coordinateShift_neg (j : Fin 2) (u : CutRing) :
    coordinateShift j (-u) = -coordinateShift j u := by
  fin_cases j <;> simp [coordinateShift]

theorem coordinateArc_tau {a : ℕ} (j : Fin 2) :
    coordinateArc a j cutTau = (coordinatePrimitive a j).val := by
  have hfloor : ⌊Real.goldenRatio⌋ = (1 : ℤ) :=
    Int.floor_eq_iff.mpr ⟨by norm_num; exact Real.one_lt_goldenRatio.le,
      by norm_num; exact Real.goldenRatio_lt_two⟩
  ext p
  have hp := (coordinate_bounds j p).1
  fin_cases j <;>
    simp [coordinateArc,coordinate,coordinatePrimitive,halfPlane,cutForm,
      Int.fract,hfloor,ordinary_cutTau] <;> intro _ <;> exact hp

theorem coordinate_preimage_add {a : ℕ} (j : Fin 2) (u v : CutRing)
    (V : Set (GenericSquare a)) :
    translate a (-coordinateShift j u) ⁻¹' (translate a (-coordinateShift j v) ⁻¹' V) =
      translate a (-coordinateShift j (u+v)) ⁻¹' V := by
  ext p
  simp only [Set.mem_preimage,coordinateShift_add,neg_add_rev,translate_add]

noncomputable def coordinateBetween (a : ℕ) (j : Fin 2) (u v : CutRing) :
    Set (GenericSquare a) :=
  translate a (-coordinateShift j u) ⁻¹' coordinateArc a j (v-u)

theorem coordinate_prefix_generated {a : ℕ}
    (B : BooleanSubalgebra (Set (GenericSquare a))) (j : Fin 2) (u : CutRing)
    (n : ℕ)
    (h : ∀ i : ℕ, i < n →
      (spatialTranslate (coordinateShift j (u+(i:CutRing)*cutTau))
        (coordinatePrimitive a j)).val ∈ B) :
    coordinateBetween a j u (u+(n:CutRing)*cutTau) ∈ B := by
  have hs {V W : Set (GenericSquare a)} (hV : V ∈ B) (hW : W ∈ B) : symmDiff V W ∈ B := by
    rw [Set.symmDiff_def]
    exact BooleanSubalgebra.sup_mem (BooleanSubalgebra.sdiff_mem hV hW)
      (BooleanSubalgebra.sdiff_mem hW hV)
  change translate a (-coordinateShift j u) ⁻¹' coordinateArc a j
      (u+(n:CutRing)*cutTau-u) ∈ B
  rw [add_sub_cancel_left]
  induction n with
  | zero =>
    rw [Nat.cast_zero,zero_mul,coordinateArc_zero_of_fract j 0 (by simp),Set.preimage_empty]
    exact BooleanSubalgebra.bot_mem
  | succ n ih =>
    have hi := ih (fun i hi => h i (by omega))
    rw [Nat.cast_succ,add_mul,one_mul,coordinateArc_add]
    have he := h n (by omega)
    change translate a (-coordinateShift j (u+(n:CutRing)*cutTau)) ⁻¹'
      (coordinatePrimitive a j).val ∈ B at he
    split_ifs
    · rw [Set.preimage_symmDiff,coordinateShift_neg,coordinate_preimage_add,
        coordinateArc_tau]
      exact hs hi he
    · rw [Set.preimage_compl,Set.preimage_symmDiff,coordinateShift_neg,
        coordinate_preimage_add,coordinateArc_tau]
      exact BooleanSubalgebra.compl_mem (hs hi he)

theorem coordinate_window_between_resolved {a : ℕ} {r : CutRing}
    (n : ℕ) (q : Fin 2 → ℤ) (j : Fin 2) (i k : ℕ) (hik : i ≤ k) (hk : k < n) :
    coordinateBetween a j (((q j+(i:ℤ)):CutRing)*cutTau)
      (((q j+(k:ℤ)):CutRing)*cutTau) ∈
      resolvedAlgebra (fun z => (InitialCoverSystem.primitiveTests (a := a) (r := r)
        (coordinateWindowPrimitives n q) z).val) := by
  let B := resolvedAlgebra (fun z => (InitialCoverSystem.primitiveTests (a := a) (r := r)
    (coordinateWindowPrimitives n q) z).val)
  have hp := coordinate_prefix_generated B j (((q j+(i:ℤ)):CutRing)*cutTau) (k-i)
  have he : (((q j+(i:ℤ)):CutRing)*cutTau) + ((k-i:ℕ):CutRing)*cutTau =
      (((q j+(k:ℤ)):CutRing)*cutTau) := by
    push_cast
    rw [Nat.cast_sub hik]
    ring
  rw [he] at hp
  apply hp
  intro t ht
  have ht' : i+t < n-1 := by omega
  have hh := resolved_test (fun z => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) z).val) (j,⟨i+t,ht'⟩)
  change (spatialTranslate (coordinateShift j
      (((q j+((i+t:ℕ):ℤ)):CutRing)*cutTau))
      (initialTest a r (coordinateTestIndex j))).val ∈ B at hh
  rw [initialTest_coordinate] at hh
  convert hh using 1
  congr 3
  push_cast
  ring

end FiniteCoordinateAlgebra

end SimpleAmenable
end
end

end OAI
