import Mathlib
import OAI.LinearAlgebra.MatrixFields.Entropy.StageCLaw
import OAI.LinearAlgebra.MatrixFields.Parameters.JointPopulation

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators

def shapeTotal (u : Shape) : ℕ := u 0 + u 1 + u 2

def ShapeBounded (u : Shape) : Prop := ∀ i, u i ≤ 16

def encodeShape (u : Shape) (h : ShapeBounded u) : JointPopulation.Shape :=
  (⟨u 0, Nat.lt_succ_of_le (h 0)⟩,
    ⟨u 1, Nat.lt_succ_of_le (h 1)⟩, ⟨u 2, Nat.lt_succ_of_le (h 2)⟩)

def decodeShape (u : JointPopulation.Shape) : Shape :=
  fun i => (JointPopulation.shapeSide i u).val

@[simp] theorem decode_encodeShape (u : Shape) (h : ShapeBounded u) :
    decodeShape (encodeShape u h) = u := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem encodeShape_side (u : Shape) (h : ShapeBounded u) (i : Fin 3) :
    (JointPopulation.shapeSide i (encodeShape u h)).val = u i :=
  congrFun (decode_encodeShape u h) i

theorem decodeShape_bounded (u : JointPopulation.Shape) : ShapeBounded (decodeShape u) := by
  intro i
  have h := (JointPopulation.shapeSide i u).isLt
  change (JointPopulation.shapeSide i u).val ≤ 16
  omega

@[simp] theorem encode_decodeShape (u : JointPopulation.Shape) :
    encodeShape (decodeShape u) (decodeShape_bounded u) = u := by
  apply Prod.ext
  · apply Fin.ext
    rfl
  · apply Prod.ext <;> apply Fin.ext <;> rfl

theorem encodeShape_inj {u v : Shape} {hu : ShapeBounded u} {hv : ShapeBounded v}
    (h : encodeShape u hu = encodeShape v hv) : u = v := by
  simpa only [decode_encodeShape] using congrArg decodeShape h

theorem encodeShape_injective :
    Function.Injective (fun u : {u : Shape // ShapeBounded u} => encodeShape u.val u.property) := by
  intro u v h
  apply Subtype.ext
  exact encodeShape_inj h

@[simp] theorem encodeShape_total (u : Shape) (h : ShapeBounded u) :
    (encodeShape u h).1.val + (encodeShape u h).2.1.val +
      (encodeShape u h).2.2.val = shapeTotal u := rfl

def physicalShape (phi : Equiv.Perm (Fin 3)) (u : Shape) : Shape :=
  fun i => u (phi.symm i)

@[simp] theorem physicalShape_source (phi : Equiv.Perm (Fin 3)) (u : Shape) (i : Fin 3) :
    physicalShape phi u (phi i) = u i := by
  simp only [physicalShape, Equiv.symm_apply_apply]

theorem physicalShape_bounded (phi : Equiv.Perm (Fin 3)) (u : Shape)
    (h : ShapeBounded u) : ShapeBounded (physicalShape phi u) :=
  fun i => h (phi.symm i)

theorem physicalShape_le (phi : Equiv.Perm (Fin 3)) {u v : Shape}
    (h : ∀ i, v i ≤ u i) : ∀ i, physicalShape phi v i ≤ physicalShape phi u i :=
  fun i => h (phi.symm i)

@[simp] theorem physicalShape_complement (phi : Equiv.Perm (Fin 3)) (u v : Shape) :
    physicalShape phi (complement u v) =
      complement (physicalShape phi u) (physicalShape phi v) := rfl

theorem physicalShape_total (phi : Equiv.Perm (Fin 3)) (u : Shape) :
    shapeTotal (physicalShape phi u) = shapeTotal u := by
  simpa [shapeTotal, physicalShape, Fin.sum_univ_succ, Nat.add_assoc] using
    (Equiv.sum_comp phi.symm u)

theorem physicalShape_injective (phi : Equiv.Perm (Fin 3)) :
    Function.Injective (physicalShape phi) := by
  intro u v h
  funext i
  simpa only [physicalShape_source] using congrFun h (phi i)

def encodePhysicalShape (phi : Equiv.Perm (Fin 3)) (u : Shape) (h : ShapeBounded u) :
    JointPopulation.Shape := encodeShape (physicalShape phi u) (physicalShape_bounded phi u h)

@[simp] theorem decode_encodePhysicalShape (phi : Equiv.Perm (Fin 3))
    (u : Shape) (h : ShapeBounded u) :
    decodeShape (encodePhysicalShape phi u h) = physicalShape phi u :=
  decode_encodeShape _ _

@[simp] theorem encodePhysicalShape_side (phi : Equiv.Perm (Fin 3))
    (u : Shape) (h : ShapeBounded u) (i : Fin 3) :
    (JointPopulation.shapeSide i (encodePhysicalShape phi u h)).val = u (phi.symm i) :=
  encodeShape_side _ _ i

theorem encodePhysicalShape_inj (phi : Equiv.Perm (Fin 3))
    {u v : Shape} {hu : ShapeBounded u} {hv : ShapeBounded v}
    (h : encodePhysicalShape phi u hu = encodePhysicalShape phi v hv) : u = v :=
  physicalShape_injective phi (encodeShape_inj h)

theorem encodePhysicalShape_total (phi : Equiv.Perm (Fin 3))
    (u : Shape) (h : ShapeBounded u) :
    (encodePhysicalShape phi u h).1.val + (encodePhysicalShape phi u h).2.1.val +
      (encodePhysicalShape phi u h).2.2.val = shapeTotal u :=
  physicalShape_total phi u

theorem mem_shapes_total {n : ℕ} {u : Shape} (hu : u ∈ shapes n) : shapeTotal u = n := by
  simp only [shapes, List.mem_flatMap, List.mem_map, List.mem_range] at hu
  obtain ⟨a, ha, b, hb, rfl⟩ := hu
  change a + b + (n - a - b) = n
  omega

theorem coordinate_le_total (u : Shape) (i : Fin 3) : u i ≤ shapeTotal u := by
  fin_cases i
  · change u 0 ≤ u 0 + u 1 + u 2
    omega
  · change u 1 ≤ u 0 + u 1 + u 2
    omega
  · change u 2 ≤ u 0 + u 1 + u 2
    omega

theorem mem_shapes_bound {n : ℕ} {u : Shape} (hu : u ∈ shapes n) (i : Fin 3) : u i ≤ n := by
  simpa only [mem_shapes_total hu] using coordinate_le_total u i

theorem mem_shapes_bounded {n : ℕ} {u : Shape} (hu : u ∈ shapes n) (hn : n ≤ 16) :
    ShapeBounded u := fun i => (mem_shapes_bound hu i).trans hn

theorem below_mem_shapes {u v : Shape} (hv : v ∈ below u) :
    v ∈ shapes (shapeTotal u / 2) := (List.mem_filter.mp hv).1

theorem below_total {u v : Shape} (hv : v ∈ below u) :
    shapeTotal v = shapeTotal u / 2 := mem_shapes_total (below_mem_shapes hv)

theorem below_le {u v : Shape} (hv : v ∈ below u) : ∀ i, v i ≤ u i := by
  have h := (List.mem_filter.mp hv).2
  have hb : v 0 ≤ u 0 ∧ v 1 ≤ u 1 ∧ v 2 ≤ u 2 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h
  intro i
  fin_cases i
  · exact hb.1
  · exact hb.2.1
  · exact hb.2.2

theorem below_bounded {u v : Shape} (hu : ShapeBounded u) (hv : v ∈ below u) :
    ShapeBounded v := fun i => (below_le hv i).trans (hu i)

theorem complement_bounded {u v : Shape} (hu : ShapeBounded u) :
    ShapeBounded (complement u v) := fun i => (Nat.sub_le (u i) (v i)).trans (hu i)

theorem complement_total {u v : Shape} (h : ∀ i, v i ≤ u i) :
    shapeTotal (complement u v) = shapeTotal u - shapeTotal v := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [shapeTotal, complement]
  omega

theorem root_shape_spec (s : Shape) (hs : s ∈ sortedInitial) :
    ShapeBounded s ∧ shapeTotal s = 16 := by
  have hm : s ∈ shapes 16 := (List.mem_filter.mp hs).1
  exact ⟨mem_shapes_bounded hm (by omega), mem_shapes_total hm⟩

theorem root_shapes_nodup : sortedInitial.Nodup := by decide +kernel

theorem stageA_below_nodup : ∀ s ∈ positiveInitial, (below s).Nodup := by
  decide +kernel

theorem stageB_below_nodup : ∀ t ∈ positiveSecond, (below t).Nodup := by
  decide +kernel

theorem stageA_get_injective (s : Shape) (hs : s ∈ positiveInitial) :
    Function.Injective (below s).get :=
  List.nodup_iff_injective_get.mp (stageA_below_nodup s hs)

theorem stageB_get_injective (t : Shape) (ht : t ∈ positiveSecond) :
    Function.Injective (below t).get :=
  List.nodup_iff_injective_get.mp (stageB_below_nodup t ht)

theorem positiveInitial_shape_spec (s : Shape) (hs : s ∈ positiveInitial) :
    ShapeBounded s ∧ shapeTotal s = 16 :=
  root_shape_spec s (List.mem_filter.mp hs).1

theorem positiveSecond_shape_spec (t : Shape) (ht : t ∈ positiveSecond) :
    ShapeBounded t ∧ shapeTotal t = 8 := by
  have hm : t ∈ shapes 8 := (List.mem_filter.mp ht).1
  exact ⟨mem_shapes_bounded hm (by omega), mem_shapes_total hm⟩

theorem stageA_shape_spec (s t : Shape) (hs : s ∈ positiveInitial) (ht : t ∈ below s) :
    ShapeBounded t ∧ shapeTotal t = 8 := by
  obtain ⟨hb, hsum⟩ := positiveInitial_shape_spec s hs
  exact ⟨below_bounded hb ht, by simpa only [hsum] using below_total ht⟩

theorem stageA_complement_spec (s t : Shape) (hs : s ∈ positiveInitial)
    (ht : t ∈ below s) : ShapeBounded (complement s t) ∧ shapeTotal (complement s t) = 8 := by
  obtain ⟨hb, hsum⟩ := positiveInitial_shape_spec s hs
  obtain ⟨_, hchild⟩ := stageA_shape_spec s t hs ht
  exact ⟨complement_bounded hb, by rw [complement_total (below_le ht), hsum, hchild]⟩

theorem stageB_shape_spec (t u : Shape) (ht : t ∈ positiveSecond) (hu : u ∈ below t) :
    ShapeBounded u ∧ shapeTotal u = 4 := by
  obtain ⟨hb, hsum⟩ := positiveSecond_shape_spec t ht
  exact ⟨below_bounded hb hu, by simpa only [hsum] using below_total hu⟩

theorem stageB_complement_spec (t u : Shape) (ht : t ∈ positiveSecond)
    (hu : u ∈ below t) : ShapeBounded (complement t u) ∧ shapeTotal (complement t u) = 4 := by
  obtain ⟨hb, hsum⟩ := positiveSecond_shape_spec t ht
  obtain ⟨_, hchild⟩ := stageB_shape_spec t u ht hu
  exact ⟨complement_bounded hb, by rw [complement_total (below_le hu), hsum, hchild]⟩

theorem stageC_shape_spec (u : Shape) (hu : u ∈ shapes 4) (hpos : positive u = true)
    (i : Fin 4) : ShapeBounded (stageCAtom u i) ∧ shapeTotal (stageCAtom u i) = 2 := by
  have hi := stageCAtom_mem u hu hpos i
  exact ⟨below_bounded (mem_shapes_bounded hu (by omega)) hi,
    by simpa only [mem_shapes_total hu] using below_total hi⟩

theorem stageC_complement_spec (u : Shape) (hu : u ∈ shapes 4) (hpos : positive u = true)
    (i : Fin 4) : ShapeBounded (complement u (stageCAtom u i)) ∧
      shapeTotal (complement u (stageCAtom u i)) = 2 := by
  have hi := stageCAtom_mem u hu hpos i
  obtain ⟨_, hchild⟩ := stageC_shape_spec u hu hpos i
  exact ⟨complement_bounded (mem_shapes_bounded hu (by omega)),
    by rw [complement_total (below_le hi), mem_shapes_total hu, hchild]⟩

end MatrixMultiplication.AllFieldHistory

end MatrixAllFields

end OAI
