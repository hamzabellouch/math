import OAI.Probability.FreeIsing.Trees.ConnectedHull
import OAI.Probability.FreeIsing.Trees.Parents

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.TreeConeCoding

def encode {b : ℕ} (c : Fin (b + 1)) : List (Fin b) → List (Fin (b + 1))
  | [] => []
  | i :: w => (finSuccAboveEquiv c i).1 :: encode (finSuccAboveEquiv c i).1 w

@[simp] theorem encode_nil {b : ℕ} (c : Fin (b + 1)) : encode c [] = [] := rfl

@[simp] theorem length_encode {b : ℕ} (c : Fin (b + 1)) (w : List (Fin b)) :
    (encode c w).length = w.length := by
  induction w generalizing c with
  | nil => rfl
  | cons i w ih => simp only [encode, List.length_cons, ih]

theorem chain_encode {b : ℕ} (c : Fin (b + 1)) (w : List (Fin b)) :
    List.IsChain (fun a b => a ≠ b) (c :: encode c w) := by
  induction w generalizing c with
  | nil => exact List.IsChain.singleton c
  | cons i w ih =>
      exact List.isChain_cons_cons.mpr ⟨(finSuccAboveEquiv c i).2.symm, ih _⟩

theorem encode_injective {b : ℕ} (c : Fin (b + 1)) : Function.Injective (encode c) := by
  intro x
  induction x generalizing c with
  | nil =>
      intro y h
      have := congrArg List.length h
      simpa only [length_encode, List.length_nil, eq_comm, List.length_eq_zero_iff] using this
  | cons i x ih =>
      intro y h
      cases y with
      | nil => have := congrArg List.length h; simp at this
      | cons j y =>
          have he := List.cons.inj h
          have hij : i = j := (finSuccAboveEquiv c).injective (Subtype.ext he.1)
          subst j
          exact congrArg (List.cons i) (ih _ he.2)

theorem encode_surjective {b : ℕ} (c : Fin (b + 1))
    (w : List (Fin (b + 1))) (hw : List.IsChain (fun a b => a ≠ b) (c :: w)) :
    ∃ x : List (Fin b), encode c x = w := by
  induction w generalizing c with
  | nil => exact ⟨[], rfl⟩
  | cons a w ih =>
      obtain ⟨hca, haw⟩ := List.isChain_cons_cons.mp hw
      obtain ⟨x, hx⟩ := ih a haw
      let i := (finSuccAboveEquiv c).symm ⟨a, hca.symm⟩
      have hi : (finSuccAboveEquiv c i).1 = a := by
        simp only [i, Equiv.apply_symm_apply]
      refine ⟨i :: x, ?_⟩
      simp only [encode, hi, hx]

def continuationEquiv {b : ℕ} (c : Fin (b + 1)) :
    List (Fin b) ≃ {w : List (Fin (b + 1)) // List.IsChain (fun a b => a ≠ b) (c :: w)} :=
  Equiv.ofBijective (fun x => ⟨encode c x, chain_encode c x⟩)
    ⟨fun _ _ h => encode_injective c (congrArg Subtype.val h), by
      rintro ⟨w, hw⟩
      obtain ⟨x, hx⟩ := encode_surjective c w hw
      exact ⟨x, Subtype.ext hx⟩⟩

@[simp] theorem encode_take {b : ℕ} (c : Fin (b + 1)) (w : List (Fin b)) (n : ℕ) :
    encode c (w.take n) = (encode c w).take n := by
  induction n generalizing c w with
  | zero => simp
  | succ n ih =>
      cases w with
      | nil => rfl
      | cons i w => simp only [List.take_succ_cons, encode, ih]

theorem chain_append_iff {α : Type*} (R : α → α → Prop) (r w : List α) (hr : r ≠ []) :
    List.IsChain R (r ++ w) ↔ List.IsChain R r ∧ List.IsChain R (r.getLast hr :: w) := by
  conv_lhs => rw [← List.dropLast_append_getLast hr]
  simp only [List.append_assoc, List.singleton_append]
  rw [List.isChain_split, List.dropLast_append_getLast]

def vertex {b : ℕ} (r : TreeVertex (b + 1)) (hr : r.1 ≠ [])
    (w : List (Fin b)) : TreeVertex (b + 1) :=
  ⟨r.1 ++ encode (r.1.getLast hr) w,
    (chain_append_iff _ _ _ hr).mpr ⟨r.2, chain_encode _ _⟩⟩

@[simp] theorem vertex_val {b : ℕ} (r : TreeVertex (b + 1)) (hr : r.1 ≠ [])
    (w : List (Fin b)) :
    (vertex r hr w).1 = r.1 ++ encode (r.1.getLast hr) w := rfl

@[simp] theorem vertex_nil {b : ℕ} (r : TreeVertex (b + 1)) (hr : r.1 ≠ []) :
    vertex r hr [] = r := by
  apply Subtype.ext
  simp

@[simp] theorem length_vertex {b : ℕ} (r : TreeVertex (b + 1)) (hr : r.1 ≠ [])
    (w : List (Fin b)) : (vertex r hr w).1.length = r.1.length + w.length := by
  simp

theorem vertex_prefix {b : ℕ} (r : TreeVertex (b + 1)) (hr : r.1 ≠ [])
    (w : List (Fin b)) : r.1 <+: (vertex r hr w).1 := List.prefix_append _ _

theorem vertex_injective {b : ℕ} (r : TreeVertex (b + 1)) (hr : r.1 ≠ []) :
    Function.Injective (vertex r hr) := by
  intro x y h
  apply encode_injective (r.1.getLast hr)
  exact List.append_cancel_left (congrArg Subtype.val h)

theorem vertex_surjective_cone {b : ℕ} (r : TreeVertex (b + 1)) (hr : r.1 ≠ [])
    (v : TreeVertex (b + 1)) (hv : r.1 <+: v.1) :
    ∃ w : List (Fin b), vertex r hr w = v := by
  obtain ⟨tail, htail⟩ := hv
  have hc : List.IsChain (fun a b => a ≠ b) (r.1.getLast hr :: tail) := by
    apply ((chain_append_iff _ _ _ hr).mp _).2
    rw [htail]
    exact v.2
  obtain ⟨w, hw⟩ := encode_surjective (r.1.getLast hr) tail hc
  refine ⟨w, Subtype.ext ?_⟩
  change r.1 ++ encode (r.1.getLast hr) w = v.1
  rw [hw, htail]

def coneEquiv {b : ℕ} (r : TreeVertex (b + 1)) (hr : r.1 ≠ []) :
    List (Fin b) ≃ {v : TreeVertex (b + 1) // r.1 <+: v.1} :=
  Equiv.ofBijective (fun w => ⟨vertex r hr w, vertex_prefix r hr w⟩)
    ⟨fun _ _ h => vertex_injective r hr (congrArg Subtype.val h), by
      rintro ⟨v, hv⟩
      obtain ⟨w, hw⟩ := vertex_surjective_cone r hr v hv
      exact ⟨w, Subtype.ext hw⟩⟩

theorem vertex_take {b : ℕ} (r : TreeVertex (b + 1)) (hr : r.1 ≠ [])
    (w : List (Fin b)) (n : ℕ) :
    vertex r hr (w.take n) =
      ConnectedHull.takeVertex (vertex r hr w) (r.1.length + n) := by
  apply Subtype.ext
  change r.1 ++ encode (r.1.getLast hr) (w.take n) =
    (r.1 ++ encode (r.1.getLast hr) w).take (r.1.length + n)
  rw [List.take_length_add_append, encode_take]

def labels {b : ℕ} {A : Type*} (r : TreeVertex (b + 1)) (hr : r.1 ≠ [])
    (U : TreeVertex (b + 1) → A) : List (Fin b) → A :=
  fun w => U (vertex r hr w)

theorem measurable_labels {b : ℕ} {A : Type*} [MeasurableSpace A]
    (r : TreeVertex (b + 1)) (hr : r.1 ≠ []) :
    Measurable (labels (A := A) r hr) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

theorem map_labels {b : ℕ} {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν]
    (r : TreeVertex (b + 1)) (hr : r.1 ≠ []) :
    Measure.map (labels r hr) (Measure.infinitePi (fun _ : TreeVertex (b + 1) => ν)) =
      Measure.infinitePi (fun _ : List (Fin b) => ν) := by
  exact Measure.map_infinitePi_infinitePi_of_inj (vertex_injective r hr)

theorem measurePreserving_labels {b : ℕ} {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν]
    (r : TreeVertex (b + 1)) (hr : r.1 ≠ []) :
    MeasurePreserving (labels r hr)
      (Measure.infinitePi (fun _ : TreeVertex (b + 1) => ν))
      (Measure.infinitePi (fun _ : List (Fin b) => ν)) :=
  ⟨measurable_labels r hr, map_labels ν r hr⟩

theorem map_uniform_labels {b : ℕ}
    (r : TreeVertex (b + 1)) (hr : r.1 ≠ []) :
    Measure.map (labels r hr) (labelMeasure (b + 1)) =
      Measure.infinitePi (fun _ : List (Fin b) => uniform01) :=
  map_labels uniform01 r hr

end Problem367.TreeConeCoding

end

end OAI
