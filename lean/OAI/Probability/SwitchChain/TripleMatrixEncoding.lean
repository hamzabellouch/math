import OAI.Probability.SwitchChain.TripleInternalEncoding

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.TripleInternalEncoding

def rowOffset (e : ℕ) : ℕ := if e = 2 then 1 else if e = 3 then 2 else 0

theorem degree_eq_extra_add_offset (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    graphDegree G v = extraColumn G v + rowOffset (internalEdgeCount G) := by
  have he := internalEdgeCount_le_three G
  have hcases : internalEdgeCount G = 0 ∨ internalEdgeCount G = 1 ∨
      internalEdgeCount G = 2 ∨ internalEdgeCount G = 3 := by omega
  rcases hcases with h | h | h | h
  · simp [extraColumn, rowOffset, h, degree_eq_zero_of_no_edges G h v]
  · simp [extraColumn, rowOffset, h]
  · have hd := one_le_degree_of_two_edges G h v
    simp [extraColumn, rowOffset, h]
    omega
  · simp [extraColumn, rowOffset, h, degree_eq_two_of_three_edges G h v]

variable (W : Type*) [Fintype W]

@[ext]
structure TripleCell (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ) where
  outside : Fin 3 → W → ℕ
  inside : SimpleGraph (Fin 3)
  edge_count : internalEdgeCount inside = e
  binary : ∀ v w, outside v w ≤ 1
  columns : ∀ w, ∑ v, outside v w = c w
  rows : ∀ v, (∑ w, outside v w) + graphDegree inside v = d v

@[ext]
structure AugmentedMatrix (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ) where
  matrix : Fin 3 → Option W → ℕ
  binary : ∀ v w, matrix v w ≤ 1
  columns : ∀ w, ∑ v, matrix v w = w.elim (columnSum e) c
  rows : ∀ v, (∑ w, matrix v w) = d v - rowOffset e

variable {W}

def encodeCell {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (A : TripleCell W e d c) : AugmentedMatrix W e d c where
  matrix v w := w.elim (extraColumn A.inside v) (A.outside v)
  binary v w := by
    cases w with
    | none => exact extraColumn_le_one A.inside v
    | some w => exact A.binary v w
  columns w := by
    cases w with
    | none =>
        simpa only [Option.elim_none, A.edge_count, columnSum] using sum_extraColumn A.inside
    | some w => exact A.columns w
  rows v := by
    rw [Fintype.sum_option]
    dsimp only [Option.elim_none, Option.elim_some]
    have hrow := A.rows v
    rw [degree_eq_extra_add_offset, A.edge_count] at hrow
    omega

def internalOfAugmented {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (he : e ≤ 3) (A : AugmentedMatrix W e d c) :
    {G : SimpleGraph (Fin 3) // internalEdgeCount G = e} :=
  (fixedEdgeEncodingEquiv e he).symm
    ⟨fun v => A.matrix v none, (fun v => A.binary v none), A.columns none⟩

theorem extraColumn_internalOfAugmented {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (he : e ≤ 3) (A : AugmentedMatrix W e d c) :
    extraColumn (internalOfAugmented he A).val = fun v => A.matrix v none := by
  exact congrArg Subtype.val ((fixedEdgeEncodingEquiv e he).apply_symm_apply
    ⟨fun v => A.matrix v none, (fun v => A.binary v none), A.columns none⟩)

def decodeMatrix {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (he : e ≤ 3) (hd : ∀ v, rowOffset e ≤ d v)
    (A : AugmentedMatrix W e d c) : TripleCell W e d c where
  outside v w := A.matrix v (some w)
  inside := (internalOfAugmented he A).val
  edge_count := (internalOfAugmented he A).property
  binary v w := A.binary v (some w)
  columns w := A.columns (some w)
  rows v := by
    rw [degree_eq_extra_add_offset, (internalOfAugmented he A).property,
      extraColumn_internalOfAugmented]
    have hrow := A.rows v
    rw [Fintype.sum_option] at hrow
    dsimp
    have hmargin := hd v
    omega

@[simp] theorem decode_encode {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (he : e ≤ 3) (hd : ∀ v, rowOffset e ≤ d v) (A : TripleCell W e d c) :
    decodeMatrix he hd (encodeCell A) = A := by
  apply TripleCell.ext
  · rfl
  · apply encoded_graph_injective
    apply Prod.ext
    · exact (internalOfAugmented he (encodeCell A)).property.trans A.edge_count.symm
    · exact extraColumn_internalOfAugmented he (encodeCell A)

@[simp] theorem encode_decode {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (he : e ≤ 3) (hd : ∀ v, rowOffset e ≤ d v) (A : AugmentedMatrix W e d c) :
    encodeCell (decodeMatrix he hd A) = A := by
  apply AugmentedMatrix.ext
  funext v w
  cases w with
  | none => exact congrFun (extraColumn_internalOfAugmented he A) v
  | some w => rfl

def tripleMatrixEquiv (e : ℕ) (he : e ≤ 3) (d : Fin 3 → ℕ) (c : W → ℕ)
    (hd : ∀ v, rowOffset e ≤ d v) :
    TripleCell W e d c ≃ AugmentedMatrix W e d c where
  toFun := encodeCell
  invFun := decodeMatrix he hd
  left_inv := decode_encode he hd
  right_inv := encode_decode he hd

theorem rowOffset_le_of_nonempty {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (h : Nonempty (TripleCell W e d c)) : ∀ v, rowOffset e ≤ d v := by
  obtain ⟨A⟩ := h
  intro v
  have hrow := A.rows v
  rw [degree_eq_extra_add_offset, A.edge_count] at hrow
  omega

theorem extraColumn_eq_margin_sub_row {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (A : TripleCell W e d c) (v : Fin 3) :
    extraColumn A.inside v = d v - rowOffset e - ∑ w, A.outside v w := by
  have hrow := A.rows v
  rw [degree_eq_extra_add_offset, A.edge_count] at hrow
  omega

theorem encode_row_eq_iff {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (A B : TripleCell W e d c) (v : Fin 3) :
    (encodeCell A).matrix v = (encodeCell B).matrix v ↔ A.outside v = B.outside v := by
  constructor
  · intro h
    funext w
    exact congrFun h (some w)
  · intro h
    funext w
    cases w with
    | none =>
        change extraColumn A.inside v = extraColumn B.inside v
        rw [extraColumn_eq_margin_sub_row, extraColumn_eq_margin_sub_row, h]
    | some w => exact congrFun h w

end Problem315.TripleInternalEncoding

end

end OAI
