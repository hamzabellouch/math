import OAI.NumberTheory.TwoPoint.Walks.ColumnForestAssembly

namespace OAI

/-! From quotient-line geometry to a complete column code, including the empty regular set. -/

namespace TwoPointCorrelations

open Finset

private theorem partition_all_omitted {α : Type*} (runs : List α) :
    partitionColumnRuns (fun _ => true) runs = runs.map Sum.inr := by
  induction runs with
  | nil => rfl
  | cons a runs ih => simp only [partitionColumnRuns, ite_true, List.map_cons, ih]

theorem indexedRegularSegments_eq_nil {α : Type*} [DecidableEq α]
    (label : ℕ → α) (omitted : α → Bool) (blocks : List (ℕ × ℕ))
    (h : ∀ z, omitted z = true) : indexedRegularSegments label omitted blocks = [] := by
  have ho : omitted = fun _ => true := funext h
  subst omitted
  have hp (runs : List (ℕ × α)) :
      (partitionColumnRuns (fun _ => true) runs).filterMap (Sum.elim some (fun _ => none)) = [] := by
    rw [partition_all_omitted]
    simp only [List.filterMap_map, Function.comp_def, Sum.elim_inr, List.filterMap_eq_nil_iff]
    simp
  apply List.flatMap_eq_nil_iff.mpr
  intro b _
  exact hp _

private def emptyForestPathCode (N : ℕ) : ForestPathData.Code N 0 :=
  (⟨BinaryTree.nil, by simp⟩, Fin.elim0)

/-- The only geometric premises are independent quotient directions,
actual line incidence, and nonzero constant intervals. All path codes,
canonical labels, occurrence references and the full equality pattern are
constructed. No nonemptiness of the regular set is required. -/
theorem column_code_from_quotient_geometry {α : Type*} [Fintype α] [DecidableEq α]
    {n N O I : ℕ} (hN : 0 < N) (hn : n ≤ N)
    (label : Fin n → α) (perfect : Finset (Fin n)) (regular : Finset α)
    (labelNat : ℕ → α) (coefficient : ℕ → ℝ)
    (chunks : List (List α ⊕ α)) (blocks : List (ℕ × ℕ))
    (hentries : columnChunkEntries chunks =
      (columnPositionEntries perfect).map (fun p => (label p.1, p.2)))
    (hblocks : chunks.filterMap (Sum.elim some (fun _ => none)) =
      blocks.map (fun b => blockLabelList labelNat b.1 b.2))
    (D : Submodule ℝ (α → ℝ)) (anchor : regular → (α → ℝ) ⧸ D)
    (hind : LinearIndependent ℝ (fun z : regular => D.mkQ (Pi.basisFun ℝ α z)))
    (hline : ∀ b ∈ blocks, ∀ t ∈ Ico b.1 (b.1 + b.2), ∀ ht : labelNat t ∈ regular,
      ∃ c : ℝ, D.mkQ (formalDeparture labelNat coefficient t) = anchor ⟨labelNat t, ht⟩ +
        c • D.mkQ (Pi.basisFun ℝ α (labelNat t)))
    (hnonzero : ∀ b ∈ blocks, ∀ a e z, b.1 ≤ a → a < e → e ≤ b.1 + b.2 →
      (∀ t ∈ Ico a e, labelNat t = z) → (∑ t ∈ Ico a e, coefficient t) ≠ 0)
    (hsize : 2 * (blocks.map Prod.snd).sum ≤ N)
    (hO : omittedPieceCount (columnChunkPieces (fun z => decide (z ∉ regular)) chunks) ≤ O)
    (hI : ((columnPositionEntries perfect).filter (fun a => !a.2)).length ≤ I) :
    ∃ code : ColumnDecoderCode N
        (indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks).length O I,
      decodeColumnPrefixPattern hn code = fun i j => decide (label i = label j) := by
  classical
  by_cases hR : regular.Nonempty
  · let base : regular := ⟨hR.choose, hR.choose_spec⟩
    let rename : α → regular := fun z => if hz : z ∈ regular then ⟨z, hz⟩ else base
    have hrename (z : α) (hz : z ∈ regular) : rename z = ⟨z, hz⟩ := by
      simp only [rename, dite_eq_left hz]
    have hname : ∀ z, decide (z ∉ regular) = false → (rename z : α) = z := by
      intro z hz
      have hr : z ∈ regular := by simpa using hz
      rw [hrename z hr]
    have hl : ∀ b ∈ blocks, ∀ t ∈ Ico b.1 (b.1 + b.2), decide (labelNat t ∉ regular) = false →
        ∃ c : ℝ, D.mkQ (formalDeparture labelNat coefficient t) = anchor (rename (labelNat t)) +
          c • D.mkQ (Pi.basisFun ℝ α (rename (labelNat t))) := by
      intro b hb t ht hr
      have hm : labelNat t ∈ regular := by simpa using hr
      simpa only [hrename _ hm] using hline b hb t ht hm
    obtain ⟨number, pathCode, hbound, hinj, hdecode⟩ := indexed_block_family_numbering D anchor
      (fun z : regular => (z : α)) rename labelNat coefficient (fun z => decide (z ∉ regular))
      blocks hind hname hl hnonzero hsize
    obtain ⟨code, _, hp⟩ := column_code_from_regular_forest hN hn label perfect regular number
      (fun z => number (rename z)) (fun z hz => congrArg number (hrename z hz))
      labelNat chunks blocks hentries hblocks pathCode hbound hinj hdecode hO hI
    exact ⟨code, hp⟩
  · have hno (z : α) : z ∉ regular := fun hz => hR ⟨z, hz⟩
    have hs := indexedRegularSegments_eq_nil labelNat (fun z => decide (z ∉ regular)) blocks
      (fun z => by simp [hno z])
    let number : regular → ℕ := fun z => False.elim (hno z z.property)
    let pathCode : ForestPathData.Code N
        (indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks).length := by
      rw [hs]
      exact emptyForestPathCode N
    have hbound : ∀ segment ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
        ∀ p ∈ segment, (0 : ℕ) < N := by simp only [hs, List.not_mem_nil, false_implies, implies_true]
    have hinj : ∀ segment ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
        ∀ p ∈ segment,
        ∀ other ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
        ∀ q ∈ other, (0 : ℕ) = 0 → p.2 = q.2 := by
      simp only [hs, List.not_mem_nil, false_implies, implies_true]
    have hd : List.ofFn (fun i => evenEntries (decodeForestPaths pathCode i)) =
        (indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks).map
          (fun segment => segment.map (fun _ => (0 : ℕ))) := by
      have hl : (indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks).length = 0 := by rw [hs]; rfl
      exact List.eq_nil_of_length_eq_zero (by simp only [List.length_ofFn, hl]) |>.trans (by rw [hs]; rfl)
    obtain ⟨code, _, hp⟩ := column_code_from_regular_forest hN hn label perfect regular number
      (fun _ => 0) (fun z hz => (hno z hz).elim)
      labelNat chunks blocks hentries hblocks pathCode hbound hinj hd hO hI
    exact ⟨code, hp⟩

end TwoPointCorrelations

end OAI
