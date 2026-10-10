import OAI.Analysis.KadisonKastler.MeasurableProjectionFrame
import OAI.Analysis.KadisonKastler.MeasurableNatEnumeration

namespace OAI

/-! # Hilbert coordinates from measurable projection frames

The nonzero Gram-Schmidt vectors form a Hilbert basis of the actual range.
Their ascending enumeration is measurable before restricting to a rank stratum.
-/

namespace KadisonKastler

open MeasureTheory InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
private theorem frame_mem_range (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤) (n : ℕ) :
    gramSchmidtNormed ℂ (fun i => P (b i)) n ∈ P.range := by
  rw [← projectionFrame_total_of_total P hP b hb]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)

/-- The nonzero projected frame, as vectors of the genuine closed range. -/
def projectionRangeFrame (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)
    (i : {n // gramSchmidtNormed ℂ (fun j => P (b j)) n ≠ 0}) : P.range :=
  ⟨gramSchmidtNormed ℂ (fun j => P (b j)) i, frame_mem_range P hP b hb i⟩

omit [CompleteSpace H] in
theorem projectionRangeFrame_orthonormal (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤) :
    Orthonormal ℂ (projectionRangeFrame P hP b hb) := by
  rw [← P.range.subtypeₗᵢ.orthonormal_comp_iff]
  exact gramSchmidtNormed_orthonormal' (fun j => P (b j))

omit [CompleteSpace H] in
theorem projectionRangeFrame_orthogonal_eq_bot (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤) :
    (Submodule.span ℂ (Set.range (projectionRangeFrame P hP b hb)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  change z = 0
  apply Subtype.ext
  have hzero (n : ℕ) : inner ℂ (gramSchmidtNormed ℂ (fun j => P (b j)) n) (z : H) = 0 := by
    by_cases hn : gramSchmidtNormed ℂ (fun j => P (b j)) n = 0
    · simp only [hn, inner_zero_left]
    · have hmem : projectionRangeFrame P hP b hb ⟨n, hn⟩ ∈
          Submodule.span ℂ (Set.range (projectionRangeFrame P hP b hb)) :=
        Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩
      have hi : inner ℂ (projectionRangeFrame P hP b hb ⟨n, hn⟩) z = 0 :=
        Submodule.inner_right_of_mem_orthogonal hmem hz
      exact hi
  have ho : (z : H) ∈
      (Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ (fun j => P (b j)))))ᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨n, rfl⟩ := hy; exact hzero n
    | zero => simp
    | add y w _ _ hy hw => simp only [inner_add_left, hy, hw, add_zero]
    | smul c y _ hy => simp only [inner_smul_left, hy, mul_zero]
  have hzorth : (z : H) ∈ P.rangeᗮ := by
    have he : P.rangeᗮ =
        (Submodule.span ℂ (Set.range (gramSchmidtNormed ℂ (fun j => P (b j)))))ᗮ := by
      rw [← projectionFrame_total_of_total P hP b hb, Submodule.orthogonal_closure]
    exact he.symm ▸ ho
  exact inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal z.property hzorth)

/-- Every closed projection range has the basis given by its surviving frame. -/
def projectionRangeHilbertBasis (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤) :
    HilbertBasis {n // gramSchmidtNormed ℂ (fun j => P (b j)) n ≠ 0} ℂ P.range := by
  letI : CompleteSpace P.range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range hP).completeSpace_coe
  exact HilbertBasis.mkOfOrthogonalEqBot (projectionRangeFrame_orthonormal P hP b hb)
    (projectionRangeFrame_orthogonal_eq_bot P hP b hb)

@[simp] theorem projectionRangeHilbertBasis_apply (P : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)
    (i : {n // gramSchmidtNormed ℂ (fun j => P (b j)) n ≠ 0}) :
    projectionRangeHilbertBasis P hP b hb i = projectionRangeFrame P hP b hb i := by
  simp only [projectionRangeHilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

variable {X : Type*} [MeasurableSpace X]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- Ascending enumeration of the nonzero projected frame, with a harmless
library default outside its genuine index range. -/
def enumeratedProjectionFrame (P : X → H →L[ℂ] H) (b : ℕ → H) (x : X) (k : ℕ) : H :=
  measurableProjectionFrame P b x (Nat.nth (fun n => measurableProjectionFrame P b x n ≠ 0) k)

omit [CompleteSpace H] [InnerProductSpace ℂ H] in
theorem measurable_enumeratedSequence (v : X → ℕ → H)
    (hv : ∀ n, Measurable fun x => v x n) (k : ℕ) :
    Measurable fun x => v x (Nat.nth (fun n => v x n ≠ 0) k) := by
  have hp (n : ℕ) : MeasurableSet {x | v x n ≠ 0} :=
    (measurableSet_eq_fun (hv n) (measurable_const : Measurable fun _ : X => (0 : H))).compl
  have hn : Measurable fun x => Nat.nth (fun n => v x n ≠ 0) k :=
    measurable_natNth (fun x n => v x n ≠ 0) hp k
  have he : Measurable fun q : X × ℕ => v q.1 q.2 :=
    measurable_from_prod_countable_left hv
  exact he.comp (measurable_id.prodMk hn)

omit [CompleteSpace H] in
theorem enumeratedProjectionFrame_measurable (P : X → H →L[ℂ] H) (b : ℕ → H)
    (hP : ∀ v : H, Measurable fun x => P x v) (k : ℕ) :
    Measurable fun x => enumeratedProjectionFrame P b x k :=
  measurable_enumeratedSequence (measurableProjectionFrame P b)
    (measurableProjectionFrame_measurable P b hP) k

end

end KadisonKastler

end OAI
