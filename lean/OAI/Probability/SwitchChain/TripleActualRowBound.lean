import OAI.Probability.SwitchChain.TripleCellTransport
import OAI.Probability.SwitchChain.TripleMatrixFinEquiv
import OAI.Probability.SwitchChain.MatrixRowVariance
import OAI.Probability.SwitchChain.CellProjectionTransport
import OAI.Probability.SwitchChain.TripleCellVarianceGluing
import OAI.Probability.SwitchChain.FiniteVarianceEuclidean

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.TripleActualRowBound

open TripleCellTransport TripleInternalEncoding
attribute [local instance] Classical.propDecidable

theorem row_variance_transport {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
    (e : X ≃ Y) (f : I → X → ℝ)
    (h : FiniteVariance.variance (fun y => ∑ i, f i (e.symm y)) ≤
      2 * ∑ i, FiniteVariance.variance (fun y => f i (e.symm y))) :
    FiniteVariance.variance (fun x => ∑ i, f i x) ≤
      2 * ∑ i, FiniteVariance.variance (f i) := by
  have hl := FiniteVariance.variance_equiv e.symm (fun x => ∑ i, f i x)
  have hr (i : I) := FiniteVariance.variance_equiv e.symm (f i)
  rw [hl] at h
  simp_rw [hr] at h
  exact h

theorem full_matrix_row_variance_transport {X C : Type*} [Fintype X] [Fintype C]
    [Nonempty X] (k : C → ℕ) (r : Fin 3 → ℕ)
    (e : X ≃ ForcedColumns.FullMargins k r) (f : Fin 3 → X → ℝ)
    (hf : ∀ i x y, (e x).val i = (e y).val i → f i x = f i y) :
    FiniteVariance.variance (fun x => ∑ i, f i x) ≤
      2 * ∑ i, FiniteVariance.variance (f i) := by
  apply row_variance_transport e f
  apply MatrixRowVariance.row_variance_bound k r ⟨e (Classical.choice inferInstance)⟩
  intro i M N hMN
  apply hf i
  simpa only [e.apply_symm_apply] using hMN

variable {n : ℕ} {d : Fin n → ℕ}
variable (T : Finset (Fin n)) (hT : T.card = 3)

def finiteCellEquiv (G : GraphState n d) : Cell T hT G ≃
    ForcedColumns.FullMargins
      (TripleMatrixFinEquiv.margins
        (internalEdgeCount (internalGraph (splitGraph T hT G)))
        (crossColumn (splitGraph T hT G)))
      (fun i => leftDegree (splitGraph T hT G) i -
        rowOffset (internalEdgeCount (internalGraph (splitGraph T hT G)))) :=
   (matrixEquiv T hT G).trans
    (TripleMatrixFinEquiv.augmentedEquiv
      (internalEdgeCount (internalGraph (splitGraph T hT G)))
      (leftDegree (splitGraph T hT G)) (crossColumn (splitGraph T hT G)))

theorem finiteCell_row_iff (G : GraphState n d) (H K : Cell T hT G) (i : Fin 3) :
    (finiteCellEquiv T hT G H).val i = (finiteCellEquiv T hT G K).val i ↔
      PairResampling.SameFiber (pair T hT i) H.val.val K.val.val := by
  change (TripleMatrixFinEquiv.augmentedEquiv _ _ _ (matrixEquiv T hT G H)).val i =
    (TripleMatrixFinEquiv.augmentedEquiv _ _ _ (matrixEquiv T hT G K)).val i ↔ _
  rw [TripleMatrixFinEquiv.augmented_row_eq_iff]
  exact (sameFiber_iff_matrixRow T hT G H K i).symm

theorem cell_row_variance (G : GraphState n d)
    (f : Fin 3 → Cell T hT G → ℝ)
    (hf : ∀ i H K, PairResampling.SameFiber (pair T hT i) H.val.val K.val.val →
      f i H = f i K) :
    FiniteVariance.variance (fun H => ∑ i, f i H) ≤
      2 * ∑ i, FiniteVariance.variance (f i) := by
  let : Nonempty (Cell T hT G) := ⟨referenceCell T hT G⟩
  apply full_matrix_row_variance_transport _ _ (finiteCellEquiv T hT G) f
  intro i H K hHK
  exact hf i H K ((finiteCell_row_iff T hT G H K i).mp hHK)

def exteriorCellEquiv (G : GraphState n d) :
    {H : GraphState n d // PairResampling.tripleExteriorKey T H =
      PairResampling.tripleExteriorKey T G} ≃ Cell T hT G :=
  outsideCellEquiv T hT G

theorem exterior_row_variance (G : GraphState n d)
    (f : Fin 3 → {H : GraphState n d // PairResampling.tripleExteriorKey T H =
      PairResampling.tripleExteriorKey T G} → ℝ)
    (hf : ∀ i H K, PairResampling.SameFiber (pair T hT i) H.val.val K.val.val →
      f i H = f i K) :
    FiniteVariance.variance (fun H => ∑ i, f i H) ≤
      2 * ∑ i, FiniteVariance.variance (f i) := by
  let e := exteriorCellEquiv T hT G
  apply row_variance_transport e f
  apply cell_row_variance T hT G
  intro i H K hHK
  exact hf i (e.symm H) (e.symm K) hHK

theorem sum_expectation_exterior (a : Finset (Fin n)) (ha : a ⊆ T)
    (k : SimpleGraph {v : Fin n // v ∉ T}) (f : PairResampling.StateSpace n d) :
    (∑ H : {H : GraphState n d // PairResampling.tripleExteriorKey T H = k},
      PairResampling.expectation n d a f H.val) =
    ∑ H : {H : GraphState n d // PairResampling.tripleExteriorKey T H = k}, f H.val := by
  let C := fun H : GraphState n d => PairResampling.tripleExteriorKey T H = k
  have hc : ∀ G H : GraphState n d, PairResampling.SameFiber a G.val H.val →
      (C G ↔ C H) := by
    intro G H h
    dsimp [C]
    rw [PairResampling.tripleExteriorKey_eq_of_sameFiber ha G H h]
  have he := CellProjectionTransport.graph_expectation_restrict a C hc f
  have hs := CellProjectionTransport.sum_expectation
    (CellProjectionTransport.restrictedSetoid (CellProjectionTransport.graphSetoid a) C)
    (CellProjectionTransport.restrict C f)
  rw [← he] at hs
  exact hs

theorem exterior_projection_norm_centered (G : GraphState n d)
    (f : PairResampling.StateSpace n d)
    (hf : (∑ H : {H : GraphState n d // PairResampling.tripleExteriorKey T H =
      PairResampling.tripleExteriorKey T G}, f H.val) = 0) :
    ‖∑ i : Fin 3, CellVarianceGluing.restrict (PairResampling.tripleExteriorKey T)
      (PairResampling.tripleExteriorKey T G)
      (PairResampling.expectation n d (pair T hT i) f)‖ ^ 2 ≤
    2 * ∑ i : Fin 3, ‖CellVarianceGluing.restrict (PairResampling.tripleExteriorKey T)
      (PairResampling.tripleExteriorKey T G)
      (PairResampling.expectation n d (pair T hT i) f)‖ ^ 2 := by
  let : Nonempty {H : GraphState n d // PairResampling.tripleExteriorKey T H =
      PairResampling.tripleExteriorKey T G} := ⟨⟨G, rfl⟩⟩
  apply FiniteVariance.norm_sum_sq_le_of_variance_bound
  · intro i
    unfold FixedBlockMarginal.average
    change (∑ H : {H : GraphState n d // PairResampling.tripleExteriorKey T H =
      PairResampling.tripleExteriorKey T G},
      PairResampling.expectation n d (pair T hT i) f H.val) / _ = 0
    rw [sum_expectation_exterior T (pair T hT i)
      (Finset.mem_powersetCard.mp (pair_mem_powersetCard T hT i)).1, hf, zero_div]
  · apply exterior_row_variance T hT G
    intro i H K hHK
    exact PairResampling.expectation_mem (pair T hT i) f H.val K.val hHK

include hT in

theorem triple_square (f : PairResampling.StateSpace n d) :
    ⟪f, ∑ a ∈ T.powersetCard 2, PairResampling.fluctuation n d a f⟫ ≤
      ‖∑ a ∈ T.powersetCard 2, PairResampling.fluctuation n d a f‖ ^ 2 := by
  apply PairResampling.vertex_triple_square_of_exterior_cellwise_row_variance T hT
  intro k g
  by_cases hk : Nonempty {H : GraphState n d // PairResampling.tripleExteriorKey T H = k}
  · obtain ⟨⟨G, hG⟩⟩ := hk
    subst k
    have hz := CellVarianceGluing.sum_restrict_sub_center_eq_zero
      (PairResampling.tripleExteriorKey T) (PairResampling.tripleExteriorKey T G) g
    have h := exterior_projection_norm_centered T hT G
      (g - CellVarianceGluing.center (PairResampling.tripleExteriorKey T) g) hz
    let y : T.powersetCard 2 → _ := fun a =>
      CellVarianceGluing.restrict (PairResampling.tripleExteriorKey T)
        (PairResampling.tripleExteriorKey T G)
        (PairResampling.expectation n d a.val
          (g - CellVarianceGluing.center (PairResampling.tripleExteriorKey T) g))
    change ‖∑ i : Fin 3, y (pairEquiv T hT i)‖ ^ 2 ≤
      2 * ∑ i : Fin 3, ‖y (pairEquiv T hT i)‖ ^ 2 at h
    rw [(pairEquiv T hT).sum_comp y,
      (pairEquiv T hT).sum_comp (fun a => ‖y a‖ ^ 2)] at h
    exact h
  · have hz (a : T.powersetCard 2) :
        CellVarianceGluing.restrict (PairResampling.tripleExteriorKey T) k
          (PairResampling.expectation n d a.val
            (g - CellVarianceGluing.center (PairResampling.tripleExteriorKey T) g)) = 0 := by
      ext H
      exact False.elim (hk ⟨H⟩)
    simp only [hz, Finset.sum_const_zero, norm_zero, zero_pow (by omega : 2 ≠ 0),
      mul_zero, le_refl]

end Problem315.TripleActualRowBound

end

end OAI
