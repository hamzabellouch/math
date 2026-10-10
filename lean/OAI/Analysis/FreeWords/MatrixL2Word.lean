import Mathlib
import OAI.Analysis.FreeWords.MatrixL2Closure
import OAI.Analysis.FreeWords.MatrixL2WordDefinitions

namespace OAI

noncomputable section

namespace KKMatrixL2

open KKTraceTransfer Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {I : Type*} {M : VonNeumannAlgebra H} {n : ℕ}

theorem EntryBound.const (a : MatrixAlg M n) : EntryBound (fun _ : I => a) := by
  refine ⟨∑ i,∑ j,‖a i j‖,by positivity,?_⟩
  intro t i j
  exact (Finset.single_le_sum (fun k _ => norm_nonneg (a i k)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => norm_nonneg (a k l))) (Finset.mem_univ i))

theorem EntryBound.mul {f g : I → MatrixAlg M n} (hf : EntryBound f) (hg : EntryBound g) :
    EntryBound (fun t => f t*g t) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  refine ⟨(n:ℝ)*(C*D),by positivity,?_⟩
  intro t i j
  change ‖∑ k,f t i k*g t k j‖ ≤ _
  calc
    _ ≤ ∑ k,‖f t i k*g t k j‖ := norm_sum_le _ _
    _ ≤ ∑ k:Fin n,C*D := Finset.sum_le_sum (fun k _ =>
      (norm_mul_le _ _).trans (mul_le_mul (hf t i k) (hg t k j) (norm_nonneg _) hC))
    _ = _ := by simp

theorem EntryBound.list_prod (w : List (I → MatrixAlg M n))
    (hw : ∀ f ∈ w, EntryBound f) : EntryBound (fun t => (w.map fun f => f t).prod) := by
  induction w with
  | nil => exact EntryBound.const 1
  | cons f w ih =>
    exact (hw f List.mem_cons_self).mul (ih (fun g hg => hw g (List.mem_cons_of_mem _ hg)))

theorem EntryBound.pair_list_prod
    (w : List ((I → MatrixAlg M n) × (I → MatrixAlg M n)))
    (hw : ∀ z ∈ w, EntryBound z.1) :
    EntryBound (I := I) (M := M) (n := n) (fun t => (w.map fun z => z.1 t).prod) := by
  induction w with
  | nil => exact EntryBound.const 1
  | cons z w ih =>
    exact (hw z List.mem_cons_self).mul (ih (fun g hg => hw g (List.mem_cons_of_mem _ hg)))

lemma matrix_l2_asymp_mul_bounded {l : Filter I}
    (τ : FaithfulNormalTrace M) (f f' g g' : I → MatrixAlg M n)
    (hC : EntryBound f') (hD : EntryBound g)
    (hf : ∀ i j, Tendsto (fun t => traceNorm τ (f t i j-f' t i j)) l (𝓝 0))
    (hg : ∀ i j, Tendsto (fun t => traceNorm τ ((g t-g' t) i j)) l (𝓝 0)) :
    ∀ i j, Tendsto (fun t => traceNorm τ ((f t*g t-f' t*g' t) i j)) l (𝓝 0) := by
  obtain ⟨C,_,hC⟩ := hC
  obtain ⟨D,_,hD⟩ := hD
  exact matrix_l2_asymp_mul M τ n f f' g g' C D hC hD hf (fun i j => hg i j)

lemma matrix_l2_word_cons {l : Filter I}
    (τ : FaithfulNormalTrace M)
    (z : (I → MatrixAlg M n) × (I → MatrixAlg M n))
    (w : List ((I → MatrixAlg M n) × (I → MatrixAlg M n)))
    (hz2 : EntryBound z.2)
    (hw1 : EntryBound (I := I) (M := M) (n := n) (fun t => (w.map fun v => v.1 t).prod))
    (hz : ∀ i j, Tendsto (fun t => traceNorm τ (z.1 t i j-z.2 t i j)) l (𝓝 0))
    (hw : ∀ i j, Tendsto (fun t => traceNorm τ
      (((w.map fun v => v.1 t).prod-(w.map fun v => v.2 t).prod) i j)) l (𝓝 0)) :
    ∀ i j, Tendsto (fun t => traceNorm τ
      ((((z::w).map fun v => v.1 t).prod-((z::w).map fun v => v.2 t).prod) i j)) l (𝓝 0) := by
  let g : I → MatrixAlg M n := fun t => (w.map fun v => v.1 t).prod
  let g' : I → MatrixAlg M n := fun t => (w.map fun v => v.2 t).prod
  have hD : EntryBound g := hw1
  have hg : ∀ i j, Tendsto (fun t => traceNorm τ ((g t-g' t) i j)) l (𝓝 0) := hw
  intro i j
  have ht := matrix_l2_asymp_mul_bounded (I := I) (M := M) (n := n) (l := l)
    τ z.1 z.2 g g' hz2 hD hz hg i j
  exact ht

theorem matrix_l2_asymp_word {I : Type*} {l : Filter I}
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M) (n : ℕ)
    (w : List ((I → MatrixAlg M n) × (I → MatrixAlg M n)))
    (hb : ∀ z ∈ w, EntryBound z.1 ∧ EntryBound z.2)
    (hz : ∀ z ∈ w, ∀ i j, Tendsto (fun t => traceNorm τ (z.1 t i j-z.2 t i j)) l (𝓝 0)) :
    ∀ i j, Tendsto (fun t => traceNorm τ
      (((w.map fun z => z.1 t).prod-(w.map fun z => z.2 t).prod) i j)) l (𝓝 0) := by
  induction w with
  | nil =>
    intro i j
    simpa [traceNorm] using (tendsto_const_nhds (x := (0:ℝ)) (f := l))
  | cons z w ih =>
    exact matrix_l2_word_cons (I := I) (M := M) (n := n) (l := l) τ z w (hb z List.mem_cons_self).2
      (EntryBound.pair_list_prod w (fun v hv => (hb v (List.mem_cons_of_mem _ hv)).1))
      (hz z List.mem_cons_self)
      (ih (fun v hv => hb v (List.mem_cons_of_mem _ hv))
        (fun v hv => hz v (List.mem_cons_of_mem _ hv)))

open KKUltraTrace KKProjectionSupport

open scoped InnerProductSpace

local instance matrixL2WordPartialOrder : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance matrixL2WordPreorder : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance matrixL2WordLE : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance matrixL2WordStarOrderedRing : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

end

end KKMatrixL2
end

end OAI
