import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.Blocks02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Topology
noncomputable section
open scoped BigOperators Topology BoundedContinuousFunction
noncomputable section
open scoped BigOperators
open MeasureTheory Filter Function
noncomputable section
open scoped BigOperators
noncomputable section
open Filter MeasureTheory
open scoped Topology BoundedContinuousFunction NNReal
noncomputable section
open scoped Topology BigOperators
noncomputable section
open scoped Topology BigOperators commutatorElement
noncomputable section
open scoped Topology BoundedContinuousFunction NNReal
noncomputable section
open scoped BigOperators
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction NNReal
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction NNReal
noncomputable section
open scoped Topology BigOperators
noncomputable section
open scoped Topology BoundedContinuousFunction NNReal BigOperators
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction NNReal
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction NNReal
namespace SourceMenuLiteral
open SourceProductChart SourceChartedMenu SourceFiniteMenuModels
open SourceAdmissible SourceBlocks SourceMenuAlignment SourcePivotPaths
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.AlignmentScales
variable {a s r s' : ℕ}

 
structure CosetPiece (F : Menu s) (K : ℝ≥0) where
  index : Fin F.size
  g : F.G index
  x : F.G index ⧸ F.Γ index
  obs : (F.G index ⧸ F.Γ index) →ᵇ ℝ
  lip : letI : MetricSpace (F.G index ⧸ F.Γ index) :=
    (F.metric index).replaceTopology (F.compatible index)
    LipschitzWith K obs
  range : ∀ z, obs z ∈ Set.Icc (0:ℝ) 1

variable {F : Menu s} {K : ℝ≥0}
def CosetPiece.eval (P : CosetPiece F K) (k : ℤ) : ℝ := P.obs (P.g^k • P.x)

def CosetPiece.lift (P : CosetPiece F K) : Piece F K where
  index := P.index
  g := P.g
  x := P.x.out
  obs := P.obs
  lip := P.lip
  range := P.range

lemma CosetPiece.lift_eval (P : CosetPiece F K) (k : ℤ) : P.lift.eval k = P.eval k := by
  change P.obs (P.g^k • (QuotientGroup.mk P.x.out : F.G P.index ⧸ F.Γ P.index)) = _
  rw [show (QuotientGroup.mk P.x.out : F.G P.index ⧸ F.Γ P.index)=P.x from Quotient.out_eq P.x]
  rfl

 

def raiseChart {G : Type} [Group G] [TopologicalSpace G] {Γ : Subgroup G}
    (C : Chart s G Γ) (h : s ≤ s') : Chart s' G Γ :=
  { C with
    step := by
      refine le_antisymm ?_ bot_le
      calc C.filtration.level (s'+1) ≤ C.filtration.level (s+1) :=
             C.filtration.antitone (Nat.add_le_add_right h 1)
           _ = ⊥ := C.step }

def raiseMenu (F : Menu s) (h : s ≤ s') : Menu s' :=
  { F with chart := fun i => raiseChart (F.chart i) h }

def CosetPiece.raise (P : CosetPiece F K) (h : s ≤ s') : CosetPiece (raiseMenu F h) K :=
  { P with }

 

structure ModelsSystem (A : Parameters a) (vs : Finset ℚ) (r : ℕ) (F : Menu s) where
  model : ℕ → Models a r
  K : ℝ≥0
  piece : ℕ → Block a → ∀ (v : ℚ), v ∈ vs →
    Fin r → ℤ → ℤ → CosetPiece F K
  represents : ∀ N B v hv c k,
    model N B v c k =
      (piece N B v hv c (k/(A.H N B.1 : ℤ)) (k%(A.M N : ℤ))).eval
        ((k-k%(A.M N : ℤ))/(A.M N : ℤ))

variable {A : Parameters a} {vs : Finset ℚ} (S : ModelsSystem A vs r F)

def ModelsSystem.lift : System A vs r F where
  model := S.model
  K := S.K
  piece N B v hv c j l := (S.piece N B v hv c j l).lift
  represents := by
    intro N B v hv c k
    rw [CosetPiece.lift_eval]
    exact S.represents N B v hv c k

def ModelsSystem.raise (h : s ≤ s') : ModelsSystem A vs r (raiseMenu F h) where
  model := S.model
  K := S.K
  piece N B v hv c j l := (S.piece N B v hv c j l).raise h
  represents := S.represents

 

theorem charted_finite_menu_alignment (a r s : ℕ) :
    ∃ (bs : Finset (Scale a)) (vs : Finset ℚ) (δ : ℝ),
      0 < δ ∧
      (∀ b ∈ bs, ∀ j, 0 < b j) ∧ (∀ v ∈ vs, 0 < v) ∧
      (∀ b ∈ bs, ∀ B : Block a, blockProduct b B.set ∈ vs) ∧
      ∀ (A : Parameters a) (F : Menu s) (S : ModelsSystem A vs r F)
        (μ : ℕ → Measure (Fin a → ℕ)),
        (∀ N (hX : ∀ i, 4*primorial (N+1) ≤ A.X N i), μ N = A.law N hX) →
        ∀ τ : ℝ, 0 < τ →
        δ ≤ Filter.liminf (fun N => (μ N).real (event bs (S.model N) (A.ht N) τ)) atTop := by
  let t := max 1 s
  have ht : 1 ≤ t := le_max_left _ _
  have hs : s ≤ t := le_max_right _ _
  refine ⟨tuples t r ht,values t r ht,delta t r ht (pivots a),
    delta_pos t r ht _,tuples_pos t r ht,values_pos t r ht,closure t r ht,?_⟩
  intro A F S μ hμ τ hτ
  exact menu_alignment_liminf t r ht A (raiseMenu F hs) (S.raise hs).lift μ hμ τ hτ

end SourceMenuLiteral

 

 

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
