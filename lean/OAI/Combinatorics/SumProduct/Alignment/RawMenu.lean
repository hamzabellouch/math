import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.MenuLiteral01
import OAI.Geometry.NilpotentCharts.FilteredBasis
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
noncomputable section
open scoped Manifold ContDiff Topology
open Function Set Manifold
noncomputable section
open Function Set Topology
noncomputable section
open Set Function Topology
open scoped Topology
noncomputable section
open Set Function Topology
open scoped Topology
noncomputable section
open Set Function Topology
open scoped Topology
noncomputable section
open Set Function Topology
open scoped Topology commutatorElement
noncomputable section
open Set Function Topology
open scoped Topology
noncomputable section
open Set Function Topology
noncomputable section
open Set Function Topology
open scoped Topology
noncomputable section
open Set Function
noncomputable section
open Set Function Topology Manifold
open scoped Manifold ContDiff Topology
noncomputable section
open Set Function Topology
open scoped Topology
noncomputable section
open Set Function Topology Manifold
open scoped Manifold ContDiff Topology
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
open scoped Manifold ContDiff Topology
open Function Set Manifold
open scoped BigOperators
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Manifold ContDiff Topology
open scoped Manifold ContDiff Topology
noncomputable section
open scoped commutatorElement
noncomputable section
open Filter Topology
noncomputable section
open Set Function Topology
open scoped Pointwise
noncomputable section
open Set Function Topology
open scoped commutatorElement Topology
namespace SourceRawMenu
open MeasureTheory Filter SourceAdmissible SourceBlocks SourceMenuAlignment
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.AlignmentScales
open scoped Manifold ContDiff Topology NNReal BoundedContinuousFunction

 

structure Menu (s : ℕ) where
  size : ℕ
  dimension : Fin size → ℕ
  G : Fin size → Type
  [group : ∀ i, Group (G i)]
  [topology : ∀ i, TopologicalSpace (G i)]
  [charted : ∀ i, ChartedSpace (EuclideanSpace ℝ (Fin (dimension i))) (G i)]
  [lie : ∀ i, LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin (dimension i))) ∞ (G i)]
  [hausdorff : ∀ i, T2Space (G i)]
  [secondCountable : ∀ i, SecondCountableTopology (G i)]
  [connected : ∀ i, ConnectedSpace (G i)]
  [simplyConnected : ∀ i, SimplyConnectedSpace (G i)]
  Γ : ∀ i, Subgroup (G i)
  [discrete : ∀ i, DiscreteTopology (Γ i)]
  [cocompact : ∀ i, CompactSpace (G i ⧸ Γ i)]
  nilpotent : ∀ i, (⊤ : Subgroup (G i)).lowerCentralSeries s = ⊥
  metric : ∀ i, MetricSpace (G i ⧸ Γ i)
  compatible : ∀ i, QuotientGroup.instTopologicalSpace (Γ i) =
    (metric i).toUniformSpace.toTopologicalSpace

attribute [instance] Menu.group Menu.topology Menu.charted Menu.lie Menu.hausdorff
  Menu.secondCountable Menu.connected Menu.simplyConnected Menu.discrete Menu.cocompact

 

structure CosetPiece {s : ℕ} (F : Menu s) (K : ℝ≥0) where
  index : Fin F.size
  g : F.G index
  x : F.G index ⧸ F.Γ index
  obs : (F.G index ⧸ F.Γ index) →ᵇ ℝ
  lip : letI : MetricSpace (F.G index ⧸ F.Γ index) :=
    (F.metric index).replaceTopology (F.compatible index)
    LipschitzWith K obs
  range : ∀ z, obs z ∈ Set.Icc (0:ℝ) 1

variable {s a r : ℕ}
def CosetPiece.eval {F : Menu s} {K : ℝ≥0} (P : CosetPiece F K) (k : ℤ) : ℝ :=
  P.obs (P.g^k • P.x)

 

structure ModelsSystem (A : Parameters a) (vs : Finset ℚ) (r : ℕ) (F : Menu s) where
  model : ℕ → Models a r
  K : ℝ≥0
  piece : ℕ → Block a → ∀ (v : ℚ), v ∈ vs →
    Fin r → ℤ → ℤ → CosetPiece F K
  represents : ∀ N B v hv c k,
    model N B v c k =
      (piece N B v hv c (k/(A.H N B.1 : ℤ)) (k%(A.M N : ℤ))).eval
        ((k-k%(A.M N : ℤ))/(A.M N : ℤ))

 

def Alignment : Prop :=
  ∀ a r s : ℕ, ∃ (bs : Finset (Scale a)) (vs : Finset ℚ) (δ : ℝ),
    0 < δ ∧
    (∀ b ∈ bs, ∀ j, 0 < b j) ∧ (∀ v ∈ vs, 0 < v) ∧
    (∀ b ∈ bs, ∀ B : Block a, blockProduct b B.set ∈ vs) ∧
    ∀ (A : Parameters a) (F : Menu s) (S : ModelsSystem A vs r F)
      (μ : ℕ → Measure (Fin a → ℕ)),
      (∀ N (hX : ∀ i, 4*primorial (N+1) ≤ A.X N i), μ N = A.law N hX) →
      ∀ τ : ℝ, 0 < τ →
      δ ≤ Filter.liminf (fun N => (μ N).real (event bs (S.model N) (A.ht N) τ)) atTop
end SourceRawMenu
namespace SourceRawMenu
open scoped Manifold ContDiff Topology NNReal BoundedContinuousFunction
variable {s : ℕ}

 

def Menu.toCharted (F : Menu s) : SourceChartedMenu.Menu s where
  size := F.size
  G := F.G
  Γ := F.Γ
  topGroup := fun i => topologicalGroup_of_lieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin (F.dimension i))) ∞
  chart i := Classical.choice (SourceRawChartGap.rawChartExists s (F.dimension i) (F.G i) (F.Γ i) (F.nilpotent i))
  metric := F.metric
  compatible := F.compatible

variable {F : Menu s} {K : ℝ≥0}
def CosetPiece.toCharted (P : CosetPiece F K) : SourceMenuLiteral.CosetPiece F.toCharted K where
  index := P.index
  g := P.g
  x := P.x
  obs := P.obs
  lip := P.lip
  range := P.range

@[simp] lemma CosetPiece.toCharted_eval (P : CosetPiece F K) (k : ℤ) :
    P.toCharted.eval k = P.eval k := rfl
end SourceRawMenu

namespace SourceRawMenu
open MeasureTheory Filter SourceAdmissible SourceBlocks SourceMenuAlignment
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.AlignmentScales
variable {a r s : ℕ} {A : Parameters a} {vs : Finset ℚ} {F : Menu s}

 

def ModelsSystem.toCharted (S : ModelsSystem A vs r F) :
    SourceMenuLiteral.ModelsSystem A vs r F.toCharted where
  model := S.model
  K := S.K
  piece N B v hv c j l := (S.piece N B v hv c j l).toCharted
  represents := S.represents

 

theorem alignment : Alignment := by
  intro a r s
  obtain ⟨bs,vs,δ,hδ,hb,hv,hcl,h⟩ := SourceMenuLiteral.charted_finite_menu_alignment a r s
  refine ⟨bs,vs,δ,hδ,hb,hv,hcl,?_⟩
  intro A F S μ hμ τ hτ
  exact h A F.toCharted S.toCharted μ hμ τ hτ
end SourceRawMenu

theorem raw_alignment_reference : SourceRawMenu.Alignment := SourceRawMenu.alignment

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
end
end
end
end
end
end

end OAI
