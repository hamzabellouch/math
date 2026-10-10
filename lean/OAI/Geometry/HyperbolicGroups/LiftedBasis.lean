import Mathlib
import OAI.Geometry.HyperbolicGroups.LiftedDiagramSampling

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
universe u v

/-- One (unoriented) elementary top triangle per actual macro edge. The finite
vertex numbering only chooses signs; it does not identify different edges. -/
abbrev MacroCell := {e : Sym2 MacroGraph.Vertex // e ∈ MacroGraph.graph.edgeSet}

def macroCell (e : MacroGraph.graph.Dart) : MacroCell := ⟨e.edge,e.edge_mem⟩
lemma macroCell_symm (e : MacroGraph.graph.Dart) : macroCell e.symm = macroCell e := by
  apply Subtype.ext
  exact e.edge_symm

def macroOrientation (e : MacroGraph.graph.Dart) : ℤ :=
  if Fintype.equivFin MacroGraph.Vertex e.fst < Fintype.equivFin MacroGraph.Vertex e.snd
    then 1 else -1

lemma macroOrientation_symm (e : MacroGraph.graph.Dart) :
    macroOrientation e.symm = -macroOrientation e := by
  have hne : Fintype.equivFin MacroGraph.Vertex e.fst ≠ Fintype.equivFin MacroGraph.Vertex e.snd :=
    fun h => e.fst_ne_snd ((Fintype.equivFin _).injective h)
  change (if Fintype.equivFin MacroGraph.Vertex e.snd < Fintype.equivFin MacroGraph.Vertex e.fst
    then (1:ℤ) else -1) = - (if Fintype.equivFin MacroGraph.Vertex e.fst <
      Fintype.equivFin MacroGraph.Vertex e.snd then 1 else -1)
  rcases lt_or_gt_of_ne hne with h | h
  · rw [ite_eq_left h,ite_eq_right (not_lt_of_ge h.le)]
  · rw [ite_eq_left h,ite_eq_right (not_lt_of_ge h.le)]; norm_num

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool) (G : Type v)

/-- Integral chains with independent coordinates for every deck translate of
an elementary top triangle, fan triangle, square, or six-cell. No topological
realization or equation on these chains is part of the definition. -/
abbrev LiftedCellularChain := (G × ((Top n w × MacroCell) ⊕ FrozenCell n w d)) →₀ ℤ

def liftedTopBasis (g : G) (a : Top n w) (e : MacroGraph.graph.Dart) :
    LiftedCellularChain n w d G :=
  Finsupp.single (g,Sum.inl (a,macroCell e)) (macroOrientation e)

lemma liftedTopBasis_symm (g : G) (a : Top n w) (e : MacroGraph.graph.Dart) :
    liftedTopBasis n w d G g a e.symm = -liftedTopBasis n w d G g a e := by
  simp only [liftedTopBasis,macroCell_symm,macroOrientation_symm,Finsupp.single_neg]

def liftedFrozenBasis (g : G) (a : FrozenCell n w d) : LiftedCellularChain n w d G :=
  Finsupp.single (g,Sum.inr a) 1

variable [Group G] (voltage : Dart n w → G)
  (hv : ∀ e, voltage (rev n w e) = (voltage e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => voltage (side n w d a i))).prod = 1)

def integralLiftedTarget := liftedWalkTarget n w d voltage hv hcell
  (liftedTopBasis n w d G) (liftedTopBasis_symm n w d G) (liftedFrozenBasis n w d G)

def integralLiftedFrozenTarget := liftedFrozenTarget n w d voltage hv hcell
  (liftedTopBasis n w d G) (liftedTopBasis_symm n w d G) (liftedFrozenBasis n w d G)

/-- The entire signed integral lifted cell vector vanishes, not just a scalar
augmentation. -/
theorem uniform_integral_lifted_chain_zero {α β δ : ℝ}
    (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (n : ℕ)
      (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
      (d : (Fin 6 → Alphabet n) → Bool),
      Occurrences.GoodUpTo M α β δ (Sum.elim w d) →
      ∀ (G : Type v) [Group G] (voltage : Dart n w → G)
        (hv : ∀ e, voltage (rev n w e) = (voltage e)⁻¹)
        (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => voltage (side n w d a i))).prod = 1)
        (P : WalkPicture.{u} (integralLiftedTarget n w d G voltage hv hcell)),
        P.FrozenMapped (integralLiftedFrozenTarget n w d G voltage hv hcell) → P.chain = 0 := by
  obtain ⟨M,hM,hh⟩ := uniform_actual_lifted_chain_zero.{u,v,v} ha hb hd
  refine ⟨M,hM,?_⟩
  intro n w d hgood G _ voltage hv hcell P hm
  exact hh n w d hgood G (LiftedCellularChain n w d G) voltage hv hcell
    (liftedTopBasis n w d G) (liftedTopBasis_symm n w d G) (liftedFrozenBasis n w d G) P hm

/-- The same final sampled arrays have the integral lifted-chain conclusion,
with no additional event or a posteriori choice of presentation. -/
theorem finalDiagramStage_integral_chain_zero (m : ℕ)
    (G : Type) [Group G]
    (voltage : Dart (finalDiagramStage m).size (finalDiagramStage m).master → G)
    (hv : ∀ e, voltage (rev (finalDiagramStage m).size (finalDiagramStage m).master e) = (voltage e)⁻¹)
    (hcell : ∀ a : Cell (finalDiagramStage m).size (finalDiagramStage m).master (finalDiagramStage m).six,
      (List.ofFn (fun i => voltage (side (finalDiagramStage m).size (finalDiagramStage m).master
        (finalDiagramStage m).six a i))).prod = 1)
    (P : WalkPicture.{0} (integralLiftedTarget (finalDiagramStage m).size (finalDiagramStage m).master
      (finalDiagramStage m).six G voltage hv hcell))
    (hm : P.FrozenMapped (integralLiftedFrozenTarget (finalDiagramStage m).size (finalDiagramStage m).master
      (finalDiagramStage m).six G voltage hv hcell)) : P.chain = 0 :=
  finalDiagramStage_lifted_chain_zero m G _ voltage hv hcell _
    (liftedTopBasis_symm _ _ _ G) _ P hm

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
