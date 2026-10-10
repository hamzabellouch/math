import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PhysicalNuclearProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CenteredGaussEquiv

namespace OAI

/-! The serialized physical nuclei and the analytic finite grid share one
explicit index. This supplies both the exact list identity and the numerical
coordinate error in physical units. -/

noncomputable section
open scoped NNReal
namespace ContinuumCoulomb.NuclearGridCoordinates
open CappedKernelProgram (Triple position)

abbrev Input := PhysicalNuclearProgram.Input
abbrev Index (x : Input) := Fin (CenteredGaussLabels.labels x.2).length

def label (x : Input) (a : Index x) : TransformedGauss.Label :=
  (CenteredGaussLabels.labels x.2).get a

def node (rho U C K : ℕ) (x : Input) (a : Index x) : Triple :=
  TransformedGauss.value rho U C K x.1.1.1 x.1.1.2 x.1.2.1.1 x.1.2.1.2 x.1.2.2
    (label x a).1 (label x a).2

def nucleus (rho U C K : ℕ) (x : Input) (a : Index x) : BinaryPosition :=
  NuclearCoordinateOutput.position
    (PhysicalNuclearProgram.scale (PhysicalNuclearProgram.factor rho x.1.1.2) (node rho U C K x a))

theorem nuclei_eq_ofFn (rho U C K : ℕ) (x : Input) :
    PhysicalNuclearProgram.nuclei rho U C K x = List.ofFn (nucleus rho U C K x) := by
  simp only [PhysicalNuclearProgram.nuclei,PhysicalNuclearProgram.triples,
    TransformedGauss.nodes,NuclearCoordinateOutput.positions,List.map_map]
  let f : TransformedGauss.Label → BinaryPosition := fun l => NuclearCoordinateOutput.position
    (PhysicalNuclearProgram.scale (PhysicalNuclearProgram.factor rho x.1.1.2)
      (TransformedGauss.value rho U C K x.1.1.1 x.1.1.2 x.1.2.1.1 x.1.2.1.2 x.1.2.2 l.1 l.2))
  change (CenteredGaussLabels.labels x.2).map f =
    List.ofFn (fun a => f ((CenteredGaussLabels.labels x.2).get a))
  have h := congrArg (List.map f) (List.ofFn_get (CenteredGaussLabels.labels x.2))
  simpa only [List.map_ofFn,Function.comp_def] using h.symm

theorem physical_coordinate_error (rho U C K : ℕ) (x : Input)
    (hrho : 0 < rho) (hN : 0 < x.1.1.2) (G : Position → Position)
    (herror : ∀ a : Index x,
      ‖position (node rho U C K x a)-
        G (gaussLatticePoint (x.1.1.2:ℝ)⁻¹ (RationalGaussNodes.index (label x a).1 (label x a).2))‖ ≤
          ((x.1.1.1:ℝ)+1)⁻¹) (a : Index x) :
    ‖realPosition (nucleus rho U C K x a).value-
      (PhysicalNuclearProgram.factor rho x.1.1.2:ℝ) •
        G (gaussLatticePoint (x.1.1.2:ℝ)⁻¹ (RationalGaussNodes.index (label x a).1 (label x a).2))‖ ≤
      (PhysicalNuclearProgram.factor rho x.1.1.2:ℝ)*((x.1.1.1:ℝ)+1)⁻¹ := by
  rw [nucleus,NuclearCoordinateOutput.real_position]
  exact PhysicalNuclearProgram.scale_error (PhysicalNuclearProgram.factor_positive hrho hN).le
    _ _ (herror a)

theorem nucleus_position_injective (rho U C K : ℕ) (x : Input)
    (hrho : 0 < rho) (hN : 0 < x.1.1.2) (G : Position → Position)
    {J : ℝ≥0} (hG : AntilipschitzWith J G)
    (herror : ∀ a : Index x,
      ‖position (node rho U C K x a)-
        G (gaussLatticePoint (x.1.1.2:ℝ)⁻¹ (RationalGaussNodes.index (label x a).1 (label x a).2))‖ ≤
          ((x.1.1.1:ℝ)+1)⁻¹)
    (hprecision : 2*(J:ℝ)*((x.1.1.1:ℝ)+1)⁻¹ < (x.1.1.2:ℝ)⁻¹/3) :
    Function.Injective (fun a : Index x => (nucleus rho U C K x a).value) := by
  have hn : Function.Injective (node rho U C K x) :=
    TransformedGauss.value_injective (label x) (CenteredGaussLabels.labels_nodup x.2).injective_get
      rho U C K x.1.1.1 hN x.1.2.1.1 x.1.2.1.2 x.1.2.2 G hG herror hprecision
  intro a b hab
  have hq := NuclearCoordinateOutput.position_value_injective hab
  have hs := PhysicalNuclearProgram.scale_injective
    (PhysicalNuclearProgram.factor_positive hrho hN).ne' hq
  exact hn hs

end ContinuumCoulomb.NuclearGridCoordinates

end

end OAI
