import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ProgramGroundIdentity

namespace OAI

/-! The literal binary-encoded unit-charge output inherits the full
ground-energy interval and validity from the computed node estimates. -/

noncomputable section
open scoped BigOperators Classical NNReal
namespace ContinuumCoulomb.UnitCoulombProgram
open CappedKernelProgram (position)

theorem ground_interval (rho U C K : ℕ) (hrho : 0 < rho) (x : Input)
    (hN : 0 < x.1.1.1.2) (hn : 0 < x.2.1) (hgap : (1:ℚ) ≤ x.2.2.2-x.2.2.1)
    (G : Position → Position) (hG : Function.Injective G) {J : ℝ≥0}
    (hAnti : AntilipschitzWith J G)
    (herror : ∀ l : TransformedGauss.Label,
      ‖position (TransformedGauss.value rho U C K x.1.1.1.1 x.1.1.1.2
        x.1.1.2.1.1 x.1.1.2.1.2 x.1.1.2.2 l.1 l.2)-
        G (gaussLatticePoint (x.1.1.1.2:ℝ)⁻¹ (RationalGaussNodes.index l.1 l.2))‖ ≤
          ((x.1.1.1.1:ℝ)+1)⁻¹)
    (hprecision : 2*(J:ℝ)*((x.1.1.1.1:ℝ)+1)⁻¹ < (x.1.1.1.2:ℝ)⁻¹/3)
    {scale center error roundError : ℝ} (hs : 0 < scale)
    (hfactor : (PhysicalNuclearProgram.factor rho x.1.1.1.2:ℝ)=scale⁻¹)
    (hlo : ((center-error:ℝ):EReal) ≤ formGroundEnergy
      (dilatedNuclei (CenteredGaussLabels.nuclei x.1.2 G hG (by positivity : 0 < (x.1.1.1.2:ℝ)⁻¹))
        scale hs.ne') x.2.1)
    (hhi : formGroundEnergy
      (dilatedNuclei (CenteredGaussLabels.nuclei x.1.2 G hG (by positivity : 0 < (x.1.1.1.2:ℝ)⁻¹))
        scale hs.ne') x.2.1 ≤ ((center+error:ℝ):EReal))
    (hsmall : 32*(scale⁻¹*((x.1.1.1.1:ℝ)+1)⁻¹)*(CenteredGaussLabels.labels x.1.2).length ≤ 1)
    (hbudget : 32*(scale⁻¹*((x.1.1.1.1:ℝ)+1)⁻¹)*(CenteredGaussLabels.labels x.1.2).length*
      (center+error+4*(x.2.1:ℝ)*((CenteredGaussLabels.labels x.1.2).length:ℝ)^2) ≤ roundError) :
    ∃ hx : (value rho U C K x).Valid,
      ((center-error-roundError:ℝ):EReal) ≤ unitGroundEnergy ((value rho U C K x).toData hx) ∧
      unitGroundEnergy ((value rho U C K x).toData hx) ≤ ((center+error+roundError:ℝ):EReal) := by
  have hnodes := TransformedGauss.nodes_nodup rho U C K x.1.1.1.1 hN
    x.1.1.2.1.1 x.1.1.2.1.2 x.1.1.2.2 (CenteredGaussLabels.labels x.1.2)
    (CenteredGaussLabels.labels_nodup x.1.2) G hAnti herror hprecision
  let hx := valid_of_nodes rho U C K x hrho hN hn hnodes hgap
  obtain ⟨hq,hl,hu⟩ := CenteredGaussLabels.numerical_ground_interval x.1.2 rho U C K x.1.1.1.1 hN
    x.1.1.2.1.1 x.1.1.2.1.2 x.1.1.2.2 G hG hAnti herror hprecision hs x.2.1 hlo hhi hsmall hbudget
  refine ⟨hx,?_,?_⟩
  · rw [program_ground_identity rho U C K x hx hs hfactor hq]
    exact hl
  · rw [program_ground_identity rho U C K x hx hs hfactor hq]
    exact hu

end ContinuumCoulomb.UnitCoulombProgram

end

end OAI
