import OAI.Analysis.HyperbolicCones.ConePositive
import OAI.Analysis.HyperbolicCones.ConeContinuity

namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator

namespace Paper256

def ambientResidual (x : Ambient) : Sym 4 := x.1.2 - phiSym x.2 (symInverse x.1.1)

theorem continuousAt_ambientResidual (x : Ambient) (hX : (x.1.1 : Mat 4 ℝ).PosDef) :
    ContinuousAt ambientResidual x := by
  have hfirst : Continuous (fun z : Ambient => z.1.1) := continuous_fst.fst
  have hsecond : Continuous (fun z : Ambient => z.1.2) := continuous_fst.snd
  have hy : Continuous (fun z : Ambient => z.2) := continuous_snd
  have hi : ContinuousAt (fun z : Ambient => symInverse z.1.1) x :=
    (continuousAt_symInverse x.1.1 hX.isUnit).comp
      (f := fun z : Ambient => z.1.1) (x := x) hfirst.continuousAt
  have hp : ContinuousAt (fun z : Ambient => phiSym z.2 (symInverse z.1.1)) x :=
    continuous_phiSym_joint.continuousAt.comp
      (f := fun z : Ambient => (z.2, symInverse z.1.1)) (x := x)
      (hy.continuousAt.prodMk hi)
  exact hsecond.continuousAt.sub hp

theorem isOpen_strict_positive_slice :
    IsOpen {x : Ambient | (x.1.1 : Mat 4 ℝ).PosDef ∧
      (ambientResidual x : Mat 4 ℝ).PosDef} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hf : ContinuousAt (fun z : Ambient => z.1.1) x :=
    (continuous_fst.fst : Continuous (fun z : Ambient => z.1.1)).continuousAt
  have hNX : ∀ᶠ H : Sym 4 in 𝓝 x.1.1, (H : Mat 4 ℝ).PosDef :=
    (isOpen_posDef 4).mem_nhds hx.1
  have hNR : ∀ᶠ H : Sym 4 in 𝓝 (ambientResidual x), (H : Mat 4 ℝ).PosDef :=
    (isOpen_posDef 4).mem_nhds hx.2
  have heX := hf.eventually hNX
  have heR := (continuousAt_ambientResidual x hx.1).eventually hNR
  filter_upwards [heX, heR] with z hz hr
  exact ⟨hz, hr⟩

theorem strict_positive_slice_subset_cone :
    {x : Ambient | (x.1.1 : Mat 4 ℝ).PosDef ∧ (ambientResidual x : Mat 4 ℝ).PosDef} ⊆
      cone := by
  intro x hx
  apply (cone_positive_slice x.1.1 x.1.2 x.2 hx.1).mpr
  exact hx.2.posSemidef

end Paper256

end

end OAI
