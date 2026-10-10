import OAI.Analysis.HyperbolicCones.ConePositive
import OAI.Analysis.HyperbolicCones.ConeContinuity

namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator

namespace Paper256

theorem basePoint_mem_interior_cone : basePoint ∈ interior cone := by
  let R : Ambient → Sym 4 := fun x => x.1.2 - phiSym x.2 (symInverse x.1.1)
  have hX : Continuous (fun x : Ambient => x.1.1) := continuous_fst.fst
  have hZ : Continuous (fun x : Ambient => x.1.2) := continuous_fst.snd
  have hY : Continuous (fun x : Ambient => x.2) := continuous_snd
  have hInv : ContinuousAt (fun x : Ambient => symInverse x.1.1) basePoint :=
    (continuousAt_symInverse (1 : Sym 4) Matrix.PosDef.one.isUnit).comp
      (f := fun x : Ambient => x.1.1) (x := basePoint) hX.continuousAt
  have hPhi : ContinuousAt (fun x : Ambient => phiSym x.2 (symInverse x.1.1)) basePoint :=
    continuous_phiSym_joint.continuousAt.comp
      (f := fun x : Ambient => (x.2, symInverse x.1.1)) (x := basePoint)
      (hY.continuousAt.prodMk hInv)
  have hR : ContinuousAt R basePoint := hZ.continuousAt.sub hPhi
  have hRone : R basePoint = 1 := by
    apply Subtype.ext
    change (1 : Mat 4 ℝ) - phi (0 : Fin 3 → ℝ) (1 : Mat 4 ℝ)⁻¹ = 1
    rw [phi_zero_parameter, sub_zero]
  have hN : ∀ᶠ H : Sym 4 in 𝓝 (1 : Sym 4), (H : Mat 4 ℝ).PosDef :=
    (isOpen_posDef 4).mem_nhds Matrix.PosDef.one
  have heX : ∀ᶠ x : Ambient in 𝓝 basePoint, (x.1.1 : Mat 4 ℝ).PosDef := by
    have hxat : ContinuousAt (fun x : Ambient => x.1.1) basePoint := hX.continuousAt
    exact hxat.eventually hN
  have heR : ∀ᶠ x : Ambient in 𝓝 basePoint, (R x : Mat 4 ℝ).PosDef := by
    have hRN : ∀ᶠ H : Sym 4 in 𝓝 (R basePoint), (H : Mat 4 ℝ).PosDef := by
      rw [hRone]
      exact hN
    have h := hR.eventually hRN
    exact h
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [heX, heR] with x hx hr
  exact (cone_positive_slice x.1.1 x.1.2 x.2 hx).mpr hr.posSemidef

end Paper256

end

end OAI
