import OAI.MathematicalPhysics.Boltzmann.Branching.DilatedCoreDensity
import OAI.MathematicalPhysics.Boltzmann.Jets.JetCoreConvergence

namespace OAI

/-! # Dilated free kernels for the actual periodic labels -/

noncomputable section

open MeasureTheory ProbabilityTheory
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice
open scoped ENNReal

namespace BoltzmannNonuniqueness.ChartKernel

theorem inputKernel_congr_base {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (c : Kernel X Velocity) (d : Kernel Y Velocity) [IsSFiniteKernel c] [IsSFiniteKernel d]
    {x : X} {y : Y} (h : c x = d y) (q : ℝ) (v : Velocity) :
    inputKernel c q (x,v) = inputKernel d q (y,v) := by
  change (coordinateKernel c q (x,v)).map _ = (coordinateKernel d q (y,v)).map _
  rw [coordinateKernel_apply,coordinateKernel_apply,h]

end BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.JetCopyDatum

def latticeVector (n : Lattice) : Velocity := WithLp.toLp 2 (fun k => (n k : ℝ))

def copyColdKernel (r s₀ η K α γ d₀ : ℝ) (i : Label) : Kernel SpaceTime Velocity :=
  (JetCoreSheet.dilatedColdKernel r η K α γ (JetGeometry.jetScale s₀ η i.annulus)
    (d₀*JetGeometry.jetScale s₀ η i.annulus^10) i.positive).comap
      (fun z => (z.1,z.2-r⁻¹ • latticeVector i.lattice)) (by fun_prop)

instance copyColdKernel_sFinite (r s₀ η K α γ d₀ : ℝ) (i : Label) :
    IsSFiniteKernel (copyColdKernel r s₀ η K α γ d₀ i) := by
  unfold copyColdKernel
  infer_instance

def copyFreeKernel (r s₀ η K α γ d₀ q : ℝ) (i : Label) : Kernel KineticPhase Velocity :=
  ChartKernel.offAxis (ChartKernel.inputKernel (copyColdKernel r s₀ η K α γ d₀ i) q)

instance copyFreeKernel_sFinite (r s₀ η K α γ d₀ q : ℝ) (i : Label) :
    IsSFiniteKernel (copyFreeKernel r s₀ η K α γ d₀ q i) := by
  unfold copyFreeKernel
  infer_instance

theorem copyFreeKernel_eq (r s₀ η K α γ d₀ q : ℝ) (i : Label) (z : KineticPhase) :
    copyFreeKernel r s₀ η K α γ d₀ q i z =
      JetCoreSheet.dilatedFreeKernel r η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) q i.positive
        ((z.1.1,z.1.2-r⁻¹ • latticeVector i.lattice),z.2) := by
  by_cases hv : VelocityWeight.transverse z.2 = 0
  · rw [copyFreeKernel,JetCoreSheet.dilatedFreeKernel,ChartKernel.offAxis_axis _ z hv,
      ChartKernel.offAxis_axis _ ((z.1.1,z.1.2-r⁻¹ • latticeVector i.lattice),z.2) hv]
  · rw [copyFreeKernel,JetCoreSheet.dilatedFreeKernel,ChartKernel.offAxis_apply _ z hv,
      ChartKernel.offAxis_apply _ ((z.1.1,z.1.2-r⁻¹ • latticeVector i.lattice),z.2) hv]
    exact ChartKernel.inputKernel_congr_base (copyColdKernel r s₀ η K α γ d₀ i)
      (JetCoreSheet.dilatedColdKernel r η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) i.positive)
      (x := z.1) (y := (z.1.1,z.1.2-r⁻¹ • latticeVector i.lattice)) rfl q z.2

theorem copyFreeKernel_bound {r s₀ η K α γ d₀ q : ℝ} (hr : 0 < r)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (i : Label) (z : KineticPhase) (ht : 0 < z.1.1) :
    copyFreeKernel r s₀ η K α γ d₀ q i z Set.univ ≤
      ENNReal.ofReal (JetCoreSheet.growthConstant K α γ q/z.1.1) := by
  have hs : 0 < JetGeometry.jetScale s₀ η i.annulus := DatumBounds.scale_pos hs₀ _
  have hsle : JetGeometry.jetScale s₀ η i.annulus ≤ 1/8 := by
    have h := JetGeometry.scale_antitone hs₀.le hη (Nat.zero_le (i.annulus+1))
    have hle : DatumBounds.scale s₀ η (i.annulus+1) ≤ s₀ := by
      simpa only [DatumBounds.scale,Nat.cast_zero,neg_zero,zero_mul,Real.exp_zero,mul_one] using h
    exact hle.trans hsmax
  rw [copyFreeKernel_eq]
  exact JetCoreSheet.dilatedFreeKernel_bound hr hK hα hγ hs (by positivity)
    (JetEnvelopeGain.thermal_width_le hdmax hs.le hsle) hq₁ hq₂ η i.positive _ ht

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
