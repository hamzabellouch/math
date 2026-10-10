import OAI.Analysis.LipschitzHilbert.Fourier.SymbolSlice
import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedBandSymbol

namespace OAI

/-! A single compactly supported master symbol for the normalized
annular multipliers. Its slices have uniform Fourier coefficient bounds. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff
namespace LipschitzHilbert.PacketRepresentation

def masterArgument (z : MasterSymbolSpace) : ℝ :=
  z.1 0+(z.2.1+z.2.2*z.1 1)*z.1 2

theorem masterArgument_temperate : Function.HasTemperateGrowth masterArgument := by
  let P : MasterSymbolSpace →L[ℝ] SymbolSpace := ContinuousLinearMap.fst ℝ _ _
  let Q : MasterSymbolSpace →L[ℝ] (ℝ × ℝ) := ContinuousLinearMap.snd ℝ _ _
  let X := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0).comp P
  let Y := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1).comp P
  let U := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2).comp P
  let V := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp Q
  let T := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp Q
  have h := X.hasTemperateGrowth.add
    ((V.hasTemperateGrowth.add (T.hasTemperateGrowth.mul Y.hasTemperateGrowth)).mul U.hasTemperateGrowth)
  change Function.HasTemperateGrowth (fun z => X z+(V z+T z*Y z)*U z) at h
  exact h

def masterCutoff (R : ℝ) (hR : 0<R) : SchwartzMap MasterSymbolSpace ℂ :=
  let b : ContDiffBump (0 : MasterSymbolSpace) := ⟨R,2*R,hR,by linarith⟩
  (b.hasCompactSupport.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp b.contDiff)

theorem masterCutoff_one (R : ℝ) (hR : 0<R) (z : MasterSymbolSpace) (hz : ‖z‖≤R) :
    masterCutoff R hR z=1 := by
  let b : ContDiffBump (0 : MasterSymbolSpace) := ⟨R,2*R,hR,by linarith⟩
  change (b z : ℂ)=1
  rw [b.one_of_mem_closedBall (by simpa using hz)]
  norm_num

def masterSymbol (psi : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0<R) :
    SchwartzMap MasterSymbolSpace ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun z => psi (masterArgument z)) (masterCutoff R hR)

theorem masterSymbol_apply (psi : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0<R)
    (z : MasterSymbolSpace) :
    masterSymbol psi R hR z=psi (masterArgument z)*masterCutoff R hR z := by
  exact SchwartzMap.smulLeftCLM_apply_apply
    (psi.hasTemperateGrowth.comp masterArgument_temperate) _ _

def normalizedSchwartzSymbol (psi : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0<R)
    (v t : ℝ) : SchwartzMap SymbolSpace ℂ := symbolSlice (masterSymbol psi R hR) (v,t)

theorem normalizedSchwartzSymbol_apply (psi : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0<R)
    (v t X Y U : ℝ) :
    normalizedSchwartzSymbol psi R hR v t (symbolPoint X Y U)=
      psi (X+(v+t*Y)*U)*masterCutoff R hR (symbolPoint X Y U,(v,t)) := by
  rw [normalizedSchwartzSymbol, symbolSlice_apply, masterSymbol_apply]
  rfl

theorem normalizedSchwartzSymbol_one (psi : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0<R)
    (v t X Y U : ℝ) (hxyz : ‖symbolPoint X Y U‖≤R) (hp : ‖(v,t)‖≤R) :
    normalizedSchwartzSymbol psi R hR v t (symbolPoint X Y U)=psi (X+(v+t*Y)*U) := by
  have hz : ‖(symbolPoint X Y U,(v,t))‖≤R := by
    rw [Prod.norm_def]
    exact max_le hxyz hp
  rw [normalizedSchwartzSymbol_apply,
    masterCutoff_one R hR (symbolPoint X Y U,(v,t)) hz, mul_one]

theorem normalizedSchwartzSymbol_uniform (psi : SchwartzMap ℝ ℂ)
    (R : ℝ) (hR : 0<R) (q : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ v t : ℝ,
      symbolCoefficientBound (normalizedSchwartzSymbol psi R hR v t) q≤C := by
  obtain ⟨C,hC,h⟩ := symbolSlice_coefficient_uniform (masterSymbol psi R hR) q
  exact ⟨C,hC,fun v t => h (v,t)⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
