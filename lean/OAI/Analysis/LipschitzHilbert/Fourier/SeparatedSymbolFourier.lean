import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-! Separation of the normalized (X,Y,U) symbol by Fourier inversion.
The two frequency coordinates and the selector coordinate are separated
inside an absolutely convergent integral. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

abbrev SymbolSpace := EuclideanSpace ℝ (Fin 3)

def symbolPoint (X Y U : ℝ) : SymbolSpace := WithLp.toLp 2 ![X,Y,U]

def frequencyCharacter (nu : SymbolSpace) (X Y : ℝ) : ℂ :=
  (Real.fourierChar (nu 0*X) : ℂ)*(Real.fourierChar (nu 1*Y) : ℂ)

def selectorCharacter (nu : SymbolSpace) (U : ℝ) : ℂ :=
  (Real.fourierChar (nu 2*U) : ℂ)

theorem symbolPoint_inner (nu : SymbolSpace) (X Y U : ℝ) :
    inner ℝ nu (symbolPoint X Y U)=nu 0*X+nu 1*Y+nu 2*U := by
  simp [PiLp.inner_apply, symbolPoint, Fin.sum_univ_succ]
  ring

theorem norm_frequencyCharacter (nu : SymbolSpace) (X Y : ℝ) :
    ‖frequencyCharacter nu X Y‖=1 := by
  simp only [frequencyCharacter, norm_mul, Circle.norm_coe, one_mul]

theorem norm_selectorCharacter (nu : SymbolSpace) (U : ℝ) :
    ‖selectorCharacter nu U‖=1 := Circle.norm_coe _

theorem separated_symbol_integrable (S : SchwartzMap SymbolSpace ℂ) (X Y U : ℝ) :
    Integrable (fun nu : SymbolSpace =>
      𝓕 S nu * frequencyCharacter nu X Y * selectorCharacter nu U) := by
  apply (𝓕 S : SchwartzMap SymbolSpace ℂ).integrable.norm.mono'
  · have hc : Continuous (fun nu : SymbolSpace =>
        𝓕 S nu * frequencyCharacter nu X Y * selectorCharacter nu U) := by
      unfold frequencyCharacter selectorCharacter
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [] with nu
    rw [norm_mul, norm_mul, norm_frequencyCharacter, norm_selectorCharacter, mul_one, mul_one]

theorem separated_symbol_fourier (S : SchwartzMap SymbolSpace ℂ) (X Y U : ℝ) :
    S (symbolPoint X Y U)=∫ nu : SymbolSpace,
      𝓕 S nu * frequencyCharacter nu X Y * selectorCharacter nu U := by
  have hinv : (𝓕⁻ (𝓕 S : SchwartzMap SymbolSpace ℂ) : SchwartzMap SymbolSpace ℂ)=S :=
    FourierTransform.fourierInv_fourier_eq _
  have h := congrArg (fun f : SchwartzMap SymbolSpace ℂ => f (symbolPoint X Y U)) hinv
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq] at h
  calc
    _ = ∫ nu : SymbolSpace, Real.fourierChar (inner ℝ nu (symbolPoint X Y U)) • 𝓕 S nu := h.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with nu
      rw [symbolPoint_inner, Real.fourierChar.map_add_eq_mul, Real.fourierChar.map_add_eq_mul]
      simp only [Circle.smul_def, Circle.coe_mul, smul_eq_mul, frequencyCharacter, selectorCharacter]
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
