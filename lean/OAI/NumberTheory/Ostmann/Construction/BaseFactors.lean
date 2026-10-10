import OAI.NumberTheory.Ostmann.Construction.HistoryFactorization
import OAI.NumberTheory.Ostmann.SchwartzCutoff

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Construction

def baseScalar (X : ℝ) (ψhat : ℝ → ℂ) (bins : List ℕ → State → ℝ)
    (outside : List ℕ) (a : State) : ℂ :=
  let total := outsideProduct outside*a.product
  (Real.sqrt (X/total) : ℂ)*ψhat (-(a.frequency:ℝ)*X/total)*(bins outside a:ℂ)

def spectatorFactor (g : (p : ℕ) → ZMod p → ℂ) (outside : List ℕ) (a : State) : ℂ :=
  (outside.map fun q => g q
    (modFraction q a.frequency ((outsideProduct outside/q)*a.product))).prod

theorem baseCoefficient_eq_scalar_spectator (X : ℝ) (ψhat : ℝ → ℂ)
    (g : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ)
    (outside : List ℕ) (a : State) :
    baseCoefficient X ψhat g bins outside a =
      baseScalar X ψhat bins outside a*spectatorFactor g outside a := rfl

def historyScalar (X : ℝ) (ψhat : ℝ → ℂ) (bins : List ℕ → State → ℝ)
    (outside : List ℕ) (φ : ℝ → ℝ) (G : ℝ) {l : ℕ} (h : History l) : ℂ :=
  (h.realWeight φ G : ℂ)*h.leafProduct (baseScalar X ψhat bins outside)

theorem history_weight_eq_scalar_spectator (X : ℝ) (ψhat : ℝ → ℂ)
    (g : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ)
    (outside : List ℕ) (φ : ℝ → ℝ) (G : ℝ) {l : ℕ} (h : History l) :
    h.weight (baseCoefficient X ψhat g bins outside) φ G =
      historyScalar X ψhat bins outside φ G h *h.leafProduct (spectatorFactor g outside) := by
  rw [History.weight_eq_realWeight_leafProduct]
  have hbase : baseCoefficient X ψhat g bins outside =
      fun a => baseScalar X ψhat bins outside a*spectatorFactor g outside a := rfl
  rw [hbase, History.leafProduct_mul]
  exact (mul_assoc _ _ _).symm

theorem baseScalar_zero_of_large_frequency (X : ℝ) (hX : 0<X)
    (bins : List ℕ → State → ℝ) (outside : List ℕ) (a : State)
    (hperiod : 0<outsideProduct outside*a.product)
    (hfrequency : ((outsideProduct outside*a.product : ℕ):ℝ)/(4*X) ≤ |(a.frequency:ℝ)|) :
    baseScalar X (fun ξ => 𝓕 SchwartzCutoff.psi ξ) bins outside a=0 := by
  have hP : (0:ℝ)<(outsideProduct outside*a.product : ℕ) := by exact_mod_cast hperiod
  have hlarge : (1:ℝ)/4 ≤ |-(a.frequency:ℝ)*X/(outsideProduct outside*a.product : ℕ)| := by
    rw [abs_div, abs_mul, abs_neg, abs_of_pos hX, abs_of_pos hP]
    apply (le_div_iff₀ hP).mpr
    have h := (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hX)).mp hfrequency
    nlinarith
  simp only [baseScalar, SchwartzCutoff.fourier_psi_zero_of_abs_ge hlarge, mul_zero, zero_mul]

end Ostmann.Construction

end

end OAI
