import Mathlib
import OAI.Geometry.PrescribedPotential.ChartTransportHigher
import OAI.Geometry.PrescribedPotential.ParameterCoreBounds

namespace OAI

/-! Integer Bounds. -/

section

 

noncomputable section
open Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap ContDiff Classical Laplacian

namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def raiseZero (s : ℝ) : L2 E →L[ℂ] L2 E :=
  liftOperator s (s + 1) (besselPotential E ℂ (-2)) (fun u hu => by
    rw [memSobolev_besselPotential_iff]
    exact hu.mono (by linarith))

def raiseDeriv (s : ℝ) (v : E) : L2 E →L[ℂ] L2 E :=
  liftOperator s (s + 1) ((besselPotential E ℂ (-2)).comp (lineDerivOpCLM ℂ 𝓢'(E, ℂ) v))
    (fun u hu => by
      change MemSobolev (s + 1) 2 (besselPotential E ℂ (-2) (∂_{v} u))
      rw [memSobolev_besselPotential_iff]
      exact hu.lineDerivOp.mono (by linarith))

lemma realize_raiseZero (s : ℝ) (u : L2 E) :
    realize (s + 1) (raiseZero s u) = besselPotential E ℂ (-2) (realize s u) :=
  realize_liftOperator _ _ _ _ _

lemma realize_raiseDeriv (s : ℝ) (v : E) (u : L2 E) :
    realize (s + 1) (raiseDeriv s v u) = besselPotential E ℂ (-2) (∂_{v} (realize s u)) :=
  realize_liftOperator _ _ _ _ _

lemma schwartzCoord_raise_one (s : ℝ) (f : 𝓢(E, ℂ)) :
    schwartzCoord (s + 1) f = raiseZero s (schwartzCoord s f) -
      (((2 * Real.pi)^2 : ℝ) : ℂ)⁻¹ • ∑ j,
        raiseDeriv s (stdOrthonormalBasis ℝ E j)
          (schwartzCoord s (∂_{stdOrthonormalBasis ℝ E j} f)) := by
  apply realize_injective (s + 1)
  simp only [map_sub, map_smul, map_sum, realize_raiseZero, realize_raiseDeriv,
    realize_schwartzCoord]
  have he := congrArg (besselPotential E ℂ (-2)) (bessel_two_laplacian (f : 𝓢'(E, ℂ)))
  rw [besselPotential_besselPotential_apply] at he
  norm_num only [neg_add_cancel, besselPotential_zero, ContinuousLinearMap.id_apply] at he
  rw [map_sub, map_smul, TemperedDistribution.laplacian_eq_sum (stdOrthonormalBasis ℝ E), map_sum] at he
  rw [he]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [← lineDerivOp_toTemperedDistributionCLM_eq]

lemma coreBound_raise_one {s t : ℝ} (T : 𝓢(E, ℂ) → 𝓢(E, ℂ))
    (hT : CoreBound s t T)
    (hD : ∀ j, CoreBound s t (fun f => ∂_{stdOrthonormalBasis ℝ E j} (T f))) :
    CoreBound s (t + 1) T := by
  obtain ⟨C, hC, hc⟩ := hT
  choose D hD0 hdb using hD
  let c : ℝ := ‖(((2 * Real.pi)^2 : ℝ) : ℂ)⁻¹‖
  refine ⟨‖raiseZero (E := E) t‖ * C + c * ∑ j, ‖raiseDeriv t (stdOrthonormalBasis ℝ E j)‖ * D j,
    add_nonneg (mul_nonneg (norm_nonneg _) hC)
      (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (hD0 j)))), fun f => ?_⟩
  rw [schwartzCoord_raise_one]
  calc
    _ ≤ ‖raiseZero t (schwartzCoord t (T f))‖ +
        c * ‖∑ j, raiseDeriv t (stdOrthonormalBasis ℝ E j)
          (schwartzCoord t (∂_{stdOrthonormalBasis ℝ E j} (T f)))‖ := by
      simpa only [norm_smul] using norm_sub_le
        (raiseZero t (schwartzCoord t (T f)))
        ((((2 * Real.pi)^2 : ℝ) : ℂ)⁻¹ • ∑ j, raiseDeriv t (stdOrthonormalBasis ℝ E j)
          (schwartzCoord t (∂_{stdOrthonormalBasis ℝ E j} (T f))))
    _ ≤ (‖raiseZero (E := E) t‖ * C) * ‖schwartzCoord s f‖ +
        c * ∑ j, (‖raiseDeriv t (stdOrthonormalBasis ℝ E j)‖ * D j) * ‖schwartzCoord s f‖ := by
      apply add_le_add
      · exact ((raiseZero t).le_opNorm _).trans (by
          simpa only [mul_assoc] using
            (mul_le_mul_of_nonneg_left (hc f) (norm_nonneg (raiseZero (E := E) t))))
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro j _
        exact ((raiseDeriv t (stdOrthonormalBasis ℝ E j)).le_opNorm _).trans (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hdb j f)
            (norm_nonneg (raiseDeriv t (stdOrthonormalBasis ℝ E j))))
    _ = _ := by rw [← Finset.sum_mul]; ring

lemma coreBound_of_words_integer (k : ℕ) {s t : ℝ} (T : 𝓢(E, ℂ) → 𝓢(E, ℂ))
    (h : ∀ ws : List E, ws.length ≤ k → CoreBound s t (fun f => schwartzWord ws (T f))) :
    CoreBound s (t + k) T := by
  induction k generalizing T with
  | zero => simpa [schwartzWord] using h [] (by simp)
  | succ k ih =>
    have ht := ih T (fun ws hw => h ws (by omega))
    have hd (j : Fin (Module.finrank ℝ E)) := ih
      (fun f => ∂_{stdOrthonormalBasis ℝ E j} (T f))
      (fun ws hw => by
        have hh := h (ws ++ [stdOrthonormalBasis ℝ E j])
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        simpa only [schwartzWord_append, schwartzWord, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply, lineDerivOpCLM_apply] using hh)
    convert coreBound_raise_one T ht hd using 1; push_cast; ring

end SobolevChart

namespace GlobalElliptic
open SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

 

theorem chartTransport_integer_bound (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ ∞ e e.source) (hs : ContDiffOn ℝ ∞ e.symm e.target)
    (κ : ChartCutoff e.source) (k : ℕ) :
    CoreBound (k : ℝ) (k : ℝ) (chartTransport e he κ) := by
  have hh := coreBound_of_words_integer k (s := (k : ℝ)) (t := 0) (chartTransport e he κ)
    (fun ws hw => chartTransport_word_bound e he hs ws κ (by exact_mod_cast hw))
  simpa only [zero_add] using hh
end GlobalElliptic

namespace FrozenPoisson.ParameterRegularity
open SobolevChart EllipticKernel
open scoped ComplexOrder MatrixOrder
variable {n : ℕ} {ι : Type*} [Fintype ι]

theorem schwartzLocal_integer_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (a : SmoothCoefficients ι (EC n))
    (hsmall : perturbationBound v (coefficientBCF a) * ellipticBound H hH < 1) (k : ℕ) :
    CoreBound (k : ℝ) ((k : ℝ) + 2) (schwartzLocal H hH t ht v a hsmall) := by
  rw [add_comm]
  apply coreBound_of_words_integer k
  intro ws hw
  apply schwartzLocal_word_bound H hH t ht v a hsmall ws
  exact_mod_cast hw
end FrozenPoisson.ParameterRegularity

end
end

end OAI
