import OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicControl
import OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicEstimates

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set Metric MeasureTheory Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic HeckeLogarithmic HeckeDeletionBounds

def binCost (B : ℝ) (χ : Character) (H : ℝ) : ℝ :=
  B*Real.log (complexity χ H) + localBound (1/2)*Real.log ((radical χ.modulus).absNorm : ℝ)

theorem binCost_nonneg {B : ℝ} (hB : 0≤B) (χ : Character) (H : ℝ) : 0≤binCost B χ H := by
  have hc : 1≤complexity χ H :=
    (Real.one_le_exp (by norm_num : (0 : ℝ)≤1)).trans (complexity_ge_exp χ H)
  have hr : (1 : ℝ)≤(radical χ.modulus).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero χ.modulus))
  exact add_nonneg (mul_nonneg hB (Real.log_nonneg hc))
    (mul_nonneg (localBound_pos (by norm_num : (0 : ℝ)<1/2)).le (Real.log_nonneg hr))

theorem polynomial_bound_in_bin (e : ℝ) (he : 0<e) (he' : e<1/1000) :
    ∃ B : ℝ, 0≤B ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (W : ℝ→ℂ) (α β : ℝ), 0<α → Function.support W⊆Icc α β →
      ContDiff ℝ ∞ W → ∀ D σ freq L C₂ Cn : ℝ, ∀ n : ℕ,
      1≤D → 0≤L → 0≤C₂ → 0≤Cn → |freq|+L≤(3*i+2 : ℕ)*T →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+8*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x∈Icc (a+8*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      ‖polynomial (χ j) W D σ freq‖ ≤ (1/(2*Real.pi))*
        (C₂*D^(a+8*e-1/2)*binCost B (χ j) ((3*i+2 : ℕ)*T)*Real.pi +
          2*(Cn*D^(3/2 : ℝ)*binCost B (χ j) ((3*i+2 : ℕ)*T)/(1+L)^n)*|2-a-8*e| +
          (Cn*D^(3/2 : ℝ)*eulerBound 2)/(1+L)^n*Real.pi) := by
  obtain ⟨B,hB,hbound⟩ := HeckePrimeDyadicControl.buffered_rectangle_control e he he'
  refine ⟨B,hB,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j W α β hα hWs hW D σ freq L C₂ Cn n
    hD hL hC₂ hCn hfreq hm₂ hmn
  have hlr : a+8*e-σ≤2-σ := by linarith
  have hmem (s : ℂ) (hs : s ∈ (uIcc (a+8*e-σ) (2-σ) ×ℂ uIcc (-L) L)) :
      a+8*e≤(s+HeckeDyadic.shift σ freq).re ∧ (s+HeckeDyadic.shift σ freq).re≤2 ∧
        |(s+HeckeDyadic.shift σ freq).im|≤(3*i+2 : ℕ)*T := by
    convert HeckeDyadic.translated_rectangle_mem (a := a+2*e) (e := e)
      (by linarith) (by linarith) hlr hL hfreq hs using 1 ; ring_nf
  have hs (s : ℂ) (hs : s ∈ (uIcc (a+8*e-σ) (2-σ) ×ℂ uIcc (-L) L)) :=
    hbound χ hχ T a i hT ha ha' hmax j (s+HeckeDyadic.shift σ freq)
      (hmem s hs).1 (hmem s hs).2.1 (hmem s hs).2.2
  have hh := polynomial_bound_of_rectangle (χ j) (hχ j) W α β hα hWs hW
    D σ freq (a+8*e-σ) (2-σ) L C₂ Cn (binCost B (χ j) ((3*i+2 : ℕ)*T)) n
    hD hlr (by linarith) hL hC₂ hCn (binCost_nonneg hB _ _)
    hm₂ hmn (fun s h => (hs s h).1) (fun s h => by
      simpa only [series, neg_div, norm_neg, logDeriv_apply, binCost] using (hs s h).2)
  convert hh using 1 ; congr 1 ; ring_nf

end SevenEighths.HeckePrimeDyadic

end

end OAI
