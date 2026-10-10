import Mathlib
import OAI.Computability.MinUncut.Analysis.GaussianQuadrature
import OAI.Computability.MinUncut.Analysis.LiteralGaussian

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace MinUncut.FiniteGaussian
open GaussianBudget MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}
local instance coordsDecEq (m n : ℕ) : DecidableEq (TestCoordinates m n) :=
  fun a b => Classical.propDecidable (a=b)

def tableGrid (m n : ℕ) (ε : ℚ) (hε : 0<ε) : GridData :=
  GridData.select (Fintype.card (TestCoordinates m n)) (Fintype.card (ScoreIndex m n))
    (2*(n^m:ℕ)+1) ε (by positivity) hε

def gridWeight (g : GridData) (j : TestCoordinates m n → Fin g.L) : ℚ :=
  ∏ i, cellWeight g.r g.T g.L (j i)

lemma tableGrid_check (m n : ℕ) (ε : ℚ) (hε : 0<ε) :
    (tableGrid m n ε hε).Check (Fintype.card (TestCoordinates m n)) (Fintype.card (ScoreIndex m n))
      (2*(n^m:ℕ)+1) ε := GridData.select_check _ _ _ _ _ _

lemma gridWeight_pos (g : GridData) (hT : 0<g.T) (hL : 0<g.L)
    (j : TestCoordinates m n → Fin g.L) : 0<gridWeight g j := by
  exact Finset.prod_pos (fun _ _ => cellWeight_pos (by exact_mod_cast hT) hL g.r _)

lemma sum_gridWeight (g : GridData) (hT : 0<g.T) (hL : 0<g.L) :
    (∑ j : TestCoordinates m n → Fin g.L, gridWeight g j)=1 := by
  unfold gridWeight
  rw [← Fintype.prod_sum]
  simp only [sum_cellWeight (show (0:ℚ)<g.T by exact_mod_cast hT) hL,Finset.prod_const_one]

lemma tableGrid_real_bound (m n : ℕ) {ε : ℚ} (hε : 0<ε) :
    let g := tableGrid m n ε hε
    (Fintype.card (TestCoordinates m n):ℝ)/(g.T:ℝ)^2+
        2*(Fintype.card (ScoreIndex m n):ℝ)*(2*(n^m:ℕ)+1)*((g.T:ℝ)/g.L)+
        2*(Fintype.card (TestCoordinates m n):ℝ)*(g.T:ℝ)*error g.r ((g.T:ℝ)^2/2) < (ε:ℝ) := by
  let g := tableGrid m n ε hε
  have hg := tableGrid_check m n ε hε
  have he1 : (Fintype.card (TestCoordinates m n):ℝ)/(g.T:ℝ)^2 < (ε:ℝ)/4 := by
    have h : (((Fintype.card (TestCoordinates m n):ℚ)/(g.T:ℚ)^2 : ℚ):ℝ) < ((ε/4:ℚ):ℝ) := Rat.cast_lt.mpr hg.2.2.1
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] using (h : (_ : ℝ) < _)
  have he2 : 2*(Fintype.card (ScoreIndex m n):ℝ)*(2*(n^m:ℕ)+1)*(g.T:ℝ)/(g.L:ℝ) < (ε:ℝ)/4 := by
    have h : ((2*(Fintype.card (ScoreIndex m n):ℚ)*(2*(n^m:ℕ)+1)*(g.T:ℚ)/g.L : ℚ):ℝ) < ((ε/4:ℚ):ℝ) := Rat.cast_lt.mpr hg.2.2.2.1
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one] using (h : (_ : ℝ) < _)
  have he3 : 2*(Fintype.card (TestCoordinates m n):ℝ)*(g.T:ℝ)*error g.r ((g.T:ℝ)^2/2) < (ε:ℝ)/4 := by
    have he := hg.2.2.2.2
    have he' : ((2*(Fintype.card (TestCoordinates m n):ℚ)*g.T*qError g.r ((g.T:ℚ)^2/2)):ℝ) < (ε:ℝ)/4 := by
      exact_mod_cast he
    simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,qError_cast,Rat.cast_div,Rat.cast_pow] using he'
  have hep : (0:ℝ)<ε := by exact_mod_cast hε
  have hbound : (Fintype.card (TestCoordinates m n):ℝ)/(g.T:ℝ)^2+
        2*(Fintype.card (ScoreIndex m n):ℝ)*(2*(n^m:ℕ)+1)*((g.T:ℝ)/g.L)+
        2*(Fintype.card (TestCoordinates m n):ℝ)*(g.T:ℝ)*error g.r ((g.T:ℝ)^2/2) < ε := by
    rw [mul_div_assoc] at he2
    linarith
  exact hbound

attribute [local irreducible] tableGrid scoreFamily

lemma rational_table_error (hn : 0<n) {σ η : ℚ} (hσ : 0≤σ) (hσ1 : σ≤1)
    (hη : 0≤η) (hη1 : η≤1) (g : GridData) (hT : 1≤(g.T:ℚ)) (hL : 0<g.L)
    (F : (ScoreIndex m n → Bool) → ℝ) (hF : ∀ t, 0≤F t ∧ F t≤1) :
    |(∫ x, F (thresholdTable (scoreFamily (σ:ℝ) (η:ℝ)) x) ∂gaussianLaw (TestCoordinates m n))-
      ∑ j : TestCoordinates m n → Fin g.L,
        (gridWeight g j:ℝ)*F (rationalScoreTable σ η (fun i => midpoint g.T g.L (j i)))| ≤
      (Fintype.card (TestCoordinates m n):ℝ)/(g.T:ℝ)^2+
        2*(Fintype.card (ScoreIndex m n):ℝ)*(2*(n^m:ℕ)+1)*((g.T:ℝ)/g.L)+
        2*(Fintype.card (TestCoordinates m n):ℝ)*(g.T:ℝ)*error g.r ((g.T:ℝ)^2/2) := by
  have hh := joint_table_error (scoreFamily (σ:ℝ) (η:ℝ)) (scoreFamily_variance hn _ _)
    (A := 2*(n^m:ℕ)+1) (by positivity)
    (scoreFamily_l1 hn (by exact_mod_cast hσ) (by exact_mod_cast hσ1)
      (by exact_mod_cast hη) (by exact_mod_cast hη1)) hT hL g.r F hF
  simp_rw [rationalScoreTable_correct hn]
  convert hh using 1 <;> simp only [gridWeight,Rat.cast_natCast]
  congr 2

lemma tableGrid_error (hn : 0<n) {σ η ε : ℚ} (hσ : 0≤σ) (hσ1 : σ≤1)
    (hη : 0≤η) (hη1 : η≤1) (hε : 0<ε)
    (F : (ScoreIndex m n → Bool) → ℝ) (hF : ∀ t, 0≤F t ∧ F t≤1) :
    |(∫ x, F (thresholdTable (scoreFamily (σ:ℝ) (η:ℝ)) x) ∂gaussianLaw (TestCoordinates m n))-
      ∑ j : TestCoordinates m n → Fin (tableGrid m n ε hε).L,
        (gridWeight (tableGrid m n ε hε) j:ℝ)*
          F (rationalScoreTable σ η (fun i => midpoint (tableGrid m n ε hε).T (tableGrid m n ε hε).L (j i)))| < ε := by
  have hg := tableGrid_check m n ε hε
  have hT : (1:ℚ)≤(tableGrid m n ε hε).T := by exact_mod_cast hg.1
  exact (rational_table_error hn hσ hσ1 hη hη1 _ hT hg.2.1 F hF).trans_lt
    (tableGrid_real_bound m n hε)

end MinUncut.FiniteGaussian

end
end

end OAI
