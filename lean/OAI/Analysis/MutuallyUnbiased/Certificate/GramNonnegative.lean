import OAI.Analysis.MutuallyUnbiased.GramData.Main
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Main
import OAI.Analysis.MutuallyUnbiased.Certificate.AuxiliaryInterpretation

namespace OAI

/-! Nonnegativity of the six literal integer Gram forms and the exact
positive scaling used by the mixed certificate. -/

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.GramNonnegative

def quadratic0 (B : Fin 7 → Basis) : ℝ :=
  ∑ i, ∑ j, realMatrix GramData.Block0.Z i j *
    (GramFunctions.Block0.forms i).mixedGram (GramFunctions.Block0.forms j) B

theorem quadratic0_nonneg (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    0 ≤ quadratic0 B :=
  GramFunctions.LinearForm.mixedGram_psd_nonneg GramFunctions.Block0.forms B hB
    (realMatrix GramData.Block0.Z) GramData.Block0.positiveDefinite.posSemidef

def quadratic1 (B : Fin 7 → Basis) : ℝ :=
  ∑ i, ∑ j, realMatrix GramData.Block1.Z i j *
    (GramFunctions.Block1.forms i).mixedGram (GramFunctions.Block1.forms j) B

theorem quadratic1_nonneg (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    0 ≤ quadratic1 B :=
  GramFunctions.LinearForm.mixedGram_psd_nonneg GramFunctions.Block1.forms B hB
    (realMatrix GramData.Block1.Z) GramData.Block1.positiveDefinite.posSemidef

def quadratic2 (B : Fin 7 → Basis) : ℝ :=
  ∑ i, ∑ j, realMatrix GramData.Block2.Z i j *
    (GramFunctions.Block2.forms i).mixedGram (GramFunctions.Block2.forms j) B

theorem quadratic2_nonneg (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    0 ≤ quadratic2 B :=
  GramFunctions.LinearForm.mixedGram_psd_nonneg GramFunctions.Block2.forms B hB
    (realMatrix GramData.Block2.Z) GramData.Block2.positiveDefinite.posSemidef

def quadratic3 (B : Fin 7 → Basis) : ℝ :=
  ∑ i, ∑ j, realMatrix GramData.Block3.Z i j *
    (GramFunctions.Block3.forms i).mixedGram (GramFunctions.Block3.forms j) B

theorem quadratic3_nonneg (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    0 ≤ quadratic3 B :=
  GramFunctions.LinearForm.mixedGram_psd_nonneg GramFunctions.Block3.forms B hB
    (realMatrix GramData.Block3.Z) GramData.Block3.positiveDefinite.posSemidef

def quadratic4 (B : Fin 7 → Basis) : ℝ :=
  ∑ i, ∑ j, realMatrix GramData.Block4.Z i j *
    (GramFunctions.Block4.forms i).mixedGram (GramFunctions.Block4.forms j) B

theorem quadratic4_nonneg (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    0 ≤ quadratic4 B :=
  GramFunctions.LinearForm.mixedGram_psd_nonneg GramFunctions.Block4.forms B hB
    (realMatrix GramData.Block4.Z) GramData.Block4.positiveDefinite.posSemidef

def quadratic5 (B : Fin 7 → Basis) : ℝ :=
  ∑ i, ∑ j, realMatrix GramData.Block5.Z i j *
    (GramFunctions.Block5.forms i).mixedGram (GramFunctions.Block5.forms j) B

theorem quadratic5_nonneg (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    0 ≤ quadratic5 B :=
  GramFunctions.LinearForm.mixedGram_psd_nonneg GramFunctions.Block5.forms B hB
    (realMatrix GramData.Block5.Z) GramData.Block5.positiveDefinite.posSemidef

def sourceGram (B : Fin 7 → Basis) : ℝ :=
  5 * ((10 : ℝ) ^ (15 - GramFunctions.Block0.decimalExponent) * quadratic0 B +
    (10 : ℝ) ^ (15 - GramFunctions.Block1.decimalExponent) * quadratic1 B +
    (10 : ℝ) ^ (15 - GramFunctions.Block2.decimalExponent) * quadratic2 B +
    (10 : ℝ) ^ (15 - GramFunctions.Block3.decimalExponent) * quadratic3 B +
    (10 : ℝ) ^ (15 - GramFunctions.Block4.decimalExponent) * quadratic4 B +
    (10 : ℝ) ^ (15 - GramFunctions.Block5.decimalExponent) * quadratic5 B)

theorem sourceGram_nonneg (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    0 ≤ sourceGram B := by
  have h0 := mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ 10 by norm_num)
    (15 - GramFunctions.Block0.decimalExponent)) (quadratic0_nonneg B hB)
  have h1 := mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ 10 by norm_num)
    (15 - GramFunctions.Block1.decimalExponent)) (quadratic1_nonneg B hB)
  have h2 := mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ 10 by norm_num)
    (15 - GramFunctions.Block2.decimalExponent)) (quadratic2_nonneg B hB)
  have h3 := mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ 10 by norm_num)
    (15 - GramFunctions.Block3.decimalExponent)) (quadratic3_nonneg B hB)
  have h4 := mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ 10 by norm_num)
    (15 - GramFunctions.Block4.decimalExponent)) (quadratic4_nonneg B hB)
  have h5 := mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ 10 by norm_num)
    (15 - GramFunctions.Block5.decimalExponent)) (quadratic5_nonneg B hB)
  unfold sourceGram
  positivity

end MUB6.Certificate.GramNonnegative

end

end OAI
