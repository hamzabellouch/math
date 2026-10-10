import Mathlib

namespace OAI

universe uι

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

structure System (ι : Type uι) [Fintype ι] where
  ratio : ι → ℝ
  offset : ι → ℝ
  weight : ι → ℝ
  ratio_pos : ∀ i, 0 < |ratio i|
  ratio_lt_one : ∀ i, |ratio i| < 1
  weight_pos : ∀ i, 0 < weight i
  weight_sum : ∑ i, weight i = 1

namespace System

variable {ι : Type uι} [Fintype ι]

def affine (S : System ι) (i : ι) (x : ℝ) : ℝ := S.ratio i * x + S.offset i

def wordAffine (S : System ι) : List ι → ℝ × ℝ
  | [] => (1, 0)
  | i :: w => (S.ratio i * (S.wordAffine w).1,
      S.ratio i * (S.wordAffine w).2 + S.offset i)

def completeMap (S : System ι) {n : ℕ} (w : Fin n → ι) : ℝ × ℝ :=
  S.wordAffine (List.ofFn w)

noncomputable def wordWeight (S : System ι) {n : ℕ} (w : Fin n → ι) : ℝ :=
  ∏ j, S.weight (w j)

noncomputable def mapSupport (S : System ι) (n : ℕ) : Finset (ℝ × ℝ) := by
  classical
  exact Finset.univ.image (S.completeMap (n := n))

noncomputable def mapMass (S : System ι) (n : ℕ) (g : ℝ × ℝ) : ℝ := by
  classical
  exact ∑ w ∈ (Finset.univ : Finset (Fin n → ι)).filter (S.completeMap · = g),
    S.wordWeight w

noncomputable def walkEntropy (S : System ι) (n : ℕ) : ℝ :=
  (∑ g ∈ S.mapSupport n, Real.negMulLog (S.mapMass n g)) / Real.log 2

noncomputable def entropyRate (S : System ι) : ℝ :=
  sInf (Set.range fun n : ℕ => S.walkEntropy (n + 1) / (n + 1 : ℕ))

noncomputable def lyapunov (S : System ι) : ℝ :=
  -(∑ i, S.weight i * (Real.log |S.ratio i| / Real.log 2))

def SelfSimilar (S : System ι) (μ : Measure ℝ) : Prop :=
  μ = ∑ i, ENNReal.ofReal (S.weight i) • μ.map (S.affine i)

end System

noncomputable def lowerHausdorffDimension (μ : Measure ℝ) : ℝ≥0∞ :=
  ⨅ (E : Set ℝ) (_ : MeasurableSet E) (_ : 0 < μ E), dimH E
open MeasureTheory

theorem entropy_rate_dimension {ι : Type uι} [Fintype ι] [Nonempty ι]
    (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) :
    lowerHausdorffDimension μ = ENNReal.ofReal (min 1 (S.entropyRate / S.lyapunov)) := by
  sorry

end EntropyRateDimension

end OAI
