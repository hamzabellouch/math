import Mathlib

namespace OAI

universe uι

section

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

def SelfSimilar (S : System ι) (μ : Measure ℝ) : Prop :=
  μ = ∑ i, ENNReal.ofReal (S.weight i) • μ.map (S.affine i)

end System

noncomputable def lowerHausdorffDimension (μ : Measure ℝ) : ℝ≥0∞ :=
  ⨅ (E : Set ℝ) (_ : MeasurableSet E) (_ : 0 < μ E), dimH E

namespace Extensions
variable {ι : Type uι} [Fintype ι]

def NoExactOverlaps (S : System ι) : Prop := Function.Injective S.wordAffine

noncomputable def symbolEntropy (S : System ι) : ℝ :=
  ∑ i, Real.negMulLog (S.weight i)

theorem homogeneous_dimension_direct {ι : Type uι} [Fintype ι] [Nonempty ι] (S : System ι)
    {lam : ℝ} (hlam : 0 < lam) (hr : ∀ i, S.ratio i = lam)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (h : NoExactOverlaps S) :
    lowerHausdorffDimension μ =
      ENNReal.ofReal (min 1 (symbolEntropy S / Real.log (1/lam))) := by
  sorry

end Extensions
end EntropyRateDimension
end

open scoped BigOperators ENNReal

namespace CorSetReference
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

noncomputable def codingPoint (r t : ι → ℝ) (ω : ℕ → ι) : ℝ :=
  ∑' n, (∏ j ∈ Finset.range n, r (ω j)) * t (ω n)


noncomputable def attractor (r t : ι → ℝ) : Set ℝ :=
  Set.range (codingPoint r t)


def word (r t : ι → ℝ) : List ι → ℝ × ℝ :=
  List.foldr (fun symbol coefficients =>
    (r symbol * coefficients.1, r symbol * coefficients.2 + t symbol)) (1, 0)

theorem cor_set {ι : Type uι} [Fintype ι] [Nonempty ι]
    (r t : ι → ℝ) (hr0 : ∀ i, 0 < |r i|) (hr1 : ∀ i, |r i| < 1)
    (hno : ∀ u v : List ι, u ≠ [] → v ≠ [] →
      word r t u = word r t v → u = v) :
    IsCompact (attractor r t) ∧ (attractor r t).Nonempty ∧
    (∃! s : ℝ, 0 ≤ s ∧ ∑ i, |r i| ^ s = 1) ∧
    (∀ s : ℝ, 0 ≤ s → (∑ i, |r i| ^ s = 1) →
      dimH (attractor r t) = ENNReal.ofReal (min 1 s)) := by
  sorry

end CorSetReference

end OAI
