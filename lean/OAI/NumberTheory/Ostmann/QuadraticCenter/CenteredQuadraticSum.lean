import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationCentered
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticSumBound

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def centeredQuadraticAmplitude {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (mInv : ZMod (∏ i, p i))
    (s v w : ℕ) : ℂ :=
  centeredProductTransform p hcop S (-((s * v * w ^ 2 : ℕ) : ZMod (∏ i, p i)) * mInv)

def centeredQuadraticSum {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (mInv : ZMod (∏ i, p i))
    (s v P : ℕ) (R h θ : ℝ) : ℂ :=
  normalizedSmoothQuadraticSum P (Real.sqrt (R / ((s : ℝ) * v / (∏ i, p i : ℕ))))
    (centeredQuadraticAmplitude p hcop S mInv s v)
    ((h + θ) * ((s : ℝ) * v / (∏ i, p i : ℕ)))

theorem centeredQuadraticSum_norm_le {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (mInv : ZMod (∏ i, p i))
    {s v : ℕ} (hs : 0 < s) (hv : 0 < v) (P : ℕ)
    {R : ℝ} (hR : 0 < R) (h θ : ℝ) :
    ‖centeredQuadraticSum p hcop S mInv s v P R h θ‖ ≤
      Real.sqrt ((∏ i, p i : ℕ) : ℝ) * cutoffFourierBound / P := by
  have hd : (0 : ℝ) < (∏ i, p i : ℕ) := by exact_mod_cast Nat.pos_of_neZero (∏ i, p i)
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  apply normalizedSmoothQuadraticSum_bound (by positivity) (Real.sqrt_nonneg _)
  intro w hw
  exact norm_centeredProductTransform_le_sqrt p hcop S _

end Ostmann.QuadraticCenter

end

end OAI
