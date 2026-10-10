import OAI.NumberTheory.JointDickman.Counting.CountingSamplingMean
import OAI.NumberTheory.JointDickman.Counting.CountingApplicationScale
import OAI.NumberTheory.JointDickman.Counting.CountingOriginParameter

namespace OAI

/-! # Sampling at the manuscript's actual block and cutoff scales -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem counting_sampling_actual_scale
    (hFord : FordUpperSieveInput) (hSD : SquarefreeSelbergDelangeInput)
    (hSW : SquarefreeCharacterEstimateInput) (hM : PrimeReciprocalMertensInput)
    (hMP : PrimeProductMertensInput) (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    {L A : ℕ} {cap : ℝ} (hL : 10000 ≤ L) (hA : 0 < A) (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
      ∀ w ε : ℝ, 0 < w → 0 < ε →
      ∃ P : MvPolynomial (Fin 4) ℝ, ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ D m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ Cmin Kerror : ℝ, 0 ≤ Cmin ∧ 0 ≤ Kerror ∧
      ∀ᶠ B : ℕ in atTop, ∀ C : ℝ, Cmin ≤ C →
      ∀ J : ℕ, ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop,
        (∑ u ∈ range (J*N), countingArithmeticCutError P m B L (amplificationMultiplier B)
          (amplificationMultiplier B/A) (A*amplificationMultiplier B) τ C w c D
          (countingOriginParameter (amplificationMultiplier B) N u) u)/(N : ℝ) <
          (J : ℝ)*(ε+Kerror/(B : ℝ))+δ := by
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  obtain ⟨τ,hτ,hτcap,hτsmall,hsample⟩ := counting_sampling_slow_mean hFord hSD hSW hM hMP
    hL (by positivity : 0 < 1/(2*(A : ℝ))) hcap
  refine ⟨τ,hτ,hτcap,hτsmall,?_⟩
  intro w ε hw hε
  obtain ⟨P,c,hc,D,m,hm,Cmin,Kerror,hCmin,hKerror,hs⟩ :=
    hsample w ((A : ℝ)/2) A ε hw (by positivity) (Nat.cast_nonneg _) hε
  refine ⟨P,c,hc,D,m,hm,Cmin,Kerror,hCmin,hKerror,?_⟩
  filter_upwards [hs,countingMajorDenominator_valid,counting_block_scale hA,
    amplificationMultiplier_comparable] with B hb hQ hscale hT
  intro C hC J δ hδ
  let S := dyadicBoxIndices (dyadicBoxLower B (amplificationMultiplier B))
    (dyadicBoxUpper B (amplificationMultiplier B))
  let f := fun k : ℤ => ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊
  let g := fun k : ℤ => ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/amplificationMultiplier B)⌋₊
  let U := max (∏ p ∈ auxiliaryPrimes B,p) (S.sup f)
  let V := max ⌊Real.exp (2*(B : ℝ))⌋₊ (S.sup g)
  have hh := hb C (amplificationMultiplier B/A) (A*amplificationMultiplier B) U V
    (countingMajorDenominator B) hC (le_max_left _ _) (le_max_left _ _)
    (fun k hk => (le_sup (f := f) hk).trans (le_max_right _ _))
    (fun k hk => (le_sup (f := g) hk).trans (le_max_right _ _))
    hQ.1 hQ.2.1 hQ.2.2 hscale.1 hscale.2.1 (by simpa only [Nat.cast_mul] using hscale.2.2.1) hscale.2.2.2.1 hscale.2.2.2.2
    (hMC B _) J δ hδ
  filter_upwards [hh] with N hN
  exact hN (countingOriginParameter (amplificationMultiplier B) N)
    (countingOriginParameter_bound _ _)
    (countingOriginParameter_step hT.1 N _)

end JointDickman

end OAI
