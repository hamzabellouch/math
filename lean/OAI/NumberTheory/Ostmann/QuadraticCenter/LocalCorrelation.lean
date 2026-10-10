import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationAllScalars
import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationBound
import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationCutoffLiteral
import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationIntervalLog

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

def unitTransformCorrelation {d e : ℕ} [NeZero d] [NeZero e]
    (f : ZMod d → ℂ) (g : ZMod e → ℂ) (c : (ZMod d)ˣ) (c' : (ZMod e)ˣ)
    (s : ZMod (Nat.lcm d e)) : ℂ :=
  Supply.unitaryDFT f ((c : ZMod d) * ZMod.castHom (Nat.dvd_lcm_left d e) (ZMod d) s) *
    conj (Supply.unitaryDFT g ((c' : ZMod e) *
      ZMod.castHom (Nat.dvd_lcm_right d e) (ZMod e) s))

theorem unit_transform_smoothed_correlation_bound {d e : ℕ} [NeZero d] [NeZero e]
    (f : ZMod d → ℂ) (g : ZMod e → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1)
    (c : (ZMod d)ˣ) (c' : (ZMod e)ˣ) (α : ℝ) (a : ℤ) (N : ℕ)
    {R S : ℝ} (hR : 0 < R) (v w w' : ℕ)
    (hN : (N : ℝ) ≤ S) (ha : S ≤ (a : ℝ)) :
    ‖∑ n ∈ Finset.range N,
      (unitTransformCorrelation f g c c' ((a + (n : ℤ) : ℤ) : ZMod (Nat.lcm d e)) *
        weylPhase (((a : ℝ) + n) * α)) *
      quadraticCutoffWeight R d e v w w' ((a : ℝ) + n)‖ ≤
        2 * cutoffFourierBound ^ 2 * ((Nat.gcd d e : ℝ) / (Real.sqrt d * Real.sqrt e)) *
          (2 * N + 2 * Nat.lcm d e * (harmonic (Nat.lcm d e) : ℝ)) := by
  exact periodic_interval_quadratic_cutoff_bound (unitTransformCorrelation f g c c')
    (by positivity) (normalized_unit_transform_correlation_le f g hf hg c c')
    α a N hR d e v w w' (Nat.pos_of_neZero d) (Nat.pos_of_neZero e) hN ha

def centeredCorrelation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℕ) (r : κ → ℕ) [∀ i, NeZero (p i)] [∀ j, NeZero (r j)]
    [NeZero (∏ i, p i)] [NeZero (∏ j, r j)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (hcor : Pairwise (fun i j => (r i).Coprime (r j)))
    (S : ∀ i, Finset (ZMod (p i))) (T : ∀ j, Finset (ZMod (r j)))
    (c : ZMod (∏ i, p i)) (c' : ZMod (∏ j, r j))
    (s : ZMod (Nat.lcm (∏ i, p i) (∏ j, r j))) : ℂ :=
  centeredProductTransform p hcop S (c * ZMod.castHom
    (Nat.dvd_lcm_left (∏ i, p i) (∏ j, r j)) (ZMod (∏ i, p i)) s) *
  conj (centeredProductTransform r hcor T (c' * ZMod.castHom
    (Nat.dvd_lcm_right (∏ i, p i) (∏ j, r j)) (ZMod (∏ j, r j)) s))

theorem centered_correlation_smoothed_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℕ) (r : κ → ℕ) [∀ i, NeZero (p i)] [∀ j, NeZero (r j)]
    [NeZero (∏ i, p i)] [NeZero (∏ j, r j)]
    (hp : ∀ i, (p i).Prime) (hr : ∀ j, (r j).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (hcor : Pairwise (fun i j => (r i).Coprime (r j)))
    (S : ∀ i, Finset (ZMod (p i))) (T : ∀ j, Finset (ZMod (r j)))
    (c : ZMod (∏ i, p i)) (c' : ZMod (∏ j, r j))
    (α : ℝ) (a : ℤ) (N : ℕ) {R H : ℝ} (hR : 0 < R) (v w w' : ℕ)
    (hN : (N : ℝ) ≤ H) (ha : H ≤ (a : ℝ)) :
    ‖∑ n ∈ Finset.range N,
      (centeredCorrelation p r hcop hcor S T c c'
        ((a + (n : ℤ) : ℤ) : ZMod (Nat.lcm (∏ i, p i) (∏ j, r j))) *
        weylPhase (((a : ℝ) + n) * α)) *
      quadraticCutoffWeight R (∏ i, p i) (∏ j, r j) v w w' ((a : ℝ) + n)‖ ≤
        2 * cutoffFourierBound ^ 2 *
          ((Nat.gcd (∏ i, p i) (∏ j, r j) : ℝ) /
            (Real.sqrt ((∏ i, p i : ℕ) : ℝ) * Real.sqrt ((∏ j, r j : ℕ) : ℝ))) *
          (2 * N + 2 * Nat.lcm (∏ i, p i) (∏ j, r j) *
            (harmonic (Nat.lcm (∏ i, p i) (∏ j, r j)) : ℝ)) := by
  exact periodic_interval_quadratic_cutoff_bound (centeredCorrelation p r hcop hcor S T c c')
    (by positivity) (normalized_centeredProduct_correlation_le p r hp hr hcop hcor S T c c')
    α a N hR (∏ i, p i) (∏ j, r j) v w w'
    (Nat.pos_of_neZero _) (Nat.pos_of_neZero _) hN ha

end Ostmann.QuadraticCenter

end

end OAI
