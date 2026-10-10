import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellReplacementUniform
import OAI.NumberTheory.Ostmann.Conclusion.RegularNorm

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open scoped BigOperators
open Ostmann.Arithmetic.PrimeCellReplacement Ostmann.Arithmetic.PrimeProgression

theorem exists_regularResidueTest_primeCell_constants :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧
      ∀ lo hi : ℝ, L₀ ≤ lo → lo ≤ hi → hi-lo ≤ 1 →
      ∀ (N : ℕ) (Z : ℝ), ⌊Real.exp hi⌋₊ ≤ N → 0 < Z →
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (p : ι → ℕ)
        [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)],
      ∀ hcop : Pairwise (fun i j => (p i).Coprime (p j)),
      ((∏ i, p i : ℕ) : ℝ) ≤ Real.exp (d*lo^(1/3 : ℝ)) →
      ∀ (g : ∀ i, ZMod (p i) → ℂ), (∀ i, g i 0 = 0) →
      (∀ i, ∑ x : ZMod (p i), ‖g i x‖^2 = (p i : ℝ)) →
      ∀ a : ∀ i, (ZMod (p i))ˣ,
      |realTestSum N (∏ i, p i) lo hi Z
          (fun x => regularResidueTest p g a (Ostmann.Supply.crtUnitsEquiv p hcop x))-
        (harmonicIntegral (∏ i, p i) lo hi/Z)*((∏ i, p i : ℕ) : ℝ)| ≤
          ((K/Z)*Real.exp (-d*lo^(1/3 : ℝ)))*((∏ i, p i : ℕ) : ℝ) := by
  obtain ⟨d,K,L₀,hd,hK,hL₀,hAP⟩ := exists_primeCell_replacement_constants
  refine ⟨d,K,L₀,hd,hK,hL₀,?_⟩
  intro lo hi hlo horder hwidth N Z hN hZ ι _ _ p _ _ hcop hmod g hg0 hgnorm a
  have hh := (hAP lo hi hlo horder hwidth N (∏ i, p i) Z hN hZ hmod).2.1
    (fun x => regularResidueTest p g a (Ostmann.Supply.crtUnitsEquiv p hcop x))
    (fun x => regularResidueTest_nonneg p g a _)
  rwa [regularResidueTest_crt_sum p hcop g hg0 hgnorm a] at hh

theorem exists_additiveRegular_primeCell_constants :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧
      ∀ lo hi : ℝ, L₀ ≤ lo → lo ≤ hi → hi-lo ≤ 1 →
      ∀ (N : ℕ) (Z : ℝ), ⌊Real.exp hi⌋₊ ≤ N → 0 < Z →
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (p : ι → ℕ)
        [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)],
      ∀ hcop : Pairwise (fun i j => (p i).Coprime (p j)),
      ((∏ i, p i : ℕ) : ℝ) ≤ Real.exp (d*lo^(1/3 : ℝ)) →
      ∀ S : ∀ i, Finset (ZMod (p i)),
      (∀ i, 0 < Ostmann.Supply.density (S i)) →
      (∀ i, Ostmann.Supply.density (S i) < 1) →
      ∀ a : ∀ i, (ZMod (p i))ˣ,
      realTestSum N (∏ i, p i) lo hi Z
          (fun x => regularResidueTest p (fun i => Ostmann.Supply.additiveTransform (S i)) a
            (Ostmann.Supply.crtUnitsEquiv p hcop x)) ≤
        ((harmonicIntegral (∏ i, p i) lo hi/Z)+
          (K/Z)*Real.exp (-d*lo^(1/3 : ℝ)))*((∏ i, p i : ℕ) : ℝ) := by
  obtain ⟨d,K,L₀,hd,hK,hL₀,hAP⟩ := exists_regularResidueTest_primeCell_constants
  refine ⟨d,K,L₀,hd,hK,hL₀,?_⟩
  intro lo hi hlo horder hwidth N Z hN hZ ι _ _ p _ _ hcop hmod S hpos hlt a
  have hh := hAP lo hi hlo horder hwidth N Z hN hZ ι p hcop hmod
    (fun i => Ostmann.Supply.additiveTransform (S i))
    (fun i => Ostmann.Supply.additiveTransform_zero (S i))
    (fun i => Ostmann.Supply.additiveTransform_parseval (S i) (hpos i) (hlt i)) a
  have hh' := (le_abs_self _).trans hh
  nlinarith

end Ostmann.Conclusion

end

end OAI
