import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellJointReplacementAlgebra
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellJointReplacementPrior

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellReplacement
open PrimeProgression
open scoped BigOperators

theorem jointComplexTestSum_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) (M : ℕ) [NeZero M] (lo hi Z main E : ι → ℝ)
    (F : (ι → (ZMod M)ˣ) → ℂ) {ε B : ℝ} (hε : 0 ≤ ε) (hB : 1 ≤ B)
    (hE : ∀ i, E i ≤ ε) (hbound : ∀ i, |main i| + E i ≤ B)
    (hmass : ∀ i (u : (ZMod M)ˣ),
      |residueMass (N i) M u (lo i) (hi i) (Z i) - main i| ≤ E i) :
    ‖jointComplexTestSum N M lo hi Z F -
      (∏ i, (main i : ℂ)) * ∑ u : ι → (ZMod M)ˣ, F u‖ ≤
      Fintype.card ι * ε * B ^ Fintype.card ι * ∑ u : ι → (ZMod M)ˣ, ‖F u‖ := by
  classical
  have hμ : ∀ i (u : (ZMod M)ˣ),
      ‖(residueMass (N i) M u (lo i) (hi i) (Z i) : ℂ)‖ ≤ B := by
    intro i u
    have ht := abs_add_le (residueMass (N i) M u (lo i) (hi i) (Z i) - main i) (main i)
    rw [sub_add_cancel] at ht
    simp only [Complex.norm_real, Real.norm_eq_abs]
    linarith [hmass i u, hbound i]
  have hν : ∀ i (u : (ZMod M)ˣ), ‖(main i : ℂ)‖ ≤ B := by
    intro i u
    have he0 : 0 ≤ E i := (abs_nonneg _).trans (hmass i 1)
    simp only [Complex.norm_real, Real.norm_eq_abs]
    linarith [hbound i]
  have he : ∀ i (u : (ZMod M)ˣ),
      ‖(residueMass (N i) M u (lo i) (hi i) (Z i) : ℂ) - (main i : ℂ)‖ ≤ ε := by
    intro i u
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using
      (hmass i u).trans (hE i)
  have h := joint_product_test_error
    (fun i (u : (ZMod M)ˣ) => (residueMass (N i) M u (lo i) (hi i) (Z i) : ℂ))
    (fun i (_ : (ZMod M)ˣ) => (main i : ℂ)) F hε hB hμ hν he
  rw [jointComplexTestSum_eq]
  simpa only [Finset.mul_sum] using h

theorem exists_joint_primeCell_replacement_constants :
    ∃ d K L₀ : ℝ, 0 < d ∧ 0 < K ∧ 1 ≤ L₀ ∧
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (N : ι → ℕ) (M : ℕ) [NeZero M]
        (lo hi Z : ι → ℝ),
        (∀ i, L₀ ≤ lo i ∧ lo i ≤ hi i ∧ hi i - lo i ≤ 1 ∧
          ⌊Real.exp (hi i)⌋₊ ≤ N i ∧ 0 < Z i ∧
          (M : ℝ) ≤ Real.exp (d * (lo i) ^ (1 / 3 : ℝ))) →
        ∀ ε B : ℝ, 0 ≤ ε → 1 ≤ B →
          (∀ i, (K / Z i) * Real.exp (-d * (lo i) ^ (1 / 3 : ℝ)) ≤ ε) →
          (∀ i, |harmonicIntegral M (lo i) (hi i) / Z i| +
            (K / Z i) * Real.exp (-d * (lo i) ^ (1 / 3 : ℝ)) ≤ B) →
          ∀ F : (ι → (ZMod M)ˣ) → ℂ,
            ‖jointComplexTestSum N M lo hi Z F -
              (∏ i, ((harmonicIntegral M (lo i) (hi i) / Z i : ℝ) : ℂ)) *
                ∑ u : ι → (ZMod M)ˣ, F u‖ ≤
              Fintype.card ι * ε * B ^ Fintype.card ι *
                ∑ u : ι → (ZMod M)ˣ, ‖F u‖ := by
  obtain ⟨d, K, L₀, hd, hK, hL₀, h⟩ := exists_primeCell_replacement_constants
  refine ⟨d, K, L₀, hd, hK, hL₀, ?_⟩
  intro ι _ _ N M _ lo hi Z hcell ε B hε hB hE hbound F
  apply jointComplexTestSum_error N M lo hi Z
    (fun i => harmonicIntegral M (lo i) (hi i) / Z i)
    (fun i => (K / Z i) * Real.exp (-d * (lo i) ^ (1 / 3 : ℝ))) F hε hB hE hbound
  intro i u
  obtain ⟨hlo, hlohi, hlen, hN, hZ, hmod⟩ := hcell i
  exact (h (lo i) (hi i) hlo hlohi hlen (N i) M (Z i) hN hZ hmod).1 u u.isUnit

end Ostmann.Arithmetic.PrimeCellReplacement

end

end OAI
