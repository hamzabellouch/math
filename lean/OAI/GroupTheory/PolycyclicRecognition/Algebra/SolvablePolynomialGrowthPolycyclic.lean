import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGrowthSubgroups
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SolvableIntegerQuotient
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicKernelPolynomialGrowth
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SolvableFiniteExtension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntegerQuotientStructure

namespace OAI

/-! # Polynomial growth forces polycyclicity in a solvable group

Induct on the integer growth degree. A virtual quotient to the integers gives
a finitely generated solvable kernel with strictly lower degree. Its cyclic
extension is polycyclic, and the final finite solvable extension is polycyclic.
-/

noncomputable section
namespace PolycyclicRecognition

theorem solvable_polynomial_growth_polycyclic_degree (d : ℕ) :
    ∀ (G : Type) [Group G] [DecidableEq G] [Group.FG G] [Group.IsSolvable G],
      ∀ (S : Finset G), (∀ s ∈ S, s⁻¹ ∈ S) →
        Subgroup.closure (S : Set G) = ⊤ →
        (∃ C : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d) →
        IsPolycyclic G := by
  induction d with
  | zero =>
    intro G _ _ _ _ S hS hgen ⟨C, hvol⟩
    have : Finite G := finite_of_bounded_wordBall_card S hS hgen C (by simpa using hvol)
    exact isPolycyclic_of_finite_solvable
  | succ d ih =>
    intro G _ _ _ _ S hS hgen ⟨C, hvol⟩
    cases finite_or_infinite G with
    | inl hfin =>
      let := hfin
      exact isPolycyclic_of_finite_solvable
    | inr hinf =>
      let := hinf
      obtain ⟨H, hHi, q, hq⟩ := infinite_fg_solvable_virtual_integer_quotient G
      let := hHi
      obtain ⟨T, hT, hTgen, K, hTvol⟩ :=
        polynomial_growth_fg_subgroup S hS hgen C (d + 1) hvol H
      obtain ⟨U, hU, hUgen, L, hUvol⟩ :=
        cyclic_kernel_polynomial_growth_drop T hT hTgen K d hTvol q hq
      have hfg := cyclic_kernel_fg_of_polynomial_growth T hT hTgen
        ⟨K, d + 1, hTvol⟩ q hq
      let : Group.FG q.ker := (Group.fg_iff_subgroup_fg q.ker).mpr hfg
      have hker : IsPolycyclic q.ker := ih q.ker U hU hUgen ⟨L, hUvol⟩
      obtain ⟨t, ht⟩ := hq (Multiplicative.ofAdd 1)
      let : IsCyclic (H ⧸ q.ker) := integerQuotient_isCyclic q t ht
      have hH : IsPolycyclic H :=
        isPolycyclic_of_normal_subgroup q.ker hker isPolycyclic_of_isCyclic
      exact (show IsVirtuallyPolycyclic G from ⟨H, hHi, hH⟩).polycyclic_of_solvable

theorem solvable_polynomial_growth_polycyclic
    {G : Type} [Group G] [DecidableEq G] [Group.FG G] [Group.IsSolvable G]
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d) :
    IsPolycyclic G := by
  obtain ⟨C, d, hvol⟩ := hvol
  exact solvable_polynomial_growth_polycyclic_degree d G S hS hgen ⟨C, hvol⟩

theorem virtually_solvable_polynomial_growth_virtually_polycyclic
    {G : Type} [Group G] [DecidableEq G] [Group.FG G]
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (H : Subgroup G) [H.FiniteIndex] [Group.IsSolvable H] :
    IsVirtuallyPolycyclic G := by
  classical
  obtain ⟨C, d, hvol⟩ := hvol
  obtain ⟨T, hT, hTgen, K, hTvol⟩ :=
    polynomial_growth_fg_subgroup S hS hgen C d hvol H
  exact ⟨H, inferInstance, solvable_polynomial_growth_polycyclic
    T hT hTgen ⟨K, d, hTvol⟩⟩

end PolycyclicRecognition

end

end OAI
