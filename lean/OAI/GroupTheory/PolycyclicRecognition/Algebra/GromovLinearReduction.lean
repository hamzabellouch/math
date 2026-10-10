import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicPolynomialNilpotence
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGrowthImages
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicKernelPolynomialGrowth

namespace OAI

/-! # The linear-group reduction in the polynomial-growth theorem

The explicit parameter below is the real-matrix specialization of Tits,
*Free subgroups in linear groups*, J. Algebra 20 (1972), Theorem 1, p.250.
Combined with harmonic representations, degree reduction, and solvable
polynomial-growth estimates, it gives virtual nilpotence.
-/

noncomputable section
namespace PolycyclicRecognition

variable
  (linearStep : ∀ (n : ℕ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℝ)),
    (∀ j : FreeGroup Bool →* H, ¬Function.Injective j) →
    ∃ K : Subgroup H, K.FiniteIndex ∧ Group.IsSolvable K)

include linearStep in
theorem polynomial_growth_virtual_integer_quotient_of_linearStep
    {G : Type} [Group G] [DecidableEq G] [Infinite G]
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d) :
    ∃ H : Subgroup G, H.FiniteIndex ∧
      ∃ q : H →* Multiplicative ℤ, Function.Surjective q := by
  classical
  let : Group.FG G := Group.fg_def.mpr ⟨S, hgen⟩
  obtain ⟨n, ρ, hρ, T, hT, hTgen, hTvol, hfree⟩ :=
    polynomial_growth_linear_image_no_free_pair S hS hgen hvol
  let : Infinite ρ.range := Set.infinite_coe_iff.mpr hρ
  obtain ⟨K, hKi, hKs⟩ := linearStep n ρ.range hfree
  let := hKi
  let := hKs
  obtain ⟨H, hHi, q, hq⟩ :=
    infinite_fg_virtually_solvable_virtual_integer_quotient K
  let := hHi
  let P := H.comap ρ.rangeRestrict
  let f : P →* H :=
    { toFun := fun x => ⟨ρ.rangeRestrict x, x.property⟩
      map_one' := Subtype.ext (map_one ρ.rangeRestrict)
      map_mul' := fun x y => Subtype.ext (map_mul ρ.rangeRestrict (x : G) (y : G)) }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := ρ.rangeRestrict_surjective y.val
    have hxP : x ∈ P := by
      change ρ.rangeRestrict x ∈ H
      rw [hx]
      exact y.property
    exact ⟨⟨x, hxP⟩, Subtype.ext hx⟩
  exact ⟨P, inferInstance, q.comp f, hq.comp hf⟩

theorem IsVirtuallyPolycyclic.exists_solvable_finiteDimension
    {G : Type} [Group G] (h : IsVirtuallyPolycyclic G) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H ∧
      HasFiniteIntegralCohomologicalDimension H := by
  obtain ⟨P, hPi, hP⟩ := h
  let := hPi
  exact exists_solvable_finiteDimension_of_finiteIndex P hP.exists_solvable_finiteDimension

include linearStep in
theorem polynomial_growth_virtually_nilpotent_degree_of_linearStep (d : ℕ) :
    ∀ (G : Type) [Group G] [DecidableEq G],
      ∀ S : Finset G, (∀ s ∈ S, s⁻¹ ∈ S) →
        Subgroup.closure (S : Set G) = ⊤ →
        (∃ C : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d) →
        Group.IsVirtuallyNilpotent G := by
  induction d with
  | zero =>
    intro G _ _ S hS hgen ⟨C, hvol⟩
    let : Finite G := finite_of_bounded_wordBall_card S hS hgen C (by simpa using hvol)
    exact ⟨⊥, inferInstance, inferInstance⟩
  | succ d ih =>
    intro G _ _ S hS hgen ⟨C, hvol⟩
    cases finite_or_infinite G with
    | inl hfin =>
      let := hfin
      exact ⟨⊥, inferInstance, inferInstance⟩
    | inr hinf =>
      let := hinf
      let : Group.FG G := Group.fg_def.mpr ⟨S, hgen⟩
      obtain ⟨H, hHi, q, hq⟩ :=
        polynomial_growth_virtual_integer_quotient_of_linearStep linearStep
          S hS hgen ⟨C, d + 1, hvol⟩
      let := hHi
      obtain ⟨T, hT, hTgen, M, hM⟩ :=
        polynomial_growth_fg_subgroup S hS hgen C (d + 1) hvol H
      obtain ⟨U, hU, hUgen, L, hL⟩ :=
        cyclic_kernel_polynomial_growth_drop T hT hTgen M d hM q hq
      let : Group.FG q.ker := (Group.fg_iff_subgroup_fg q.ker).mpr
        (cyclic_kernel_fg_of_polynomial_growth T hT hTgen ⟨M, d + 1, hM⟩ q hq)
      have hker := ih q.ker U hU hUgen ⟨L, hL⟩
      have hkp := isVirtuallyPolycyclic_of_finitelyGenerated_virtuallyNilpotent q.ker hker
      obtain ⟨t, ht⟩ := hq (Multiplicative.ofAdd 1)
      let : IsCyclic (H ⧸ q.ker) := integerQuotient_isCyclic q t ht
      obtain ⟨V, hVi, hVs, _⟩ := exists_solvable_finiteDimension_of_cyclic_extension
        q.ker hkp.exists_solvable_finiteDimension
      let := hVi
      let := hVs
      exact virtuallyNilpotent_of_finiteIndex H
        (virtually_solvable_polynomial_growth_virtually_nilpotent
          T hT hTgen ⟨M, d + 1, hM⟩ V)

include linearStep in
theorem gromovPolynomialGrowthInput_of_linearStep
    {G : Type} [Group G] [DecidableEq G] : GromovPolynomialGrowthInput G := by
  intro S hS hgen ⟨C, d, hvol⟩
  exact polynomial_growth_virtually_nilpotent_degree_of_linearStep linearStep d G
    S hS hgen ⟨C, hvol⟩

end PolycyclicRecognition

end

end OAI
