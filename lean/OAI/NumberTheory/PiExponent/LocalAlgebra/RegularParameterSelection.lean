import OAI.NumberTheory.PiExponent.LocalAlgebra.FinsuppCandidates
import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection2
import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceExtObstruction
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalLowExt

namespace OAI

noncomputable section
universe u
open IsLocalRing RingTheory.Sequence CategoryTheory CategoryTheory.Abelian
namespace PiExponentSiegel.W58

variable (k : Type u) [Field k] (n : ℕ)
variable (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]

theorem polynomialLocal_regular_prefix_maximal_not_associated
    (rs : List (Localization.AtPrime P))
    (hreg : IsRegular (Localization.AtPrime P) rs)
    (hshort : (rs.length : ℕ∞) < P.height) :
    ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime P))
      (Localization.AtPrime P ⧸ Ideal.ofList rs) := by
  intro hass
  obtain ⟨i, hi, hnonzero⟩ :=
    PiExponentJets.W18.regular_sequence_associatedPrime_ext_obstruction
      rs hreg (maximalIdeal (Localization.AtPrime P)) hass
  have hile : (i : ℕ∞) ≤ rs.length := by exact_mod_cast hi
  have hvanish := PiExponentSiegelAux.W30.polynomialLocal_residueExt_below_height
    k n P i (hile.trans_lt hshort)
  change Subsingleton (Ext
    (ModuleCat.of (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ maximalIdeal (Localization.AtPrime P)))
    (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P)) i) at hvanish
  exact hnonzero hvanish

variable [Infinite k]

theorem polynomialLocal_exists_constant_regular_parameters
    {J : Type*} (generators : J → Localization.AtPrime P)
    (hrad : (Ideal.span (Set.range generators)).radical =
      maximalIdeal (Localization.AtPrime P))
    (h : ℕ) (hheight : P.height = (h : ℕ∞)) :
    ∃ cs : List (J →₀ k), cs.length = h ∧
      IsRegular (Localization.AtPrime P)
        (cs.map (Finsupp.linearCombination k generators)) ∧
      Ideal.ofList (cs.map (Finsupp.linearCombination k generators)) ≤
        Ideal.span (Set.range generators) ∧
      (Ideal.ofList (cs.map (Finsupp.linearCombination k generators))).radical =
        maximalIdeal (Localization.AtPrime P) := by
  apply exists_constant_regular_parameters_of_no_maximal_associated
    (k := k) generators hrad h
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P), hheight]
    rfl
  · intro rs hreg hshort
    apply polynomialLocal_regular_prefix_maximal_not_associated k n P rs hreg
    rw [hheight]
    exact_mod_cast hshort

theorem polynomialLocal_exists_constant_regular_parameters_actual_height
    {J : Type*} (generators : J → Localization.AtPrime P)
    (hrad : (Ideal.span (Set.range generators)).radical =
      maximalIdeal (Localization.AtPrime P)) :
    ∃ h : ℕ, P.height = (h : ℕ∞) ∧
      ∃ cs : List (J →₀ k), cs.length = h ∧
        IsRegular (Localization.AtPrime P)
          (cs.map (Finsupp.linearCombination k generators)) ∧
        Ideal.ofList (cs.map (Finsupp.linearCombination k generators)) ≤
          Ideal.span (Set.range generators) ∧
        (Ideal.ofList (cs.map (Finsupp.linearCombination k generators))).radical =
          maximalIdeal (Localization.AtPrime P) := by
  obtain ⟨h, hh, _⟩ :=
    PiExponentJets.PolynomialLocalResidueResolution.exists_regularParameters_actual_height k n P
  exact ⟨h, hh, polynomialLocal_exists_constant_regular_parameters k n P generators hrad h hh⟩

theorem polynomialLocal_exists_degree_bounded_regular_parameters
    {J : Type*} (f : J → MvPolynomial (Fin n) k) (d h : ℕ)
    (hdegree : ∀ j, (f j).totalDegree ≤ d)
    (hheight : P.height = (h : ℕ∞))
    (hrad : ((Ideal.span (Set.range f)).map
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))).radical =
        maximalIdeal (Localization.AtPrime P)) :
    ∃ cs : List (J →₀ k), cs.length = h ∧
      let gs := cs.map (Finsupp.linearCombination k f)
      gs.length = h ∧
      (∀ g ∈ gs, g.totalDegree ≤ d) ∧
      Ideal.ofList gs ≤ Ideal.span (Set.range f) ∧
      IsRegular (Localization.AtPrime P)
        (gs.map (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))) ∧
      ((Ideal.ofList gs).map
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))).radical =
          maximalIdeal (Localization.AtPrime P) := by
  let φ : MvPolynomial (Fin n) k →ₐ[k] Localization.AtPrime P :=
    IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k) (Localization.AtPrime P)
  have hgen : (Ideal.span (Set.range (φ ∘ f))).radical =
      maximalIdeal (Localization.AtPrime P) := by
    change (Ideal.span (Set.range
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P) ∘ f))).radical = _
    simpa only [Ideal.map_span, ← Set.range_comp] using hrad
  obtain ⟨cs, hlen, hreg, _, hmax⟩ :=
    polynomialLocal_exists_constant_regular_parameters k n P (φ ∘ f) hgen h hheight
  have hmap : (cs.map (Finsupp.linearCombination k f)).map
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P)) =
      cs.map (Finsupp.linearCombination k (φ ∘ f)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro c _
    exact Finsupp.apply_linearCombination k φ.toLinearMap f c
  refine ⟨cs, hlen, by simpa only [List.length_map] using hlen, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hg
    exact PiExponentJets.W22.linearCombination_totalDegree_le f c hdegree
  · apply Ideal.span_le.mpr
    intro g hg
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hg
    exact PiExponentJets.W22.linearCombination_mem_ideal f c _
      (fun j => Ideal.subset_span (Set.mem_range_self j))
  · rwa [hmap]
  · rwa [Ideal.map_ofList, hmap]

end PiExponentSiegel.W58

end

end OAI
