import OAI.Algebra.FormalGroup.Honda.Universality

namespace OAI

noncomputable section

namespace HeightThree.CanonicalUniversality
open MvPowerSeries HondaTarget HondaConstruction HondaCoordinates HondaSpecialFiber HondaDifferentials

lemma honda_frobenius (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [CharP K p] :
    (hondaLaw p K).toPowerSeries^p =
      expand p hp.out.ne_zero (hondaLaw p K).toPowerSeries := by
  have hm : (hondaLaw p K).toPowerSeries.map (frobenius K p) =
      (hondaLaw p K).toPowerSeries := by
    change ((integralSpecial p).toPowerSeries.map (Int.castRingHom K)).map _ = _
    rw [MvPowerSeries.map_map]
    have hh : (frobenius K p).comp (Int.castRingHom K) = Int.castRingHom K := by ext z; simp
    rw [hh]
    rfl
  rw [← map_frobenius_expand p hp.out.ne_zero, map_expand, hm]

noncomputable def data (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [CharP K p] : ArtinianUniversality.Data p K := by
  let H := (honda_nonlinear_expand p K).choose
  have hH := (honda_nonlinear_expand p K).choose_spec
  have hc := reducedHonda_heightCoordinates p K
  let g := (Ideal.mem_span_singleton.mp hc.2.2.2).choose
  have hg := (Ideal.mem_span_singleton.mp hc.2.2.2).choose_spec
  exact {
    gamma := hondaLaw p K
    family := reducedHonda p K
    family_comm := inferInstance
    special := reducedHonda_specialFiber p K
    honda := integralSpecial_honda p K
    nonlinear := H
    nonlinear_eq := hH
    frobenius := honda_frobenius p K
    first := hc.2.1
    remainder := g
    second := by linear_combination hg }

theorem reducedHonda_isUniversal (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [CharP K p] :
    IsUniversal (hondaLaw p K) (reducedHonda p K) := by
  exact (data p K).isUniversal p

theorem canonical_hasUniversalHeightCoordinates (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [CharP K p] :
    HasUniversalHeightCoordinates p (hondaLaw p K) := by
  exact ⟨reducedHonda p K, inferInstance, reducedHonda_specialFiber p K,
    reducedHonda_isUniversal p K, reducedHonda_heightCoordinates p K⟩

end HeightThree.CanonicalUniversality

end

end OAI
