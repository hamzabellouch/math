import OAI.Probability.SLE.Geometry.InvertedArcComponents
import OAI.Probability.SLE.Geometry.SimpleSlitRiemann

namespace OAI

/-! A Riemann chart including infinity for the complement of a reflected
simple slit. Zero in this domain represents infinity before inversion. -/
noncomputable section
open Set Complex Metric Function
open scoped ComplexConjugate

namespace SLEExactGauge

theorem reflected_slit_inverted_simplyConnected
    (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    IsSimplyConnected (invertedExterior (reflectedArcSet p)) := by
  let q : C(unitInterval,ℂ) := ⟨fun t => conj (p t),Complex.continuous_conj.comp p.continuous⟩
  have hq0 : q 0=0 := by simp [q,h0]
  have hp : ∀ t : unitInterval, 0 < t → p t ≠ 0 := by
    intro t ht he
    have hh := hH t ht.ne'
    simp only [he,upperHalfPlane,mem_ofPred_eq,zero_im,lt_self_iff_false] at hh
  have hq : ∀ t : unitInterval, 0 < t → q t ≠ 0 := by
    intro t ht he
    apply hp t ht
    have hh := congrArg conj he
    simpa [q] using hh
  have he : reflectedArcSet p=range p ∪ range q := by
    unfold reflectedArcSet
    congr 1
    exact (range_comp conj p).symm
  have hK : IsCompact (reflectedArcSet p) := by
    rw [he]
    exact (isCompact_range p.continuous).union (isCompact_range q.continuous)
  have hK0 : (0:ℂ) ∈ reflectedArcSet p := Or.inl ⟨0,h0⟩
  apply TauCeti.isSimplyConnected_of_filledHull_subset (invertedExterior_isOpen hK)
    (invertedExterior_connected hK.isBounded hK0
      (reflectedArc_complement_connected p hi h0 hH))
  intro z hz
  by_contra hzD
  have hb : Bornology.IsBounded
      (connectedComponentIn (invertedExterior (reflectedArcSet p))ᶜ z) := hz
  rw [he] at hzD hb
  exact invertedExterior_two_arcs_components_unbounded p q h0 hq0 hp hq hzD hb

theorem reflected_slit_exists_inverted_disk_chart
    (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    ∃ f : ℂ → ℂ, BijOn f (invertedExterior (reflectedArcSet p)) (ball 0 1) ∧
      DifferentiableOn ℂ f (invertedExterior (reflectedArcSet p)) ∧
      DifferentiableOn ℂ (invFunOn f (invertedExterior (reflectedArcSet p))) (ball 0 1) ∧
      LeftInvOn (invFunOn f (invertedExterior (reflectedArcSet p))) f
        (invertedExterior (reflectedArcSet p)) ∧
      RightInvOn (invFunOn f (invertedExterior (reflectedArcSet p))) f (ball 0 1) := by
  have hK : IsCompact (reflectedArcSet p) := (isCompact_range p.continuous).union
    ((isCompact_range p.continuous).image Complex.continuous_conj)
  apply TauCeti.exists_bijOn_ball_differentiableOn_invFunOn (invertedExterior_isOpen hK)
    (reflected_slit_inverted_simplyConnected p hi h0 hH)
  intro he
  have hp1 : p 1 ≠ 0 := by
    intro hp1
    have ht := hi (hp1.trans h0.symm)
    norm_num at ht
  have hm : (p 1)⁻¹ ∈ invertedExterior (reflectedArcSet p) := by rw [he]; trivial
  rcases hm with hz|hz
  · exact inv_ne_zero hp1 hz
  · apply hz
    rw [inv_inv]
    exact Or.inl (mem_range_self 1)

end SLEExactGauge

end

end OAI
