import OAI.Probability.SLE.Geometry.InvertedArcComponents

namespace OAI

/-! The upper component of the inverted reflected-slit domain is a
conjugate-inversion image of the original half-plane slit domain. -/
noncomputable section
open Set Complex Function
open scoped ComplexConjugate

namespace SLEExactGauge

def conjugateInversion (z : ℂ) : ℂ := (conj z)⁻¹

@[simp] lemma conjugateInversion_involutive (z : ℂ) :
    conjugateInversion (conjugateInversion z)=z := by
  simp only [conjugateInversion,map_inv₀,conj_conj,inv_inv]

lemma conjugateInversion_upper {z : ℂ} (hz : z ∈ upperHalfPlane) :
    conjugateInversion z ∈ upperHalfPlane := by
  have hzn : z ≠ 0 := by
    intro he
    simp only [upperHalfPlane,mem_ofPred_eq,he,zero_im,lt_self_iff_false] at hz
  change 0 < ((conj z)⁻¹).im
  rw [inv_im,conj_im,neg_neg]
  exact div_pos hz (normSq_pos.mpr (by simpa using hzn))

theorem reflected_inverted_upper_image
    (p : C(unitInterval,ℂ)) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    invertedExterior (reflectedArcSet p) ∩ upperHalfPlane =
      conjugateInversion '' (upperHalfPlane \ range p) := by
  have hp : ∀ t, 0 ≤ (p t).im := by
    intro t
    by_cases ht : t=0
    · simp [ht,h0]
    · exact (hH t ht).le
  have hn : ∀ z ∈ upperHalfPlane, z ≠ (0:ℂ) := by
    intro z hz he
    simp only [upperHalfPlane,mem_ofPred_eq,he,zero_im,lt_self_iff_false] at hz
  apply Subset.antisymm
  · rintro z ⟨hzD,hzH⟩
    have hzn := hn z hzH
    have hnot : conjugateInversion z ∉ range p := by
      intro he
      have hzinv : z⁻¹ ∈ reflectedArcSet p := by
        right
        refine ⟨conjugateInversion z,he,?_⟩
        simp only [conjugateInversion,map_inv₀,conj_conj]
      exact (hzD.resolve_left hzn) hzinv
    exact ⟨conjugateInversion z,⟨conjugateInversion_upper hzH,hnot⟩,
      conjugateInversion_involutive z⟩
  · rintro z ⟨w,⟨hwH,hwP⟩,rfl⟩
    refine ⟨Or.inr ?_,conjugateInversion_upper hwH⟩
    intro he
    have hwInv : (conj w) ∈ reflectedArcSet p := by
      simpa only [conjugateInversion,inv_inv] using he
    rcases hwInv with ⟨t,ht⟩|⟨v,hv,heq⟩
    · have hh := congrArg Complex.im ht
      rw [conj_im] at hh
      have hpt := hp t
      change 0 < w.im at hwH
      linarith
    · have hvw : v=w := by
        have hh := congrArg conj heq
        simpa only [conj_conj] using hh
      exact hwP (hvw ▸ hv)

theorem reflected_inverted_upper_connected
    (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    IsConnected (invertedExterior (reflectedArcSet p) ∩ upperHalfPlane) := by
  rw [reflected_inverted_upper_image p h0 hH]
  apply (simple_arc_halfPlane_complement_connected p hi h0 hH).image
  intro z hz
  have hzn : conj z ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [conj_im,zero_im] at hh
    have hzH := hz.1
    change 0 < z.im at hzH
    linarith
  exact (Complex.continuous_conj.continuousAt.inv₀ hzn).continuousWithinAt

end SLEExactGauge

end

end OAI
