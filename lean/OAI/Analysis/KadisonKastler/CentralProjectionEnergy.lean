import OAI.Analysis.KadisonKastler.ProjectionCommutatorEnergy

namespace OAI

/-! # A commutator gap forces contraction of the central-vector projection -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem centralProjection_pairedCut (K : Submodule ℂ H) [CompleteSpace K]
    {p q : H →L[ℂ] H} (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q)
    (hK : ∀ x ∈ K, p x = q x) (ξ : H) :
    K.starProjection (pairedProjectionCut p q ξ) = K.starProjection ξ := by
  let Q := pairedProjectionCut p q
  have hQ := pairedProjectionCut_isProjection hp hq hc
  have hfix (x : H) (hx : x ∈ K) : Q x = x := by
    have hd : (p - q) x = 0 := by simpa only [sub_apply,sub_eq_zero] using hK x hx
    have hzero : ((p - q) * (p - q)) x = 0 := by rw [mul_apply_eq_comp,hd,map_zero]
    rw [pairedProjectionCut_complement hp hq hc] at hzero
    change x - Q x = 0 at hzero
    exact (sub_eq_zero.mp hzero).symm
  have he : K.starProjection (Q ξ) = K.starProjection ξ := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (K.starProjection_apply_mem ξ)
    intro w hw
    rw [inner_sub_left]
    have hs : Q.adjoint = Q := hQ.isSelfAdjoint.star_eq
    rw [← Q.adjoint_inner_right,hs,hfix w hw]
    simpa only [inner_sub_left] using K.starProjection_inner_eq_zero ξ w hw
  exact he

theorem centralProjection_energy_le (K : Submodule ℂ H) [CompleteSpace K]
    {p q : H →L[ℂ] H} (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q)
    (hK : ∀ x ∈ K, p x = q x) (ξ : H) :
    ‖K.starProjection ξ‖ ^ 2 + ‖(p - q) ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
  have hn : ‖K.starProjection ξ‖ ≤ ‖pairedProjectionCut p q ξ‖ := by
    rw [← centralProjection_pairedCut K hp hq hc hK ξ]
    exact K.norm_starProjection_apply_le _
  have he := pairedProjectionCut_energy hp hq hc ξ
  nlinarith [norm_nonneg (K.starProjection ξ),norm_nonneg (pairedProjectionCut p q ξ)]

theorem centralProjection_contraction_of_gap (K : Submodule ℂ H) [CompleteSpace K]
    {p q : H →L[ℂ] H} (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q)
    (hK : ∀ x ∈ K, p x = q x) (ξ : H) (γ : ℝ)
    (hgap : γ * ‖ξ‖ ^ 2 ≤ ‖(p - q) ξ‖ ^ 2) :
    ‖K.starProjection ξ‖ ^ 2 ≤ (1 - γ) * ‖ξ‖ ^ 2 := by
  have he := centralProjection_energy_le K hp hq hc hK ξ
  nlinarith

end

end KadisonKastler

end OAI
