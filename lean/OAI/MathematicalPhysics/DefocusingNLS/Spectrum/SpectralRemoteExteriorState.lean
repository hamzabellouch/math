import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteExteriorSymbol

namespace OAI

/-! A common bounded tail for the position and velocity of the actual
canonical exterior profiles. -/

open Set Filter Topology Polynomial
namespace DefocusingNLS

theorem spectralRemote_exterior_state_bound
    (nu a : ℕ → ℂ) (nu0 a0 : ℂ) (hnu : Tendsto nu atTop (𝓝 nu0))
    (ha : Tendsto a atTop (𝓝 a0)) (delta L : ℝ) (hd : 0 < delta)
    (ha0 : ‖a0‖+2*delta < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (nu n) n (a n) L) :
    ∃ T M : ℝ, 0 ≤ T ∧ L ≤ T ∧ 1 ≤ M ∧ ∀ᶠ n in atTop, ∀ t, T ≤ t →
      ‖radialExteriorCanonical (nu n) n (a n) L t‖ ≤ M ∧
      ‖(radialExteriorCanonical (nu n) n (a n) L t).1‖ ≤ ‖a0‖+delta := by
  obtain ⟨j,hj⟩ := exists_nat_gt (radialExteriorMatrixBound nu0)
  have hj' : radialExteriorMatrixBound nu0 < 2*(j : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  obtain ⟨T,C,hT,hLT,hC,v,w,_,hv,hb⟩ :=
    radialExteriorCanonical_uniform_remainder nu a nu0 a0 hnu ha delta L hd ha0 hX j hj'
  let P := fun n => radialExteriorExpansion (nu n) n (a n) j
  let Q := radialFreeExpansion nu0 a0 j
  have hdeg : ∀ᶠ n in atTop, (P n).natDegree ≤ j :=
    Eventually.of_forall (fun n => radialExteriorExpansion_degree _ _ _ _)
  have hc : ∀ i, i ≤ j → Tendsto (fun n => (P n).coeff i) atTop (𝓝 (Q.coeff i)) :=
    fun i _ => radialExteriorExpansion_coefficient_limit nu a nu0 a0 hnu ha (by linarith) j i
  obtain ⟨D0,hD0,h0⟩ := spectralRemote_polynomial_jet_bound P Q j 0 hdeg
    (radialFreeExpansion_degree _ _ _) hc
  obtain ⟨D1,hD1,h1⟩ := spectralRemote_polynomial_jet_bound P Q j 1 hdeg
    (radialFreeExpansion_degree _ _ _) hc
  refine ⟨T,max (D0+D1+C) 1,hT,hLT,le_max_right _ _,?_⟩
  filter_upwards [hb,h0,h1] with n hn h0n h1n
  intro t ht
  refine ⟨?_,(hn t ht).1⟩
  have htp : 0 ≤ t := hT.trans ht
  have hp : ‖radialPolynomialJet (P n) t‖ ≤ D0+D1 := by
    change max ‖radialExteriorPolynomialFunction (P n) t‖
      ‖radialExteriorPolynomialFunction (radialPolynomialEuler (P n)) t‖ ≤ _
    apply max_le
    · exact (h0n t htp).trans (le_add_of_nonneg_right hD1)
    · have he : iteratedDeriv 1 (radialExteriorPolynomialFunction (P n)) t =
          radialExteriorPolynomialFunction (radialPolynomialEuler (P n)) t := by
        rw [iteratedDeriv_radialExteriorPolynomial]
        rfl
      rw [← he]
      exact (h1n t htp).trans (le_add_of_nonneg_left hD0)
  have hu : ‖radialExteriorUnweight (2*(j : ℝ)) (v n) t‖ ≤ C := by
    apply (radialExteriorUnweight_norm _ t (v n) C
      ((v n).norm_coe_le_norm t |>.trans (hv n))).trans
    apply mul_le_of_le_one_left hC
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (by positivity)) htp)
  rw [(hn t ht).2.2]
  exact ((norm_add_le _ _).trans (add_le_add hp hu)).trans (le_max_left _ _)

end DefocusingNLS

end OAI
