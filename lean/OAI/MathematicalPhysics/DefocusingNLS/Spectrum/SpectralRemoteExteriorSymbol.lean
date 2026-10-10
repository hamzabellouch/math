import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteApproximationSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemotePolynomialJets
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorUniformRemainder
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialODEGrowthRegularity

namespace OAI

/-! The actual canonical exterior expansions yield uniform logarithmic
symbols once their coarse ODE derivative bounds have been supplied. -/

open Set Filter Topology Polynomial
open scoped ContDiff BoundedContinuousFunction
namespace DefocusingNLS

theorem spectralRemote_exterior_uniform_approximation
    (nu a : ℕ → ℂ) (nu0 a0 : ℂ) (hnu : Tendsto nu atTop (𝓝 nu0))
    (ha : Tendsto a atTop (𝓝 a0)) (delta L : ℝ) (hd : 0 < delta)
    (ha0 : ‖a0‖+2*delta < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (nu n) n (a n) L) (J : ℕ) :
    ∃ j : ℕ, J ≤ j ∧ ∃ A T : ℝ, 0 ≤ A ∧ ∀ᶠ n in atTop, ∀ t, T ≤ t →
      ‖(radialExteriorCanonical (nu n) n (a n) L t).1-
        radialExteriorPolynomialFunction (radialExteriorExpansion (nu n) n (a n) j) t‖ ≤
          A*Real.exp (-(2*(j : ℝ))*t) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (radialExteriorMatrixBound nu0)
  let j := max J k+1
  have hJ : J ≤ j := (le_max_left J k).trans (Nat.le_succ _)
  have hj : radialExteriorMatrixBound nu0 < 2*(j : ℝ) := by
    have hkj : k ≤ j := (le_max_right J k).trans (Nat.le_succ _)
    have hkj' : (k : ℝ) ≤ j := by exact_mod_cast hkj
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  obtain ⟨T,A,_,_,hA,v,w,_,hv,hb⟩ :=
    radialExteriorCanonical_uniform_remainder nu a nu0 a0 hnu ha delta L hd ha0 hX j hj
  refine ⟨j,hJ,A,T,hA,?_⟩
  filter_upwards [hb] with n hn
  intro t ht
  have he := (hn t ht).2.2
  have hdiff : (radialExteriorCanonical (nu n) n (a n) L t).1-
      radialExteriorPolynomialFunction (radialExteriorExpansion (nu n) n (a n) j) t =
      (radialExteriorUnweight (2*(j : ℝ)) (v n) t).1 := by
    rw [he]
    simp only [Prod.fst_add,radialPolynomialJet,add_sub_cancel_left]
  rw [hdiff]
  exact (norm_fst_le _).trans ((radialExteriorUnweight_norm _ t (v n) A
    ((v n).norm_coe_le_norm t |>.trans (hv n))).trans_eq (mul_comm _ _))

theorem spectralRemote_exterior_symbol
    (nu a : ℕ → ℂ) (nu0 a0 : ℂ) (hnu : Tendsto nu atTop (𝓝 nu0))
    (ha : Tendsto a atTop (𝓝 a0)) (delta L : ℝ) (hd : 0 < delta)
    (ha0 : ‖a0‖+2*delta < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (nu n) n (a n) L)
    (S : ℕ → ℝ) (hS : Tendsto S atTop atTop)
    (hgrowth : ∀ k : ℕ, ∃ C B T : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ᶠ n in atTop,
      ∀ t, T ≤ t → ‖iteratedDeriv k (fun s => (radialExteriorCanonical (nu n) n (a n) L s).1) t‖ ≤
        B*Real.exp (C*t)) :
    HasUniformLogJetBound S 0 (fun n t => (radialExteriorCanonical (nu n) n (a n) L t).1) := by
  apply spectralRemote_approximation_symbol _
    (fun n j => radialExteriorPolynomialFunction (radialExteriorExpansion (nu n) n (a n) j)) L S hS
  · filter_upwards [hX] with n hn
    exact radialExteriorODE_position_contDiffOn _ _ _ L (fun t ht =>
      ((radialExteriorCanonical_spec hn).2.2 t ht.le).2)
  · exact fun n j => radialPolynomialFunction_contDiff _
  · exact hgrowth
  · intro j k
    exact spectralRemote_polynomial_jet_bound _ (radialFreeExpansion nu0 a0 j) j k
      (Eventually.of_forall (fun n => radialExteriorExpansion_degree _ _ _ _))
      (radialFreeExpansion_degree _ _ _)
      (fun i _ => radialExteriorExpansion_coefficient_limit nu a nu0 a0 hnu ha (by linarith) j i)
  · exact spectralRemote_exterior_uniform_approximation nu a nu0 a0 hnu ha delta L hd ha0 hX

end DefocusingNLS

end OAI
