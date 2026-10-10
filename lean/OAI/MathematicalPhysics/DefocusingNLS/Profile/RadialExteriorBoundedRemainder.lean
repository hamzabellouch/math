import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorUniformRemainder

namespace OAI

/-! Bounded coefficient functions and weighted remainders for the actual
canonical profile, with one common subunit bound. -/

open Filter Topology Set Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialExteriorCanonical_bounded_remainder
    (ν m : ℕ → ℂ) (ν₀ m₀ : ℂ)
    (hν : Tendsto ν atTop (𝓝 ν₀)) (hm : Tendsto m atTop (𝓝 m₀))
    (δ L : ℝ) (hδ : 0 < δ) (hsmall : ‖m₀‖+2*δ < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (ν n) n (m n) L)
    (j : ℕ) (hj : radialExteriorMatrixBound ν₀ < 2*(j : ℝ)) :
    ∃ T ρ C : ℝ, 0 ≤ T ∧ L ≤ T ∧ 0 < ρ ∧ ρ < 1 ∧ 0 ≤ C ∧
      ∃ q e : ℕ → ℝ →ᵇ ℂ,
        (∀ n, ‖e n‖ ≤ C) ∧ (∀ n t, ‖q n t‖ ≤ ρ) ∧
        ∀ᶠ n in atTop, ∀ t, T ≤ t →
          q n t=(radialExteriorCanonical (ν n) n (m n) L t).1 ∧
          ‖radialExteriorPolynomialFunction (radialExteriorExpansion (ν n) n (m n) j) t‖ ≤ ρ ∧
          q n t-radialExteriorPolynomialFunction (radialExteriorExpansion (ν n) n (m n) j) t=
            (Real.exp (-(2*(j : ℝ))*t) : ℂ)*e n t := by
  classical
  obtain ⟨T,C,hT,hLT,hC,v,w,_hvw,hv,hdata⟩ :=
    radialExteriorCanonical_uniform_remainder ν m ν₀ m₀ hν hm δ L hδ hsmall hX j hj
  let ρ := ‖m₀‖+δ
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hX.and hdata)
  let e : ℕ → ℝ →ᵇ ℂ := fun n => BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => (v n t).1) (v n).continuous.fst C
      (fun t => (norm_fst_le _).trans (((v n).norm_coe_le_norm t).trans (hv n)))
  let q : ℕ → ℝ →ᵇ ℂ := fun n => if hn : N ≤ n then
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun t => (radialExteriorCanonical (ν n) n (m n) L (max T t)).1)
      (((radialExteriorCanonical_spec (hN n hn).1).1.fst).comp (continuous_const.max continuous_id))
      ρ (fun t => ((hN n hn).2 (max T t) (le_max_left _ _)).1)
    else 0
  have he (n : ℕ) : ‖e n‖ ≤ C := by
    apply (BoundedContinuousFunction.norm_le hC).mpr
    intro t
    exact (norm_fst_le _).trans (((v n).norm_coe_le_norm t).trans (hv n))
  have hq (n : ℕ) (t : ℝ) : ‖q n t‖ ≤ ρ := by
    by_cases hn : N ≤ n
    · change ‖(if hn : N ≤ n then _ else (0 : ℝ →ᵇ ℂ)) t‖ ≤ _
      rw [dite_eq_left hn]
      exact ((hN n hn).2 (max T t) (le_max_left _ _)).1
    · simp only [q,dite_eq_right hn]
      change ‖(0 : ℂ)‖ ≤ ρ
      simpa only [norm_zero] using hρ.le
  refine ⟨T,ρ,C,hT,hLT,hρ,hρ1,hC,q,e,he,hq,?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn t ht
  have hqt : q n t=(radialExteriorCanonical (ν n) n (m n) L t).1 := by
    dsimp only [q]
    rw [dite_eq_left hn]
    change (radialExteriorCanonical (ν n) n (m n) L (max T t)).1=_
    rw [max_eq_right ht]
  refine ⟨hqt,((hN n hn).2 t ht).2.1,?_⟩
  rw [hqt]
  have hh := congrArg Prod.fst (((hN n hn).2 t ht).2.2)
  rw [hh]
  simp only [radialPolynomialJet,Prod.fst_add,radialExteriorUnweight,
    Prod.smul_fst,Complex.real_smul,add_sub_cancel_left]
  rfl

end DefocusingNLS

end OAI
