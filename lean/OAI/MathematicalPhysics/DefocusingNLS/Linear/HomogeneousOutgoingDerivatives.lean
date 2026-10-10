import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralInterpolation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalOutgoing

namespace OAI

/-! # Differentiated bounds for the constructed outgoing spectral columns -/

open Set Filter Topology Polynomial
open scoped ContDiff

namespace DefocusingNLS

local notation "V₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem homogeneous_circular_positive_derivatives
    (ν νp νm eta : ℂ) (m : ℕ) (q : ℝ → ℂ × ℂ) (Y : ℝ → V₄)
    (L U M : ℝ) (hM : 0 ≤ M)
    (hq : ∀ t, L < t → HasDerivAt q (radialExteriorODEField ν m t (q t)) t)
    (hY : ∀ t, L < t → HasDerivAt Y (circularLeadingField t (Y t) +
      circularBoundedField νp νm eta m (q t).1 (Y t)) t)
    (hbq : ∀ t, U ≤ t → ‖q t‖ ≤ M) (hbY : ∀ t, U ≤ t → ‖Y t‖ ≤ M)
    (P : ℕ → ℂ[X] × ℂ[X])
    (happrox : ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ v : CircularTailSpace, ∀ t, 0 ≤ t →
      Y t = circularPolynomialJet (P j) t + circularUnweight (2 * (j : ℝ)) v t) :
    (∀ k : ℕ, 0 < k → ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in atTop,
      ‖iteratedDeriv k (fun s => (Y s).1.1) t‖ ≤ A * Real.exp (-2 * t)) ∧
    (∀ k : ℕ, 0 < k → ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in atTop,
      ‖iteratedDeriv k (fun s => (Y s).2.1) t‖ ≤ A * Real.exp (-2 * t)) := by
  have hs := homogeneousSpectral_solution_contDiffOn ν νp νm eta m q Y L hq hY
  have hg (i : Fin 6) (k : ℕ) : ∃ C B T : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ t, T ≤ t → ‖iteratedDeriv k (fun s => homogeneousSpectralState q Y s i) t‖ ≤
        B * Real.exp (C * t) := by
    obtain ⟨C, B, T, hC, hB, _hT, hb⟩ :=
      homogeneousSpectral_derivatives_exponential_bound ν νp νm eta m q Y L U M
        hM hq hY hbq hbY i k
    exact ⟨C, B, T, hC, hB, hb⟩
  have hap : ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ A T : ℝ, 0 ≤ A ∧
      ∀ t, T ≤ t → ‖(Y t).1.1 - radialExteriorPolynomialFunction (P j).1 t‖ ≤
        A * Real.exp (-(2 * (j : ℝ)) * t) := by
    intro J
    obtain ⟨j, hj, v, hv⟩ := happrox J
    refine ⟨j, hj, ‖v‖, 0, norm_nonneg _, ?_⟩
    intro t ht
    have he : (Y t).1.1 - radialExteriorPolynomialFunction (P j).1 t =
        (circularUnweight (2 * (j : ℝ)) v t).1.1 := by
      rw [hv t ht]
      simp only [circularPolynomialJet, Prod.fst_add, add_sub_cancel_left]
    rw [he]
    exact (norm_fst_le _).trans ((norm_fst_le _).trans
      ((circularUnweight_norm (2 * (j : ℝ)) t v).trans_eq (mul_comm _ _)))
  have ham : ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ A T : ℝ, 0 ≤ A ∧
      ∀ t, T ≤ t → ‖(Y t).2.1 - radialExteriorPolynomialFunction (P j).2 t‖ ≤
        A * Real.exp (-(2 * (j : ℝ)) * t) := by
    intro J
    obtain ⟨j, hj, v, hv⟩ := happrox J
    refine ⟨j, hj, ‖v‖, 0, norm_nonneg _, ?_⟩
    intro t ht
    have he : (Y t).2.1 - radialExteriorPolynomialFunction (P j).2 t =
        (circularUnweight (2 * (j : ℝ)) v t).2.1 := by
      rw [hv t ht]
      simp only [circularPolynomialJet, Prod.snd_add, Prod.fst_add, add_sub_cancel_left]
    rw [he]
    exact (norm_fst_le _).trans ((norm_snd_le _).trans
      ((circularUnweight_norm (2 * (j : ℝ)) t v).trans_eq (mul_comm _ _)))
  constructor
  · intro k hk
    apply radial_arbitrary_approximation_positive_derivative_decay
      (fun s => (Y s).1.1) (fun j => (P j).1) L hs.fst.fst _ hap k hk
    intro j
    simpa only [homogeneousSpectralState_two] using hg 2 j
  · intro k hk
    apply radial_arbitrary_approximation_positive_derivative_decay
      (fun s => (Y s).2.1) (fun j => (P j).2) L hs.snd.fst _ ham k hk
    intro j
    simpa only [homogeneousSpectralState_four] using hg 4 j

theorem homogeneous_canonical_circular_positive_derivatives
    (ν νp νm eta b : ℂ) (m : ℕ) (L : ℝ)
    (hX : HasRadialExterior ν m b L) (Y : ℝ → V₄) (c : ℂ × ℂ)
    (hY : ∀ t, 0 ≤ t → HasDerivAt Y (circularLeadingField t (Y t) +
      circularBoundedField νp νm eta m (radialExteriorCanonical ν m b L t).1 (Y t)) t)
    (hlim : Tendsto Y atTop (𝓝 ((c.1, 0), (c.2, 0))))
    (happrox : ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ v : CircularTailSpace, ∀ t, 0 ≤ t →
      Y t = circularPolynomialJet
        (spectralOutgoingPolynomial νp νm eta m (radialExteriorExpansion ν m b j) c j) t +
          circularUnweight (2 * (j : ℝ)) v t) :
    (∀ k : ℕ, 0 < k → ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in atTop,
      ‖iteratedDeriv k (fun s => (Y s).1.1) t‖ ≤ A * Real.exp (-2 * t)) ∧
    (∀ k : ℕ, 0 < k → ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in atTop,
      ‖iteratedDeriv k (fun s => (Y s).2.1) t‖ ≤ A * Real.exp (-2 * t)) := by
  let M := max (‖(b, (0 : ℂ))‖ + 1) (‖((c.1, (0 : ℂ)), (c.2, (0 : ℂ)))‖ + 1)
  obtain ⟨Uq, hUq⟩ := eventually_atTop.mp
    ((radialExteriorCanonical_spec hX).2.1.tendsto.norm.eventually
      (gt_mem_nhds (show ‖(b, (0 : ℂ))‖ < ‖(b, (0 : ℂ))‖ + 1 by linarith)))
  obtain ⟨UY, hUY⟩ := eventually_atTop.mp
    (hlim.norm.eventually (gt_mem_nhds
      (show ‖((c.1, (0 : ℂ)), (c.2, (0 : ℂ)))‖ <
        ‖((c.1, (0 : ℂ)), (c.2, (0 : ℂ)))‖ + 1 by linarith)))
  apply homogeneous_circular_positive_derivatives ν νp νm eta m
    (radialExteriorCanonical ν m b L) Y (max L 0) (max Uq UY) M
    (le_trans (by positivity : 0 ≤ ‖(b, (0 : ℂ))‖ + 1) (le_max_left _ _))
    _ _ _ _ _ happrox
  · intro t ht
    exact ((radialExteriorCanonical_spec hX).2.2 t
      ((le_max_left L 0).trans ht.le)).2
  · intro t ht
    exact hY t ((le_max_right L 0).trans ht.le)
  · intro t ht
    exact (hUq t ((le_max_left Uq UY).trans ht)).le.trans (le_max_left _ _)
  · intro t ht
    exact (hUY t ((le_max_right Uq UY).trans ht)).le.trans (le_max_right _ _)

end DefocusingNLS

end OAI
