import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLogCoefficients
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingDerivatives

namespace OAI

/-! # Normalized falling-Euler derivatives of the outgoing columns

Factoring the exact physical exponential leaves only a finite recurrence
in the bounded normalized jets. This is the value-row estimate needed in
the transverse-defect argument.
-/

open Set Filter Topology
open scoped ContDiff

namespace DefocusingNLS

local notation "V" => ℂ × ℂ
local notation "V₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem HasLogJetBound.of_tendsto_positive_decay
    (f : ℝ → ℂ) (L : ℝ) (c : ℂ) (hf : ContDiffOn ℝ ∞ f (Ioi L))
    (hlim : Tendsto f atTop (𝓝 c))
    (hb : ∀ k : ℕ, 0 < k → ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in atTop,
      ‖iteratedDeriv k f t‖ ≤ A * Real.exp (-2 * t)) : HasLogJetBound 0 f := by
  refine ⟨⟨L, hf⟩, ?_⟩
  intro k
  cases k with
  | zero =>
      refine ⟨‖c‖ + 1, by positivity, ?_⟩
      simpa only [iteratedDeriv_zero, zero_mul, Real.exp_zero, mul_one] using
        (hlim.norm.eventually (gt_mem_nhds (show ‖c‖ < ‖c‖ + 1 by linarith))).mono
          (fun _ h => h.le)
  | succ k =>
      obtain ⟨A, hA, hbound⟩ := hb (k + 1) (by omega)
      refine ⟨A, hA, ?_⟩
      filter_upwards [hbound, eventually_ge_atTop (0 : ℝ)] with t ht ht0
      simpa only [zero_mul, Real.exp_zero, mul_one] using ht.trans
        (mul_le_of_le_one_right hA (Real.exp_le_one_iff.mpr (by linarith)))

theorem homogeneous_canonical_circular_value_logJets
    (ν νp νm eta b : ℂ) (m : ℕ) (L : ℝ)
    (hX : HasRadialExterior ν m b L) (Y : ℝ → V₄) (c : V)
    (hY : ∀ t, 0 ≤ t → HasDerivAt Y (circularLeadingField t (Y t) +
      circularBoundedField νp νm eta m (radialExteriorCanonical ν m b L t).1 (Y t)) t)
    (hlim : Tendsto Y atTop (𝓝 ((c.1, 0), (c.2, 0))))
    (happrox : ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ v : CircularTailSpace, ∀ t, 0 ≤ t →
      Y t = circularPolynomialJet
        (spectralOutgoingPolynomial νp νm eta m (radialExteriorExpansion ν m b j) c j) t +
          circularUnweight (2 * (j : ℝ)) v t) :
    HasLogJetBound 0 (fun t => (Y t).1.1) ∧
      HasLogJetBound 0 (fun t => (Y t).2.1) := by
  have hs := homogeneousSpectral_solution_contDiffOn ν νp νm eta m
    (radialExteriorCanonical ν m b L) Y (max L 0)
    (fun t ht => ((radialExteriorCanonical_spec hX).2.2 t
      ((le_max_left L 0).trans ht.le)).2)
    (fun t ht => hY t ((le_max_right L 0).trans ht.le))
  obtain ⟨hp, hm⟩ := homogeneous_canonical_circular_positive_derivatives
    ν νp νm eta b m L hX Y c hY hlim happrox
  exact ⟨HasLogJetBound.of_tendsto_positive_decay _ _ c.1 hs.fst.fst
      hlim.fst_nhds.fst_nhds hp,
    HasLogJetBound.of_tendsto_positive_decay _ _ c.2 hs.snd.fst
      hlim.snd_nhds.fst_nhds hm⟩

noncomputable def homogeneousNormalizedEuler (ν : ℂ) (f : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => f
  | n + 1 => fun t => deriv (homogeneousNormalizedEuler ν f n) t +
      (ν - (n : ℂ)) * homogeneousNormalizedEuler ν f n t

theorem homogeneousNormalizedEuler_smooth (ν : ℂ) (f : ℝ → ℂ) (L : ℝ)
    (hf : ContDiffOn ℝ ∞ f (Ioi L)) (n : ℕ) :
    ContDiffOn ℝ ∞ (homogeneousNormalizedEuler ν f n) (Ioi L) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
      exact (ih.deriv_of_isOpen isOpen_Ioi (by simp)).add (contDiffOn_const.mul ih)

theorem homogeneousNormalizedEuler_bound (ν : ℂ) (f : ℝ → ℂ)
    (hf : HasLogJetBound 0 f) (n : ℕ) :
    HasLogJetBound 0 (homogeneousNormalizedEuler ν f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih.deriv.add (ih.const_mul _)

theorem homogeneousEulerDeriv_normalized (νp νm : ℂ) (f g : ℝ → ℂ) (L : ℝ)
    (hf : ContDiffOn ℝ ∞ f (Ioi L)) (hg : ContDiffOn ℝ ∞ g (Ioi L)) (n : ℕ) :
    ∀ t, L < t →
      homogeneousEulerDeriv
        (fun s => (Complex.exp (νp * (s : ℂ)) * f s,
          Complex.exp (νm * (s : ℂ)) * g s)) n t =
        (Complex.exp (νp * (t : ℂ)) * homogeneousNormalizedEuler νp f n t,
          Complex.exp (νm * (t : ℂ)) * homogeneousNormalizedEuler νm g n t) := by
  induction n with
  | zero => intro t ht; rfl
  | succ n ih =>
      intro t ht
      let fp := homogeneousNormalizedEuler νp f n
      let fm := homogeneousNormalizedEuler νm g n
      have hfp : HasDerivAt fp (deriv fp t) t :=
        (((homogeneousNormalizedEuler_smooth νp f L hf n) t ht).contDiffAt
          (Ioi_mem_nhds ht)).differentiableAt (by simp) |>.hasDerivAt
      have hfm : HasDerivAt fm (deriv fm t) t :=
        (((homogeneousNormalizedEuler_smooth νm g L hg n) t ht).contDiffAt
          (Ioi_mem_nhds ht)).differentiableAt (by simp) |>.hasDerivAt
      have hp := ((hasDerivAt_id t).ofReal_comp.const_mul νp).cexp
      have hm := ((hasDerivAt_id t).ofReal_comp.const_mul νm).cexp
      simp only [id_eq, Complex.ofReal_one, mul_one] at hp hm
      have hEq : homogeneousEulerDeriv
          (fun s => (Complex.exp (νp * (s : ℂ)) * f s,
            Complex.exp (νm * (s : ℂ)) * g s)) n =ᶠ[𝓝 t]
          (fun s => (Complex.exp (νp * (s : ℂ)) * fp s,
            Complex.exp (νm * (s : ℂ)) * fm s)) := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        exact ih s hs
      have hd := ((hp.mul hfp).prodMk (hm.mul hfm)).congr_of_eventuallyEq hEq
      change deriv (homogeneousEulerDeriv _ n) t - (n : ℝ) •
        homogeneousEulerDeriv _ n t = _
      rw [hd.deriv, ih t ht]
      apply Prod.ext
      all_goals
        simp only [homogeneousNormalizedEuler, Prod.fst_sub, Prod.snd_sub,
          Prod.smul_fst, Prod.smul_snd, Complex.real_smul, fp, fm]
        push_cast
        ring

end DefocusingNLS

end OAI
