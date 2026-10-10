import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSolutionContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPerturbationExistence

namespace OAI

/-! # Continuity of the actual nonlinear perturbation with varying scale

The profile, residual and initial perturbation may all vary continuously.
Every bounded family solving the actual local polynomial equation is then
continuous in the finite-slab norm.  This applies to the small solutions
already constructed by the uniform nonlinear step theorem.
-/

open Set

namespace DefocusingNLS

theorem continuous_expandingRadiusCurve_family
    {P : Type*} [TopologicalSpace P] (T : ℝ)
    (L : P → {L : ℝ // 1 ≤ L}) (hL : Continuous L) :
    Continuous (fun z : P × Icc (0 : ℝ) T =>
      expandingRadiusCurve (L z.1).1 T (L z.1).2 z.2) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp (hL.comp continuous_fst)).mul
    (Real.continuous_exp.comp ((continuous_subtype_val.comp continuous_snd).div_const 2))

theorem continuous_expandingPerturbationReaction_family
    {P : Type*} [TopologicalSpace P] (a k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (L : P → {L : ℝ // 1 ≤ L}) (hL : Continuous L)
    (q g : P → C(Icc (0 : ℝ) T, FourierL2)) (hq : Continuous q) (hg : Continuous g) :
    Continuous (fun z : P × ((Icc (0 : ℝ) T) × FourierL2) =>
      expandingPerturbationReaction a k (L z.1).1 T ha ha1 hk (L z.1).2 m
        (q z.1) (g z.1) z.2) := by
  have hl : Continuous (fun z : P × ((Icc (0 : ℝ) T) × FourierL2) =>
      expandingRadiusCurve (L z.1).1 T (L z.1).2 z.2.1) :=
    (continuous_expandingRadiusCurve_family T L hL).comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hqv : Continuous (fun z : P × ((Icc (0 : ℝ) T) × FourierL2) => q z.1 z.2.1) :=
    continuous_eval.comp ((hq.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))
  have hgv : Continuous (fun z : P × ((Icc (0 : ℝ) T) × FourierL2) => g z.1 z.2.1) :=
    continuous_eval.comp ((hg.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))
  exact ((((continuous_expandingOddPower_scale a k ha ha1 hk m).comp
    (hl.prodMk (hqv.add (continuous_snd.comp continuous_snd)))).sub
    ((continuous_expandingOddPower_scale a k ha ha1 hk m).comp (hl.prodMk hqv))).const_smul
      (-Complex.I : ℂ)).sub hgv

theorem continuous_expandingPerturbation_family
    {P : Type*} [TopologicalSpace P] (a b k T R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (m : ℕ) (hR : 0 ≤ R)
    (L : P → {L : ℝ // 1 ≤ L}) (hL : Continuous L)
    (q g : P → C(Icc (0 : ℝ) T, FourierL2)) (hq : Continuous q) (hg : Continuous g)
    (hqbound : ∀ p t, ‖q p t‖ ≤ R)
    (u₀ : P → FourierL2) (hu₀ : Continuous u₀)
    (u : P → C(Icc (0 : ℝ) T, FourierL2))
    (hu : ∀ p, u p = expandingPicard a b k (L p).1 T ha hk (L p).2 hT
      (expandingPerturbationReaction a k (L p).1 T ha ha1 hk (L p).2 m (q p) (g p))
      (u₀ p) (u p))
    (hub : ∀ p, ‖u p‖ ≤ 1) :
    Continuous u := by
  obtain ⟨K, hK, hlip⟩ := exists_expandingPerturbationReaction_local_lipschitz
    a k ha ha1 hk m R hR
  apply continuous_expandingMild_bounded_family a b k T 1 K ha hk hT hK L hL
    (fun p => expandingPerturbationReaction a k (L p).1 T ha ha1 hk (L p).2 m (q p) (g p))
    (continuous_expandingPerturbationReaction_family a k T ha ha1 hk m L hL q g hq hg)
    u₀ hu₀ u hu
  · intro p t
    exact (ContinuousMap.norm_coe_le_norm (u p) t).trans (hub p)
  · intro p
    exact hlip (L p).1 T (L p).2 (q p) (g p) (hqbound p)

end DefocusingNLS

end OAI
