import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPerturbationContinuity

namespace OAI

/-! # Joint scale and data continuity of the actual profile propagator

The potential is the derivative of the actual odd-power map.  Its strong
joint continuity and uniform boundedness suffice on a finite slab; the
Schrödinger group is never required to be continuous in operator norm.
-/

open Set

namespace DefocusingNLS

theorem continuous_expandingProfileReaction_family
    {P : Type*} [TopologicalSpace P] (a k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (L : P → {L : ℝ // 1 ≤ L}) (hL : Continuous L)
    (q g : P → C(Icc (0 : ℝ) T, FourierL2)) (hq : Continuous q) (hg : Continuous g) :
    Continuous (fun z : P × ((Icc (0 : ℝ) T) × FourierL2) =>
      expandingProfileReaction a k T ha ha1 hk m
        (expandingRadiusCurve (L z.1).1 T (L z.1).2) (q z.1) (g z.1) z.2) := by
  have hl : Continuous (fun z : P × ((Icc (0 : ℝ) T) × FourierL2) =>
      expandingRadiusCurve (L z.1).1 T (L z.1).2 z.2.1) :=
    (continuous_expandingRadiusCurve_family T L hL).comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hqv : Continuous (fun z : P × ((Icc (0 : ℝ) T) × FourierL2) => q z.1 z.2.1) :=
    continuous_eval.comp ((hq.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))
  have hgv : Continuous (fun z : P × ((Icc (0 : ℝ) T) × FourierL2) => g z.1 z.2.1) :=
    continuous_eval.comp ((hg.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))
  exact (((continuous_expandingLinearization_scale a k ha ha1 hk m).comp
    (hl.prodMk (hqv.prodMk (continuous_snd.comp continuous_snd)))).const_smul
      (-Complex.I : ℂ)).add hgv

theorem continuous_expandingProfileTrajectory_family
    {P : Type*} [TopologicalSpace P] (a b k T R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (m : ℕ) (hR : 0 ≤ R)
    (L : P → {L : ℝ // 1 ≤ L}) (hL : Continuous L)
    (q : P → C(Icc (0 : ℝ) T, FourierL2)) (hq : Continuous q)
    (hqbound : ∀ p t, ‖q p t‖ ≤ R)
    (u₀ : P → FourierL2) (hu₀ : Continuous u₀) :
    Continuous (fun p => expandingProfileTrajectory a b k (L p).1 T ha ha1 hk
      (L p).2 hT m R hR (q p) (hqbound p) (u₀ p)) := by
  obtain ⟨K, hK, hbound⟩ := exists_expandingProfileReaction_lipschitz a k ha ha1 hk m R hR
  let u := fun p => expandingProfileTrajectory a b k (L p).1 T ha ha1 hk
    (L p).2 hT m R hR (q p) (hqbound p) (u₀ p)
  apply continuous_expandingMild_family a b k T K ha hk hT hK L hL
    (fun p => expandingProfileReaction a k T ha ha1 hk m
      (expandingRadiusCurve (L p).1 T (L p).2) (q p) 0)
    (continuous_expandingProfileReaction_family a k T ha ha1 hk m L hL q (fun _ => 0)
      hq continuous_const) u₀ hu₀ u
  · intro p
    apply ContinuousMap.ext
    intro t
    exact expandingProfileTrajectory_eq a b k (L p).1 T ha ha1 hk (L p).2 hT m R hR
      (q p) (hqbound p) (u₀ p) t
  · intro p j t
    exact hbound T (expandingRadiusCurve (L p).1 T (L p).2) (q p) 0 (hqbound p)
      t (u p t) (u j t)

theorem continuous_expandingStepRemainder_family
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
      (u₀ p) (u p)) (hub : ∀ p, ‖u p‖ ≤ 1) :
    Continuous (fun p => u p ⟨T, hT, le_rfl⟩ -
      expandingProfileTrajectory a b k (L p).1 T ha ha1 hk (L p).2 hT m R hR
        (q p) (hqbound p) (u₀ p) ⟨T, hT, le_rfl⟩) :=
  (continuous_eval_const _ |>.comp
    (continuous_expandingPerturbation_family a b k T R ha ha1 hk hT m hR L hL q g
      hq hg hqbound u₀ hu₀ u hu hub)).sub
    (continuous_eval_const _ |>.comp
      (continuous_expandingProfileTrajectory_family a b k T R ha ha1 hk hT m hR
        L hL q hq hqbound u₀ hu₀))

end DefocusingNLS

end OAI
