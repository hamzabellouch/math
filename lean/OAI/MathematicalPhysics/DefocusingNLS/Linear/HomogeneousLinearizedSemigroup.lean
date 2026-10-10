import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearizedRestart

namespace OAI

/-! # The actual homogeneous linearized semigroup

Finite-slab solutions agree on their common interval and restart at every
nonnegative time. These identities give the strongly continuous evolution
whose time-one map enters the finite-rank decomposition.
-/

open Set Filter Topology
open scoped NNReal

namespace DefocusingNLS

attribute [local irreducible] homogeneousFreeOperator

section

variable (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
  (m : ℕ) (q : HomogeneousY a k)

noncomputable def homogeneousLinearizedStep (t : ℝ≥0) :
    HomogeneousY a k →L[ℝ] HomogeneousY a k :=
  (ContinuousMap.evalCLM (R := ℝ) ⟨(t : ℝ), t.2, le_rfl⟩).comp
    (homogeneousLinearizedPropagator a b k t ha ha1 hk t.2 m q)

theorem homogeneousLinearizedStep_eq_slab (T : ℝ) (hT : 0 ≤ T)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ T) (f : HomogeneousY a k) :
    homogeneousLinearizedStep a b k ha ha1 hk m q t f =
      homogeneousLinearizedTrajectory a b k T ha ha1 hk hT m q f ⟨t, t.2, ht⟩ := by
  symm
  exact homogeneousLinearizedTrajectory_restrict a b k t T ha ha1 hk t.2 ht m q f
    ⟨t, t.2, le_rfl⟩

@[simp] theorem homogeneousLinearizedStep_zero :
    homogeneousLinearizedStep a b k ha ha1 hk m q 0 = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro f
  change homogeneousLinearizedTrajectory a b k 0 ha ha1 hk (by positivity) m q f
    ⟨0, le_rfl, le_rfl⟩ = f
  rw [homogeneousLinearizedTrajectory_eq]
  simp only [homogeneousFreeOperator_zero, homogeneousDuhamel, intervalIntegral.integral_same,
    add_zero]

theorem homogeneousLinearizedStep_add (s t : ℝ≥0) :
    homogeneousLinearizedStep a b k ha ha1 hk m q (s + t) =
      (homogeneousLinearizedStep a b k ha ha1 hk m q t).comp
        (homogeneousLinearizedStep a b k ha ha1 hk m q s) := by
  apply ContinuousLinearMap.ext
  intro f
  have hr := homogeneousLinearizedTrajectory_restart a b k s t ha ha1 hk s.2 t.2 m q f
    ⟨t, t.2, le_rfl⟩
  have hs := homogeneousLinearizedTrajectory_restrict a b k s (s + t) ha ha1 hk s.2
    (le_add_of_nonneg_right t.2) m q f ⟨s, s.2, le_rfl⟩
  change homogeneousLinearizedTrajectory a b k (s + t) ha ha1 hk (add_nonneg s.2 t.2)
    m q f ⟨s + t, add_nonneg s.2 t.2, le_rfl⟩ =
      homogeneousLinearizedTrajectory a b k t ha ha1 hk t.2 m q
        (homogeneousLinearizedTrajectory a b k s ha ha1 hk s.2 m q f
          ⟨s, s.2, le_rfl⟩) ⟨t, t.2, le_rfl⟩
  exact hr.trans (congrArg (fun v => homogeneousLinearizedTrajectory a b k t ha ha1 hk
    t.2 m q v ⟨t, t.2, le_rfl⟩) hs)

theorem homogeneousLinearizedStep_nat (n : ℕ) :
    homogeneousLinearizedStep a b k ha ha1 hk m q n =
      (homogeneousLinearizedStep a b k ha ha1 hk m q 1) ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, pow_zero, homogeneousLinearizedStep_zero]
    rfl
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, homogeneousLinearizedStep_add, ih, pow_succ']
    rfl

theorem continuous_homogeneousLinearizedStep_apply :
    Continuous (fun p : ℝ≥0 × HomogeneousY a k =>
      homogeneousLinearizedStep a b k ha ha1 hk m q p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let T : ℝ := p.1 + 1
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  let g := fun z : ℝ≥0 × HomogeneousY a k =>
    homogeneousLinearizedPropagator a b k T ha ha1 hk hT m q z.2
      (projIcc 0 T hT z.1)
  have hg : Continuous g :=
    (continuous_homogeneousLinearizedPropagator_apply a b k T ha ha1 hk hT m q).comp
      ((((continuous_projIcc (h := hT)).comp (continuous_subtype_val.comp continuous_fst))).prodMk
        continuous_snd)
  apply hg.continuousAt.congr_of_eventuallyEq
  have hp : (p.1 : ℝ) < T := by dsimp only [T]; linarith
  have htime : Tendsto (fun z : ℝ≥0 × HomogeneousY a k => (z.1 : ℝ)) (𝓝 p)
      (𝓝 (p.1 : ℝ)) := (continuous_subtype_val.comp continuous_fst).continuousAt
  filter_upwards [htime.eventually (gt_mem_nhds hp)] with z hz
  rw [homogeneousLinearizedStep_eq_slab a b k ha ha1 hk m q T hT z.1 hz.le]
  change _ = homogeneousLinearizedTrajectory a b k T ha ha1 hk hT m q z.2
    (projIcc 0 T hT z.1)
  congr 1
  exact (projIcc_of_mem hT ⟨z.1.2, hz.le⟩).symm

end

end DefocusingNLS

end OAI
