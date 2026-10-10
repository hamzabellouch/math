import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearizedBound

namespace OAI

/-! # Bounded real-linear propagators for the actual profile potential

The potential is the Fréchet derivative of the actual odd-power map at q.
Its finite-slab trajectory is linear in the data, quantitatively bounded,
and jointly continuous in the elapsed time and the initial vector.
-/

open Set

namespace DefocusingNLS

attribute [local irreducible] homogeneousFreeOperator

section

variable (a b k T : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
  (hT : 0 ≤ T) (m : ℕ) (q : HomogeneousY a k)

local notation "B" => homogeneousLinearizedPotential a k ha ha1 hk m q

noncomputable def homogeneousLinearizedTrajectory (u₀ : HomogeneousY a k) :
    C(Icc (0 : ℝ) T, HomogeneousY a k) :=
  Classical.choose (existsUnique_homogeneousLinearized_finiteSlab
    a b k T ha ha1 hk hT m q u₀).exists

local notation "S" => homogeneousLinearizedTrajectory a b k T ha ha1 hk hT m q

theorem homogeneousLinearizedTrajectory_eq (u₀ : HomogeneousY a k)
    (t : Icc (0 : ℝ) T) :
    S u₀ t = homogeneousFreeOperator a b k t ha ha1 hk u₀ +
      homogeneousDuhamel a b k ha ha1 hk t (homogeneousPotentialHistory T hT B (S u₀)) :=
  Classical.choose_spec (existsUnique_homogeneousLinearized_finiteSlab
    a b k T ha ha1 hk hT m q u₀).exists t

theorem homogeneousLinearizedTrajectory_unique (u₀ : HomogeneousY a k)
    (u : C(Icc (0 : ℝ) T, HomogeneousY a k))
    (hu : ∀ t : Icc (0 : ℝ) T, u t = homogeneousFreeOperator a b k t ha ha1 hk u₀ +
      homogeneousDuhamel a b k ha ha1 hk t (homogeneousPotentialHistory T hT B u)) :
    u = S u₀ :=
  (existsUnique_homogeneousLinearized_finiteSlab a b k T ha ha1 hk hT m q u₀).unique
    hu (homogeneousLinearizedTrajectory_eq a b k T ha ha1 hk hT m q u₀)

private theorem linearized_history_zero : homogeneousPotentialHistory T hT B 0 = fun _ => 0 := by
  funext t
  simp only [homogeneousPotentialHistory, ContinuousMap.zero_apply, map_zero]

private theorem linearized_history_add (u v : C(Icc (0 : ℝ) T, HomogeneousY a k)) :
    homogeneousPotentialHistory T hT B (u + v) = fun t =>
      homogeneousPotentialHistory T hT B u t + homogeneousPotentialHistory T hT B v t := by
  funext t
  exact map_add B _ _

private theorem linearized_history_smul (c : ℝ) (u : C(Icc (0 : ℝ) T, HomogeneousY a k)) :
    homogeneousPotentialHistory T hT B (c • u) = fun t =>
      c • homogeneousPotentialHistory T hT B u t := by
  funext t
  exact map_smul B c _

@[simp] theorem homogeneousLinearizedTrajectory_zero : S 0 = 0 := by
  symm
  apply homogeneousLinearizedTrajectory_unique a b k T ha ha1 hk hT m q
  intro t
  rw [linearized_history_zero a k T ha ha1 hk hT m q, homogeneousDuhamel_zero,
    map_zero, add_zero]
  rfl

theorem homogeneousLinearizedTrajectory_add (u₀ v₀ : HomogeneousY a k) :
    S (u₀ + v₀) = S u₀ + S v₀ := by
  symm
  apply homogeneousLinearizedTrajectory_unique a b k T ha ha1 hk hT m q
  intro t
  rw [linearized_history_add a k T ha ha1 hk hT m q,
    homogeneousDuhamel_add a b k t ha ha1 hk _ _
      (continuous_homogeneousPotentialHistory T hT B (S u₀))
      (continuous_homogeneousPotentialHistory T hT B (S v₀)), map_add]
  change S u₀ t + S v₀ t = _
  rw [homogeneousLinearizedTrajectory_eq a b k T ha ha1 hk hT m q u₀,
    homogeneousLinearizedTrajectory_eq a b k T ha ha1 hk hT m q v₀]
  abel

theorem homogeneousLinearizedTrajectory_smul (c : ℝ) (u₀ : HomogeneousY a k) :
    S (c • u₀) = c • S u₀ := by
  symm
  apply homogeneousLinearizedTrajectory_unique a b k T ha ha1 hk hT m q
  intro t
  rw [linearized_history_smul a k T ha ha1 hk hT m q,
    homogeneousDuhamel_real_smul, ContinuousLinearMap.map_smul_of_tower]
  change c • S u₀ t = _
  rw [homogeneousLinearizedTrajectory_eq a b k T ha ha1 hk hT m q u₀, smul_add]

theorem homogeneousLinearizedTrajectory_norm_le (u₀ : HomogeneousY a k) :
    ‖S u₀‖ ≤ 2 * Real.exp ((2 * (‖B‖ + 1)) * T) * ‖u₀‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  apply (homogeneousLinearized_mild_bound a b k T ha ha1 hk hT m q u₀
    (S u₀) (homogeneousLinearizedTrajectory_eq a b k T ha ha1 hk hT m q u₀) t).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left t.2.2 (by positivity))) (by norm_num))
      (norm_nonneg u₀)

noncomputable def homogeneousLinearizedPropagator :
    HomogeneousY a k →L[ℝ] C(Icc (0 : ℝ) T, HomogeneousY a k) :=
  let L : HomogeneousY a k →ₗ[ℝ] C(Icc (0 : ℝ) T, HomogeneousY a k) :=
    { toFun := S
      map_add' := homogeneousLinearizedTrajectory_add a b k T ha ha1 hk hT m q
      map_smul' := homogeneousLinearizedTrajectory_smul a b k T ha ha1 hk hT m q }
  L.mkContinuous (2 * Real.exp ((2 * (‖B‖ + 1)) * T))
    (homogeneousLinearizedTrajectory_norm_le a b k T ha ha1 hk hT m q)

@[simp] theorem homogeneousLinearizedPropagator_apply (u₀ : HomogeneousY a k) :
    homogeneousLinearizedPropagator a b k T ha ha1 hk hT m q u₀ = S u₀ := rfl

theorem homogeneousLinearizedPropagator_norm_le :
    ‖homogeneousLinearizedPropagator a b k T ha ha1 hk hT m q‖ ≤
      2 * Real.exp ((2 * (‖B‖ + 1)) * T) :=
  LinearMap.mkContinuous_norm_le _ (by positivity)
    (homogeneousLinearizedTrajectory_norm_le a b k T ha ha1 hk hT m q)

theorem continuous_homogeneousLinearizedPropagator_apply :
    Continuous (fun p : Icc (0 : ℝ) T × HomogeneousY a k =>
      homogeneousLinearizedPropagator a b k T ha ha1 hk hT m q p.2 p.1) := by
  exact continuous_eval.comp
    (((homogeneousLinearizedPropagator a b k T ha ha1 hk hT m q).continuous.comp
      continuous_snd).prodMk continuous_fst)

end

end DefocusingNLS

end OAI
