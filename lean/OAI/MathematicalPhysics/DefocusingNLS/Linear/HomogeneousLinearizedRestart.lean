import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearizedFlow

namespace OAI

/-! # Restart for the actual whole-space profile linearization

Splitting the Duhamel integral proves the autonomous restart identity on
finite slabs. The same physical potential is used on both sides.
-/

open Set

namespace DefocusingNLS

attribute [local irreducible] homogeneousFreeOperator

theorem homogeneousDuhamel_congr_on (a b k t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ht : 0 ≤ t)
    (r q : ℝ → HomogeneousY a k) (hrq : EqOn r q (Icc 0 t)) :
    homogeneousDuhamel a b k ha ha1 hk t r =
      homogeneousDuhamel a b k ha ha1 hk t q := by
  unfold homogeneousDuhamel
  apply intervalIntegral.integral_congr
  intro s hs
  change homogeneousFreeOperator a b k (t - s) ha ha1 hk (r s) =
    homogeneousFreeOperator a b k (t - s) ha ha1 hk (q s)
  rw [hrq (by simpa only [uIcc_of_le ht] using hs)]

theorem homogeneousLinearizedTrajectory_restrict
    (a b k S T : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (hS : 0 ≤ S) (hST : S ≤ T) (m : ℕ) (q u₀ : HomogeneousY a k)
    (t : Icc (0 : ℝ) S) :
    homogeneousLinearizedTrajectory a b k T ha ha1 hk (hS.trans hST) m q u₀
        ⟨t, t.2.1, t.2.2.trans hST⟩ =
      homogeneousLinearizedTrajectory a b k S ha ha1 hk hS m q u₀ t := by
  let B := homogeneousLinearizedPotential a k ha ha1 hk m q
  let u := homogeneousLinearizedTrajectory a b k T ha ha1 hk (hS.trans hST) m q u₀
  let v : C(Icc (0 : ℝ) S, HomogeneousY a k) :=
    { toFun := fun s => u ⟨s, s.2.1, s.2.2.trans hST⟩
      continuous_toFun := u.continuous.comp (continuous_subtype_val.subtype_mk _) }
  have hv : ∀ s : Icc (0 : ℝ) S,
      v s = homogeneousFreeOperator a b k s ha ha1 hk u₀ +
        homogeneousDuhamel a b k ha ha1 hk s (homogeneousPotentialHistory S hS B v) := by
    intro s
    have heq : homogeneousDuhamel a b k ha ha1 hk s
        (homogeneousPotentialHistory T (hS.trans hST) B u) =
        homogeneousDuhamel a b k ha ha1 hk s (homogeneousPotentialHistory S hS B v) := by
      apply homogeneousDuhamel_congr_on a b k s ha ha1 hk s.2.1
      intro τ hτ
      have hτS : τ ∈ Icc 0 S := ⟨hτ.1, hτ.2.trans s.2.2⟩
      have hτT : τ ∈ Icc 0 T := ⟨hτ.1, hτS.2.trans hST⟩
      change B (u (projIcc 0 T (hS.trans hST) τ)) = B (v (projIcc 0 S hS τ))
      rw [projIcc_of_mem _ hτT, projIcc_of_mem _ hτS]
      rfl
    exact (homogeneousLinearizedTrajectory_eq a b k T ha ha1 hk (hS.trans hST)
      m q u₀ ⟨s, s.2.1, s.2.2.trans hST⟩).trans
        (congrArg (fun w => homogeneousFreeOperator a b k s ha ha1 hk u₀ + w) heq)
  have heq := homogeneousLinearizedTrajectory_unique a b k S ha ha1 hk hS m q u₀ v hv
  exact congrArg (fun w : C(Icc (0 : ℝ) S, HomogeneousY a k) => w t) heq

theorem homogeneousLinearizedTrajectory_restart
    (a b k S T : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (hS : 0 ≤ S) (hT : 0 ≤ T) (m : ℕ) (q u₀ : HomogeneousY a k)
    (t : Icc (0 : ℝ) T) :
    homogeneousLinearizedTrajectory a b k (S + T) ha ha1 hk (add_nonneg hS hT) m q u₀
        ⟨S + t, add_nonneg hS t.2.1, add_le_add le_rfl t.2.2⟩ =
      homogeneousLinearizedTrajectory a b k T ha ha1 hk hT m q
        (homogeneousLinearizedTrajectory a b k (S + T) ha ha1 hk (add_nonneg hS hT) m q u₀
          ⟨S, hS, le_add_of_nonneg_right hT⟩) t := by
  let B := homogeneousLinearizedPotential a k ha ha1 hk m q
  let u := homogeneousLinearizedTrajectory a b k (S + T) ha ha1 hk (add_nonneg hS hT) m q u₀
  let v : C(Icc (0 : ℝ) T, HomogeneousY a k) :=
    { toFun := fun s => u ⟨S + s, add_nonneg hS s.2.1, add_le_add le_rfl s.2.2⟩
      continuous_toFun := u.continuous.comp
        ((continuous_const.add continuous_subtype_val).subtype_mk _) }
  let r := homogeneousPotentialHistory (S + T) (add_nonneg hS hT) B u
  have hr : Continuous r := continuous_homogeneousPotentialHistory _ _ _ _
  have hv : ∀ s : Icc (0 : ℝ) T,
      v s = homogeneousFreeOperator a b k s ha ha1 hk
        (u ⟨S, hS, le_add_of_nonneg_right hT⟩) +
          homogeneousDuhamel a b k ha ha1 hk s (homogeneousPotentialHistory T hT B v) := by
    intro s
    have hfree : homogeneousFreeOperator a b k (S + s) ha ha1 hk u₀ =
        homogeneousFreeOperator a b k s ha ha1 hk
          (homogeneousFreeOperator a b k S ha ha1 hk u₀) := by
      rw [add_comm S (s : ℝ), homogeneousFreeOperator_add]
    have hduh : homogeneousDuhamel a b k ha ha1 hk s (fun τ => r (S + τ)) =
        homogeneousDuhamel a b k ha ha1 hk s (homogeneousPotentialHistory T hT B v) := by
      apply homogeneousDuhamel_congr_on a b k s ha ha1 hk s.2.1
      intro τ hτ
      have hτT : τ ∈ Icc 0 T := ⟨hτ.1, hτ.2.trans s.2.2⟩
      have hSτ : S + τ ∈ Icc 0 (S + T) :=
        ⟨add_nonneg hS hτ.1, add_le_add le_rfl hτT.2⟩
      change B (u (projIcc 0 (S + T) (add_nonneg hS hT) (S + τ))) =
        B (v (projIcc 0 T hT τ))
      rw [projIcc_of_mem _ hSτ, projIcc_of_mem _ hτT]
      rfl
    calc
      v s = homogeneousFreeOperator a b k (S + s) ha ha1 hk u₀ +
          homogeneousDuhamel a b k ha ha1 hk (S + s) r :=
        homogeneousLinearizedTrajectory_eq a b k (S + T) ha ha1 hk
          (add_nonneg hS hT) m q u₀ _
      _ = homogeneousFreeOperator a b k s ha ha1 hk
          (homogeneousFreeOperator a b k S ha ha1 hk u₀ +
            homogeneousDuhamel a b k ha ha1 hk S r) +
          homogeneousDuhamel a b k ha ha1 hk s (homogeneousPotentialHistory T hT B v) := by
        rw [hfree, homogeneousDuhamel_restart a b k S s ha ha1 hk r hr, hduh, map_add]
        abel
      _ = _ := by
        rw [← homogeneousLinearizedTrajectory_eq a b k (S + T) ha ha1 hk
          (add_nonneg hS hT) m q u₀ ⟨S, hS, le_add_of_nonneg_right hT⟩]
  have heq := homogeneousLinearizedTrajectory_unique a b k T ha ha1 hk hT m q
    (u ⟨S, hS, le_add_of_nonneg_right hT⟩) v hv
  exact congrArg (fun w : C(Icc (0 : ℝ) T, HomogeneousY a k) => w t) heq

end DefocusingNLS

end OAI
