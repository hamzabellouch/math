import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingMildLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousWeakMildIdentification
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingLinearizedPhysicalLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileUniformBound
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileInitial
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingNonprincipalEnergy

namespace OAI

/-! # The actual profile-trajectory limit satisfies the whole-space linearized mild equation -/

open Set MeasureTheory Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

attribute [local irreducible] expandingProfileTrajectory expandingTorusFunction

theorem expandingProfile_limit_equation (a b k T Q M C : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (m : ℕ) (hQ : 0 ≤ Q) (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n)
    (q : ℕ → C(Icc (0 : ℝ) T, FourierL2)) (hq : ∀ n s, ‖q n s‖ ≤ Q)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
    (Q₀ : HomogeneousY a k) (v : Icc (0 : ℝ) T → HomogeneousY a k)
    (hv : ∀ s, ‖v s‖ ≤ C)
    (hvc : ∀ y : E, Continuous (fun s => homogeneousPhysicalCLM a k ha ha1 hk (v s) y))
    (hqp : ∀ (s : Icc (0 : ℝ) T) (y : E),
      Tendsto (fun n => expandingPhysicalContinuous a k (expandingRadius (L n) s)
        ha ha1 hk ((hL n).trans (expandingRadius_ge (L n) s (hL n) s.2.1)) (q n s) y)
        atTop (𝓝 (homogeneousPhysicalCLM a k ha ha1 hk Q₀ y)))
    (hvp : ∀ (s : Icc (0 : ℝ) T) (y : E),
      Tendsto (fun n => expandingPhysicalContinuous a k (expandingRadius (L n) s)
        ha ha1 hk ((hL n).trans (expandingRadius_ge (L n) s (hL n) s.2.1))
        (expandingProfileTrajectory a b k (L n) T ha ha1 hk (hL n) hT m Q hQ (q n) (hq n) (f n) s) y)
        atTop (𝓝 (homogeneousPhysicalCLM a k ha ha1 hk (v s) y)))
    (t : Icc (0 : ℝ) T) :
    v t = homogeneousFreeOperator a b k t ha ha1 hk (v ⟨0, le_rfl, hT⟩) +
      homogeneousDuhamel a b k ha ha1 hk t
        (fun s => homogeneousLinearizedPotential a k ha ha1 hk m Q₀ (v (projIcc 0 T hT s))) := by
  let S := fun n => expandingProfileTrajectory a b k (L n) T ha ha1 hk (hL n) hT
    m Q hQ (q n) (hq n) (f n)
  let r := fun n => expandingReactionHistory T hT
    (expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve (L n) T (hL n)) (q n) 0) (S n)
  let B := homogeneousLinearizedPotential a k ha ha1 hk m Q₀
  obtain ⟨K, hK, hKb⟩ := exists_expandingProfileTrajectory_bound a b k ha ha1 hk m Q hQ
  obtain ⟨D, hD, hDb⟩ := exists_expandingLinearized_norm_bound a k Q ha ha1 hk hQ m
  let A := (K + 1) * Real.exp ((K + 1) * T) * M
  have hSb (n : ℕ) (s : Icc (0 : ℝ) T) : ‖S n s‖ ≤ A :=
    ((ContinuousMap.norm_coe_le_norm (S n) s).trans
      (hKb (L n) T (hL n) hT (q n) (hq n) (f n))).trans
      (mul_le_mul_of_nonneg_left (hf n) (by positivity))
  have hrcont (n : ℕ) : Continuous (r n) := continuous_expandingReactionHistory T hT _ (S n)
  have hre (n : ℕ) (s : ℝ) : r n s =
      expandingLinearizedPotential a k (expandingRadius (L n) (projIcc 0 T hT s)) ha ha1 hk
        ((hL n).trans (expandingRadius_ge (L n) _ (hL n) (projIcc 0 T hT s).2.1)) m
        (q n (projIcc 0 T hT s)) (S n (projIcc 0 T hT s)) := by
    change (-Complex.I) • (_ : FourierL2) + (0 : FourierL2) = _
    exact add_zero _
  have hrb (n : ℕ) (s : ℝ) : ‖r n s‖ ≤ D * A := by
    rw [hre]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      ((mul_le_mul_of_nonneg_right (hDb _ _ _ (hq n _)) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hSb n _) hD))
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := fun s hs => ⟨hs.1, hs.2.trans t.2.2⟩
  have hgiT : IntegrableOn (fun s => B (v (projIcc 0 T hT s))) (Icc 0 T) :=
    B.integrable_comp (integrableOn_homogeneous_clamped a k T C ha ha1 hk hT v hv hvc)
  have hgi : IntegrableOn (fun s => B (v (projIcc 0 T hT s))) (Icc 0 t) :=
    hgiT.mono_set hsub
  apply expandingMild_physical_limit a b k t M A (D * A) ha ha1 hk t.2.1 L hL f
    (fun n => S n t) r hf (fun n => hSb n t) (fun n s _ => hrb n s)
    (fun n => (hrcont n).continuousOn)
    (fun n => expandingProfileTrajectory_eq a b k (L n) T ha ha1 hk (hL n) hT
      m Q hQ (q n) (hq n) (f n) t)
    (v ⟨0, le_rfl, hT⟩) (v t) (fun s => B (v (projIcc 0 T hT s)))
    (B.continuous.comp_stronglyMeasurable
      (stronglyMeasurable_homogeneous_clamped a k T ha ha1 hk hT v hvc)) hgi
  · intro y
    have h := hvp ⟨0, le_rfl, hT⟩ y
    simpa only [expandingProfileTrajectory_initial, expandingRadius, zero_div,
      Real.exp_zero, mul_one] using h
  · exact hvp t
  · intro s hs y
    have he : projIcc 0 T hT s = ⟨s, hsub hs⟩ := projIcc_of_mem _ (hsub hs)
    have h := tendsto_expandingLinearizedPotential_physical a k ha ha1 hk m
      (fun n => expandingRadius (L n) s)
      (fun n => (hL n).trans (expandingRadius_ge (L n) s (hL n) hs.1))
      (fun n => q n ⟨s, hsub hs⟩) (fun n => S n ⟨s, hsub hs⟩)
      Q₀ (v ⟨s, hsub hs⟩) y (hqp ⟨s, hsub hs⟩ y) (hvp ⟨s, hsub hs⟩ y)
    simpa only [hre, he, B] using h

theorem expandingProfile_limit_identification (a b k T Q M C : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (m : ℕ) (hQ : 0 ≤ Q) (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n)
    (q : ℕ → C(Icc (0 : ℝ) T, FourierL2)) (hq : ∀ n s, ‖q n s‖ ≤ Q)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
    (Q₀ : HomogeneousY a k) (v : Icc (0 : ℝ) T → HomogeneousY a k)
    (hv : ∀ s, ‖v s‖ ≤ C)
    (hvc : ∀ y : E, Continuous (fun s => homogeneousPhysicalCLM a k ha ha1 hk (v s) y))
    (hqp : ∀ (s : Icc (0 : ℝ) T) (y : E),
      Tendsto (fun n => expandingPhysicalContinuous a k (expandingRadius (L n) s)
        ha ha1 hk ((hL n).trans (expandingRadius_ge (L n) s (hL n) s.2.1)) (q n s) y)
        atTop (𝓝 (homogeneousPhysicalCLM a k ha ha1 hk Q₀ y)))
    (hvp : ∀ (s : Icc (0 : ℝ) T) (y : E),
      Tendsto (fun n => expandingPhysicalContinuous a k (expandingRadius (L n) s)
        ha ha1 hk ((hL n).trans (expandingRadius_ge (L n) s (hL n) s.2.1))
        (expandingProfileTrajectory a b k (L n) T ha ha1 hk (hL n) hT m Q hQ (q n) (hq n) (f n) s) y)
        atTop (𝓝 (homogeneousPhysicalCLM a k ha ha1 hk (v s) y)))
    : v = fun t => homogeneousLinearizedTrajectory a b k T ha ha1 hk hT m Q₀
        (v ⟨0, le_rfl, hT⟩) t := by
  apply homogeneousLinearizedTrajectory_eq_of_bounded_mild a b k T C ha ha1 hk hT m Q₀
    (v ⟨0, le_rfl, hT⟩) v hv hvc
  exact fun t => expandingProfile_limit_equation a b k T Q M C ha ha1 hk hT m hQ L hL q hq
    f hf Q₀ v hv hvc hqp hvp t

end DefocusingNLS

end OAI
