import OAI.Analysis.MarkovType.DyadicBellman
import OAI.Analysis.MarkovType.HomogeneousPotential
import OAI.Analysis.MarkovType.SmoothnessBounds

namespace OAI

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

noncomputable def dyadicPowerSeminorm {p A K : ℝ} (hp : 1 ≤ p)
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) : Seminorm ℝ X :=
  potentialSeminorm p (lt_of_lt_of_le zero_lt_one hp) (bellmanPotential p K)
    (bellmanPotential_nonneg hMT)
    (fun a x => by
      simpa only [Real.norm_eq_abs] using
        bellmanPotential_smul (lt_of_lt_of_le zero_lt_one hp) hMT a x)
    (bellmanPotential_convex hp hMT)

@[simp] theorem dyadicPowerSeminorm_apply {p A K : ℝ} (hp : 1 ≤ p)
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (x : X) :
    dyadicPowerSeminorm hp hMT x = bellmanPotential p K x ^ (1 / p) := rfl

theorem dyadicPowerSeminorm_rpow {p A K : ℝ} (hp : 1 ≤ p)
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (x : X) :
    (dyadicPowerSeminorm hp hMT x) ^ p = bellmanPotential p K x :=
  potentialSeminorm_rpow _ _ _ _ _ _ _

theorem norm_le_dyadicPowerSeminorm {p A K : ℝ} (hp : 1 ≤ p)
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (x : X) :
    ‖x‖ ≤ dyadicPowerSeminorm hp hMT x := by
  apply (Real.rpow_le_rpow_iff (norm_nonneg x)
    (apply_nonneg (dyadicPowerSeminorm hp hMT) x)
    (lt_of_lt_of_le zero_lt_one hp)).1
  rw [dyadicPowerSeminorm_rpow]
  exact (bellmanPotential_bounds hMT x).1

theorem dyadicPowerSeminorm_le_mul_norm {p A K L : ℝ} (hp : 1 ≤ p)
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K)
    (hL : 0 ≤ L) (hA : A ≤ L ^ p) (x : X) :
    dyadicPowerSeminorm hp hMT x ≤ L * ‖x‖ := by
  apply (Real.rpow_le_rpow_iff (apply_nonneg (dyadicPowerSeminorm hp hMT) x)
    (mul_nonneg hL (norm_nonneg x)) (lt_of_lt_of_le zero_lt_one hp)).1
  rw [dyadicPowerSeminorm_rpow, Real.mul_rpow hL (norm_nonneg x)]
  exact (bellmanPotential_bounds hMT x).2.trans
    (mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg (norm_nonneg x) p))

theorem dyadicPowerSeminorm_add_sub_le {p A K : ℝ} (hp : 1 ≤ p)
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (x y : X) :
    ((dyadicPowerSeminorm hp hMT (x + y)) ^ p +
      (dyadicPowerSeminorm hp hMT (x - y)) ^ p) / 2 ≤
        (dyadicPowerSeminorm hp hMT x) ^ p + K * ‖y‖ ^ p := by
  simp only [dyadicPowerSeminorm_rpow]
  exact bellmanPotential_add_sub_le hMT x y

theorem dyadicPowerSeminorm_symmetricPowerSmooth {p A K : ℝ} (hp : 1 ≤ p)
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (hK : 0 ≤ K) :
    SymmetricPowerSmooth (dyadicPowerSeminorm hp hMT) p K := by
  intro x y
  exact (dyadicPowerSeminorm_add_sub_le hp hMT x y).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg y) (norm_le_dyadicPowerSeminorm hp hMT y)
        (le_trans zero_le_one hp)) hK))

theorem exists_powerSmooth_equivalentSeminorm_of_finiteDyadicType
    {p T : ℝ} (hp : 1 < p) (hT : 1 ≤ T)
    (hMT : FiniteDyadicUpperEstimate (X := X) p (T ^ p) (T ^ p)) :
    ∃ ν : Seminorm ℝ X,
      (∀ x, ‖x‖ ≤ ν x ∧ ν x ≤ T * ‖x‖) ∧ SymmetricPowerSmooth ν p (T ^ p) := by
  refine ⟨dyadicPowerSeminorm hp.le hMT, ?_, ?_⟩
  · intro x
    exact ⟨norm_le_dyadicPowerSeminorm hp.le hMT x,
      dyadicPowerSeminorm_le_mul_norm hp.le hMT (le_trans zero_le_one hT) le_rfl x⟩
  · exact dyadicPowerSeminorm_symmetricPowerSmooth hp.le hMT
      (Real.rpow_nonneg (le_trans zero_le_one hT) p)

end MarkovSuperreflexivity

end OAI
