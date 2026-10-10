import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.Model
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace OAI

/-! The bounded overlap needed by the near-node form estimate follows from
separation of the actual nuclear positions, by disjoint small balls. -/

noncomputable section
open MeasureTheory Metric
open scoped BigOperators Classical ENNReal
namespace ContinuumCoulomb

theorem separated_position_card_bound {ι : Type*} [Fintype ι]
    (R : ι → Position) (y : Position) {d L : ℝ} (hd : 0 < d) (hL : 0 ≤ L)
    (hsep : ∀ i j, i ≠ j → d ≤ ‖R i-R j‖)
    (hball : ∀ i, ‖R i-y‖ ≤ L) :
    (Fintype.card ι : ℝ)*d^3 ≤ (2*L+d)^3 := by
  let δ := d/2
  let ρ := L+δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := add_pos_of_nonneg_of_pos hL hδ
  have hdisj : Pairwise (fun i j => Disjoint (ball (R i) δ) (ball (R j) δ)) := by
    intro i j hij
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    calc
      δ+δ = d := by dsimp [δ]; ring
      _ ≤ _ := hsep i j hij
  have hsub : (⋃ i, ball (R i) δ) ⊆ ball y ρ := by
    apply Set.iUnion_subset
    intro i
    apply ball_subset_ball'
    rw [dist_eq_norm]
    dsimp only [ρ]
    linarith only [hball i]
  have hv : (Fintype.card ι : ℝ≥0∞)*ENNReal.ofReal (δ^3)*volume (ball (0:Position) 1) ≤
      ENNReal.ofReal (ρ^3)*volume (ball (0:Position) 1) := by
    calc
      _ = volume (⋃ i, ball (R i) δ) := by
        rw [measure_iUnion hdisj (fun _ => measurableSet_ball)]
        simp only [tsum_fintype,volume.addHaar_ball_of_pos _ hδ,
          finrank_euclideanSpace_fin,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc]
      _ ≤ volume (ball y ρ) := measure_mono hsub
      _ = _ := by
        simpa only [finrank_euclideanSpace_fin] using volume.addHaar_ball_of_pos y hρ
  have hj : (Fintype.card ι : ℝ≥0∞)*ENNReal.ofReal (δ^3) ≤ ENNReal.ofReal (ρ^3) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos volume (0:Position) zero_lt_one).ne'
      measure_ball_lt_top.ne).mp hv
  have hr := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le 3) hj
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal (pow_nonneg hδ.le 3)] at hr
  calc
    _ = 8*((Fintype.card ι:ℝ)*δ^3) := by dsimp [δ]; ring
    _ ≤ 8*ρ^3 := mul_le_mul_of_nonneg_left hr (by norm_num)
    _ = _ := by dsimp [ρ,δ]; ring

theorem separated_ball_overlap {m : ℕ} (R : Fin m → Position) (y : Position)
    {d L : ℝ} (hd : 0 < d) (hL : 0 ≤ L)
    (hsep : ∀ i j, i ≠ j → d ≤ ‖R i-R j‖) :
    ((Finset.univ.filter (fun i => ‖R i-y‖ ≤ L)).card : ℝ)*d^3 ≤ (2*L+d)^3 := by
  let s := Finset.univ.filter (fun i => ‖R i-y‖ ≤ L)
  have h := separated_position_card_bound (ι := {i // i ∈ s}) (fun i => R i.val) y hd hL
    (fun i j hij => hsep i j (fun h => hij (Subtype.ext h)))
    (fun i => (Finset.mem_filter.mp i.property).2)
  simpa only [Fintype.card_coe] using h

end ContinuumCoulomb

end

end OAI
