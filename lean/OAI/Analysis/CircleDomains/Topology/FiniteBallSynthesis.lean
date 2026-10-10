import OAI.Analysis.CircleDomains.Modulus.BallMaximalPayment
import OAI.Analysis.CircleDomains.Modulus.DisjointBallPayments

namespace OAI

/-! The finite ball-synthesis estimate is derived from the published
planar maximal inequality, disjoint payment regions, and Cauchy--Schwarz. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def finiteBallDensity {ι : Type*} (F : Finset ι) (c : ι → ℂ) (d a : ι → ℝ) (z : ℂ) : ℝ :=
  ∑ j ∈ F, (ball (c j) (d j)).indicator (fun _ => a j/d j) z

 theorem finiteBallDensity_memLp {ι : Type*} (F : Finset ι) (c : ι → ℂ) (d a : ι → ℝ) :
    MemLp (finiteBallDensity F c d a) 2 volume := by
  apply memLp_finsetSum
  intro j _
  exact memLp_indicator_const 2 measurableSet_ball _ (Or.inr measure_ball_lt_top.ne)

 theorem finiteBallDensity_nonneg {ι : Type*} (F : Finset ι) (c : ι → ℂ) {d a : ι → ℝ}
    (ha : ∀ j ∈ F, 0 ≤ a j) (hd : ∀ j ∈ F, 0 ≤ d j) (z : ℂ) :
    0 ≤ finiteBallDensity F c d a z :=
  Finset.sum_nonneg (fun j hj => indicator_nonneg (fun _ _ => div_nonneg (ha j hj) (hd j hj)) z)

 theorem finiteBallDensity_energy_eq {ι : Type*} (F : Finset ι) (c : ι → ℂ) (d a : ι → ℝ) :
    (∫ z, finiteBallDensity F c d a z^2) =
      ∑ j ∈ F, a j/d j*(∫ z in ball (c j) (d j), finiteBallDensity F c d a z) := by
  let S := finiteBallDensity F c d a
  have hS := finiteBallDensity_memLp F c d a
  have hi (j : ι) : Integrable ((ball (c j) (d j)).indicator
      (fun z => (a j/d j)*S z)) volume := by
    have hj := memLp_indicator_const (μ := (volume : Measure ℂ)) 2
      (s := ball (c j) (d j)) measurableSet_ball (a j/d j) (Or.inr measure_ball_lt_top.ne)
    have hh := hj.integrable_mul hS
    change Integrable (fun z => (ball (c j) (d j)).indicator (fun _ => a j/d j) z*S z) volume at hh
    simpa only [← indicator_mul_left] using hh
  have he (z : ℂ) : S z^2 = ∑ j ∈ F, (ball (c j) (d j)).indicator
      (fun z => (a j/d j)*S z) z := by
    calc
      _ = S z*S z := pow_two _
      _ = _ := by conv_lhs => lhs; unfold S finiteBallDensity
                  rw [Finset.sum_mul]
                  simp only [indicator_mul_left]
  change (∫ z, S z^2) = _
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ => hi j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_indicator measurableSet_ball,integral_const_mul]

 theorem finiteBallDensity_filter_ne_zero {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (c : ι → ℂ) (d a : ι → ℝ) :
    finiteBallDensity (F.filter (fun j => a j ≠ 0)) c d a = finiteBallDensity F c d a := by
  classical
  funext z
  simp only [finiteBallDensity,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · rfl
  · have hj : a j = 0 := not_ne_iff.mp h
    simp only [hj,zero_div,indicator_zero]

 theorem exists_finite_ball_synthesis_constant (hmaximal : PlanarMaximalL2) {k : ℝ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [DecidableEq ι], ∀ (F : Finset ι)
      (c : ι → ℂ) (d a : ι → ℝ) (E : ι → Set ℂ),
      (∀ j ∈ F, 0 < d j) → (∀ j ∈ F, 0 ≤ a j) →
      (∀ j ∈ F, MeasurableSet (E j)) → Set.Pairwise (↑F) (Disjoint on E) →
      (∀ j ∈ F, E j ⊆ ball (c j) (d j)) →
      (∀ j ∈ F, k*d j^2 ≤ volume.real (E j)) →
      (∫ z, finiteBallDensity F c d a z^2) ≤ C*(∑ j ∈ F, a j^2) := by
  obtain ⟨A,hA,hmax⟩ := hmaximal
  let P := (4*Real.pi)^2*Real.pi*A^2
  let C := P/k^2
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨C,div_pos hP (sq_pos_of_pos hk),?_⟩
  intro ι _ F c d a E hd ha hE hdisj hsub hsize
  let S := finiteBallDensity F c d a
  have hS := finiteBallDensity_memLp F c d a
  have hS0 := finiteBallDensity_nonneg F c ha (fun j hj => (hd j hj).le)
  obtain ⟨m,_,hm0,hm,hmEnergy,hmAvg⟩ := hmax S hS
  let B := ∑ j ∈ F, a j^2
  let Q := ∫ z, S z^2
  let T := ∑ j ∈ F, a j/d j*(∫ z in E j, m z)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hQ : 0 ≤ Q := integral_nonneg (fun _ => sq_nonneg _)
  have hp : k*Q ≤ (4*Real.pi)*T := by
    rw [show Q = ∫ z, finiteBallDensity F c d a z^2 from rfl,
      finiteBallDensity_energy_eq,Finset.mul_sum,show T = _ from rfl,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hh := maximal_ball_payment hS hm hm0 hmAvg (hd j hj) hk
      (hE j hj) (hsub j hj) (hsize j hj)
    have hsame : (∫ z in ball (c j) (d j), ‖S z‖) =
        ∫ z in ball (c j) (d j), S z := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => Real.norm_of_nonneg (hS0 z))
    rw [hsame] at hh
    convert mul_le_mul_of_nonneg_left hh (div_nonneg (ha j hj) (hd j hj).le) using 1 <;> ring
  have hT : T^2 ≤ Real.pi*B*(∫ z, m z^2) :=
    sum_disjoint_ball_payments_sq_le F hd hE hdisj hsub hm hm0
  have hp2 : k^2*Q^2 ≤ (4*Real.pi)^2*T^2 := by
    simpa only [← pow_two,mul_pow] using mul_self_le_mul_self (mul_nonneg hk.le hQ) hp
  have hprod : (k^2*Q)*Q ≤ (P*B)*Q := by
    calc
      _ = k^2*Q^2 := by ring
      _ ≤ (4*Real.pi)^2*T^2 := hp2
      _ ≤ (4*Real.pi)^2*(Real.pi*B*(∫ z, m z^2)) :=
        mul_le_mul_of_nonneg_left hT (sq_nonneg _)
      _ ≤ (4*Real.pi)^2*(Real.pi*B*(A^2*Q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmEnergy
          (mul_nonneg Real.pi_pos.le hB)) (sq_nonneg _)
      _ = (P*B)*Q := by dsimp [P]; ring
  by_cases hzero : Q = 0
  · change Q ≤ C*B
    rw [hzero]
    exact mul_nonneg (div_nonneg hP.le (sq_nonneg _)) hB
  · have hQpos : 0 < Q := lt_of_le_of_ne hQ (Ne.symm hzero)
    have hh : k^2*Q ≤ P*B := (mul_le_mul_iff_left₀ hQpos).mp hprod
    change Q ≤ P/k^2*B
    have hh' : Q ≤ (P*B)/k^2 := (le_div_iff₀ (sq_pos_of_pos hk)).mpr (by nlinarith only [hh])
    simpa only [div_mul_eq_mul_div] using hh'

end CircleDomainRigidity

end

end OAI
