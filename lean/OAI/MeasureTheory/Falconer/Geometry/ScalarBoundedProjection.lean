import OAI.MeasureTheory.Falconer.Estimates.ScalarZoomBounds
import OAI.MeasureTheory.Falconer.Geometry.ScalarDyadicProjection

namespace OAI

/-! The scalar projection theorem for arbitrary bounded real point sets,
 at every sufficiently fine dyadic resolution. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_bounded_projection {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let W := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ X : Finset ℝ, X.Nonempty → (∀ x ∈ X, |x| ≤ 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 →
      ((scalarCells δ (X+X)).card:ℝ) ≤ W*(X.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass X u r ≤ W*r^κ*(X.card:ℝ)) →
      ∀ E : Finset ℝ, E.Nonempty → (∀ a ∈ E, |a| ≤ 1) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass E u r ≤ W*r^(2*κ)*(E.card:ℝ)) →
      ∃ a ∈ E, W*(X.card:ℝ) < ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) := by
  obtain ⟨η,N0,hη,hN0,hprojection⟩ := scalar_dyadic_projection hκ hκ1
  obtain ⟨N1,hN1,hloss⟩ := scalar_fixed_losses hη (by norm_num : (0:ℝ) < 2)
    (by positivity : (0:ℝ) < (4:ℝ)^(2*κ))
  refine ⟨η/4,max N0 N1,by positivity,lt_of_lt_of_le hN0 (le_max_left _ _),?_⟩
  intro N hN
  dsimp only
  intro X hX hXbound hsep hsize hadd hpoint E hE hEbound hEball
  let δ := (1/2:ℝ)^N
  let W := Real.exp ((η/4)*(N:ℝ)*Real.log 2)
  let Wf := Real.exp (η*(N+2:ℕ)*Real.log 2)
  let Y := scalarZoom (-2) 4 X
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hδf : (1/2:ℝ)^(N+2) = δ/4 := by
    rw [pow_add]
    dsimp [δ]
    norm_num
    ring
  have hW : 0 < W := Real.exp_pos _
  have hW1 : 1 ≤ W := Real.one_le_exp_iff.mpr (by positivity)
  have hExp : Real.exp (η*(N:ℝ)*Real.log 2) ≤ Wf := by
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]
  obtain ⟨hcover,hball⟩ := hloss N ((le_max_right _ _).trans hN)
  have hcover' : 2*W ≤ Wf := hcover.trans hExp
  have hball' : (4:ℝ)^(2*κ)*W ≤ Wf := hball.trans hExp
  have hpointFactor : (4:ℝ)^κ*W ≤ Wf :=
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)) hW.le).trans hball'
  have hYcard : Y.card = X.card := scalarZoom_card (by norm_num) X
  have hYne : Y.Nonempty := hX.image _
  have hYunit : ∀ y ∈ Y, 0 ≤ y ∧ y < 1 := scalar_quarter_zoom_unit X hXbound
  have hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → (1/2:ℝ)^(N+2) ≤ |x-y| := by
    rw [hδf]
    exact scalarZoom_separated (by norm_num) X hsep
  have htransfer (a : ℝ) : ((scalarCells ((1/2:ℝ)^(N+2)) (Y+Y.image (fun x => a*x))).card:ℝ) ≤
      2*((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) := by
    dsimp only [Y]
    rw [hδf,scalar_zoom_linear_sum]
    exact_mod_cast scalar_zoom_cells hδ (by norm_num : (0:ℝ) < 4) ((1+a)*(-2))
      (X+X.image (fun x => a*x))
  have hYdouble : ((scalarCells ((1/2:ℝ)^(N+2)) (Y+Y)).card:ℝ) ≤ Wf*(Y.card:ℝ) := by
    have hh := htransfer 1
    simp only [one_mul,Finset.image_id'] at hh
    rw [hYcard]
    have hm := mul_le_mul_of_nonneg_right hcover' (Nat.cast_nonneg X.card)
    nlinarith
  have hYballs : ∀ u r : ℝ, (1/2:ℝ)^(N+2) ≤ r → r ≤ 1 →
      scalarBallMass Y u r ≤ Wf*r^κ*(Y.card:ℝ) := by
    intro u r hr hr1
    rw [hδf] at hr
    have hh := scalar_zoom_ball_bound hδ (by norm_num : (1:ℝ) ≤ 4) hW1 hκ.le (-2) X hpoint u r hr hr1
    have hm := mul_le_mul_of_nonneg_right hpointFactor
      (mul_nonneg (Real.rpow_nonneg ((div_pos hδ (by norm_num)).le.trans hr) κ) (Nat.cast_nonneg Y.card))
    nlinarith
  have hEballs : ∀ u r : ℝ, (1/2:ℝ)^(N+2) ≤ r → r ≤ 1 →
      scalarBallMass E u r ≤ Wf*r^(2*κ)*(E.card:ℝ) := by
    intro u r hr hr1
    rw [hδf] at hr
    have hh := scalar_refined_ball_bound (div_pos hδ (by norm_num)) hδ1
      (by norm_num : (1:ℝ) ≤ 4) (by linarith : δ ≤ 4*(δ/4)) hW.le
      (by linarith : 0 ≤ 2*κ) E hEball u r hr hr1
    have hm := mul_le_mul_of_nonneg_right hball'
      (mul_nonneg (Real.rpow_nonneg ((div_pos hδ (by norm_num)).le.trans hr) (2*κ)) (Nat.cast_nonneg E.card))
    nlinarith
  have hYsize : Real.log (Y.card:ℝ) ≤ (1-κ)*(N+2:ℕ)*Real.log 2 := by
    rw [hYcard]
    push_cast
    have hh : 0 ≤ (1-κ)*Real.log 2 := mul_nonneg (sub_nonneg.mpr hκ1)
      (Real.log_pos (by norm_num : (1:ℝ) < 2)).le
    nlinarith
  obtain ⟨a,ha,hgain⟩ := hprojection (N+2) (by omega) Y hYne hYunit hYsep hYsize
    hYdouble hYballs E hE hEbound hEballs
  by_contra hn
  push Not at hn
  have hh := htransfer a
  have hp := hn a ha
  have hm := mul_le_mul_of_nonneg_right hcover' (Nat.cast_nonneg X.card)
  rw [hYcard] at hgain
  nlinarith

end Falconer.Regularization

end OAI
