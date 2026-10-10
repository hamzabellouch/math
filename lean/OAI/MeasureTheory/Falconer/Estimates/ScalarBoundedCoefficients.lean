import OAI.MeasureTheory.Falconer.Geometry.ScalarBoundedProjection
import OAI.MeasureTheory.Falconer.Estimates.ScalarDivideBudget

namespace OAI

/-! The scalar projection gain with coefficients in any fixed bounded
interval, preserving the original coefficient in the conclusion. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_bounded_coefficients {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (M : ℕ) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let W := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ X : Finset ℝ, X.Nonempty → (∀ x ∈ X, |x| ≤ 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 →
      ((scalarCells δ (X+X)).card:ℝ) ≤ W*(X.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass X u r ≤ W*r^κ*(X.card:ℝ)) →
      ∀ E : Finset ℝ, E.Nonempty → (∀ a ∈ E, |a| ≤ M) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass E u r ≤ W*r^(2*κ)*(E.card:ℝ)) →
      ∃ a ∈ E, W*(X.card:ℝ) < ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) := by
  classical
  obtain ⟨η,N0,hη,hN0,hprojection⟩ := scalar_bounded_projection hκ hκ1
  let m := M+1
  have hm : 0 < m := by dsimp [m]; omega
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0:ℝ) < m := by positivity
  obtain ⟨εD,ND,hεD,hεDη,hND,hbudget⟩ := scalar_divide_budget_absorption hη M m
  obtain ⟨NF,hNF,hfactor⟩ := scalar_fixed_losses hη
    (by positivity : (0:ℝ) < (m:ℝ)^(2*κ)) zero_lt_one
  let ε := min εD (η/4)
  have hε : 0 < ε := lt_min hεD (by positivity)
  have hεη : ε ≤ η := (min_le_left _ _).trans hεDη
  refine ⟨ε,max N0 (max ND NF),hε,lt_of_lt_of_le hN0 (le_max_left _ _),?_⟩
  intro N hN
  dsimp only
  intro X hX hXbound hsep hsize hd hball E hE hEbound hEball
  let δ := (1/2:ℝ)^N
  let W := Real.exp (ε*(N:ℝ)*Real.log 2)
  let WD := Real.exp (εD*(N:ℝ)*Real.log 2)
  let WF := Real.exp (η*(N:ℝ)*Real.log 2)
  have hδ : 0 < δ := by positivity
  have hlog : 0 ≤ (N:ℝ)*Real.log 2 := by positivity
  have hexp (a b : ℝ) (hab : a ≤ b) :
      Real.exp (a*(N:ℝ)*Real.log 2) ≤ Real.exp (b*(N:ℝ)*Real.log 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hab hlog]
  have hWWD : W ≤ WD := hexp _ _ (min_le_left _ _)
  have hWWF : W ≤ WF := hexp _ _ hεη
  have hW1 : 1 ≤ W := Real.one_le_exp_iff.mpr (by positivity)
  have hWD1 : 1 ≤ WD := Real.one_le_exp_iff.mpr (by positivity)
  have hscaled : (m:ℝ)^(2*κ)*W ≤ WF := by
    calc
      _ ≤ (m:ℝ)^(2*κ)*Real.exp ((η/4)*(N:ℝ)*Real.log 2) :=
        mul_le_mul_of_nonneg_left (hexp _ _ (min_le_right _ _)) (by positivity)
      _ ≤ _ := (hfactor N ((le_max_right _ _).trans ((le_max_right _ _).trans hN))).1
  let F := scalarZoom 0 (m:ℝ) E
  have hF : F.Nonempty := hE.image _
  have hFc : F.card = E.card := scalarZoom_card hmpos.ne' E
  have hFbound : ∀ a ∈ F, |a| ≤ 1 := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    rw [sub_zero,abs_div,abs_of_pos hmpos]
    apply (div_le_one hmpos).2
    exact (hEbound b hb).trans (by dsimp [m]; push_cast; linarith)
  have hFball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass F u r ≤ WF*r^(2*κ)*(F.card:ℝ) := by
    intro u r hr hr1
    have hδm : δ/(m:ℝ) ≤ δ := div_le_self hδ.le hmR
    have hh := scalar_zoom_ball_bound hδ hmR hW1 (by positivity : 0 ≤ 2*κ)
      0 E hEball u r (hδm.trans hr) hr1
    have hh' := mul_le_mul_of_nonneg_right hscaled
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) (2*κ)) (Nat.cast_nonneg F.card))
    change scalarBallMass F u r ≤ (m:ℝ)^(2*κ)*W*r^(2*κ)*(F.card:ℝ) at hh
    nlinarith
  have hpoint : ∀ u r : ℝ, δ ≤ r → r ≤ 1 →
      scalarBallMass X u r ≤ WF*r^κ*(X.card:ℝ) := by
    intro u r hr hr1
    apply (hball u r hr hr1).trans
    have hm := mul_le_mul_of_nonneg_right hWWF
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) κ) (Nat.cast_nonneg X.card))
    nlinarith
  have hdF : ((scalarCells δ (X+X)).card:ℝ) ≤ WF*(X.card:ℝ) :=
    hd.trans (mul_le_mul_of_nonneg_right hWWF (Nat.cast_nonneg _))
  obtain ⟨a,ha,hgain⟩ := hprojection N ((le_max_left _ _).trans hN)
    X hX hXbound hsep hsize hdF hpoint F hF hFbound hFball
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
  by_contra hn
  push Not at hn
  have hXc : (scalarCells δ X).card = X.card :=
    Finset.card_image_of_injOn (scalarCells_injective hδ hsep)
  have hdD : ((scalarCells δ (X+X)).card:ℝ) ≤ WD*(scalarCells δ X).card := by
    rw [hXc]
    exact hd.trans (mul_le_mul_of_nonneg_right hWWD (Nat.cast_nonneg _))
  have hbD : ((scalarCells δ (X+X.image (fun x => b*x))).card:ℝ) ≤ WD*(scalarCells δ X).card := by
    rw [hXc]
    exact (hn b hb).trans (mul_le_mul_of_nonneg_right hWWD (Nat.cast_nonneg _))
  have hdiv := scalar_divide_coefficient hδ (zero_le_one.trans hWD1) X hX M m hm
    (hEbound b hb) hdD hbD
  have hbudget' := hbudget N ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hh := hdiv.trans (mul_le_mul_of_nonneg_right hbudget' (Nat.cast_nonneg _))
  rw [hXc] at hh
  simp only [sub_zero] at hgain
  exact (not_lt_of_ge hh) hgain

end Falconer.Regularization

end OAI
