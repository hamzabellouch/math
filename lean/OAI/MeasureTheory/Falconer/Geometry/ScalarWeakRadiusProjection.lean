import OAI.MeasureTheory.Falconer.Geometry.ScalarBoundedProjection
import OAI.MeasureTheory.Falconer.Geometry.ScalarMaxRatioProjection
import OAI.MeasureTheory.Falconer.Estimates.ScalarRatioFamily

namespace OAI

/-! Scalar projection gain when the coefficient radius is allowed the same
small power loss as the ball and projection estimates. Normalization uses
an actual maximal coefficient and costs only a fixed polynomial. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_weak_radius_projection {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let W := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ X : Finset ℝ, X.Nonempty → (∀ x ∈ X, |x| ≤ 1) →
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) →
      Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 →
      ((scalarCells δ (X+X)).card:ℝ) ≤ W*(X.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass X u r ≤ W*r^κ*(X.card:ℝ)) →
      ∀ E : Finset ℝ, E.Nonempty → (∀ a ∈ E, |a| ≤ W) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass E u r ≤ W*r^(2*κ)*(E.card:ℝ)) →
      ∃ a ∈ E, W*(X.card:ℝ) < ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) := by
  classical
  obtain ⟨η,N0,hη,hN0,hprojection⟩ := scalar_bounded_projection hκ hκ1
  obtain ⟨N1,hN1,hloss⟩ := scalar_fixed_losses hη
    (by norm_num : (0:ℝ) < 68096*(5:ℝ)^8) zero_lt_one
  let ε := η/36
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε,max N0 N1,hε,lt_of_lt_of_le hN0 (le_max_left _ _),?_⟩
  intro N hN
  dsimp only
  intro X hX hXbound hsep hsize hd hpoint E hE hEbound hEball
  let δ := (1/2:ℝ)^N
  let W := Real.exp (ε*(N:ℝ)*Real.log 2)
  let WF := Real.exp (η*(N:ℝ)*Real.log 2)
  have hδ : 0 < δ := by positivity
  have hW1 : 1 ≤ W := Real.one_le_exp_iff.mpr (by positivity)
  have hW0 : 0 ≤ W := (Real.exp_pos _).le
  have hlog : 0 ≤ (N:ℝ)*Real.log 2 := by positivity
  have hpower (n : ℕ) (hn : (n:ℝ) ≤ 36) : W^n ≤ WF := by
    rw [show W = Real.exp (ε*(N:ℝ)*Real.log 2) from rfl,← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    dsimp [ε]
    have hh := mul_le_mul_of_nonneg_right hn (mul_nonneg hη.le hlog)
    nlinarith
  have hWWF : W ≤ WF := by simpa only [pow_one] using hpower 1 (by norm_num)
  have hbudget : (68096*(5:ℝ)^8)*W^9 ≤ WF := by
    have he : W^9 = Real.exp ((η/4)*(N:ℝ)*Real.log 2) := by
      rw [show W = Real.exp (ε*(N:ℝ)*Real.log 2) from rfl,← Real.exp_nat_mul]
      congr 1
      dsimp [ε]
      ring
    rw [he]
    exact (hloss N ((le_max_right _ _).trans hN)).1
  have hpointF : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass X u r ≤ WF*r^κ*(X.card:ℝ) := by
    intro u r hr hr1
    have hh := mul_le_mul_of_nonneg_right hWWF
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) κ) (Nat.cast_nonneg X.card))
    exact (hpoint u r hr hr1).trans (by nlinarith)
  have hdF : ((scalarCells δ (X+X)).card:ℝ) ≤ WF*(X.card:ℝ) :=
    hd.trans (mul_le_mul_of_nonneg_right hWWF (Nat.cast_nonneg _))
  by_contra hn
  push Not at hn
  obtain ⟨b,hb,hmax⟩ := E.exists_max_image (fun a => |a|) hE
  by_cases hb1 : |b| ≤ 1
  · have heball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass E u r ≤ WF*r^(2*κ)*(E.card:ℝ) := by
      intro u r hr hr1
      have hh := mul_le_mul_of_nonneg_right hWWF
        (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) (2*κ)) (Nat.cast_nonneg E.card))
      exact (hEball u r hr hr1).trans (by nlinarith)
    obtain ⟨a,ha,hgain⟩ := hprojection N ((le_max_left _ _).trans hN) X hX hXbound hsep hsize
      hdF hpointF E hE (fun a ha => (hmax a ha).trans hb1) heball
    have hh := (hn a ha).trans (mul_le_mul_of_nonneg_right hWWF (Nat.cast_nonneg _))
    exact (not_lt_of_ge hh) hgain
  · have hbpos : 0 < |b| := zero_lt_one.trans (lt_of_not_ge hb1)
    have hbne : b ≠ 0 := abs_pos.mp hbpos
    let F := E.image (fun a => -a/(-b))
    have hF : F.Nonempty := hE.image _
    have hFbound : ∀ a ∈ F, |a| ≤ 1 := by
      intro a ha
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
      rw [neg_div_neg_eq,abs_div]
      exact (div_le_one hbpos).2 (hmax x hx)
    have hFball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass F u r ≤ WF*r^(2*κ)*(F.card:ℝ) := by
      intro u r hr _
      have hh := scalar_ratio_family_ball hδ (by positivity : 0 ≤ 2*κ) hW1 hW1
        (neg_ne_zero.mpr hbne) (by simpa only [abs_neg] using hEbound b hb)
        E E (Finset.Subset.refl _) (by simp : (E.card:ℝ) ≤ 1*(E.card:ℝ)) hEball u r hr
      have hp : W^(2*κ) ≤ W^2 := by
        have hh := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith : 2*κ ≤ 2)
        simpa only [Real.rpow_two] using hh
      have hc : 1*W*W^(2*κ) ≤ WF := by
        calc
          _ ≤ W*W^2 := by nlinarith
          _ = W^3 := by ring
          _ ≤ WF := hpower 3 (by norm_num)
      have hm := mul_le_mul_of_nonneg_right hc
        (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) (2*κ)) (Nat.cast_nonneg F.card))
      change scalarBallMass F u r ≤ (1*W*W^(2*κ))*r^(2*κ)*(F.card:ℝ) at hh
      exact hh.trans (by nlinarith)
    obtain ⟨a,ha,hgain⟩ := hprojection N ((le_max_left _ _).trans hN)
      X hX hXbound hsep hsize hdF hpointF F hF hFbound hFball
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    have hXc : (scalarCells δ X).card = X.card :=
      Finset.card_image_of_injOn (scalarCells_injective hδ hsep)
    have hp (a : ℝ) (ha : a ∈ E) :
        ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) ≤ W*(scalarCells δ X).card := by
      rw [hXc]
      exact hn a ha
    have hh := scalar_max_ratio_projection hδ hW1 X hX (hEbound x hx)
      (lt_of_not_ge hb1).le (by simpa only [hXc] using hd) (hp x hx) (hp b hb)
    have hupper := hh.trans (mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _))
    rw [hXc] at hupper
    simp only [neg_div_neg_eq] at hgain
    exact (not_lt_of_ge hupper) hgain

end Falconer.Regularization

end OAI
