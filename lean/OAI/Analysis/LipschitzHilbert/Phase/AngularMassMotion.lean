import OAI.Analysis.LipschitzHilbert.Phase.AngularBoundaryLocality
import OAI.Analysis.LipschitzHilbert.Estimates.ExponentialVariation
import OAI.Analysis.LipschitzHilbert.Phase.AngularSourceAmplitude

namespace OAI

/-! The actual source averaging scale makes every boundary submass move
by order G^(-1/2), including submasses from other shifted blocks. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

/-- The two locality terms are small on the manuscript's averaging cell.
The stronger B² eligibility and width hypotheses retain a spare factor B. -/
theorem source_mass_motion_budget {rho child w B G gap a : ℝ}
    (_hrho : 0 < rho) (hchild : 0 < child) (hw : 0 < w)
    (hB : 1 ≤ B) (hG : 0 < G) (hgap : gap ≤ rho)
    (hblock : rho ≤ B*child) (ha : |a| ≤ w/(child*Real.sqrt G)) :
    (rho/(B^2*w)+(3*rho+gap)/(B^2*w))*|a| ≤ 5/Real.sqrt G := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hroot : 0 < Real.sqrt G := Real.sqrt_pos.mpr hG
  have hden : 0 < B^2*w := mul_pos (sq_pos_of_pos hB0) hw
  have hra : rho*|a| ≤ B*w/Real.sqrt G := by
    calc
      _ ≤ (B*child)*(w/(child*Real.sqrt G)) :=
        mul_le_mul hblock ha (abs_nonneg _) (mul_pos hB0 hchild).le
      _ = _ := by field_simp [hchild.ne', hroot.ne']
  calc
    _ = ((4*rho+gap)*|a|)/(B^2*w) := by ring
    _ ≤ (5*(rho*|a|))/(B^2*w) := by
      apply div_le_div_of_nonneg_right _ hden.le
      nlinarith [abs_nonneg a]
    _ ≤ (5*(B*w/Real.sqrt G))/(B^2*w) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hra (by norm_num)) hden.le
    _ = (5/Real.sqrt G)/B := by field_simp [hB0.ne', hw.ne', hroot.ne']
    _ ≤ 5/Real.sqrt G := div_le_self (by positivity) hB

namespace AngularGrid

variable {ι : Type*}

/-- At H=w/(child sqrt G), concrete boundary submasses have uniformly
small logarithmic motion. Here the top width lower bound is exactly the
consequence W=m w≥B²w used in the source. -/
theorem boundary_submass_source_motion (g : AngularGrid) (tops : Finset ι)
    (T : ι → SlopeBox) (w B K D : ℝ) (hw : 0 < w) (hB : 1 ≤ B)
    (hK : 0 < K) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (base h i : ℕ) (hhi : h ≤ i) (gap : ℝ) (hgap0 : 0 ≤ gap) (hgap : gap ≤ g.width h)
    (s sR : ℝ) (hs : g.index h s = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (A : Finset ι) (hA : A.Nonempty)
    (hsub : A ⊆ g.boundaryTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) base i gap s)
    (a : ℝ) (ha : |a| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ) :
    |Real.log (∑ t ∈ A, (T t).weight K D (SlopeBox.lineShift sR a z)) -
      Real.log (∑ t ∈ A, (T t).weight K D z)| ≤
        (5*D/K)/Real.sqrt (g.branching:ℝ) := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hG : (0:ℝ) < g.branching := by
    exact_mod_cast (show 0 < g.branching by have := g.branching_ge_two; omega)
  have hmotion := g.boundary_submass_log_line_motion tops T w (B^2*w) (g.rootWidth/B^2)
    K D hw (mul_pos (sq_pos_of_pos hB0) hw) hK hD hwidth base h i hhi gap hgap0
    s sR hs A hA hsub a z
  have heq : (g.rootWidth/B^2)/((g.branching:ℝ)^h*w) = g.width h/(B^2*w) := by
    simp only [width, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq] at hmotion
  have hbudget := source_mass_motion_budget (g.width_pos h) hchild hw hB hG hgap hblock ha
  calc
    _ ≤ (D/K)*(g.width h/(B^2*w)+(3*g.width h+gap)/(B^2*w))*|a| := hmotion
    _ = (D/K)*((g.width h/(B^2*w)+(3*g.width h+gap)/(B^2*w))*|a|) := by ring
    _ ≤ (D/K)*(5/Real.sqrt (g.branching:ℝ)) :=
      mul_le_mul_of_nonneg_left hbudget (div_nonneg hD hK.le)
    _ = _ := by ring

end AngularGrid

/-- Moving numerator and denominator logarithms give the exact uniform
bound needed for one child-to-boundary ratio. -/
theorem positive_ratio_log_motion {a b a' b' delta : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b')
    (hA : |Real.log a'-Real.log a| ≤ delta)
    (hB : |Real.log b'-Real.log b| ≤ delta) :
    |Real.log (a'/b')-Real.log (a/b)| ≤ 2*delta := by
  rw [Real.log_div ha'.ne' hb'.ne', Real.log_div ha.ne' hb.ne']
  calc
    _ = |(Real.log a'-Real.log a)-(Real.log b'-Real.log b)| := by congr 1; ring
    _ ≤ |Real.log a'-Real.log a|+|Real.log b'-Real.log b| := abs_sub _ _
    _ ≤ _ := by linarith

/-- A logarithmic perturbation of a nonzero exponential gives relative
complex motion; the bound does not involve the original logarithm. -/
theorem exponential_relative_motion {a b : ℂ} {E : ℝ}
    (hE : 0 ≤ E) (hmove : ‖b-a‖ ≤ E) :
    ‖Complex.exp b/Complex.exp a-1‖ ≤ Real.exp E*E := by
  have harg : (b-a).re ≤ E := (Complex.re_le_norm _).trans hmove
  have h := norm_exp_sub_le_of_re_le 0 (b-a) E hE harg
  rw [Complex.exp_zero, sub_zero] at h
  have heq : Complex.exp b/Complex.exp a = Complex.exp (b-a) := by
    rw [Complex.exp_sub]
  rw [heq]
  exact h.trans (mul_le_mul_of_nonneg_left hmove (Real.exp_pos E).le)

/-- A finite product of transition exponentials depends only on the
motion of its specified logarithms, never their magnitudes. -/
theorem transition_product_relative_motion {J : Type*} (s : Finset J)
    (phase : J → ℂ) (loss0 loss1 : J → ℝ) (Z delta : ℝ)
    (hZ : 0 ≤ Z) (hdelta : 0 ≤ delta)
    (hphase : ∀ j ∈ s, ‖phase j‖ ≤ Z)
    (hloss : ∀ j ∈ s, |loss1 j-loss0 j| ≤ delta) :
    ‖(∏ j ∈ s, Complex.exp (phase j*(loss1 j:ℂ))) /
        (∏ j ∈ s, Complex.exp (phase j*(loss0 j:ℂ))) - 1‖ ≤
      Real.exp ((s.card:ℝ)*Z*delta)*((s.card:ℝ)*Z*delta) := by
  rw [← Complex.exp_sum, ← Complex.exp_sum]
  apply exponential_relative_motion (by positivity)
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ s, ‖phase j*(loss1 j:ℂ)-phase j*(loss0 j:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ s, Z*delta := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hphase j hj) (hloss j hj) (abs_nonneg _) hZ
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

namespace AngularGrid

/-- The actual block transition product has small relative motion once
its concrete child and boundary masses have the preceding local bounds. -/
theorem source_path_relative_motion {ι X : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (lower upper : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) upper) (x0 x1 : X)
    (Z delta : ℝ) (hZ : 0 ≤ Z) (hdelta : 0 ≤ delta)
    (hphase : ∀ j ∈ Finset.Ico lower upper, ‖phase j‖ ≤ Z)
    (hmass : ∀ j ∈ Finset.Ico lower upper,
      |Real.log (g.mass tops slope precision cutoff weight (j+1) (g.index (j+1) (slope top)) x1) -
        Real.log (g.mass tops slope precision cutoff weight (j+1) (g.index (j+1) (slope top)) x0)| ≤ delta)
    (hboundary : ∀ j ∈ Finset.Ico lower upper,
      |Real.log (g.sourceBoundaryMass tops slope precision cutoff weight K gap j
          (g.index (j+1) (slope top)) x1) -
        Real.log (g.sourceBoundaryMass tops slope precision cutoff weight K gap j
          (g.index (j+1) (slope top)) x0)| ≤ delta) :
    ‖g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x1)
        lower upper (slope top) /
      g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x0)
        lower upper (slope top) - 1‖ ≤
      Real.exp ((upper-lower:ℕ)*Z*(2*delta))*((upper-lower:ℕ)*Z*(2*delta)) := by
  let n := fun j x => g.mass tops slope precision cutoff weight (j+1)
    (g.index (j+1) (slope top)) x
  let b := fun j x => g.sourceBoundaryMass tops slope precision cutoff weight K gap j
    (g.index (j+1) (slope top)) x
  have hn (j : ℕ) (hj : j ∈ Finset.Ico lower upper) (x : X) : 0 < n j x := by
    apply g.path_mass_pos tops slope precision cutoff weight hw (j+1) top htop
    exact g.eligible_of_le (hp top htop) (by have := (Finset.mem_Ico.mp hj).2; omega) he
  have hb (j : ℕ) (hj : j ∈ Finset.Ico lower upper) (x : X) : 0 < b j x :=
    (hn j hj x).trans_le (g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
      (fun t x => (hw t x).le) hK gap j (slope top) x).1
  have h := transition_product_relative_motion (Finset.Ico lower upper) phase
    (fun j => Real.log (n j x0/b j x0)) (fun j => Real.log (n j x1/b j x1))
    Z (2*delta) hZ (by positivity) hphase (fun j hj =>
      positive_ratio_log_motion (hn j hj x0) (hb j hj x0) (hn j hj x1) (hb j hj x1)
        (hmass j hj) (hboundary j hj))
  simpa only [packetPathProduct, sourceTransition, analyticTransition, n, b, Nat.card_Ico] using h

end AngularGrid

end LipschitzHilbert

end

end OAI
