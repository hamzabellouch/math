import OAI.Analysis.LienardCycles.RiccatiDerivatives

namespace OAI

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter MeasureTheory
open scoped Topology

namespace QuinticLienard.Riccati

theorem inverse_square_integral_bound {v vp q : ℝ → ℝ} {ν a S : ℝ}
    (hS : 0 ≤ S) (ha : 0 < a+ν)
    (hv : ∀ s, HasDerivAt v (vp s) s)
    (hvp : ∀ s ∈ Icc 0 S, HasDerivAt vp (q s*v s) s)
    (hpos : ∀ s, 0 < v s) (hq : ∀ s ∈ Icc 0 S, ν^2 ≤ q s)
    (hv0 : v 0 = 1) (hvp0 : vp 0 = a) :
    (∫ s in (0:ℝ)..S, 1/(v s)^2) < 1/(a+ν) := by
  have hc : Continuous v := continuous_iff_continuousAt.mpr (fun s => (hv s).continuousAt)
  have hpc : ContinuousOn vp (Icc 0 S) := fun s hs => (hvp s hs).continuousAt.continuousWithinAt
  let w : ℝ → ℝ := fun s => Real.exp (-ν*s)*(vp s+ν*v s)
  have hwc : ContinuousOn w (Icc 0 S) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (hpc.add (continuous_const.mul hc).continuousOn)
  have hwd (s : ℝ) (hs : s ∈ Icc 0 S) :
      HasDerivAt w (Real.exp (-ν*s)*(q s-ν^2)*v s) s := by
    have he := (((hasDerivAt_id s).const_mul (-ν)).exp).mul
      ((hvp s hs).add ((hv s).const_mul ν))
    convert he using 1 <;> (first | rfl | (dsimp; ring))
  have hwm : MonotoneOn w (Icc 0 S) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hwc
      (fun s hs => (hwd s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    intro s hs
    rw [(hwd s (interior_subset hs)).deriv]
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (sub_nonneg.mpr (hq s (interior_subset hs)))) (hpos s).le
  have hw (s : ℝ) (hs : s ∈ Icc 0 S) : a+ν ≤ w s := by
    have hh := hwm (show (0:ℝ) ∈ Icc 0 S from ⟨le_rfl,hS⟩) hs hs.1
    simpa [w,hv0,hvp0] using hh
  let f : ℝ → ℝ := fun s => 1/(v s)^2
  have hfc : Continuous f := continuous_const.div (hc.pow 2) (fun s => pow_ne_zero _ (ne_of_gt (hpos s)))
  let H : ℝ → ℝ := fun s => (a+ν)*(∫ y in (0:ℝ)..s, f y)+Real.exp (-ν*s)/(v s)
  have hHd (s : ℝ) : HasDerivAt H ((a+ν-w s)/(v s)^2) s := by
    have he := ((hfc.integral_hasStrictDerivAt 0 s).hasDerivAt.const_mul (a+ν)).add
      ((((hasDerivAt_id s).const_mul (-ν)).exp).div (hv s) (ne_of_gt (hpos s)))
    convert he using 1 <;> (first | rfl | (dsimp [H,w,f]; ring))
  have hHc : Continuous H := continuous_iff_continuousAt.mpr (fun s => (hHd s).continuousAt)
  have hHm : AntitoneOn H (Icc 0 S) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hHc.continuousOn
      (fun s _ => (hHd s).differentiableAt.differentiableWithinAt)
    intro s hs
    rw [(hHd s).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hw s (interior_subset hs))) (sq_nonneg _)
  have hHS := hHm (show (0:ℝ) ∈ Icc 0 S from ⟨le_rfl,hS⟩) ⟨hS,le_rfl⟩ hS
  have h0 : H 0 = 1 := by simp [H,hv0]
  rw [h0] at hHS
  have hterm : 0 < Real.exp (-ν*S)/v S := div_pos (Real.exp_pos _) (hpos S)
  have hbound : (a+ν)*(∫ s in (0:ℝ)..S, 1/(v s)^2) < 1 := by
    change (a+ν)*(∫ s in (0:ℝ)..S, f s) < 1
    dsimp [H] at hHS
    linarith
  exact (lt_div_iff₀ ha).mpr (by simpa [mul_comm] using hbound)

noncomputable def multiplier (u : ℝ → ℝ) (b d c y : ℝ) : ℝ :=
  Real.exp (-(∫ s in c..y, b*u s+d/2))

lemma multiplier_pos (u : ℝ → ℝ) (b d c y : ℝ) : 0 < multiplier u b d c y :=
  Real.exp_pos _

@[simp] lemma multiplier_initial (u : ℝ → ℝ) (b d c : ℝ) : multiplier u b d c c = 1 := by
  simp [multiplier]

lemma multiplier_deriv {u : ℝ → ℝ} (hu : Continuous u) (b d c y : ℝ) :
    HasDerivAt (multiplier u b d c)
      (-(b*u y+d/2)*multiplier u b d c y) y := by
  have hc : Continuous (fun s => b*u s+d/2) := (continuous_const.mul hu).add continuous_const
  convert (hc.integral_hasStrictDerivAt c y).hasDerivAt.neg.exp using 1
  · rfl
  · dsimp [multiplier]; ring

theorem multiplier_second_deriv {u : ℝ → ℝ} (b d c : ℝ)
    (hc : Continuous u) (y : ℝ)
    (hu : HasDerivAt u (d*u y+b*(u y)^2-y) y) :
    HasDerivAt (fun y => -(b*u y+d/2)*multiplier u b d c y)
      ((b*y+d^2/4)*multiplier u b d c y) y := by
  have he := (((hu.const_mul b).add_const (d/2)).neg).mul
    (multiplier_deriv hc b d c y)
  convert he using 1; (first | rfl | (dsimp; ring))

theorem quadratic_inverse_square_bound {u : ℝ → ℝ} {b d m n ν : ℝ}
    (hc : Continuous u) (hb : 0 ≤ b) (hmn : 0 ≤ m+n) (hd : d < 0)
    (hν : 0 ≤ ν) (hνsq : ν^2 = d^2/4-b*m) (hu0 : u (-m) = 0)
    (hu : ∀ y ∈ Icc (-m) n, HasDerivAt u (d*u y+b*(u y)^2-y) y) :
    (∫ y in (-m)..n, 1/(multiplier u b d (-m) y)^2) < 1/(ν-d/2) := by
  let V := multiplier u b d (-m)
  let v : ℝ → ℝ := fun s => V (-m+s)
  let vp : ℝ → ℝ := fun s => -(b*u (-m+s)+d/2)*V (-m+s)
  let q : ℝ → ℝ := fun s => b*(-m+s)+d^2/4
  have hv (s : ℝ) : HasDerivAt v (vp s) s := by
    simpa [v,vp,Function.comp_def] using
      (multiplier_deriv hc b d (-m) (-m+s)).comp s ((hasDerivAt_id s).const_add (-m))
  have hvp (s : ℝ) (hs : s ∈ Icc 0 (m+n)) : HasDerivAt vp (q s*v s) s := by
    have hys : -m+s ∈ Icc (-m) n := by constructor <;> linarith [hs.1,hs.2]
    simpa [vp,q,v,Function.comp_def] using
      (multiplier_second_deriv b d (-m) hc (-m+s) (hu _ hys)).comp s
        ((hasDerivAt_id s).const_add (-m))
  have he := inverse_square_integral_bound (v := v) (vp := vp) (q := q)
    (a := -d/2) (ν := ν) hmn (by linarith) hv hvp
    (fun s => multiplier_pos _ _ _ _ _) (fun s hs => by
      dsimp [q]
      rw [hνsq]
      nlinarith [mul_nonneg hb hs.1])
    (by simp [v,V]) (by simp [vp,V,hu0]; ring)
  have hi : (∫ s in (0:ℝ)..(m+n), 1/(v s)^2) =
      ∫ y in (-m)..n, 1/(multiplier u b d (-m) y)^2 := by
    dsimp [v,V]
    have hh := intervalIntegral.integral_comp_add_left
      (f := fun y => 1/(multiplier u b d (-m) y)^2) (a := (0:ℝ)) (b := m+n) (-m)
    have hab : -m+(m+n)=n := by ring
    simpa only [add_zero,hab] using hh
  rw [hi] at he
  convert he using 1; ring

theorem endpoint_variation_bound {u : ℝ → ℝ} {b d m n ν l w : ℝ}
    (hc : Continuous u) (hb : 0 < b) (hm : 0 < m) (hn : 0 < n) (hd : d < 0)
    (hν : 0 ≤ ν) (hνsq : ν^2 = d^2/4-b*m) (hu0 : u (-m) = 0)
    (hu : ∀ y ∈ Icc (-m) n, HasDerivAt u (d*u y+b*(u y)^2-y) y)
    (hw : w = 1/m-l/n+d*(1+l)+2*b*m*
      (∫ y in (-m)..n, 1/(multiplier u b d (-m) y)^2)) :
    w ≤ 1/m-l/n+d*l-2*ν := by
  have hi := quadratic_inverse_square_bound hc hb.le (by linarith) hd hν hνsq hu0 hu
  have hden : 0 < ν-d/2 := by linarith
  have hid : 2*b*m*(1/(ν-d/2)) = -d-2*ν := by
    rw [mul_one_div]
    apply (div_eq_iff (ne_of_gt hden)).mpr
    nlinarith [hνsq]
  have hmul := mul_le_mul_of_nonneg_left hi.le (show 0 ≤ 2*b*m by positivity)
  rw [hid] at hmul
  rw [hw]
  linarith

end QuinticLienard.Riccati

end OAI
