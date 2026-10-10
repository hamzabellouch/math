import OAI.Geometry.RCD.Sobolev.CompactScalarPrimitive
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace OAI

/-! # A finite-jet extension of the regularized entropy

On the prescribed bounded nonnegative interval the second derivative is
exactly the reciprocal of the value plus epsilon. The two primitives
vanish at zero and have the global bounds needed for L² heat calculus.
-/

open Set Filter Metric MeasureTheory
open scoped Topology NNReal Interval
noncomputable section
namespace RegularPointCoordinates

theorem exists_local_smooth_entropy {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) :
    ∃ (Φ φ ψ : ℝ → ℝ) (C D B E : ℝ≥0),
      LipschitzWith C Φ ∧ LipschitzWith D φ ∧ Continuous ψ ∧
      Φ 0=0 ∧ φ 0=0 ∧
      (∀ a, HasDerivAt Φ (φ a) a) ∧ (∀ a, HasDerivAt φ (ψ a) a) ∧
      (∀ a, |φ a| ≤ B) ∧ (∀ a, |ψ a| ≤ E) ∧
      ∀ a ∈ Icc 0 M, ψ a=(ε+a)⁻¹ ∧
        φ a=Real.log (ε+a)-Real.log ε ∧
        Φ a=(ε+a)*(Real.log (ε+a)-Real.log ε)-a := by
  let c := M+1
  let κ : ContDiffBump c := ⟨c+ε/4,c+ε/2,by dsimp [c]; linarith,by linarith⟩
  let ψ := fun a => κ a*(ε+a)⁻¹
  have hc0 : κ.rOut < dist (-ε) c := by
    change c+ε/2 < |(-ε)-c|
    rw [abs_of_neg (show -ε-c<0 by dsimp [c]; linarith)]
    linarith
  have hz : ψ =ᶠ[𝓝 (-ε)] (fun _ => 0) := by
    have hn := (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds hc0
    filter_upwards [hn] with a ha
    change κ a*(ε+a)⁻¹=0
    have hak : κ a=0 := κ.zero_of_le_dist (show κ.rOut ≤ dist a c from ha.le)
    rw [hak,zero_mul]
  have hc : Continuous ψ := continuous_iff_continuousAt.mpr fun a => by
    by_cases ha : a = -ε
    · subst a
      exact continuousAt_const.congr_of_eventuallyEq hz
    · exact κ.continuous.continuousAt.mul
        ((continuous_const.add continuous_id).continuousAt.inv₀ (by change ε+a≠0; intro he; apply ha; linarith))
  have hs : HasCompactSupport ψ := κ.hasCompactSupport.mul_right
  have heq (a : ℝ) (ha : a ∈ Icc 0 M) : ψ a=(ε+a)⁻¹ := by
    have hai : a ∈ ball c κ.rIn := by
      change |a-c| < c+ε/4
      rw [abs_of_neg (show a-c<0 by dsimp [c]; linarith [ha.2])]
      linarith [ha.1]
    change κ a*(ε+a)⁻¹=(ε+a)⁻¹
    rw [κ.one_of_mem_closedBall (Metric.ball_subset_closedBall hai),one_mul]
  obtain ⟨Φ,φ,C,D,B,E,hΦ,hφ,hΦ0,hφ0,hdΦ,hdφ,hB,hE,hφI,hΦI⟩ :=
    compact_scalar_two_primitives hc hs
  refine ⟨Φ,φ,ψ,C,D,B,E,hΦ,hφ,hc,hΦ0,hφ0,hdΦ,hdφ,hB,hE,?_⟩
  intro a ha
  have hpos (s : ℝ) (hs : s ∈ Icc 0 a) : 0 < ε+s := by linarith [hs.1]
  have hlog (s : ℝ) (hs : s ∈ Icc 0 M) :
      φ s=Real.log (ε+s)-Real.log ε := by
    rw [hφI]
    have hint : IntervalIntegrable (fun x => (ε+x)⁻¹) volume 0 s :=
      ((continuousOn_const.add continuousOn_id).inv₀
        (fun x hx => by change ε+x≠0; linarith [hx.1])).intervalIntegrable_of_Icc hs.1
    calc
      _ = ∫ x in 0..s, (ε+x)⁻¹ := intervalIntegral.integral_congr fun x hx =>
        heq x ⟨(uIcc_of_le hs.1 ▸ hx).1,le_trans (uIcc_of_le hs.1 ▸ hx).2 hs.2⟩
      _ = _ := by
        simpa only [add_zero] using intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun x => Real.log (ε+x)) (fun x hx => by
            have hp : 0 < ε+x := by rw [uIcc_of_le hs.1] at hx; linarith [hx.1]
            simpa only [id_eq,one_div] using ((hasDerivAt_id x).const_add ε).log hp.ne') hint
  refine ⟨heq a ha,hlog a ha,?_⟩
  rw [hΦI]
  let G := fun s => (ε+s)*(Real.log (ε+s)-Real.log ε)-s
  have hdG (s : ℝ) (hs : s ∈ Icc 0 a) :
      HasDerivAt G (Real.log (ε+s)-Real.log ε) s := by
    have hd := (((hasDerivAt_id s).const_add ε).mul
      ((((hasDerivAt_id s).const_add ε).log (hpos s hs).ne').sub_const (Real.log ε))).sub (hasDerivAt_id s)
    change HasDerivAt G
      (1*(Real.log (ε+s)-Real.log ε)+(ε+s)*(1/(ε+s))-1) s at hd
    have he : 1*(Real.log (ε+s)-Real.log ε)+(ε+s)*(1/(ε+s))-1 =
        Real.log (ε+s)-Real.log ε := by
      rw [one_mul,one_div,mul_inv_cancel₀ (hpos s hs).ne']
      ring
    rw [he] at hd
    exact hd
  have hint : IntervalIntegrable (fun s => Real.log (ε+s)-Real.log ε) volume 0 a :=
    ((continuousOn_const.add continuousOn_id).log
      (fun x hx => (hpos x hx).ne')).sub continuousOn_const |>.intervalIntegrable_of_Icc ha.1
  calc
    _ = ∫ s in 0..a, Real.log (ε+s)-Real.log ε := intervalIntegral.integral_congr fun s hs =>
      hlog s ⟨(uIcc_of_le ha.1 ▸ hs).1,le_trans (uIcc_of_le ha.1 ▸ hs).2 ha.2⟩
    _ = G a-G 0 := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hdG s (uIcc_of_le ha.1 ▸ hs)) hint
    _ = _ := by simp only [G,add_zero,sub_self,mul_zero,sub_zero]

end RegularPointCoordinates

end

end OAI
