import Mathlib
import OAI.Geometry.WeakHessian.Transport.CDPlanLeg
import OAI.Geometry.WeakHessian.HeatFlow.CommonLocalHeatLegs
import OAI.Geometry.WeakHessian.Geodesics.LocalTwoLegLimit

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma geodesic_dist_initial_le {γ : Curve X} (hγ : IsGeodesic γ) (t : Time) :
    dist (γ t) (γ timeZero) ≤ dist (γ timeZero) (γ timeOne) := by
  rw [hγ t timeZero]
  change |(t:ℝ)-0| *dist (γ timeZero) (γ timeOne) ≤ _
  rw [sub_zero,abs_of_nonneg t.property.1]
  exact mul_le_of_le_one_left dist_nonneg t.property.2

lemma WeakHessianUpperBound.rcd_local_midpoint {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G)
    (σ : Curve X) (hσ : IsGeodesic σ) {R c : ℝ}
    (hR : 0 < R) (hshort : dist (σ timeZero) (σ timeOne) < R)
    (hlocal : ∀ x,dist x (σ timeHalf) < R → G x ≤ c) :
    (F (σ timeZero)+F (σ timeOne))/2-c/8*dist (σ timeZero) (σ timeOne)^2 ≤ F (σ timeHalf) := by
  let o := σ timeHalf
  let x₀ := σ timeZero
  let x₁ := σ timeOne
  let D := dist x₀ x₁
  have hd0 : dist o x₀ = D/2 := by
    change dist (σ timeHalf) (σ timeZero) = _
    rw [hσ timeHalf timeZero]
    norm_num [timeHalf,timeZero,D,x₀,x₁]; ring
  have hd1 : dist o x₁ = D/2 := by
    change dist (σ timeHalf) (σ timeOne) = _
    rw [hσ timeHalf timeOne]
    norm_num [timeHalf,timeOne,D,x₀,x₁]; ring
  obtain ⟨LD₀,hLD₀⟩ := boundedHopfMap_lipschitz (midpointDualTest x₀ D) zero_lt_one
  obtain ⟨LD₁,hLD₁⟩ := boundedHopfMap_lipschitz (midpointDualTest x₁ D) zero_lt_one
  apply midpoint_bound_of_local_two_leg_approx (LD := (LD₀:ℝ)+(LD₁:ℝ))
    (J := 2*(‖midpointDualTest x₀ D‖+‖midpointDualTest x₁ D‖)) (CG := CG) (CF := CF) (L := (L:ℝ))
  have hgap : 0 < R-3*R/4 := by linarith
  filter_upwards [eventually_local_scaling_admissible c CG CF hgap,self_mem_nhdsWithin] with s hadm hs
  have hsp : 0 < s := hs
  filter_upwards [(eventually_lt_nhds (show (0:ℝ) < R/12 by positivity)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with r hrR hr
  have hrp : 0 < r := hr
  intro δ q hδ hq
  obtain ⟨μ,B,hB,hμcap,hμs⟩ := exists_small_ball_law hfull hfin o hrp
  obtain ⟨μ₀,B₀,hB₀,hμ₀cap,hμ₀s⟩ := exists_small_ball_law hfull hfin x₀ hrp
  obtain ⟨μ₁,B₁,hB₁,hμ₁cap,hμ₁s⟩ := exists_small_ball_law hfull hfin x₁ hrp
  obtain ⟨π₀,C₀,hC₀,hπ₀,hb₀,hg₀,hi₀,_,hcap₀,ht₀,hE₀⟩ :=
    hrcd.1.exists_plan_leg hN hfin μ μ₀ o x₀ hrp.le hμs hμ₀s hB hB₀ hμcap hμ₀cap
  obtain ⟨π₁,C₁,hC₁,hπ₁,hb₁,hg₁,hi₁,_,hcap₁,ht₁,hE₁⟩ :=
    hrcd.1.exists_plan_leg hN hfin μ μ₁ o x₁ hrp.le hμs hμ₁s hB hB₁ hμcap hμ₁cap
  have htrack₀ : ∀ᵐ γ ∂π₀,∀ t : Time,dist (γ t) o < 3*R/4 := by
    filter_upwards [hg₀,ht₀] with γ hγ hγt t
    have H := dist_triangle (γ t) (γ timeZero) o
    have H' := geodesic_dist_initial_le hγ t
    rw [hd0] at hγt
    change D < R at hshort
    linarith [hγt.1,hγt.2.2]
  have htrack₁ : ∀ᵐ γ ∂π₁,∀ t : Time,dist (γ t) o < 3*R/4 := by
    filter_upwards [hg₁,ht₁] with γ hγ hγt t
    have H := dist_triangle (γ t) (γ timeZero) o
    have H' := geodesic_dist_initial_le hγ t
    rw [hd1] at hγt
    change D < R at hshort
    linarith [hγt.1,hγt.2.2]
  obtain ⟨d,hd,he,hdecay,_,_,_⟩ := hrcd.1.exists_strong_entropy_confinement hN hfull hfin o
  have hdecay' : MemLp (fun x => Real.exp (-d*dist x o)) 2 m := by simpa only [neg_mul] using hdecay
  let E := ∫ x,Real.exp (-(d*dist x o)) ∂m
  let Q₀ := ((C₀:ℝ)+1)*(‖hdecay'.toLp (fun x => Real.exp (-d*dist x o))‖+1)
  let Q₁ := ((C₁:ℝ)+1)*(‖hdecay'.toLp (fun x => Real.exp (-d*dist x o))‖+1)
  have hD : 0 ≤ D/2+2*r := by dsimp [D]; positivity
  have H := vanishing_diffusion_local_two_leg
    (Z := D^2/4-((LD₀:ℝ)+(LD₁:ℝ))*(r+δ*(D/2+2*r))-
      2*(‖midpointDualTest x₀ D‖+‖midpointDualTest x₁ D‖)*q)
    (E := (D/2+2*r)^2) (s := s) (A := 4*r^2+16*s*CF)
    (B := 8*(|Real.log (B:ℝ)|+E+1)) (C := |Real.log (C₀:ℝ)|+|Real.log (C₁:ℝ)|+2*(E+1))
    (d := d) (f := 2*F o-F x₀-F x₁) (L := (L:ℝ)) (R := 2*r+δ*(D+4*r))
    hsp.le hd.le L.property (localizedActionBound_scaling_limit K c CG hsp.le)
    (curvatureTailBound_scaling_limit K c CG CF s (hopfUniformLip (midpointDualTest x₀ D) q) Q₀ d R (3*R/4) hadm.2)
    (curvatureTailBound_scaling_limit K c CG CF s (hopfUniformLip (midpointDualTest x₁ D) q) Q₁ d R (3*R/4) hadm.2) ?_
  · convert H using 1
    dsimp [o,x₀,x₁,D]
    ring
  · filter_upwards [localized_small_scaled_eventually (K := K) hadm.1,self_mem_nhdsWithin] with T hsmall hT
    have hTp : 0 < T := hT
    have hβ : d ≤ d+(R-3*R/4)/(4*T) := by linarith [div_nonneg hgap.le (by positivity : (0:ℝ) ≤ 4*T)]
    obtain ⟨M,hM0,hM,hcomp⟩ := hHess.rcd_common_local_heat_legs hN hrcd hfull hfin hF hFb hGb hGc
      o x₀ x₁ μ hrp.le hμs hB hμcap hd he hdecay' hC₀ hC₁ hπ₀ hπ₁ hb₀ hb₁ hg₀ hg₁ hi₀ hi₁ hcap₀ hcap₁
      (D₀ := D/2+2*r) (D₁ := D/2+2*r) hD hD
      (ht₀.mono fun γ hγ => hγ.2.1) (ht₁.mono fun γ hγ => hγ.2.1)
      (by simpa only [hd0] using ht₀.mono fun γ hγ => hγ.2.2)
      (by simpa only [hd1] using ht₁.mono fun γ hγ => hγ.2.2)
      (by simpa only [hd0] using hE₀) (by simpa only [hd1] using hE₁)
      htrack₀ htrack₁ hlocal (Rd := D) le_rfl hLD₀ hLD₁
      (a := s/T) (div_pos hsp hTp) hTp.le (by linarith : T < 2*T) hδ hq hβ hsmall
    rw [div_mul_cancel₀ s hTp.ne'] at hcomp
    rw [mul_div_cancel₀ s hTp.ne'] at hM
    refine ⟨M,hM0,?_,?_⟩
    · convert hM using 1
      dsimp [E]
      ring
    · convert hcomp using 1 <;> dsimp [D,E,Q₀,Q₁] <;> ring
end WeakHessian

end
end

end OAI
