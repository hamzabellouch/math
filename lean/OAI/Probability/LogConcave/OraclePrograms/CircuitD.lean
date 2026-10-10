import Mathlib
import OAI.Probability.LogConcave.Numerics.Picard

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

def circuitD {d : ℕ} (F : Point d → ℝ) (x : Point d) : ℝ :=
  Real.sqrt d+‖gradient F x‖
lemma circuitD_nonneg {d : ℕ} (F : Point d → ℝ) (x : Point d) : 0 ≤ circuitD F x := by
  unfold circuitD; positivity
lemma sqrt_le_circuitD {d : ℕ} (F : Point d → ℝ) (x : Point d) : Real.sqrt d ≤ circuitD F x := by
  unfold circuitD; exact le_add_of_nonneg_right (norm_nonneg _)
lemma field_zero_eq_gradient {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) :
    primitiveField F x r 0=gradient F x := by simp [primitiveField]

def circuitGrowthConstant : ℝ := 8*(terminalTransportConstant+1)*(Real.pi+1)
lemma circuitGrowthConstant_pos : 0<circuitGrowthConstant := by
  unfold circuitGrowthConstant
  positivity [terminalTransportConstant_pos]

lemma probabilityInitialRms_growth {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam : ℝ≥0) {r : ℝ} (hr : 0≤r) (hL : (lam:ℝ)*r≤1) :
    probabilityInitialRms F x lam r ≤ circuitGrowthConstant*r*circuitD F x := by
  let C := terminalTransportConstant
  let D := circuitD F x
  have hC : 0<C := terminalTransportConstant_pos
  have hD : 0≤D := circuitD_nonneg F x
  have hdc : ‖primitiveField F x r 0‖≤D := by
    rw [field_zero_eq_gradient]; exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hds : Real.sqrt d≤D := sqrt_le_circuitD F x
  have hL0 : 0≤(lam:ℝ)*r := by positivity
  have ha : r*‖primitiveField F x r 0‖+(lam:ℝ)*r^2*Real.pi*Real.sqrt d ≤ r*(Real.pi+1)*D := by
    have h₁ := mul_le_mul_of_nonneg_left hdc hr
    have h₂ := mul_le_mul_of_nonneg_right hL (show 0≤r*Real.pi*Real.sqrt d by positivity)
    have h₃ := mul_le_mul_of_nonneg_left hds (show 0≤r*Real.pi by positivity)
    nlinarith
  have hb : (lam:ℝ)*r^2*Real.sqrt d ≤ r*D := by
    have h₁ := mul_le_mul_of_nonneg_right hL (show 0≤r*Real.sqrt d by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hds hr
    nlinarith
  have ha' := pow_le_pow_left₀ (show 0≤r*‖primitiveField F x r 0‖+(lam:ℝ)*r^2*Real.pi*Real.sqrt d by positivity) ha 2
  have hb' := pow_le_pow_left₀ (show 0≤(lam:ℝ)*r^2*Real.sqrt d by positivity) hb 2
  have hs := Real.sq_sqrt (show 0≤(d:ℝ) by positivity)
  have hm₁ := mul_le_mul_of_nonneg_left ha' (show 0≤2*C^2 by positivity)
  have hm₂ := mul_le_mul_of_nonneg_left hb' (show 0≤2*C^2 by positivity)
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by exact mul_nonneg (mul_nonneg circuitGrowthConstant_pos.le hr) hD,?_⟩
  change 2*(C*(r*‖primitiveField F x r 0‖+(lam:ℝ)*r^2*Real.pi*Real.sqrt d))^2+
    2*(C*((lam:ℝ)*r^2))^2*d ≤ _
  have hn : 2*C^2*(r*(Real.pi+1)*D)^2+2*C^2*(r*D)^2 ≤
      (circuitGrowthConstant*r*D)^2 := by
    have hp : 1≤Real.pi+1 := by linarith [Real.pi_pos]
    have hmul : r*D ≤ (Real.pi+1)*(r*D) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (show 0≤r*D by positivity)
    have h := pow_le_pow_left₀ (by positivity : 0≤r*D) hmul 2
    have hc : 4*C^2 ≤ (8*(C+1))^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg (r*(Real.pi+1)*D))
    dsimp only [circuitGrowthConstant]
    change _ ≤ (8*(C+1)*(Real.pi+1)*r*D)^2
    nlinarith [mul_nonneg (show 0≤2*C^2 by positivity) (sub_nonneg.mpr h)]
  nlinarith [hm₁,hm₂]

lemma conditionalMean_flow_growth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r) (hr1 : r≤1)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1) (hT0 : 0≤T) (hT1 : T<1)
    (z : Point d) :
    ‖conditionalFieldMean F x r T (fullProbabilityFlow hF x hr hl T z)‖ ≤
      circuitGrowthConstant*(circuitD F x+‖z‖) := by
  let C := terminalTransportConstant
  let B := Real.pi*Real.sqrt d+‖z‖+‖primitiveField F x r 0‖
  have hC : 0<C := terminalTransportConstant_pos
  have hB : 0≤B := by dsimp [B]; positivity
  have hf := probabilityFlow_initial_displacement hF x hr hl z ⟨hT0,hT1.le⟩
  have hn := norm_le_norm_sub_add (fullProbabilityFlow hF x hr hl T z) z
  have h₁ := mul_le_mul_of_nonneg_right hr1 (norm_nonneg (primitiveField F x r 0))
  have h₂ := mul_le_mul_of_nonneg_right (show (lam:ℝ)*r^2≤1 by linarith)
    (show 0≤Real.pi*Real.sqrt d+‖z‖ by positivity)
  have hfb : ‖fullProbabilityFlow hF x hr hl T z‖ ≤ (C+1)*B := by
    have h := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hC.le
    dsimp [C,B] at *
    nlinarith [norm_nonneg (primitiveField F x r 0),Real.sqrt_nonneg (d:ℝ),Real.pi_pos]
  have hm := conditionalFieldMean_center_zero_bound hF x hr hl hT0 hT1
    (fullProbabilityFlow hF x hr hl T z)
  have hmn := norm_le_norm_sub_add (conditionalFieldMean F x r T (fullProbabilityFlow hF x hr hl T z))
    (primitiveField F x r 0)
  have hinside : Real.pi*Real.sqrt d+‖fullProbabilityFlow hF x hr hl T z‖+
      r*‖primitiveField F x r 0‖ ≤ (C+2)*B := by
    dsimp [B] at *
    nlinarith [norm_nonneg z]
  have hmul := mul_le_mul hL hinside (by positivity : 0≤Real.pi*Real.sqrt d+
    ‖fullProbabilityFlow hF x hr hl T z‖+r*‖primitiveField F x r 0‖) (by norm_num : (0:ℝ)≤1)
  have hfin : ‖conditionalFieldMean F x r T (fullProbabilityFlow hF x hr hl T z)‖ ≤ (2*C+5)*B := by
    have hc : ‖primitiveField F x r 0‖≤B := by
      dsimp [B]; exact le_add_of_nonneg_left (by positivity)
    nlinarith
  have hB' : B≤(Real.pi+1)*(circuitD F x+‖z‖) := by
    dsimp [B,circuitD]
    rw [field_zero_eq_gradient]
    nlinarith [mul_nonneg Real.pi_pos.le (norm_nonneg z),
      mul_nonneg Real.pi_pos.le (norm_nonneg (gradient F x)), Real.sqrt_nonneg (d:ℝ)]
  have hc : 2*C+5≤8*(C+1) := by linarith
  exact hfin.trans ((mul_le_mul hc hB' hB (by positivity)).trans_eq (by
    dsimp only [circuitGrowthConstant]; change _=8*(C+1)*(Real.pi+1)*(circuitD F x+‖z‖); ring))

lemma harmonicStationaryMoment_growth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r) (hr1 : r≤1)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1) (hT0 : 0≤T) (hT1 : T<1) :
    harmonicStationaryMoment F x r T ≤ 4*circuitGrowthConstant^2*(circuitD F x)^2 := by
  have hm := (conditionalFieldMean_lipschitz hF x hr hl hT0 hT1).continuous
  have hg := gaussian_growth_sq_moment (hm.comp (fullProbabilityFlow_lipschitz hF x hr hl ⟨hT0,hT1.le⟩).continuous)
    circuitGrowthConstant_pos.le (circuitD_nonneg F x)
    (conditionalMean_flow_growth hF x hr hr1 hl hL hT0 hT1)
  have he : harmonicStationaryMoment F x r T =
      ∫z,‖conditionalFieldMean F x r T (fullProbabilityFlow hF x hr hl T z)‖^2 ∂stdGaussian (Point d) := by
    have hm' : AEStronglyMeasurable (fun y => ‖conditionalFieldMean F x r T y‖^2)
        ((gibbs (centeringPotential F x r T)).map (fun y => (productPointEquiv d d y).1)) :=
      (hm.norm.pow 2).aestronglyMeasurable
    have e₁ := integral_map ((productPointEquiv d d).continuous.fst.measurable.aemeasurable) hm'
    change (∫y,‖conditionalFieldMean F x r T y‖^2
      ∂(gibbs (centeringPotential F x r T)).map (fun y => (productPointEquiv d d y).1))=_ at e₁
    rw [centering_position_law hF x hr hl hT0 hT1] at e₁
    have e₂ := integral_map
      ((fullProbabilityFlow_lipschitz hF x hr hl ⟨hT0,hT1.le⟩).continuous.measurable.aemeasurable)
      (show AEStronglyMeasurable (fun y => ‖conditionalFieldMean F x r T y‖^2)
        ((stdGaussian (Point d)).map (fullProbabilityFlow hF x hr hl T)) from
        (hm.norm.pow 2).aestronglyMeasurable)
    rw [fullProbabilityFlow_interpolation_closed hF x hr hl hT0 hT1] at e₂
    exact e₁.symm.trans e₂
  rw [he]
  apply hg.2.trans
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg (d:ℝ)) (sqrt_le_circuitD F x) 2
  rw [Real.sq_sqrt (Nat.cast_nonneg d)] at hs
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg circuitGrowthConstant)]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set
open scoped Classical BigOperators NNReal

variable {d : ℕ}

lemma circuitD_change {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x y : Point d) : circuitD F y≤circuitD F x+(lam:ℝ)*‖y-x‖ := by
  have he := hF.gradient_lipschitz.dist_le_mul y x
  rw [dist_eq_norm,dist_eq_norm] at he
  have hn := norm_le_norm_add_norm_sub (gradient F x) (gradient F y)
  rw [norm_sub_rev] at hn
  dsimp [circuitD]
  linarith

lemma primitiveExpectedField_growth {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1) :
    ‖primitiveExpectedField F x r‖≤(2*Real.pi+2)*circuitD F x := by
  have he := terminal_mean_error hF x hr hl (0:Point d)
  rw [norm_zero,add_zero,field_zero_eq_gradient] at he
  have hn := norm_le_norm_add_norm_sub (gradient F x) (primitiveExpectedField F x r)
  have h₁ := mul_le_mul_of_nonneg_right hL (show 0≤2*Real.pi*Real.sqrt d by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hl (show 0≤2*‖gradient F x‖ by positivity)
  have h₃ := mul_nonneg (show 0≤2*Real.pi by positivity) (norm_nonneg (gradient F x))
  dsimp [circuitD]
  nlinarith [Real.sqrt_nonneg (d:ℝ)]

namespace MeanTree
variable {X : Type*} [MeasurableSpace X]

theorem eval_circuitD_bound {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) (z : X) {A B : ℝ} (hB : 0≤B)
    (hsmall : (lam:ℝ)*A*(2*Real.pi+2)≤1)
    (E : MeanTree X d) (hw : weight E≤A) (hweights : centersBound A E)
    (hb : circuitD F x+(lam:ℝ)*‖base E z-x‖≤B)
    (hc : centers (fun r b => 0≤r ∧ (lam:ℝ)*r^2≤1/2 ∧ (lam:ℝ)*r≤1 ∧
      circuitD F x+(lam:ℝ)*‖b z-x‖≤B) E) :
    circuitD F (E.eval F z)≤((depth E:ℝ)+1)*B := by
  induction E with | node k b hm a r C ih =>
    have hchild (i : Fin k) := ih i (hweights i).1 (hweights i).2 (hc i).1.2.2.2 (hc i).2
    have hd (i : Fin k) : (depth (C i):ℝ)+1≤(depth (node k b hm a r C):ℝ) := by
      exact_mod_cast (Finset.le_sup (f:=fun j => depth (C j)+1) (Finset.mem_univ i))
    have hmean (i : Fin k) : ‖primitiveExpectedField F ((C i).eval F z) (r i)‖≤
        (2*Real.pi+2)*(depth (node k b hm a r C):ℝ)*B := by
      apply (primitiveExpectedField_growth hF _ (hc i).1.1 (hc i).1.2.1 (hc i).1.2.2.1).trans
      exact (mul_le_mul_of_nonneg_left
        ((hchild i).trans (mul_le_mul_of_nonneg_right (hd i) hB)) (by positivity)).trans_eq (by ring)
    have hs : ‖∑i,a i • primitiveExpectedField F ((C i).eval F z) (r i)‖≤
        (∑i,|a i|)*((2*Real.pi+2)*(depth (node k b hm a r C):ℝ)*B) := by
      apply (norm_sum_le _ _).trans
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun i _ => by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hmean i) (abs_nonneg _))
    have hn : ‖(node k b hm a r C).eval F z-x‖≤‖b z-x‖+
        (∑i,|a i|)*((2*Real.pi+2)*(depth (node k b hm a r C):ℝ)*B) := by
      change ‖b z+(∑i,a i • primitiveExpectedField F ((C i).eval F z) (r i))-x‖≤_
      rw [add_sub_right_comm]
      exact (norm_add_le _ _).trans (add_le_add le_rfl hs)
    have hD := (circuitD_change hF x ((node k b hm a r C).eval F z)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hn lam.coe_nonneg))
    change (∑i,|a i|)≤A at hw
    have hmcoef := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw lam.coe_nonneg)
      (show 0≤2*Real.pi+2 by positivity)
    have hcoef : (lam:ℝ)*(∑i,|a i|)*(2*Real.pi+2)≤1 := hmcoef.trans hsmall
    have hh := mul_le_mul_of_nonneg_right hcoef
      (show 0≤(depth (node k b hm a r C):ℝ)*B by positivity)
    change circuitD F x+(lam:ℝ)*‖b z-x‖≤B at hb
    nlinarith
end MeanTree
end LogConcaveSampling

end

end

end OAI
