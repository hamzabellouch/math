import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.UnshiftedCellCountBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.ShellCutoffBounds
import OAI.Analysis.CoulombIonization.FormDomain.GraphWeightIntegral

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Filter
open scoped BigOperators InnerProductSpace

section
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue

def dyadicShell {r : ℝ} (hr : 0 < r) (k : ℕ) := shellCutoff (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) k) hr)
def dyadicInside {r : ℝ} (hr : 0 < r) (k : ℕ) := radialInside 0
  (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) k) hr).le
  (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) k) hr)

lemma dyadicShell_partition {r : ℝ} (hr : 0 < r) (k : ℕ) (x : Space) :
    (dyadicShell hr k).value x^2 = (dyadicInside hr (k+1)).value x^2-(dyadicInside hr k).value x^2 := by
  have hh := shellCutoff_partition (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) k) hr) x
  convert hh using 1 <;> simp only [dyadicShell,dyadicInside,pow_succ,mul_left_comm,mul_comm]

lemma dyadicShell_sum {r : ℝ} (hr : 0 < r) (K : ℕ) (x : Space) :
    (∑ k ∈ Finset.range K, (dyadicShell hr k).value x^2) =
      (dyadicInside hr K).value x^2-(dyadicInside hr 0).value x^2 := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ,ih,dyadicShell_partition]; ring

lemma dyadicShell_total_sum {N : ℕ} {r : ℝ} (hr : 0 < r) (K : ℕ) (x : Configuration N) :
    (∑ k ∈ Finset.range K, (oneBodySquareTotal (dyadicShell hr k)).value x) =
      (oneBodySquareTotal (dyadicInside hr K)).value x-(oneBodySquareTotal (dyadicInside hr 0)).value x := by
  simp only [oneBodySquareTotal_value]
  rw [Finset.sum_comm]
  simp_rw [dyadicShell_sum]
  rw [Finset.sum_sub_distrib]

lemma dyadicShell_graph_sum {N : ℕ} {r : ℝ} (hr : 0 < r) (K : ℕ) (F : fermionGraph N) :
    (∑ k ∈ Finset.range K, (oneBodySquareTotal (dyadicShell hr k)).apply F) =
      (oneBodySquareTotal (dyadicInside hr K)).apply F-(oneBodySquareTotal (dyadicInside hr 0)).apply F := by
  exact finite_apply_sum_eq_sub (Finset.range K) (fun k => oneBodySquareTotal (dyadicShell hr k))
    (oneBodySquareTotal (dyadicInside hr K)) (oneBodySquareTotal (dyadicInside hr 0))
    (dyadicShell_total_sum hr K) F

lemma real_inner_sum_left {V α : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T : Finset α) (f : α → V) (G : V) :
    (∑ k ∈ T, (⟪f k,G⟫_ℂ).re) = (⟪∑ k ∈ T, f k,G⟫_ℂ).re := by
  rw [sum_inner]
  exact (Complex.re_sum _ _).symm

lemma dyadicShell_residual_sum {N : ℕ} {r : ℝ} (hr : 0 < r) (K : ℕ)
    (F G : fermionGraph N) :
    (∑ k ∈ Finset.range K, (⟪(oneBodySquareTotal (dyadicShell hr k)).apply F,G⟫_ℂ).re) =
      (⟪(oneBodySquareTotal (dyadicInside hr K)).apply F-(oneBodySquareTotal (dyadicInside hr 0)).apply F,G⟫_ℂ).re := by
  exact (real_inner_sum_left (Finset.range K) (fun k =>
    (oneBodySquareTotal (dyadicShell hr k)).apply F) G).trans
    (congrArg (fun H : fermionGraph N => (⟪H,G⟫_ℂ).re) (dyadicShell_graph_sum hr K F))
end

attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue

lemma oneBodySquareTotal_deriv {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (x : Configuration N) (j : Fin N) (a : Fin 3) :
    lineDeriv ℝ (oneBodySquareTotal p).value x (direction j a) =
      2*p.value (x j)*lineDeriv ℝ p.value (x j) (spaceDirections a) := by
  classical
  unfold oneBodySquareTotal
  change lineDeriv ℝ (fun y => ∑ i, (p.oneBody i).value y^2) x _ = _
  rw [lineDeriv_sumSquares]
  simp only [SmoothMultiplier.oneBody,oneBody_coordinate_derivative,mul_ite,mul_zero]
  simp

lemma oneBodySquareTotal_bound_one {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hp : ∀ x, |p.value x| ≤ 1) (x : Configuration N) :
    |(oneBodySquareTotal p).value x| ≤ N := by
  rw [oneBodySquareTotal_value,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  calc
    _ ≤ ∑ _ : Fin N, (1:ℝ) := Finset.sum_le_sum fun i _ => by
      simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hp (x i)) 2
    _ = _ := by simp

lemma FermionMultiplier.graph_bound_explicit {N : ℕ} (p : FermionMultiplier N)
    {C D : ℝ} (hC : ∀ x, |p.value x| ≤ C)
    (hD : ∀ i a x, |lineDeriv ℝ p.value x (direction i a)| ≤ D) (F : fermionGraph N) :
    ‖p.apply F‖^2 ≤ (3*C^2+6*(N:ℝ)*D^2)*‖F‖^2 := by
  have hm := p.mass_bound hC F
  have hk := p.kinetic_bound hC (fun _ => D) hD F
  have hkin : 0 ≤ ∑ s,∑ i,∑ a,‖graphComponent s (some (i,a)) F‖^2 :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => sq_nonneg _
  have hS : 0 ≤ ∑ i : Fin N,∑ a : Fin 3,D^2 := by positivity
  have hh := graph_multiplier_arithmetic (sq_nonneg _) hkin hS hm hk
    (fermionGraph_norm_sq F) (fermionGraph_norm_sq (p.apply F))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  convert hh using 1
  ring

lemma radialInside_square_graph_bound {N : ℕ} {r u : ℝ} (hr : 0 < r)
    (hu : r ≤ u) (F : fermionGraph N) :
    ‖(oneBodySquareTotal (radialInside 0 (hr.trans_le hu).le (hr.trans_le hu))).apply F‖^2 ≤
      (3*(N:ℝ)^2+6*(N:ℝ)*(2*(Real.pi*smoothTransitionBound)/r)^2)*‖F‖^2 := by
  let p := radialInside 0 (hr.trans_le hu).le (hr.trans_le hu)
  apply FermionMultiplier.graph_bound_explicit _ (oneBodySquareTotal_bound_one p (fun x => radialInside_abs_le 0 (hr.trans_le hu).le (hr.trans_le hu) x))
  intro i a x
  rw [oneBodySquareTotal_deriv,abs_mul,abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hc : 0 ≤ Real.pi*smoothTransitionBound := (mul_pos Real.pi_pos smoothTransitionBound_pos).le
  have hd := (radialInside_deriv_le 0 (hr.trans_le hu).le (hr.trans_le hu) (x i) a).trans
    (div_le_div_of_nonneg_left hc hr hu)
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left (radialInside_abs_le 0 (hr.trans_le hu).le (hr.trans_le hu) (x i)) (by norm_num : (0:ℝ)≤2)) hd
    (abs_nonneg _) (by norm_num : (0:ℝ)≤2*1)
  simpa only [mul_one,mul_div_assoc] using hh

end
open MeasureTheory Filter
open scoped BigOperators
open CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue

def rawExteriorCount {N : ℕ} (r : ℝ) (x : Configuration N) : ℝ :=
  ∑ i, if r ≤ ‖x i‖ then 1 else 0
lemma rawExteriorCount_nonneg {N : ℕ} (r : ℝ) (x : Configuration N) : 0 ≤ rawExteriorCount r x := by
  apply Finset.sum_nonneg; intro i _; split_ifs <;> norm_num
lemma rawExteriorCount_le {N : ℕ} (r : ℝ) (x : Configuration N) : rawExteriorCount r x ≤ N := by
  calc _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum fun i _ => by split_ifs <;> norm_num
       _ = _ := by simp
lemma rawExteriorCount_measurable {N : ℕ} (r : ℝ) : Measurable (rawExteriorCount (N := N) r) := by
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.ite (measurableSet_le measurable_const (continuous_norm.measurable.comp (measurable_pi_apply i))) measurable_const
lemma rawExteriorCount_integrable {N : ℕ} (F : fermionGraph N) (r : ℝ) :
    Integrable (rawExteriorCount r) (graphRawLaw F) :=
  graph_weight_integrable F _ (rawExteriorCount_measurable r) (fun x => by
    rw [Real.norm_of_nonneg (rawExteriorCount_nonneg r x)]; exact rawExteriorCount_le r x)

def smoothExteriorWeight {N : ℕ} {r : ℝ} (hr : 0 < r) : Configuration N → ℝ :=
  (oneBodySquareTotal (radialOutside 0 hr.le hr)).value
lemma smoothExteriorWeight_nonneg {N : ℕ} {r : ℝ} (hr : 0 < r) (x : Configuration N) :
    0 ≤ smoothExteriorWeight hr x := by
  rw [smoothExteriorWeight,oneBodySquareTotal_value]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma smoothExteriorWeight_measurable {N : ℕ} {r : ℝ} (hr : 0 < r) :
    Measurable (smoothExteriorWeight (N := N) hr) :=
  (oneBodySquareTotal (radialOutside 0 hr.le hr)).regular.continuous.measurable
lemma smoothExteriorWeight_bound {N : ℕ} {r : ℝ} (hr : 0 < r) (x : Configuration N) :
    ‖smoothExteriorWeight hr x‖ ≤ N := by
  exact oneBodySquareTotal_bound_one (radialOutside 0 hr.le hr) (radialOutside_abs_le 0 hr.le hr) x
lemma smoothExteriorWeight_integrable {N : ℕ} {r : ℝ} (hr : 0 < r) (F : fermionGraph N) :
    Integrable (smoothExteriorWeight hr) (graphRawLaw F) :=
  graph_weight_integrable F _ (smoothExteriorWeight_measurable hr) (smoothExteriorWeight_bound hr)

lemma exterior_count_le_smooth_annulus {N : ℕ} {r : ℝ} (hr : 0 < r) (x : Configuration N) :
    rawExteriorCount r x ≤ smoothExteriorWeight hr x+rawAnnularCount r (2*r) x := by
  unfold rawExteriorCount rawAnnularCount
  rw [smoothExteriorWeight,oneBodySquareTotal_value]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : r ≤ ‖x i‖
  · rw [ite_eq_left hi]
    by_cases hj : ‖x i‖ ≤ 2*r
    · rw [ite_eq_left ⟨hi,hj⟩]; linarith [sq_nonneg ((radialOutside 0 hr.le hr).value (x i))]
    · have he := (radialCut_outer hr.le hr (y := 0) (x := x i) (by simp only [sub_zero]; linarith)).2
      change (radialOutside 0 hr.le hr).value (x i) = 1 at he
      rw [he,one_pow,ite_eq_right (by tauto),add_zero]
  · rw [ite_eq_right hi,ite_eq_right (by tauto),add_zero]
    exact sq_nonneg _
lemma outer_count_le_smooth {N : ℕ} {r : ℝ} (hr : 0 < r) (x : Configuration N) :
    rawExteriorCount (2*r) x ≤ smoothExteriorWeight hr x := by
  rw [rawExteriorCount,smoothExteriorWeight,oneBodySquareTotal_value]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · have he := (radialCut_outer hr.le hr (y := 0) (x := x i) (by simp only [sub_zero]; linarith)).2
    change (radialOutside 0 hr.le hr).value (x i) = 1 at he
    rw [he,one_pow]
  · exact sq_nonneg _

lemma dyadic_gradient_weight_sum {N : ℕ} {r : ℝ} (hr : 0 < r) (K : ℕ) (x : Configuration N) :
    (∑ k ∈ Finset.range K, rawGradientWeight (dyadicShell hr k) x) ≤
      (24*(Real.pi*smoothTransitionBound)^2/r^2)*rawExteriorCount r x := by
  unfold rawGradientWeight
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i : Fin N, ∑ a : Fin 3,
        (8*(Real.pi*smoothTransitionBound)^2/r^2)*(if r ≤ ‖x i‖ then 1 else 0) := by
      apply Finset.sum_le_sum; intro i _
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum (fun a _ => dyadic_shell_deriv_sum hr K (x i) a)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,rawExteriorCount]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

lemma dyadic_gradient_error_sum {N : ℕ} {r : ℝ} (hr : 0 < r) (K : ℕ) (F : fermionGraph N) :
    (∑ k ∈ Finset.range K, oneBodyGradientError (dyadicShell hr k) F) ≤
      (24*(Real.pi*smoothTransitionBound)^2/r^2)*∫ x, rawExteriorCount r x ∂graphRawLaw F := by
  have hD (k : ℕ) (a : Fin 3) (x : Space) := shellCutoff_deriv_le
    (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) k) hr) x a
  have hi (k : ℕ) := rawGradientWeight_integrable (dyadicShell hr k) F (hD k)
  simp_rw [gradientError_eq_integral (dyadicShell hr _) F (hD _)]
  rw [←integral_finsetSum _ (fun k _ => hi k),←integral_const_mul]
  exact integral_mono (integrable_finsetSum _ (fun k _ => hi k))
    ((rawExteriorCount_integrable F r).const_mul _) (dyadic_gradient_weight_sum hr K)

end CoulombAtom

end

end OAI
