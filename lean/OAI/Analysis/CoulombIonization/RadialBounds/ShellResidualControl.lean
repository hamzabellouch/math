import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.ShellTelescoping
import OAI.Analysis.CoulombIonization.RadialBounds.ShellAbsorptionNumerics

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue sectorExcessOperator

lemma norm_sub_square_bound {V : Type*} [SeminormedAddCommGroup V] (v w : V) :
    ‖v-w‖^2 ≤ 2*‖v‖^2+2*‖w‖^2 := by
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le v w) 2
  nlinarith [sq_nonneg (‖v‖-‖w‖)]

def shellGraphConstant (N : ℕ) (r : ℝ) : ℝ :=
  4*(3*(N:ℝ)^2+6*(N:ℝ)*(2*(Real.pi*smoothTransitionBound)/r)^2)
lemma shellGraphConstant_nonneg (N : ℕ) (r : ℝ) : 0 ≤ shellGraphConstant N r := by
  unfold shellGraphConstant; positivity

lemma dyadicShell_sum_graph_bound {N : ℕ} {r : ℝ} (hr : 0 < r) (K : ℕ) (F : fermionGraph N) :
    ‖(∑ k ∈ Finset.range K, (oneBodySquareTotal (dyadicShell hr k)).apply F)‖^2 ≤
      shellGraphConstant N r*‖F‖^2 := by
  have hu : r ≤ (2:ℝ)^K*r := le_mul_of_one_le_left hr.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have hK := radialInside_square_graph_bound hr hu F
  have h0 := radialInside_square_graph_bound hr (le_rfl : r ≤ r) F
  have hsub := norm_sub_square_bound ((oneBodySquareTotal (dyadicInside hr K)).apply F)
    ((oneBodySquareTotal (dyadicInside hr 0)).apply F)
  change ‖(oneBodySquareTotal (dyadicInside hr K)).apply F‖^2 ≤ _ at hK
  have hz : dyadicInside hr 0 = radialInside 0 hr.le hr := by simp only [dyadicInside,pow_zero,one_mul]
  rw [hz] at hsub
  have hbound : ‖(oneBodySquareTotal (dyadicInside hr K)).apply F-
      (oneBodySquareTotal (dyadicInside hr 0)).apply F‖^2 ≤ shellGraphConstant N r*‖F‖^2 := by
    rw [hz]
    dsimp only [shellGraphConstant]
    linarith only [hK,h0,hsub]
  exact (congrArg (fun H : fermionGraph N => ‖H‖^2) (dyadicShell_graph_sum hr K F)).le.trans hbound

lemma dyadicShell_residual_square {Z r η B : ℝ} {N : ℕ} (hZ : 0 ≤ Z) (hr : 0 < r)
    (hη : 0 ≤ η) (F : fermionGraph N) (hF : (⟪F,sectorExcessOperator Z N F⟫_ℂ).re ≤ η)
    (hB : ‖F‖^2 ≤ B) (K : ℕ) :
    (∑ k ∈ Finset.range K, (⟪(oneBodySquareTotal (dyadicShell hr k)).apply F,
      sectorExcessOperator Z N F⟫_ℂ).re)^2 ≤ η*(‖sectorExcessOperator Z N‖*shellGraphConstant N r*B) := by
  have hG := (dyadicShell_sum_graph_bound hr K F).trans
    (mul_le_mul_of_nonneg_left hB (shellGraphConstant_nonneg N r))
  have hh := positive_form_residual_bound (sectorExcessOperator Z N)
    (sectorExcessOperator_positive hZ N) F (∑ k ∈ Finset.range K,
      (oneBodySquareTotal (dyadicShell hr k)).apply F) hη hF hG
  exact (congrArg (fun t : ℝ => t^2) (real_inner_sum_left (Finset.range K)
    (fun k => (oneBodySquareTotal (dyadicShell hr k)).apply F) (sectorExcessOperator Z N F))).le.trans hh

lemma dyadicShell_residual_le {Z r η B ε : ℝ} {N : ℕ} (hZ : 0 ≤ Z) (hr : 0 < r)
    (hη : 0 ≤ η) (hε : 0 ≤ ε) (F : fermionGraph N) (hF : (⟪F,sectorExcessOperator Z N F⟫_ℂ).re ≤ η)
    (hB : ‖F‖^2 ≤ B) (ha : η*(‖sectorExcessOperator Z N‖*shellGraphConstant N r*B) ≤ ε^2) (K : ℕ) :
    (∑ k ∈ Finset.range K, (⟪(oneBodySquareTotal (dyadicShell hr k)).apply F,
      sectorExcessOperator Z N F⟫_ℂ).re) ≤ ε := by
  have hh := (dyadicShell_residual_square hZ hr hη F hF hB K).trans ha
  nlinarith only [hh,sq_nonneg ((∑ k ∈ Finset.range K,
    (⟪(oneBodySquareTotal (dyadicShell hr k)).apply F,sectorExcessOperator Z N F⟫_ℂ).re)+ε),hε]

end
section
open MeasureTheory Filter
open scoped BigOperators
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue

lemma multiplier_weight_integrable {N : ℕ} (F : fermionGraph N) (p : FermionMultiplier N) :
    Integrable p.value (graphRawLaw F) := by
  obtain ⟨A,hA⟩ := p.bound
  exact graph_weight_integrable F _ p.regular.continuous.measurable hA
lemma multiplier_weightedMass_eq_integral {N : ℕ} (F : fermionGraph N) (p : FermionMultiplier N) :
    weightedMass F p.value = ∫ x, p.value x ∂graphRawLaw F := by
  obtain ⟨A,hA⟩ := p.bound
  exact weightedMass_eq_integral F _ p.regular.continuous.measurable hA
lemma weightedMass_finite_sum {α : Type*} {N : ℕ} (T : Finset α)
    (p : α → FermionMultiplier N) (F : fermionGraph N) :
    (∑ k ∈ T, weightedMass F (p k).value) = ∫ x, (∑ k ∈ T, (p k).value x) ∂graphRawLaw F := by
  simp_rw [multiplier_weightedMass_eq_integral]
  exact (integral_finsetSum _ (fun k _ => multiplier_weight_integrable F (p k))).symm

lemma smoothExteriorWeight_count_sub {N : ℕ} {r : ℝ} (hr : 0 < r) (x : Configuration N) :
    smoothExteriorWeight hr x = (N:ℝ)-(oneBodySquareTotal (dyadicInside hr 0)).value x := by
  have hz : dyadicInside hr 0 = radialInside 0 hr.le hr := by simp only [dyadicInside,pow_zero,one_mul]
  rw [smoothExteriorWeight,oneBodySquareTotal_value,hz,oneBodySquareTotal_value]
  have hh (i : Fin N) : (radialOutside 0 hr.le hr).value (x i)^2 =
      1-(radialInside 0 hr.le hr).value (x i)^2 := by
    have hp := radialCut_partition 0 hr.le hr (x i)
    simp only [Fin.sum_univ_two,radialCut,Matrix.cons_val_zero,Matrix.cons_val_one] at hp
    linarith only [hp]
  simp_rw [hh]
  rw [Finset.sum_sub_distrib]; simp

lemma dyadicShell_total_sum_nonneg {N : ℕ} {r : ℝ} (hr : 0 < r) (K : ℕ) (x : Configuration N) :
    0 ≤ ∑ k ∈ Finset.range K, (oneBodySquareTotal (dyadicShell hr k)).value x := by
  simp only [oneBodySquareTotal_value]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma dyadicShell_total_sum_bound {N : ℕ} {r : ℝ} (hr : 0 < r) (K : ℕ) (x : Configuration N) :
    ‖∑ k ∈ Finset.range K, (oneBodySquareTotal (dyadicShell hr k)).value x‖ ≤ N := by
  rw [Real.norm_of_nonneg (dyadicShell_total_sum_nonneg hr K x),dyadicShell_total_sum]
  have hn : 0 ≤ (oneBodySquareTotal (dyadicInside hr 0)).value x := by
    rw [oneBodySquareTotal_value]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hK := (le_abs_self ((oneBodySquareTotal (dyadicInside hr K)).value x)).trans
    (oneBodySquareTotal_bound_one (dyadicInside hr K) (radialInside_abs_le 0 _ _) x)
  linarith only [hn,hK]
lemma dyadicInside_tendsto {r : ℝ} (hr : 0 < r) (x : Space) :
    Tendsto (fun K => (dyadicInside hr K).value x) atTop (nhds 1) := by
  have ht : Tendsto (fun K : ℕ => (2:ℝ)^K*r) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).atTop_mul_const hr
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_atTop.1 ht) ‖x‖] with K hK
  exact (radialCut_inner (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) K) hr).le
    (mul_pos (pow_pos (by norm_num : (0:ℝ)<2) K) hr) (y := 0) (x := x) (by simpa using hK)).1.symm
lemma dyadicShell_total_sum_tendsto {N : ℕ} {r : ℝ} (hr : 0 < r) (x : Configuration N) :
    Tendsto (fun K => ∑ k ∈ Finset.range K, (oneBodySquareTotal (dyadicShell hr k)).value x)
      atTop (nhds (smoothExteriorWeight hr x)) := by
  simp_rw [dyadicShell_total_sum,oneBodySquareTotal_value]
  rw [smoothExteriorWeight_count_sub,oneBodySquareTotal_value]
  have hh := tendsto_finsetSum (s := (Finset.univ : Finset (Fin N)))
    (fun i _ => (dyadicInside_tendsto hr (x i)).pow 2)
  simp only [one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hh
  exact hh.sub_const _

lemma dyadicShell_mass_sum_tendsto {N : ℕ} {r : ℝ} (hr : 0 < r) (F : fermionGraph N) :
    Tendsto (fun K => ∑ k ∈ Finset.range K, weightedMass F (oneBodySquareTotal (dyadicShell hr k)).value)
      atTop (nhds (∫ x, smoothExteriorWeight hr x ∂graphRawLaw F)) := by
  simp_rw [weightedMass_finite_sum]
  apply tendsto_integral_of_dominated_convergence (fun _ => (N:ℝ))
    (fun K => (Finset.measurable_sum _ (fun k _ => (oneBodySquareTotal (dyadicShell hr k)).regular.continuous.measurable)).aestronglyMeasurable)
    (integrable_const _) (fun K => ae_of_all _ (dyadicShell_total_sum_bound hr K))
    (ae_of_all _ (dyadicShell_total_sum_tendsto hr))

end
open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
open CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply oneBodySquareTotal fermionGraphValue sectorExcessOperator
  weightedMass oneBodyGradientError graphRawLaw

lemma sum_linear_inequality {α : Type*} (T : Finset α) (a b c : α → ℝ) (t : ℝ)
    (h : ∀ k ∈ T, t*a k ≤ b k+2*c k) :
    t*(∑ k ∈ T, a k) ≤ (∑ k ∈ T, b k)+2*(∑ k ∈ T, c k) := by
  calc _ = ∑ k ∈ T, t*a k := Finset.mul_sum ..
       _ ≤ ∑ k ∈ T, (b k+2*c k) := Finset.sum_le_sum h
       _ = _ := by rw [Finset.sum_add_distrib,Finset.mul_sum]

theorem actual_smooth_exterior_number {Z s r η B ε : ℝ} {N : ℕ}
    (hZ : 0 ≤ Z) (hs : 0 < s) (hs1 : s ≤ 1) (hr : 0 < r)
    (hR : actualShellRadius*s ≤ r)
    (hN : PriceMinimizes (energy Z) (1/s^4) (N+1))
    (hη : 0 ≤ η) (hε : 0 ≤ ε) (F : fermionGraph (N+1))
    (hF : (⟪F,sectorExcessOperator Z (N+1) F⟫_ℂ).re ≤ η)
    (hB : ‖F‖^2 ≤ B)
    (ha : η*(‖sectorExcessOperator Z (N+1)‖*shellGraphConstant (N+1) r*B) ≤ ε^2) :
    (1/s^4)*(∫ x, smoothExteriorWeight hr x ∂graphRawLaw F) ≤
      (24*(Real.pi*smoothTransitionBound)^2/r^2)*
        (∫ x, rawExteriorCount r x ∂graphRawLaw F)+2*ε := by
  have hh (K : ℕ) : (1/s^4)*(∑ k ∈ Finset.range K,
      weightedMass F (oneBodySquareTotal (dyadicShell hr k)).value) ≤
      (24*(Real.pi*smoothTransitionBound)^2/r^2)*
        (∫ x, rawExteriorCount r x ∂graphRawLaw F)+2*ε := by
    have hsum := sum_linear_inequality (Finset.range K)
      (fun k => weightedMass F (oneBodySquareTotal (dyadicShell hr k)).value)
      (fun k => oneBodyGradientError (dyadicShell hr k) F)
      (fun k => (⟪(oneBodySquareTotal (dyadicShell hr k)).apply F,sectorExcessOperator Z (N+1) F⟫_ℂ).re)
      (1/s^4) (fun k _ =>
      actual_shell_number hZ hs hs1 (hR.trans (le_mul_of_one_le_left hr.le
        (one_le_pow₀ (by norm_num : (1:ℝ)≤2)))) hN F (dyadicShell hr k)
        (shellCutoff_compact (mul_pos (pow_pos (by norm_num) k) hr))
        (fun y hy => by
          have h := shellCutoff_support (mul_pos (pow_pos (by norm_num) k) hr) y hy
          exact ⟨by linarith [mul_pos (pow_pos (by norm_num : (0:ℝ)<2) k) hr],h.2⟩))
    exact hsum.trans (add_le_add (dyadic_gradient_error_sum hr K F)
      (mul_le_mul_of_nonneg_left (dyadicShell_residual_le hZ hr hη hε F hF hB ha K) (by norm_num)))
  exact le_of_tendsto ((dyadicShell_mass_sum_tendsto hr F).const_mul (1/s^4))
    (Eventually.of_forall hh)

lemma rawAnnularCount_graph_integrable {N : ℕ} (F : fermionGraph N) (a b : ℝ) :
    Integrable (rawAnnularCount a b) (graphRawLaw F) :=
  graph_weight_integrable F _ (rawAnnularCount_measurable a b) (fun x => by
    rw [Real.norm_of_nonneg (rawAnnularCount_nonneg a b x)]; exact rawAnnularCount_le a b x)

theorem actual_exterior_number_absorbed {Z s r η B ε : ℝ} {N : ℕ}
    (hZ : 0 ≤ Z) (hs : 0 < s) (hs1 : s ≤ 1) (hr : 0 < r)
    (hR : actualShellRadius*s ≤ r)
    (hN : PriceMinimizes (energy Z) (1/s^4) (N+1))
    (hη : 0 ≤ η) (hε : 0 ≤ ε) (F : fermionGraph (N+1))
    (hF : (⟪F,sectorExcessOperator Z (N+1) F⟫_ℂ).re ≤ η)
    (hB : ‖F‖^2 ≤ B)
    (ha : η*(‖sectorExcessOperator Z (N+1)‖*shellGraphConstant (N+1) r*B) ≤ ε^2)
    (hab : 2*(24*(Real.pi*smoothTransitionBound)^2/r^2) ≤ 1/s^4) :
    (1/s^4)*(∫ x, rawExteriorCount (2*r) x ∂graphRawLaw F) ≤
      2*(24*(Real.pi*smoothTransitionBound)^2/r^2)*
        (∫ x, rawAnnularCount r (2*r) x ∂graphRawLaw F)+4*ε := by
  have hh := actual_smooth_exterior_number hZ hs hs1 hr hR hN hη hε F hF hB ha
  have hk := integral_mono (rawExteriorCount_integrable F r)
    ((smoothExteriorWeight_integrable hr F).add (rawAnnularCount_graph_integrable F r (2*r)))
    (exterior_count_le_smooth_annulus hr)
  simp only [Pi.add_apply] at hk
  rw [integral_add (smoothExteriorWeight_integrable hr F)
    (rawAnnularCount_graph_integrable F r (2*r))] at hk
  have hout := integral_mono (rawExteriorCount_integrable F (2*r))
    (smoothExteriorWeight_integrable hr F) (outer_count_le_smooth hr)
  have hn : 0 ≤ ∫ x, smoothExteriorWeight hr x ∂graphRawLaw F :=
    integral_nonneg (smoothExteriorWeight_nonneg hr)
  have hc : 0 ≤ 24*(Real.pi*smoothTransitionBound)^2/r^2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hk hc
  have hmul' := mul_le_mul_of_nonneg_right hab hn
  have hmul'' := mul_le_mul_of_nonneg_left hout (by positivity : 0 ≤ 1/s^4)
  nlinarith only [hh,hmul,hmul',hmul'']

end CoulombAtom

end

end OAI
