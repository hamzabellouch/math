import OAI.Analysis.FourierLLogL.Weak.Layers

noncomputable section
open MeasureTheory Filter Set Function
open scoped ENNReal BigOperators Topology

namespace OAI

namespace FourierLLogL
def cloudSet (f : Torus → ℂ) (th : ℝ) :=
    {x : Torus | ENNReal.ofReal th < symmetricMaximal f x}

namespace Weak
open Real
open scoped Classical
variable {f : Torus → ℂ}
lemma cloud_meas (f : Torus → ℂ) (s : ℝ) : MeasurableSet (cloudSet f s) :=
    measurableSet_lt measurable_const (measurable_symmetricMaximal f)

lemma cloudy (f : Torus → ℂ) {s : ℝ} (hs : 0 ≤ s) (x : Torus) :
    x ∈ cloudSet f s ↔ ∃ N, s < ‖symmetricPartialSum f N x‖ := by
  change _ < ⨆ N, ENNReal.ofReal ‖symmetricPartialSum f N x‖ ↔ _
  rw [lt_iSup_iff]
  simp only [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs]

private lemma good_law (h : GoodBound) :
    ∃ (d : ℝ), 0 ≤ d ∧ ∃ (L : ℕ), 4 ≤ L ∧
    (∑' (n : ℕ), ENNReal.ofReal (d/((n+L:ℕ)+1:ℝ)^2)) ≤ ENNReal.ofReal (1/32:ℝ) ∧
    ∀ (f : Torus → ℂ), inside f → ∀ n : ℕ, ∃ G : Set Torus, MeasurableSet G ∧
      circleMeasure Gᶜ ≤ ENNReal.ofReal (d / ((n+L:ℕ)+1:ℝ)^2) ∧
      (∫⁻ x in G, symmetricMaximal (piece f n) x ∂circleMeasure) ≤
        ENNReal.ofReal (allowance f n * (d * (2:ℝ)^(n+L))) := by
  classical
  obtain ⟨d,hd,h⟩ := h
  obtain ⟨N,hN⟩ := eventually_atTop.1 h
  let p (i : ℕ) := d/ ((i+1:ℝ)^2)
  have he : Summable p := by
    have hh : Summable (fun i : ℕ => 1 / ((i+1:ℕ):ℝ)^2) :=
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))
    simpa [p,div_eq_mul_inv] using hh.mul_left d
  let P i := ENNReal.ofReal (p i)
  have hP (i : ℕ) : 0 ≤ p i := by unfold p; positivity
  have hp : (∑' i,P i) ≠ ∞ := by unfold P; rw [← ENNReal.ofReal_tsum_of_nonneg hP he]; exact ENNReal.ofReal_ne_top
  have HR := (ENNReal.tendsto_sum_nat_add P hp).eventually
    (gt_mem_nhds (show (0:ℝ≥0∞) < ENNReal.ofReal (1/32:ℝ) by positivity))
  obtain ⟨L,hH,hL⟩ := (HR.and (eventually_ge_atTop (N+4))).exists
  refine ⟨d, hd,L,by omega,hH.le,?_⟩
  intro f hh n
  let a := allowance f n; let q := piece f n; let k := n+L
  obtain ⟨ha,hq,hc,hG⟩ := taxpayer hh n
  change 0<a at ha
  let g (x : Torus) := ((a⁻¹:ℝ):ℂ)*q x
  have hv (x : Torus) : ‖g x‖ = a⁻¹ * ‖q x‖ := by simp only [g,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.2 ha)]
  have hs : ∫ x, ‖g x‖ ∂circleMeasure ≤ 1 := by
    simp_rw [hv]
    rw [integral_const_mul,← div_eq_inv_mul]; exact (div_le_one ha).mpr hc
  have ht : ∀ᵐ x ∂circleMeasure, ‖g x‖ ≤ exp ((2:ℝ)^k) := ae_of_all _ fun x => by
    rw [hv,←div_eq_inv_mul]
    apply (div_le_iff₀ ha).mpr
    rw [mul_comm]
    apply (hG x).trans; unfold k; apply mul_le_mul_of_nonneg_left _ ha.le; apply exp_monotone; apply pow_le_pow_right₀ (by norm_num); omega
  obtain ⟨G,hM,hz,hT⟩ := hN k (by unfold k; omega) g (hq.const_mul _) hs ht
  refine ⟨G,hM,hz,?_⟩
  have H : piece f n = (fun x => (a:ℂ)*g x) := by
    funext x; unfold g q; rw [←mul_assoc,←Complex.ofReal_mul,mul_inv_cancel₀ ha.ne',
      Complex.ofReal_one,one_mul]
  rw [H]
  simp_rw [symmetricMaximal_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_pos ha,lintegral_const_mul _ (measurable_symmetricMaximal g),
    ENNReal.ofReal_mul ha.le]
  exact mul_le_mul_right hT _

lemma median_budget (hp : GoodBound) :
    ∃ L : ℝ, 0 < L ∧ ∀ (f : Torus → ℂ), inside f → circleMeasure.real (cloudSet f L) ≤ 1/16 := by
  classical
  obtain ⟨d,hd,n,hn,hh,h⟩ := good_law hp
  let k := d*(2:ℝ)^n
  let T := k*tollMax
  have hK : 0 ≤ k := by unfold k; positivity
  have hT : 0 ≤ T := mul_nonneg hK (by
    unfold tollMax
    have H : (0:ℝ) ≤ ∑' i, (2:ℝ)^(i+1)*grit i :=
      tsum_nonneg fun _ => mul_nonneg (by positivity) (grit_pos _).le
    linarith [exp_pos 2])
  let L := 32*(T+1)
  have hL : 0 < L := by unfold L; linarith
  refine ⟨L,hL,?_⟩
  intro f hf
  choose G hG hx hM using h f hf
  let g (j : ℕ) := (G j).indicator (symmetricMaximal (piece f j))
  let E := ⋂ j, G j
  let q (x) := ∑' j,g j x
  let μ := circleMeasure
  have hq j : Measurable (g j) := (measurable_symmetricMaximal _).indicator (hG _)
  have hi : (∫⁻ x,q x ∂circleMeasure) ≤ ENNReal.ofReal T := by
    obtain ⟨hS,hV⟩ := toll_bound hf
    unfold q
    rw [lintegral_tsum (fun j => (hq j).aemeasurable)]
    have HC (j) : (∫⁻ x,g j x ∂circleMeasure) ≤ ENNReal.ofReal (k*((2:ℝ)^j*allowance f j)) := by
      unfold g; rw [lintegral_indicator (hG j)]
      apply le_trans (hM j)
      unfold k; rw [pow_add]; exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
    apply (ENNReal.tsum_le_tsum HC).trans
    have HT (i : ℕ) : 0 ≤ k*((2:ℝ)^i*allowance f i) := by
      have hi := (taxpayer hf i).1; change 0 < allowance f i at hi; positivity
    rw [←ENNReal.ofReal_tsum_of_nonneg HT (hS.mul_left _), hS.tsum_mul_left]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hV hK)
  have HG : μ Eᶜ ≤ ENNReal.ofReal (1/32:ℝ) := by
    unfold E; rw [compl_iInter]
    exact (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum hx).trans hh)
  let X := {x : Torus | ENNReal.ofReal L ≤ q x}
  have HA : μ X ≤ ENNReal.ofReal (1/32:ℝ) := by
    have Hp : 0 < ENNReal.ofReal L := by positivity
    have H := mul_meas_ge_le_lintegral₀ (μ:=circleMeasure) (show AEMeasurable (fun x => ∑' i,g i x) circleMeasure from AEMeasurable.tsum (fun i => (hq i).aemeasurable)) (ENNReal.ofReal L)
    apply (ENNReal.mul_le_mul_iff_right Hp.ne' (show ENNReal.ofReal L ≠ ∞ from ENNReal.ofReal_ne_top)).mp
    apply le_trans (H.trans hi)
    rw [← ENNReal.ofReal_mul hL.le]
    exact ENNReal.ofReal_le_ofReal (by unfold L; linarith)
  have HV : cloudSet f L ⊆ Eᶜ∪X := by
    intro x he
    rcases (cloudy f hL.le x).1 he with ⟨i,hi⟩
    by_cases h : x∈E
    · right
      have hq (j) : g j x=symmetricMaximal (piece f j) x := Set.indicator_of_mem (mem_iInter.mp h j) _
      apply le_trans (ENNReal.ofReal_le_ofReal hi.le) (le_trans (paid_transform hf x i) _)
      change _ ≤ ∑' j,g j x; simp_rw [hq]
      exact le_rfl
    left; exact h
  have He : μ (cloudSet f L) ≤ ENNReal.ofReal (1/16:ℝ) := by
    apply le_trans ((measure_mono HV).trans (measure_union_le _ _)) ((add_le_add HG HA).trans _)
    rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have H := ENNReal.toReal_mono ENNReal.ofReal_ne_top He
  rw [ENNReal.toReal_ofReal (by positivity)] at H; exact H

end Weak
end FourierLLogL

end OAI
