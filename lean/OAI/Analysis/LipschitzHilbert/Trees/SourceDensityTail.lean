import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityGeometry
import OAI.Analysis.LipschitzHilbert.Estimates.TopWeightIntegral

namespace OAI

/-! The density kernel has a quantitative tail outside a dilated slope
box. This turns a weighted density test into the unweighted witness used
by the finite keeper construction. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace LipschitzHilbert
namespace SlopeBox

def densityKernel (T : SlopeBox) (D : ℝ) (z : ℝ×ℝ) : ℝ :=
  (1+T.radius z)^(-D)

theorem densityKernel_nonneg (T : SlopeBox) (D : ℝ) (z : ℝ×ℝ) :
    0 ≤ T.densityKernel D z := Real.rpow_nonneg (by linarith [T.radius_nonnegative z]) _

theorem densityKernel_le_one (T : SlopeBox) {D : ℝ} (hD : 0 ≤ D) (z : ℝ×ℝ) :
    T.densityKernel D z ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith [T.radius_nonnegative z]) (neg_nonpos.mpr hD)

theorem densityKernel_eq_weight (T : SlopeBox) (D : ℝ) (z : ℝ×ℝ) :
    T.densityKernel D z = ((2:ℝ)^D)⁻¹*T.weight 1 D z := by
  have htwo : (2:ℝ)^D ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) D).ne'
  simp only [densityKernel,weight,div_one,←mul_assoc,inv_mul_cancel₀ htwo,one_mul]

theorem densityKernel_integrable (T : SlopeBox) {D : ℝ} (hD : 2 < D) :
    Integrable (T.densityKernel D) (volume.prod volume) := by
  have h := (T.weight_integrable (by norm_num : (0:ℝ)<1) hD).const_mul (((2:ℝ)^D)⁻¹)
  exact h.congr (Eventually.of_forall (fun z => (T.densityKernel_eq_weight D z).symm))

theorem integral_densityKernel (T : SlopeBox) (D : ℝ) :
    (∫ z, T.densityKernel D z ∂volume.prod volume) =
      (∫ z, topProfile D z ∂volume.prod volume)*T.area := by
  simp_rw [T.densityKernel_eq_weight D]
  rw [integral_const_mul,T.integral_weight (by norm_num : (0:ℝ)<1) D]
  have htwo : (2:ℝ)^D ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) D).ne'
  simp only [one_pow,mul_one,SlopeBox.area]
  field_simp [htwo]

end SlopeBox

theorem densitySpatialBox_iff (T : SlopeBox) (K : ℝ) (z : ℝ×ℝ) :
    z ∈ densitySpatialBox T K ↔ |T.horizontal z| ≤ K ∧ |T.transverse z| ≤ K := by
  simp only [densitySpatialBox,mem_ofPred_eq,SlopeBox.horizontal,SlopeBox.transverse,
    abs_div,abs_of_pos T.length_pos,abs_of_pos T.width_pos,
    div_le_iff₀ T.length_pos,div_le_iff₀ T.width_pos]

theorem densitySpatialBox_radius_lt (T : SlopeBox) (K : ℝ) {z : ℝ×ℝ}
    (hz : z ∉ densitySpatialBox T K) : K < T.radius z := by
  by_contra h
  have hr : T.radius z ≤ K := le_of_not_gt h
  apply hz
  rw [densitySpatialBox_iff]
  constructor
  · exact (le_add_of_nonneg_right (abs_nonneg _)).trans hr
  · exact (le_add_of_nonneg_left (abs_nonneg _)).trans hr

theorem densityKernel_tail (T : SlopeBox) {K D : ℝ} (hK : 1 ≤ K) (hD : 3 ≤ D) :
    (∫ z in (densitySpatialBox T K)ᶜ, T.densityKernel D z ∂volume.prod volume) ≤
      K^(3-D)*(∫ z, topProfile 3 z ∂volume.prod volume)*T.area := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hker := T.densityKernel_integrable (by linarith : 2 < D)
  have hthree := T.densityKernel_integrable (by norm_num : (2:ℝ)<3)
  have hpoint (z : ℝ×ℝ) (hz : z ∈ (densitySpatialBox T K)ᶜ) :
      T.densityKernel D z ≤ K^(3-D)*T.densityKernel 3 z := by
    have hr : K ≤ 1+T.radius z := by linarith [densitySpatialBox_radius_lt T K hz]
    have hb : 0 < 1+T.radius z := by linarith [T.radius_nonnegative z]
    have hp := Real.rpow_le_rpow_of_nonpos hKpos hr (by linarith : 3-D ≤ 0)
    calc
      _ = (1+T.radius z)^(3-D)*T.densityKernel 3 z := by
        unfold SlopeBox.densityKernel
        rw [← Real.rpow_add hb]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (T.densityKernel_nonneg 3 z)
  calc
    _ ≤ ∫ z in (densitySpatialBox T K)ᶜ, K^(3-D)*T.densityKernel 3 z ∂volume.prod volume :=
      setIntegral_mono_on hker.integrableOn (hthree.const_mul _).integrableOn
        (densitySpatialBox_measurable T K).compl hpoint
    _ ≤ ∫ z, K^(3-D)*T.densityKernel 3 z ∂volume.prod volume :=
      setIntegral_le_integral (hthree.const_mul _) (Eventually.of_forall
        (fun z => mul_nonneg (Real.rpow_nonneg hKpos.le _) (T.densityKernel_nonneg 3 z)))
    _ = _ := by rw [integral_const_mul,T.integral_densityKernel 3]; ring

theorem density_witness_mass (T : SlopeBox) {K D eta : ℝ}
    (hK : 1 ≤ K) (hD : 3 ≤ D) (_heta : 0 ≤ eta)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (omega : Set ℝ)
    (hE : MeasurableSet E) (hEfinite : (volume.prod volume) E ≠ ∞)
    (hu : Measurable u) (homega : MeasurableSet omega)
    (htail : K^(3-D)*(∫ z, topProfile 3 z ∂volume.prod volume) ≤ eta/2)
    (hdensity : eta*T.area ≤ ∫ z in E ∩ u ⁻¹' omega,
      T.densityKernel D z ∂volume.prod volume) :
    (eta/2)*T.area ≤ (volume.prod volume).real (densityTest E u T omega K) := by
  let A := E ∩ u ⁻¹' omega
  have hA : MeasurableSet A := hE.inter (hu homega)
  have hker := T.densityKernel_integrable (by linarith : 2 < D)
  have hbox := densitySpatialBox_measurable T K
  have hsplit := integral_inter_add_sdiff hbox (hker.integrableOn :
    IntegrableOn (T.densityKernel D) A (volume.prod volume))
  have htest : A ∩ densitySpatialBox T K = densityTest E u T omega K := by
    ext z
    exact and_right_comm
  have htestFinite : (volume.prod volume) (A ∩ densitySpatialBox T K) ≠ ∞ :=
    measure_ne_top_of_subset (fun _ hz => hz.1.1) hEfinite
  have hinside : (∫ z in A ∩ densitySpatialBox T K, T.densityKernel D z ∂volume.prod volume) ≤
      (volume.prod volume).real (A ∩ densitySpatialBox T K) := by
    have h := setIntegral_mono_on hker.integrableOn
      (integrableOn_const htestFinite : IntegrableOn (fun _ : ℝ×ℝ => (1:ℝ))
        (A ∩ densitySpatialBox T K) (volume.prod volume)) (hA.inter hbox)
      (fun z _ => T.densityKernel_le_one (by linarith : 0 ≤ D) z)
    simpa only [setIntegral_const,smul_eq_mul,mul_one] using h
  have houtside : (∫ z in A\densitySpatialBox T K, T.densityKernel D z ∂volume.prod volume) ≤
      (eta/2)*T.area := by
    have hmono := setIntegral_mono_set
      (hker.integrableOn : IntegrableOn (T.densityKernel D) (densitySpatialBox T K)ᶜ (volume.prod volume))
      (Eventually.of_forall (fun z => T.densityKernel_nonneg D z))
      (Eventually.of_forall (fun z (hz : z ∈ A\densitySpatialBox T K) => hz.2))
    exact hmono.trans ((densityKernel_tail T hK hD).trans
      (mul_le_mul_of_nonneg_right htail (by exact mul_nonneg T.length_pos.le T.width_pos.le)))
  rw [htest] at hinside
  rw [htest] at hsplit
  linarith

/-- A fixed decay order gives the manuscript's small polynomial spatial
enlargement at every polynomial density threshold. -/
theorem density_tail_at_power_scale (a : ℝ) (ha : 0 ≤ a) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      (L^(a/100+1))^(3-(203:ℝ))*(∫ z, topProfile 3 z ∂volume.prod volume) ≤ L^(-a)/2 := by
  let C := ∫ z, topProfile 3 z ∂volume.prod volume
  have hC : 0 ≤ C := integral_nonneg (topProfile_nonnegative 3)
  refine ⟨max 1 (2*C),le_max_left _ _,?_⟩
  intro L hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have hCL : 2*C ≤ L := (le_max_right _ _).trans hL
  have hratio : C/L ≤ (1/2:ℝ) := (div_le_iff₀ hLpos).mpr (by linarith)
  have hpower : (L^(a/100+1))^(3-(203:ℝ)) = L^(-2*a-200) := by
    rw [← Real.rpow_mul hLpos.le]
    congr 1
    ring
  change (L^(a/100+1))^(3-(203:ℝ))*C ≤ L^(-a)/2
  rw [hpower]
  calc
    _ ≤ L^(-a-1)*C := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) hC
    _ = L^(-a)*(C/L) := by
      rw [sub_eq_add_neg,Real.rpow_add hLpos,Real.rpow_neg_one]
      ring
    _ ≤ L^(-a)*(1/2) := mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hLpos.le _)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
