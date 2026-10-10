import OAI.Geometry.Perimeter.Regularity.SlabScaling
import OAI.Geometry.Perimeter.Regularity.TangentPlanes

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem nearby_full_support_planes {q M δ : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hM : 0≤M) (hstep : SlabContractionProperty n q M δ)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖=1) {a : ℝ} (ha : 0 < a) (haδ : 4*a < δ)
    (hs : FullSlab E v 8 a) {p : Euc n}
    (hp : p∈perimeterSupport E ∩ Metric.ball 0 1) :
    ∃ w : Euc n, ‖w‖=1 ∧ ‖w-v‖≤8*M*a ∧
      ∀ j x, x∈perimeterSupport E → ‖x-p‖≤2*q^j →
        |inner ℝ w (x-p)|≤4*a*(2*M+1/(4*q))*(1/2)^j*‖x-p‖ := by
  have hminF := locally_minimizing_blownUpSet hmin p (by norm_num : (0:ℝ)<1/2)
  have hzeroF : (0:Euc n)∈perimeterSupport (blownUpSet E p (1/2)) := by
    rw [perimeterSupport_blownUpSet hmin.1 p (by norm_num),smul_zero,add_zero]
    exact hp.1
  obtain ⟨w,hw,hwd,htan⟩ := exists_full_support_tangent_plane hq hq1 hM hstep
    hminF hzeroF hv (by positivity : 0 < 4*a) haδ (hs.recenter_half hmin.1 ha.le hp)
  refine ⟨w,hw,by nlinarith [hwd],fun j x hx hxp ↦ ?_⟩
  let y := (2:ℝ)•(x-p)
  have hxy : p+(1/2:ℝ)•y=x := by dsimp [y]; module
  have hyS : y∈perimeterSupport (blownUpSet E p (1/2)) := by
    rw [perimeterSupport_blownUpSet hmin.1 p (by norm_num),hxy]
    exact hx
  have hyn : ‖y‖=2*‖x-p‖ := by rw [norm_smul,Real.norm_of_nonneg (by norm_num)]
  have hyB : ‖y‖≤4*q^j := by rw [hyn]; linarith
  have hh := htan j y hyS hyB
  change |inner ℝ w ((2:ℝ)•(x-p))|≤_ at hh
  rw [real_inner_smul_right,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),hyn] at hh
  nlinarith

theorem nearby_chord_bound {q M δ : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hM : 0≤M) (hstep : SlabContractionProperty n q M δ)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖=1) {a : ℝ} (ha : 0 < a) (haδ : 4*a < δ)
    (hs : FullSlab E v 8 a) {p x : Euc n}
    (hp : p∈perimeterSupport E ∩ Metric.ball 0 1)
    (hx : x∈perimeterSupport E ∩ Metric.ball 0 1) :
    |inner ℝ v (x-p)|≤a*(16*M+1/q)*‖x-p‖ := by
  obtain ⟨w,hw,hwd,htan⟩ := nearby_full_support_planes hq hq1 hM hstep hmin hv ha haδ hs hp
  have hxp : ‖x-p‖≤2*q^0 := by
    have hh := norm_sub_le x p
    have hnx : ‖x‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hx.2
    have hnp : ‖p‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hp.2
    simp only [pow_zero,mul_one]
    linarith
  have ht := htan 0 x hx.1 hxp
  simp only [pow_zero,mul_one] at ht
  have hi : inner ℝ v (x-p)=inner ℝ (v-w) (x-p)+inner ℝ w (x-p) := by rw [inner_sub_left]; ring
  calc
    |inner ℝ v (x-p)| ≤ ‖v-w‖*‖x-p‖+|inner ℝ w (x-p)| := by
      rw [hi]
      exact (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm _ _) le_rfl)
    _ ≤ (8*M*a)*‖x-p‖+4*a*(2*M+1/(4*q))*‖x-p‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (by simpa only [norm_sub_rev] using hwd)
        (norm_nonneg _)) ht
    _ = a*(16*M+1/q)*‖x-p‖ := by field_simp; ring

theorem projection_injective_on_support {E : Set (Euc n)} {v : Euc n}
    (hchord : ∀ p∈perimeterSupport E ∩ Metric.ball 0 1,
      ∀ x∈perimeterSupport E ∩ Metric.ball 0 1,
        |inner ℝ v (x-p)|≤(1/2)*‖x-p‖) (hv : ‖v‖=1) :
    Set.InjOn (fun x ↦ x-inner ℝ v x•v) (perimeterSupport E ∩ Metric.ball 0 1) := by
  intro x hx p hp he
  have hh := hchord p hp x hx
  have hex : x-p=inner ℝ v (x-p)•v := by
    rw [inner_sub_right,sub_smul]
    change x-inner ℝ v x•v=p-inner ℝ v p•v at he
    calc
      x-p = (x-inner ℝ v x•v)-(p-inner ℝ v p•v) +
        (inner ℝ v x•v-inner ℝ v p•v) := by abel
      _ = inner ℝ v x•v-inner ℝ v p•v := by rw [he,sub_self,zero_add]
  have hn : ‖x-p‖=|inner ℝ v (x-p)| := by
    calc
      ‖x-p‖ = ‖inner ℝ v (x-p)•v‖ := congrArg norm hex
      _ = _ := by rw [norm_smul,hv,mul_one,Real.norm_eq_abs]
  rw [← hn] at hh
  have hz : ‖x-p‖=0 := by linarith [norm_nonneg (x-p)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end RPISingularHarnack

end

end OAI
