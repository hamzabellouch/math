import OAI.Probability.SLE.Loewner.ReflectedExteriorAnalytic
import OAI.Probability.SLE.Loewner.UnivalentLocalBound
import OAI.Probability.SLE.Loewner.SlitCapacityRemainder

namespace OAI

/-! Coarse uniform control of the reflected chart near a small slit.
Only a fixed numerical constant is needed for driver continuity. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

lemma reflected_disk_ball_subset {p : C(unitInterval,ℂ)} {L : ℝ} (hL : 0<L)
    (hp : ∀ t : unitInterval, ‖p t‖<L) :
    ball (0:ℂ) (1/L) ⊆ invertedExterior (reflectedArcSet p) := by
  intro w hw
  by_cases hw0 : w=0
  · exact Or.inl hw0
  apply Or.inr
  intro hmem
  have hn := norm_pos_iff.mpr hw0
  have hw' : ‖w‖<1/L := mem_ball_zero_iff.mp hw
  have hinv : L<‖w⁻¹‖ := by
    rw [norm_inv,inv_eq_one_div]
    apply (lt_div_iff₀ hn).mpr
    have hh := (lt_div_iff₀ hL).mp hw'
    nlinarith
  exact (not_lt_of_ge hinv.le) (reflectedArcSet_norm_lt hp hmem)

lemma ReflectedCapacityChart.slope_le_radius {p : C(unitInterval,ℂ)}
    (Q : ReflectedCapacityChart p) {L : ℝ} (hL : 0<L)
    (hp : ∀ t : unitInterval, ‖p t‖<L) : Q.slope≤L := by
  have hsub := reflected_disk_ball_subset hL hp
  have hm : MapsTo Q.diskMap (ball 0 (1/L)) (closedBall (Q.diskMap 0) 1) := by
    intro w hw
    rw [Q.disk_zero]
    exact ball_subset_closedBall (Q.disk_bijOn.mapsTo (hsub hw))
  have hh := Complex.norm_deriv_le_div_of_mapsTo_ball (Q.disk_differentiable.mono hsub)
    hm (one_div_pos.mpr hL)
  simpa only [Q.disk_derivative,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Q.slope_pos,one_div_one_div] using hh

lemma ReflectedCapacityChart.diskMap_lower {p : C(unitInterval,ℂ)}
    (Q : ReflectedCapacityChart p) (h0 : p 0=0) {L : ℝ} (hL : 0<L)
    (hp : ∀ t : unitInterval, ‖p t‖<L) {z : ℂ}
    (hz : z∉reflectedArcSet p) (hzL : ‖z‖≤L) :
    (1/L)*Q.slope/(128*Real.pi)≤‖Q.diskMap z⁻¹‖ := by
  have hsub := reflected_disk_ball_subset hL hp
  have hd := Q.disk_differentiable.mono hsub
  have hi := Q.disk_bijOn.injOn.mono hsub
  have hc := univalent_coarse_ball_subset_image (one_div_pos.mpr hL) hd hi
  rw [Q.disk_zero,Q.disk_derivative,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Q.slope_pos] at hc
  by_contra hn
  have hsmall : Q.diskMap z⁻¹∈ball (0:ℂ) ((1/L)*Q.slope/(128*Real.pi)) :=
    mem_ball_zero_iff.mpr (lt_of_not_ge hn)
  obtain ⟨w,hw,he⟩ := hc hsmall
  have hew : w=z⁻¹ := Q.disk_bijOn.injOn (hsub hw) (Q.inverse_mem hz) he
  rw [hew] at hw
  have hz0 : z≠0 := by
    intro hez
    subst z
    exact hz (Or.inl ⟨0,h0⟩)
  have hzn := norm_pos_iff.mpr hz0
  have hh : ‖z‖⁻¹<1/L := by simpa only [mem_ball_zero_iff,norm_inv] using hw
  have hmul := (lt_div_iff₀ hL).mp hh
  have hmul' := mul_lt_mul_of_pos_right hmul hzn
  have hid : ‖z‖⁻¹*L*‖z‖=L := by field_simp
  rw [hid,one_mul] at hmul'
  exact (not_lt_of_ge hzL) hmul'

lemma ReflectedCapacityChart.exterior_scaled_bound {p : C(unitInterval,ℂ)}
    (Q : ReflectedCapacityChart p) (h0 : p 0=0) {L : ℝ} (hL : 0<L)
    (hp : ∀ t : unitInterval, ‖p t‖<L) {z : ℂ}
    (hz : z∉reflectedArcSet p) (hzL : ‖z‖≤L) :
    Q.slope*‖slitExteriorMap Q.diskMap z‖≤(128*Real.pi)*L := by
  have hb := Q.diskMap_lower h0 hL hp hz hzL
  have hC : 0<128*Real.pi := by positivity
  have hz0 : z≠0 := fun he => hz (Or.inl ⟨0,h0.trans he.symm⟩)
  have hf0 : Q.diskMap z⁻¹≠0 := by
    intro he
    exact inv_ne_zero hz0 (Q.disk_bijOn.injOn (Q.inverse_mem hz)
      (zero_mem_invertedExterior _) (he.trans Q.disk_zero.symm))
  have hfn : 0<‖Q.diskMap z⁻¹‖ := norm_pos_iff.mpr hf0
  change Q.slope*‖(Q.diskMap z⁻¹)⁻¹‖≤(128*Real.pi)*L
  rw [norm_inv,←div_eq_mul_inv]
  apply (div_le_iff₀ hfn).mpr
  have hmul := mul_le_mul_of_nonneg_right ((div_le_iff₀ hC).mp hb) hL.le
  have he : (1/L)*Q.slope*L=Q.slope := by field_simp
  rw [he] at hmul
  nlinarith

lemma ReflectedCapacityChart.joukowski_scaled_bound {p : C(unitInterval,ℂ)}
    (Q : ReflectedCapacityChart p) (h0 : p 0=0) {L : ℝ} (hL : 0<L)
    (hp : ∀ t : unitInterval, ‖p t‖<L) {z : ℂ}
    (hz : z∉reflectedArcSet p) (hzL : ‖z‖≤L) :
    ‖(Q.slope:ℂ)*exteriorJoukowski (slitExteriorMap Q.diskMap z)‖≤
      (128*Real.pi+1)*L := by
  have hW := Q.exterior_norm h0 hz
  have hi : ‖(slitExteriorMap Q.diskMap z)⁻¹‖≤1 := by
    rw [norm_inv,inv_eq_one_div]
    exact (div_le_one (lt_trans zero_lt_one hW)).mpr hW.le
  have ht := norm_add_le (slitExteriorMap Q.diskMap z) (slitExteriorMap Q.diskMap z)⁻¹
  change ‖(Q.slope:ℂ)*(slitExteriorMap Q.diskMap z+(slitExteriorMap Q.diskMap z)⁻¹)‖≤_
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Q.slope_pos]
  have hb := Q.exterior_scaled_bound h0 hL hp hz hzL
  have ha := Q.slope_le_radius hL hp
  nlinarith [mul_le_mul_of_nonneg_left ht Q.slope_pos.le,
    mul_le_mul_of_nonneg_left hi Q.slope_pos.le]

end SLEExactGauge

end

end OAI
