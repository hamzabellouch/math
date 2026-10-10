import OAI.Probability.SLE.Loewner.UnivalentOddRoot

namespace OAI

/-! The odd-root transform produces an actual exterior univalent map.
Its first Laurent coefficient is the negative derivative of the root
factor; the remainder is represented by a holomorphic disk function. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

def rootExteriorChart (q : ℂ → ℂ) (z : ℂ) : ℂ := z/(q (z⁻¹^2))

lemma root_exterior_laurent_data {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (ball 0 1)) (hq0 : q 0=1)
    (hne : ∀ z∈ball (0:ℂ) 1, q z≠0) :
    ∃ b : ℂ → ℂ, DifferentiableOn ℂ b (ball 0 1) ∧ b 0= -deriv q 0 ∧
      (∀ z : ℂ, z≠0 → rootExteriorChart q z=z+z⁻¹*b (z⁻¹^2)) ∧
      Tendsto (fun z : ℂ => z*(rootExteriorChart q z-z)) (cocompact ℂ) (𝓝 (-deriv q 0)) := by
  let b := dslope (fun z => (q z)⁻¹) 0
  have hqi : DifferentiableOn ℂ (fun z => (q z)⁻¹) (ball 0 1) := hq.inv hne
  have hb : DifferentiableOn ℂ b (ball 0 1) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds (0:ℂ) zero_lt_one)).mpr hqi
  have hb0 : b 0= -deriv q 0 := by
    dsimp only [b]
    rw [dslope_same]
    have hd := ((hq.differentiableAt (ball_mem_nhds (0:ℂ) zero_lt_one)).hasDerivAt).inv
      (by rw [hq0]; exact one_ne_zero)
    change HasDerivAt (fun z => (q z)⁻¹) _ 0 at hd
    simpa [hq0] using hd.deriv
  have he (z : ℂ) (hz : z≠0) : rootExteriorChart q z=z+z⁻¹*b (z⁻¹^2) := by
    have hid := sub_smul_dslope (fun z => (q z)⁻¹) 0 (z⁻¹^2)
    change (z⁻¹^2-0)*b (z⁻¹^2)=(q (z⁻¹^2))⁻¹-(q 0)⁻¹ at hid
    rw [hq0,inv_one,sub_zero] at hid
    dsimp only [rootExteriorChart]
    have hqi : (q (z⁻¹^2))⁻¹=1+z⁻¹^2*b (z⁻¹^2) := by linear_combination -hid
    rw [div_eq_mul_inv,hqi]
    field_simp
  refine ⟨b,hb,hb0,he,?_⟩
  have hinv : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0))
  have hpow : Tendsto (fun z : ℂ => z⁻¹^2) (cocompact ℂ) (𝓝 0) := by
    simpa using hinv.pow 2
  have hlim := (hb.differentiableAt (ball_mem_nhds (0:ℂ) zero_lt_one)).continuousAt.tendsto.comp hpow
  rw [hb0] at hlim
  apply hlim.congr'
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  have hz0 : z≠0 := hz
  rw [he z hz0]
  dsimp only [Function.comp_def]
  field_simp
  ring

lemma root_exterior_univalent {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (ball 0 1))
    (hne : ∀ z∈ball (0:ℂ) 1, q z≠0)
    (hi : InjOn (fun z : ℂ => z*q (z^2)) (ball 0 1)) :
    DifferentiableOn ℂ (rootExteriorChart q) {z : ℂ | 1<‖z‖} ∧
      InjOn (rootExteriorChart q) {z : ℂ | 1<‖z‖} := by
  have hzinv (z : ℂ) (hz : 1<‖z‖) : ‖z⁻¹‖<1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hz
  have hzsq (z : ℂ) (hz : 1<‖z‖) : z⁻¹^2∈ball (0:ℂ) 1 := by
    rw [mem_ball_zero_iff,norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (hzinv z hz) (by norm_num)
  constructor
  · intro z hz
    have hz0 : z≠0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hz))
    have harg := (hasDerivAt_inv hz0).differentiableAt.pow 2
    have hcomp : DifferentiableAt ℂ (fun w : ℂ => q (w⁻¹^2)) z :=
      ((hq.differentiableAt (isOpen_ball.mem_nhds (hzsq z hz))).comp z harg)
    exact ((differentiableAt_id : DifferentiableAt ℂ (fun w : ℂ => w) z).div hcomp
      (hne _ (hzsq z hz))).differentiableWithinAt
  · intro z hz w hw he
    have hz0 : z≠0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hz))
    have hw0 : w≠0 := norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hw))
    have hzi : z⁻¹∈ball (0:ℂ) 1 := mem_ball_zero_iff.mpr (hzinv z hz)
    have hwi : w⁻¹∈ball (0:ℂ) 1 := mem_ball_zero_iff.mpr (hzinv w hw)
    have hrecip : z⁻¹*q (z⁻¹^2)=w⁻¹*q (w⁻¹^2) := by
      have hh := congrArg Inv.inv he
      simpa [rootExteriorChart,div_eq_mul_inv,mul_comm] using hh
    exact inv_injective (hi hzi hwi hrecip)

end SLEExactGauge

end

end OAI
