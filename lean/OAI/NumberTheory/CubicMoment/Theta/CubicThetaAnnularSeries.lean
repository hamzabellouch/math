import OAI.NumberTheory.CubicMoment.Theta.CubicThetaForcingProfile
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaForcingCore
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! The fixed open-annulus transport of a continuous radial profile.
At most one actual primitive row contributes at any point. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

instance cubicThetaBottomRow_countable : Countable CubicThetaBottomRow := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  exact Function.Injective.countable (f:=fun r : CubicThetaBottomRow => (r.c,r.d))
    (fun _ _ h => CubicThetaBottomRow.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

lemma CubicThetaBottomRow.pointHeight_continuous (r : CubicThetaBottomRow) :
    Continuous (fun p : CubicThetaPoint => r.height p.val) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (r.height_contDiffAt p.property).continuousAt.comp continuous_subtype_val.continuousAt

def cubicThetaAnnularTerm (f : C(CubicThetaForcingBand,ℂ))
    (r : CubicThetaBottomRow) (p : CubicThetaPoint) : ℂ :=
  if 1<r.height p.val ∧ r.height p.val<2 then
    star r.phase*f (projIcc 1 2 (by norm_num) (r.height p.val)) else 0

def cubicThetaAnnularSeries (f : C(CubicThetaForcingBand,ℂ)) (p : CubicThetaPoint) : ℂ :=
  ∑' r : CubicThetaBottomRow, cubicThetaAnnularTerm f r p

lemma cubicThetaAnnularTerm_high {f : C(CubicThetaForcingBand,ℂ)}
    {r : CubicThetaBottomRow} {p : CubicThetaPoint}
    (h : cubicThetaAnnularTerm f r p≠0) : 1<r.height p.val ∧ r.height p.val<2 := by
  by_contra hn
  exact h (ite_eq_right hn)

lemma cubicThetaAnnularTerm_support (f : C(CubicThetaForcingBand,ℂ)) (p : CubicThetaPoint) :
    (Function.support (fun r => cubicThetaAnnularTerm f r p)).Subsingleton := by
  intro r hr t ht
  exact cubicThetaIncomingRows_unique p.property
    (cubicThetaAnnularTerm_high hr).1 (cubicThetaAnnularTerm_high ht).1

lemma cubicThetaAnnularTerm_measurable (f : C(CubicThetaForcingBand,ℂ))
    (r : CubicThetaBottomRow) : Measurable (cubicThetaAnnularTerm f r) := by
  have hh := r.pointHeight_continuous
  have hm : MeasurableSet {p : CubicThetaPoint | 1<r.height p.val ∧ r.height p.val<2} :=
    ((isOpen_lt continuous_const hh).inter (isOpen_lt hh continuous_const)).measurableSet
  exact (continuous_const.mul (f.continuous.comp (continuous_projIcc.comp hh))).measurable.ite
    hm measurable_const

lemma cubicThetaAnnularSeries_measurable (f : C(CubicThetaForcingBand,ℂ)) :
    Measurable (cubicThetaAnnularSeries f) :=
  Measurable.tsum (fun r => cubicThetaAnnularTerm_measurable f r)

lemma cubicThetaAnnularTerm_norm (f : C(CubicThetaForcingBand,ℂ))
    (r : CubicThetaBottomRow) (p : CubicThetaPoint) :
    ‖cubicThetaAnnularTerm f r p‖≤‖f‖ := by
  unfold cubicThetaAnnularTerm
  split_ifs
  · rw [norm_mul,norm_star,r.phase_norm,one_mul]
    exact f.norm_coe_le_norm _
  · simpa only [norm_zero] using _root_.norm_nonneg f

lemma cubicThetaAnnularSeries_norm (f : C(CubicThetaForcingBand,ℂ)) (p : CubicThetaPoint) :
    ‖cubicThetaAnnularSeries f p‖≤‖f‖ := by
  classical
  by_cases h : ∃ r, cubicThetaAnnularTerm f r p≠0
  · obtain ⟨r,hr⟩ := h
    have he : cubicThetaAnnularSeries f p=cubicThetaAnnularTerm f r p := by
      apply tsum_eq_single
      intro t ht
      by_contra hn
      exact ht ((cubicThetaAnnularTerm_support f p) hn hr)
    rw [he]
    exact cubicThetaAnnularTerm_norm f r p
  · have hz : ∀ r, cubicThetaAnnularTerm f r p=0 := by simpa using h
    simp only [cubicThetaAnnularSeries,hz,tsum_zero,norm_zero]
    exact _root_.norm_nonneg f

lemma cubicThetaAnnularSeries_add (f g : C(CubicThetaForcingBand,ℂ)) (p : CubicThetaPoint) :
    cubicThetaAnnularSeries (f+g) p=cubicThetaAnnularSeries f p+cubicThetaAnnularSeries g p := by
  have he (r : CubicThetaBottomRow) : cubicThetaAnnularTerm (f+g) r p=
      cubicThetaAnnularTerm f r p+cubicThetaAnnularTerm g r p := by
    unfold cubicThetaAnnularTerm
    split_ifs <;> simp only [ContinuousMap.add_apply,mul_add,add_zero]
  simp_rw [cubicThetaAnnularSeries,he]
  exact (summable_of_hasFiniteSupport (cubicThetaAnnularTerm_support f p).finite).tsum_add
    (summable_of_hasFiniteSupport (cubicThetaAnnularTerm_support g p).finite)

lemma cubicThetaAnnularSeries_smul (c : ℂ) (f : C(CubicThetaForcingBand,ℂ)) (p : CubicThetaPoint) :
    cubicThetaAnnularSeries (c • f) p=c*cubicThetaAnnularSeries f p := by
  have he (r : CubicThetaBottomRow) : cubicThetaAnnularTerm (c • f) r p=
      c*cubicThetaAnnularTerm f r p := by
    unfold cubicThetaAnnularTerm
    split_ifs
    · simp only [ContinuousMap.smul_apply,smul_eq_mul]
      ring
    · simp only [mul_zero]
  simp_rw [cubicThetaAnnularSeries,he]
  exact tsum_mul_left

lemma cubicThetaAnnularSeries_forcing (s : ℂ) (p : CubicThetaPoint) :
    cubicThetaAnnularSeries (cubicThetaForcingProfile s) p=cubicThetaForcingSeries p.val s := by
  apply tsum_congr
  intro r
  unfold cubicThetaAnnularTerm cubicThetaForcingTerm
  split_ifs with h
  · rw [projIcc_of_mem (by norm_num) ⟨h.1.le,h.2.le⟩,cubicThetaForcingProfile_apply]
  · have hv : r.height p.val≤1 ∨ 2≤r.height p.val := by
      simpa only [not_and_or,not_lt] using h
    rw [cubicThetaIncomingForcing_zero_closed s hv,mul_zero]

end CubicFirstMoment

end

end OAI
