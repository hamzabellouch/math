import OAI.NumberTheory.CubicMoment.Estimates.HuxleyGaussianPacking

namespace OAI

/-! Periodized Gaussian rows over the actual finite set of residue fractions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def huxleyPeriodizedGaussian (t : ℝ) (x : ℂ) : ℝ :=
  ∑' z : Eisenstein, Real.exp (-t*‖(z:ℂ)-x‖^2)

lemma huxleyPeriodizedGaussian_nonneg (t : ℝ) (x : ℂ) :
    0 ≤ huxleyPeriodizedGaussian t x := tsum_nonneg (fun _ => (Real.exp_pos _).le)

lemma huxleyPeriodizedGaussian_summable {t : ℝ} (ht : 0 < t) (x : ℂ) :
    Summable (fun z : Eisenstein => Real.exp (-t*‖(z:ℂ)-x‖^2)) := by
  let a : Eisenstein := residueRepresentative 1 0
  let lift : Eisenstein → HuxleyLift := fun z => ⟨1,a,z-a⟩
  have hi : Function.Injective lift := by
    intro z w h
    have he := congrArg HuxleyLift.shift h
    simpa only [lift,sub_left_inj] using he
  have hr (z : Eisenstein) : (lift z).reduced 1 := by
    dsimp only [HuxleyLift.reduced,lift]
    refine ⟨one_ne_zero,?_,isCoprime_one_left,?_⟩
    · simp [norm]
    · change residueRepresentative 1 (Ideal.Quotient.mk (modulus 1) a) = a
      dsimp only [a]
      rw [residueRepresentative_spec]
  have hs := (huxleyLiftGaussian_summable 1 zero_lt_one x ht).comp_injective hi
  change Summable (fun z => huxleyLiftGaussian 1 t x (lift z)) at hs
  apply hs.congr
  intro z
  rw [huxleyLiftGaussian,ite_eq_left (hr z)]
  have he : (lift z).frequency = (z:ℂ) := by simp [lift,HuxleyLift.frequency]
  rw [he]

lemma huxleyPeriodizedGaussian_neg (t : ℝ) (x : ℂ) :
    huxleyPeriodizedGaussian t (-x) = huxleyPeriodizedGaussian t x := by
  unfold huxleyPeriodizedGaussian
  simp only [sub_neg_eq_add]
  rw [← (Equiv.neg Eisenstein).tsum_eq (fun z : Eisenstein => Real.exp (-t*‖(z:ℂ)+x‖^2))]
  apply tsum_congr
  intro z
  simp only [Equiv.neg_apply]
  have he : ((-z:Eisenstein):ℂ)+x = -((z:ℂ)-x) := by push_cast; ring
  rw [he,norm_neg]

lemma huxleyPeriodizedGaussian_row_bound (Q : ℝ) (hQ : 0 < Q)
    {t : ℝ} (ht : 0 < t) (P : Finset HuxleyLift)
    (hred : ∀ p ∈ P, p.reduced Q) (hzero : ∀ p ∈ P, p.shift = 0) (x : ℂ) :
    (∑ p ∈ P, huxleyPeriodizedGaussian t (x-p.frequency)) ≤
      huxleyGaussianConstant*(1+Q^2/t) := by
  let lift : ({p // p ∈ P} × Eisenstein) → HuxleyLift :=
    fun p => ⟨p.1.val.denominator,p.1.val.numerator,p.2⟩
  have hinj : Function.Injective lift := by
    intro a b hab
    apply Prod.ext
    · apply Subtype.ext
      apply HuxleyLift.ext
      · simpa only [lift] using congrArg HuxleyLift.denominator hab
      · simpa only [lift] using congrArg HuxleyLift.numerator hab
      · exact (hzero _ a.1.property).trans (hzero _ b.1.property).symm
    · exact congrArg HuxleyLift.shift hab
  have hr (p : {p // p ∈ P} × Eisenstein) : (lift p).reduced Q := by
    exact hred p.1.val p.1.property
  have he (p : {p // p ∈ P} × Eisenstein) :
      huxleyLiftGaussian Q t x (lift p) =
        Real.exp (-t*‖(p.2:ℂ)-(x-p.1.val.frequency)‖^2) := by
    rw [huxleyLiftGaussian,ite_eq_left (hr p)]
    have hz : (lift p).frequency-x = (p.2:ℂ)-(x-p.1.val.frequency) := by
      dsimp [lift,HuxleyLift.frequency]
      rw [hzero _ p.1.property]
      push_cast
      ring
    rw [hz]
  have hs := huxleyLiftGaussian_summable Q hQ x ht
  have hc := hs.comp_injective hinj
  change Summable (fun p => huxleyLiftGaussian Q t x (lift p)) at hc
  have hb := hc.tsum_le_tsum_of_inj lift hinj
    (fun i hi => by unfold huxleyLiftGaussian; split_ifs <;> positivity)
    (fun i => le_rfl) hs
  have hex : (∑' p : {p // p ∈ P} × Eisenstein, huxleyLiftGaussian Q t x (lift p)) =
      ∑ p ∈ P, huxleyPeriodizedGaussian t (x-p.frequency) := by
    rw [hc.tsum_prod]
    simp_rw [he]
    rw [tsum_fintype]
    exact Finset.sum_coe_sort P (fun p => huxleyPeriodizedGaussian t (x-p.frequency))
  rw [hex] at hb
  exact hb.trans (huxleyLiftGaussian_tsum_bound Q hQ x ht)

end CubicFirstMoment

end

end OAI
