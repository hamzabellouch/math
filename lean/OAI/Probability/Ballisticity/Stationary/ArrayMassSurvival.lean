import Mathlib
import OAI.Probability.Ballisticity.Stationary.ArrayProfileConsistency
import OAI.Probability.Ballisticity.Walk.ArrayCostGrowth
import OAI.Probability.Ballisticity.Estimates.ClassMoment

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma arrayProfileMass_total_le_one {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hP : ArrayProfilesConsistent e Y) (i : ℤ) (p : StationaryCompact.Label) :
    (∑' z, arrayProfileMass e i p z Y)≤1 := by
  apply ENNReal.summable.tsum_le_of_sum_le
  intro s
  dsimp only [arrayProfileMass]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun z _ => (Y.2.2.1 (i,p,z)).property.1)]
  exact ENNReal.ofReal_le_one.mpr (hP.2 i p s)

lemma upperHorizontalKernel_mass_sum {d : ℕ} (e : Direction d) (H : ℕ)
    (ξ : UpperRows e) (x : HorizontalSpace e) :
    (∑' z, upperHorizontalKernel e H ξ x {z})=upperHorizontalKernel e H ξ x Set.univ := by
  simpa only [Set.indicator_univ] using
    (upperHorizontalKernel e H ξ x).tsum_indicator_apply_singleton Set.univ MeasurableSet.univ

lemma arrayKernelImage_total_le_discount {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hP : ArrayProfilesConsistent e Y) (hc : ArrayContinuation e Y)
    (i : ℤ) (m a H : ℕ) (hH : arrayWindowHeight e i m Y=H) :
    arrayKernelImage e i m a H Set.univ Y≤expNeg (arrayWindowCost e i m Y) := by
  calc
    _ = ∑' z, arrayKernelImage e i m a H {z} Y := by
      unfold arrayKernelImage
      calc
        _ = ∑' x, ∑' z, arrayProfileMass e i (i,a) x Y *
            upperHorizontalKernel e H (arrayUpperRows e i m a Y) x {z} := by
          congr 1
          funext x
          rw [ENNReal.tsum_mul_left,upperHorizontalKernel_mass_sum]
        _ = _ := ENNReal.tsum_comm
    _ ≤ ∑' z, arrayDiscountedProfile e i m a z Y := ENNReal.tsum_le_tsum (fun z => hc i m a H z hH)
    _ = expNeg (arrayWindowCost e i m Y)*(∑' z, arrayProfileMass e (i+m) (i,a) z Y) := by
      simp only [arrayDiscountedProfile,ENNReal.tsum_mul_left]
    _ ≤ expNeg (arrayWindowCost e i m Y)*1 := mul_le_mul_right (arrayProfileMass_total_le_one e Y hP _ _) _
    _ = _ := mul_one _

lemma arraySelfMass_mul_q_le_discount {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hP : ArrayProfilesConsistent e Y) (hc : ArrayContinuation e Y)
    (i : ℤ) (m a H : ℕ) (hH : arrayWindowHeight e i m Y=H)
    (hq : upperNoDrop e (arrayUpperRows e i m a Y)≤upperHorizontalKernel e H (arrayUpperRows e i m a Y) 0 Set.univ) :
    arrayProfileMass e i (i,a) 0 Y * upperNoDrop e (arrayUpperRows e i m a Y)≤
      expNeg (arrayWindowCost e i m Y) := by
  apply le_trans (mul_le_mul_right hq _)
  exact (ENNReal.le_tsum 0).trans (arrayKernelImage_total_le_discount e Y hP hc i m a H hH)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def arrayCurrentData {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e) : CurrentData e :=
  (typedCurrentArrayWindow e i 0 Y).1
lemma arrayCurrentData_measurable {d : ℕ} (e : Direction d) (i : ℤ) : Measurable (arrayCurrentData e i) :=
  (typedCurrentArrayWindow_measurable e i 0).fst
lemma typedCurrentArrayWindow_data {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ) (Y : ActualEpisodeArray e) :
    (typedCurrentArrayWindow e i m Y).1=arrayCurrentData e i Y := rfl

lemma ennreal_negative_power_exp_lower {q : ℝ≥0∞} {lam t : ℝ} (hlam : 0≤lam)
    (hq : q≤ENNReal.ofReal (Real.exp (-t))) :
    ENNReal.ofReal (Real.exp (lam*t))≤q^(-lam) := by
  have h := ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hq hlam)
  rw [←ENNReal.rpow_neg,←ENNReal.rpow_neg] at h
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),Real.rpow_def_of_pos (Real.exp_pos _)] at h
  simpa only [Real.log_exp,neg_mul_neg,mul_comm] using h

lemma selfmass_nodrop_bound {mass q c : ℝ≥0∞} {r t : ℝ}
    (hr : 0<r) (hm : ENNReal.ofReal r≤ mass) (hc : c≠⊤)
    (hcost : 2*t≤c.toReal) (hrt : Real.exp (-t)≤r)
    (hbound : mass*q≤expNeg c) : q≤ENNReal.ofReal (Real.exp (-t)) := by
  have hexp : expNeg c=ENNReal.ofReal (Real.exp (-c.toReal)) := by
    rw [←ENNReal.ofReal_toReal (expNeg_ne_top _),expNeg_toReal_of_ne_top c hc]
  have hb : ENNReal.ofReal r*q≤ENNReal.ofReal (Real.exp (-c.toReal)) :=
    (mul_le_mul_left hm q).trans (hbound.trans_eq hexp)
  have hr0 : ENNReal.ofReal r≠0 := (ENNReal.ofReal_pos.mpr hr).ne'
  apply (ENNReal.mul_le_mul_iff_right hr0 ENNReal.ofReal_ne_top).mp
  apply hb.trans
  rw [←ENNReal.ofReal_mul hr.le]
  apply ENNReal.ofReal_le_ofReal
  calc
    Real.exp (-c.toReal) ≤ Real.exp (-2*t) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-t)*Real.exp (-t) := by rw [←Real.exp_add]; congr 1; ring
    _ ≤ r*Real.exp (-t) := mul_le_mul_of_nonneg_right hrt (Real.exp_nonneg _)

lemma array_selectedProduct_lower {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hP : ArrayProfilesConsistent e Y) (hc : ArrayContinuation e Y) (i : ℤ) (m H n : ℕ)
    (hH : arrayWindowHeight e i m Y=H) (hfin : arrayWindowCost e i m Y≠⊤)
    (hq : ∀ a, upperNoDrop e (arrayUpperRows e i m a Y)≤
      upperHorizontalKernel e H (arrayUpperRows e i m a Y) 0 Set.univ)
    {r lam t : ℝ} (hr : 0<r) (hlam : 0≤lam) (ht : 2*t≤(arrayWindowCost e i m Y).toReal)
    (hrt : Real.exp (-t)≤r) (hs : ∃ a, CurrentClassSelection e n r (arrayCurrentData e i Y) a) :
    ENNReal.ofReal (Real.exp ((n:ℝ)*lam*t))≤ selectedClassProduct e n r lam (typedCurrentArrayWindow e i m Y) := by
  have hs' := hs
  rw [←typedCurrentArrayWindow_data e i m Y] at hs'
  simp only [selectedClassProduct,ite_eq_left hs']
  calc
    _ = ∏ _j : Fin n, ENNReal.ofReal (Real.exp (lam*t)) := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←ENNReal.ofReal_pow (Real.exp_nonneg _),
        ←Real.exp_nat_mul,mul_assoc]
    _ ≤ _ := by
      apply Finset.prod_le_prod
      intro j _
      apply ennreal_negative_power_exp_lower hlam
      apply selfmass_nodrop_bound hr _ hfin ht hrt
        (arraySelfMass_mul_q_le_discount e Y hP hc i m _ H hH (hq _))
      exact ENNReal.ofReal_le_ofReal ((currentSelect_spec e n r _ hs').1 j)

end DirectionalTransience

end

end OAI
