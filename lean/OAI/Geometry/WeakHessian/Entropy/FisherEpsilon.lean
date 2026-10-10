import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatMassNonneg
import OAI.Geometry.WeakHessian.Entropy.RenormalizedEntropy
import OAI.Geometry.WeakHessian.Entropy.RegularizedEntropyIntegrable
import OAI.Geometry.WeakHessian.LocalBounds.WeightedPairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma renormalizedEntropy_integrable {a : ℝ} (ha : 0 < a) (u : Lp ℝ 2 m) (hi : Integrable u m) :
    Integrable (fun x => renormalizedEntropy a (u x)) m :=
  (regularizedEntropy_integrable ha u).add (hi.const_mul (Real.log a))

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma integral_renormalizedEntropy {a : ℝ} (ha : 0 < a) (u : Lp ℝ 2 m) (hi : Integrable u m) :
    (∫ x,renormalizedEntropy a (u x) ∂m) =
      (∫ x,regularizedEntropy a (u x) ∂m)+Real.log a*(∫ x,u x ∂m) := by
  exact (integral_add (regularizedEntropy_integrable ha u) (hi.const_mul (Real.log a))).trans
    (congrArg (fun z => (∫ x,regularizedEntropy a (u x) ∂m)+z) (integral_const_mul _ _))

lemma CurvatureDimension.cheegerHeat_renormalizedEntropy_FTC {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    (∫ t in 0..b,∫ x,(weakGradient m (cheegerHeat h t u) x)^2/(cheegerHeat h t u x+a) ∂m) =
      (∫ x,renormalizedEntropy a (u x) ∂m)-(∫ x,renormalizedEntropy a (cheegerHeat h b u x) ∂m) := by
  have hmass := hcd.cheegerHeat_mass_nonneg hN hfull hfin o h u hun hi hb
  rw [integral_renormalizedEntropy ha u hi,integral_renormalizedEntropy ha _ hmass.1,hmass.2]
  simpa only [add_sub_add_right_eq_sub] using hcd.cheegerHeat_regularizedEntropy_FTC hfin o h hu hun ha hb

lemma CurvatureDimension.cheegerHeat_regularizedFisher_action_bound {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 ≤ b) :
    (∫ t in 0..b,∫ x,(weakGradient m (cheegerHeat h t u) x)^2/(cheegerHeat h t u x+a) ∂m) ≤
      ‖u‖^2/2+
      ‖hU.toLp (fun x => u x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*b)*
        ‖hD.toLp (fun x => V x*Real.exp (-V x))‖+(∫ x,Real.exp (-V x) ∂m) := by
  have ht := (hcd.cheegerHeat_mass_nonneg hN hfull hfin o h u hun hi hb).1
  have hUt := (hcd.cheegerHeat_weighted hfin o h u hV hU hb).1
  have hpair := weighted_pairing hUt hD
  have hE0 : (∫ x,renormalizedEntropy a (u x) ∂m) ≤ ‖u‖^2/2 := by
    have H := integral_mono_ae (renormalizedEntropy_integrable ha u hi)
      ((Lp.memLp u).integrable_sq.div_const 2) (hun.mono fun x hx => renormalizedEntropy_upper ha ha1 hx)
    rw [integral_div] at H
    have he : (∫ x,u x^2 ∂m) = ‖u‖^2 := by
      simpa only [L2.inner_def,RCLike.inner_apply,conj_trivial,pow_two] using real_inner_self_eq_norm_sq u
    rwa [he] at H
  have hEt : -(∫ x,cheegerHeat h b u x*V x ∂m)-(∫ x,Real.exp (-V x) ∂m) ≤
      (∫ x,renormalizedEntropy a (cheegerHeat h b u x) ∂m) := by
    have H := integral_mono_ae (hpair.1.neg.sub hw) (renormalizedEntropy_integrable ha _ ht) (by
      filter_upwards [cheegerHeat_nonneg h hb u hun] with x hx
      have H := renormalizedEntropy_lower ha hx (Real.exp_pos (-V x))
      simpa only [Real.log_exp,mul_neg,Pi.sub_apply,Pi.neg_apply] using! H)
    change (∫ x,-(cheegerHeat h b u x*V x)-Real.exp (-V x) ∂m) ≤ _ at H
    have he : (∫ x,-(cheegerHeat h b u x*V x)-Real.exp (-V x) ∂m) =
        -(∫ x,cheegerHeat h b u x*V x ∂m)-(∫ x,Real.exp (-V x) ∂m) := by
      calc
        _ = (∫ x,-(cheegerHeat h b u x*V x) ∂m)-(∫ x,Real.exp (-V x) ∂m) :=
          integral_sub (by simpa only [Pi.neg_apply] using! hpair.1.neg) hw
        _ = _ := by rw [integral_neg]
    rw [he] at H
    exact H
  have hm := (le_abs_self (∫ x,cheegerHeat h b u x*V x ∂m)).trans hpair.2
  have hB := hcd.cheegerHeat_weighted_norm hfin o h u hV hU hb
  have hm' := hm.trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  rw [hcd.cheegerHeat_renormalizedEntropy_FTC hN hfull hfin o h hu hun hi ha hb]
  linarith
end WeakHessian

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable def fisherEpsilon (n : ℕ) : ℝ := 1/((n:ℝ)+1)
lemma fisherEpsilon_pos (n : ℕ) : 0 < fisherEpsilon n := by unfold fisherEpsilon; positivity
lemma fisherEpsilon_le_one (n : ℕ) : fisherEpsilon n ≤ 1 := by
  unfold fisherEpsilon
  exact (div_le_one (by positivity)).mpr (by have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)
lemma fisherEpsilon_antitone : Antitone fisherEpsilon := by
  intro n k hnk
  unfold fisherEpsilon
  gcongr
lemma fisherEpsilon_tendsto : Tendsto fisherEpsilon atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

lemma regularizedFisher_mono {v g : ℝ} (hv : 0 ≤ v) :
    Monotone (fun n => g^2/(v+fisherEpsilon n)) := by
  intro n k hnk
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by linarith [fisherEpsilon_pos k])
  have H := fisherEpsilon_antitone hnk
  linarith

lemma regularizedFisher_tendsto {v g : ℝ} (hv : 0 ≤ v) (hz : v = 0 → g = 0) :
    Tendsto (fun n => g^2/(v+fisherEpsilon n)) atTop (𝓝 (g^2/v)) := by
  rcases hv.eq_or_lt with hv | hv
  · simp only [hv.symm,hz hv.symm,zero_pow (by decide : 2 ≠ 0),zero_div]
    exact tendsto_const_nhds
  · simpa only [add_zero,Pi.div_apply] using! tendsto_const_nhds.div
      (tendsto_const_nhds.add fisherEpsilon_tendsto) (by simpa using hv.ne')

lemma ofReal_fisher_eq_iSup {v g : ℝ} (hv : 0 ≤ v) (hz : v = 0 → g = 0) :
    ENNReal.ofReal (g^2/v) = ⨆ n,ENNReal.ofReal (g^2/(v+fisherEpsilon n)) :=
  tendsto_nhds_unique (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (regularizedFisher_tendsto hv hz))
    (tendsto_atTop_iSup (fun _ _ hij => ENNReal.ofReal_le_ofReal (regularizedFisher_mono hv hij)))

variable {X : Type*} [MeasurableSpace X] {m : Measure X}
lemma integrable_regularizedFisher {u g : X → ℝ} (hu : AEStronglyMeasurable u m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hg : MemLp g 2 m) {a : ℝ} (ha : 0 < a) :
    Integrable (fun x => g x^2/(u x+a)) m := by
  apply (hg.integrable_sq.div_const a).mono' ((hg.aestronglyMeasurable.pow 2).div₀ (hu.add_const a))
  filter_upwards [hun] with x hx
  simp only [Pi.div_apply,Pi.pow_apply]
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (by linarith))]
  exact div_le_div_of_nonneg_left (sq_nonneg _) ha (by linarith)

lemma lintegral_fisher_eq_iSup {u g : X → ℝ} (hu : AEStronglyMeasurable u m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hg : MemLp g 2 m)
    (hz : ∀ᵐ x ∂m,u x = 0 → g x = 0) :
    (∫⁻ x,ENNReal.ofReal (g x^2/u x) ∂m) =
      ⨆ n,ENNReal.ofReal (∫ x,g x^2/(u x+fisherEpsilon n) ∂m) := by
  have he : (fun x => ENNReal.ofReal (g x^2/u x)) =ᵐ[m]
      fun x => ⨆ n,ENNReal.ofReal (g x^2/(u x+fisherEpsilon n)) := by
    filter_upwards [hun,hz] with x hx hz
    exact ofReal_fisher_eq_iSup hx hz
  rw [lintegral_congr_ae he,lintegral_iSup']
  · congr 1
    funext n
    exact (ofReal_integral_eq_lintegral_ofReal
      (integrable_regularizedFisher hu hun hg (fisherEpsilon_pos n))
      (hun.mono fun x hx => div_nonneg (sq_nonneg _) (by linarith [fisherEpsilon_pos n]))).symm
  · exact fun n => ((hg.aestronglyMeasurable.pow 2).div₀ (hu.add_const (fisherEpsilon n))).aemeasurable.ennreal_ofReal
  · filter_upwards [hun] with x hx
    exact fun _ _ hij => ENNReal.ofReal_le_ofReal (regularizedFisher_mono hx hij)

lemma fisher_action_of_regularization {T : Type*} [MeasurableSpace T] {ν : Measure T}
    {u g : T → X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ᵐ t ∂ν,AEStronglyMeasurable (u t) m)
    (hun : ∀ᵐ t ∂ν,∀ᵐ x ∂m,0 ≤ u t x)
    (hg : ∀ᵐ t ∂ν,MemLp (g t) 2 m)
    (hz : ∀ᵐ t ∂ν,∀ᵐ x ∂m,u t x = 0 → g t x = 0)
    (hR : ∀ n,Integrable (fun t => ∫ x,g t x^2/(u t x+fisherEpsilon n) ∂m) ν)
    (hB : ∀ n,(∫ t,∫ x,g t x^2/(u t x+fisherEpsilon n) ∂m ∂ν) ≤ C) :
    (∀ᵐ t ∂ν,Integrable (fun x => g t x^2/u t x) m) ∧
      Integrable (fun t => ∫ x,g t x^2/u t x ∂m) ν ∧
      (∫ t,∫ x,g t x^2/u t x ∂m ∂ν) ≤ C := by
  let R : ℕ → T → ℝ := fun n t => ∫ x,g t x^2/(u t x+fisherEpsilon n) ∂m
  let I : T → ℝ≥0∞ := fun t => ∫⁻ x,ENNReal.ofReal (g t x^2/u t x) ∂m
  have he : I =ᵐ[ν] fun t => ⨆ n,ENNReal.ofReal (R n t) := by
    filter_upwards [hu,hun,hg,hz] with t hu hn hg hz
    exact lintegral_fisher_eq_iSup hu hn hg hz
  have hmono : ∀ᵐ t ∂ν,Monotone (fun n => ENNReal.ofReal (R n t)) := by
    filter_upwards [hu,hun,hg] with t hu hn hg
    intro n k hnk
    apply ENNReal.ofReal_le_ofReal
    exact integral_mono_ae (integrable_regularizedFisher hu hn hg (fisherEpsilon_pos n))
      (integrable_regularizedFisher hu hn hg (fisherEpsilon_pos k))
      (hn.mono fun x hx => regularizedFisher_mono hx hnk)
  have hIm : AEMeasurable I ν :=
    (AEMeasurable.iSup (fun n => (hR n).1.aemeasurable.ennreal_ofReal)).congr he.symm
  have hIb : (∫⁻ t,I t ∂ν) ≤ ENNReal.ofReal C := by
    rw [lintegral_congr_ae he,lintegral_iSup' (fun n => (hR n).1.aemeasurable.ennreal_ofReal) hmono]
    apply iSup_le
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hR n)]
    · exact ENNReal.ofReal_le_ofReal (hB n)
    · filter_upwards [hun] with t hn
      exact integral_nonneg_of_ae (hn.mono fun x hx => div_nonneg (sq_nonneg _) (by linarith [fisherEpsilon_pos n]))
  have hIf : (∫⁻ t,I t ∂ν) ≠ ∞ := ne_of_lt (hIb.trans_lt ENNReal.ofReal_lt_top)
  have hIa : ∀ᵐ t ∂ν,I t < ∞ := ae_lt_top' hIm hIf
  have hsp : ∀ᵐ t ∂ν,Integrable (fun x => g t x^2/u t x) m := by
    filter_upwards [hu,hun,hg,hIa] with t hu hn hg hf
    apply (lintegral_ofReal_ne_top_iff_integrable ((hg.aestronglyMeasurable.pow 2).div₀ hu)
      (hn.mono fun x hx => div_nonneg (sq_nonneg _) hx)).mp
    exact hf.ne
  have htr : (fun t => (I t).toReal) =ᵐ[ν] fun t => ∫ x,g t x^2/u t x ∂m := by
    filter_upwards [hsp,hun] with t hi hn
    rw [show I t = ENNReal.ofReal (∫ x,g t x^2/u t x ∂m) from
      (ofReal_integral_eq_lintegral_ofReal hi (hn.mono fun x hx => div_nonneg (sq_nonneg _) hx)).symm,
      ENNReal.toReal_ofReal (integral_nonneg_of_ae (hn.mono fun x hx => div_nonneg (sq_nonneg _) hx))]
  refine ⟨hsp,(integrable_toReal_of_lintegral_ne_top hIm hIf).congr htr,?_⟩
  rw [← integral_congr_ae htr,integral_toReal hIm hIa]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hIb).trans_eq (ENNReal.toReal_ofReal hC)
lemma integral_regularizedFisher_tendsto {u g : X → ℝ} (hu : AEStronglyMeasurable u m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hg : MemLp g 2 m)
    (hz : ∀ᵐ x ∂m,u x = 0 → g x = 0) (hI : Integrable (fun x => g x^2/u x) m) :
    Tendsto (fun n => ∫ x,g x^2/(u x+fisherEpsilon n) ∂m) atTop (𝓝 (∫ x,g x^2/u x ∂m)) :=
  integral_tendsto_of_tendsto_of_monotone
    (fun n => integrable_regularizedFisher hu hun hg (fisherEpsilon_pos n)) hI
    (hun.mono fun x hx => regularizedFisher_mono hx)
    (by filter_upwards [hun,hz] with x hx hz; exact regularizedFisher_tendsto hx hz)

lemma integral_regularizedFisher_action_tendsto {T : Type*} [MeasurableSpace T] {ν : Measure T}
    {u g : T → X → ℝ}
    (hu : ∀ᵐ t ∂ν,AEStronglyMeasurable (u t) m)
    (hun : ∀ᵐ t ∂ν,∀ᵐ x ∂m,0 ≤ u t x)
    (hg : ∀ᵐ t ∂ν,MemLp (g t) 2 m)
    (hz : ∀ᵐ t ∂ν,∀ᵐ x ∂m,u t x = 0 → g t x = 0)
    (hR : ∀ n,Integrable (fun t => ∫ x,g t x^2/(u t x+fisherEpsilon n) ∂m) ν)
    (hI : ∀ᵐ t ∂ν,Integrable (fun x => g t x^2/u t x) m)
    (hIt : Integrable (fun t => ∫ x,g t x^2/u t x ∂m) ν) :
    Tendsto (fun n => ∫ t,∫ x,g t x^2/(u t x+fisherEpsilon n) ∂m ∂ν) atTop
      (𝓝 (∫ t,∫ x,g t x^2/u t x ∂m ∂ν)) := by
  apply integral_tendsto_of_tendsto_of_monotone hR hIt
  · filter_upwards [hu,hun,hg] with t hu hn hg
    intro n k hnk
    exact integral_mono_ae (integrable_regularizedFisher hu hn hg (fisherEpsilon_pos n))
      (integrable_regularizedFisher hu hn hg (fisherEpsilon_pos k))
      (hn.mono fun x hx => regularizedFisher_mono hx hnk)
  · filter_upwards [hu,hun,hg,hz,hI] with t ht hn hg hz hi
    exact integral_regularizedFisher_tendsto ht hn hg hz hi
end WeakHessian

end
end InlinedFile0

end OAI
