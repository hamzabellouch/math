import Mathlib
import OAI.Probability.Ballisticity.Stationary.EpisodeRandomStart

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma fluctuationRadius_order_above {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) (hne : 0<μ {x | S x≠0}) {s t : ℝ}
    (hs : fluctuationScale μ S 1<s) (hst : s≤t) :
    fluctuationRadius μ S s ≤ fluctuationRadius μ S t := by
  by_cases he : s=t
  · simp only [he,le_refl]
  have hst' : s<t := lt_of_le_of_ne hst he
  have hss := (fluctuationRadius_spec μ S hS hI hne zero_lt_one hs).2
  have htt := (fluctuationRadius_spec μ S hS hI hne zero_lt_one (hs.trans hst')).2
  by_contra hh
  have hh := fluctuationScale_mono μ S hS hne (fluctuationRadius_pos μ S t) (not_le.mp hh).le
  rw [htt,hss] at hh
  exact (not_le_of_gt hst') hh

lemma fluctuationRadius_stage_order {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) (hne : 0<μ {x | S x≠0}) (f b : ℝ) (hf : 0≤f) (hb : 0≤b) :
    ∃ R : ℝ, 1≤R ∧ ∀ sfloor, R≤ sfloor → StageRadiusOrder (fluctuationRadius μ S) f b sfloor := by
  let B := max 1 (fluctuationScale μ S 1+1)
  let R := max 1 (B/Real.exp (-f*b))
  refine ⟨R,le_max_left _ _,?_⟩
  intro sfloor hfloor s hs
  have hexp : Real.exp (-f*b)≤1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hs0 : 0≤ s := le_trans (by norm_num : (0:ℝ)≤1) ((le_max_left 1 _).trans (hfloor.trans hs))
  have hsB : B ≤ s*Real.exp (-f*b) := (div_le_iff₀ (Real.exp_pos _)).mp ((le_max_right 1 _).trans (hfloor.trans hs))
  apply fluctuationRadius_order_above μ S hS hI hne
  · exact lt_of_lt_of_le (by dsimp only [B]; linarith [le_max_right (1:ℝ) (fluctuationScale μ S 1+1)]) hsB
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hs0

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

noncomputable def episodeScaleRadius {d : ℕ} (ν : Measure (Row d)) (e f : Direction d) : ℝ → ℝ :=
  fluctuationRadius (independentConditionedPairLaw ν (realPosition (step e)))
    (commonIncrementProcess (realPosition (step e)) f 0)

structure OperationalConstants {d : ℕ} (ν : Measure (Row d)) (e f : Direction d) (D : ℝ) where
  fexp : ℝ
  g : ℝ
  χ : ℝ
  K : ℝ
  b : ℝ
  sfloor : ℝ
  k : ℕ
  κ : ℝ≥0
  hk : 2 ≤ k
  hκ0 : 0 < κ
  hκ1 : κ ≤ 1
  rows : ∀ᵐ ω ∂environmentLaw ν, ∀ y u, κ ≤ (ω y).1 u
  hf : 0 < fexp
  hg : 0 < g
  hgap : g < χ
  hK : 0 < K
  hb : 0 < b
  hs : 1 ≤ sfloor
  hbκ : -Real.log κ ≤ b
  coeff : 1/g+(1+fexp/g)*D/K ≤ (1/2:ℝ)/32
  small : (1+fexp/g)*Real.exp (-(K*b))/(K*b) ≤ 1/2
  order : StageRadiusOrder (episodeScaleRadius ν e f) fexp b sfloor
  height : ∀ s, sfloor ≤ s → s*Real.exp (g*b) ≤ (episodeStageH χ b s:ℝ)
  stages : ∀ s, sfloor ≤ s → ∀ a : ℝ, ∀ π : BudgetProfile (k:=k) e f a (episodeScaleRadius ν e f s),
    environmentLaw ν (stageBadEvent e f (episodeStageH χ b s)
      (episodeScaleRadius ν e f (s*Real.exp (-fexp*b)))
      (episodeScaleRadius ν e f (s*Real.exp (g*b))) π.val
      (ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))) ≤ ENNReal.ofReal (Real.exp (-2*(K*b)))

lemma operational_constants_exist {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) (D : ℝ) (hD : 0≤D) :
    Nonempty (OperationalConstants ν e f D) := by
  obtain ⟨κ,hκ0,hκae⟩ := environment_uniform_elliptic ν hue
  have hκ1 : κ≤1 := by
    obtain ⟨ω,hω⟩ := hκae.exists
    exact (hω 0 e).trans (row_entry_le_one (ω 0) e)
  obtain ⟨fexp,g,χ,K,hf,hg,hgap,hK,hgsmall,hKsmall,k,hk,hparams⟩ :=
    operational_stage_parameters ν hue e f hef htrans D hD
  have hc : 0≤1+fexp/g := by positivity
  have hlarge := eventually_ge_atTop (max (-Real.log κ) (2*(1+fexp/g)/K))
  obtain ⟨b,hbparam,hblarge⟩ := (hparams.and hlarge).exists
  obtain ⟨hb,oldfloor,holdfloor,hheight,hstages⟩ := hbparam
  have hbκ : -Real.log κ≤b := (le_max_left _ _).trans hblarge
  have hcoeff : 1/g+(1+fexp/g)*D/K ≤ (1/2:ℝ)/32 := by linarith
  have hsmall : (1+fexp/g)*Real.exp (-(K*b))/(K*b)≤1/2 := by
    have hden : 0<K*b := mul_pos hK hb
    have he : Real.exp (-(K*b))≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hden.le)
    have hb2 : 2*(1+fexp/g)≤b*K := (div_le_iff₀ hK).mp ((le_max_right _ _).trans hblarge)
    apply (div_le_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left he hc
    nlinarith
  let μ := independentConditionedPairLaw ν (realPosition (step e))
  let S := commonIncrementProcess (realPosition (step e)) f 0
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν _
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν _ htrans))
  have hS : Measurable S := measurable_commonIncrementProcess _ _ _
  have hI : Integrable S μ := independent_commonWordIncrement_integrable ν hue _
    (signed_direction_unit e) htrans (signedHeight e) (signedHeight_projection e)
    (signedHeight_step_le e) f
  have hne : 0<μ {x | S x≠0} := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  obtain ⟨R,hR,horder⟩ := fluctuationRadius_stage_order μ S hS hI hne fexp b hf.le hb.le
  let sfloor := max oldfloor R
  have hsf : oldfloor≤ sfloor := le_max_left _ _
  refine ⟨{ fexp := fexp
            g := g
            χ := χ
            K := K
            b := b
            sfloor := sfloor
            k := k
            κ := κ
            hk := hk
            hκ0 := hκ0
            hκ1 := hκ1
            rows := hκae
            hf := hf
            hg := hg
            hgap := hgap
            hK := hK
            hb := hb
            hs := holdfloor.trans hsf
            hbκ := hbκ
            coeff := hcoeff
            small := hsmall
            order := horder sfloor (le_max_right _ _)
            height := ?_
            stages := ?_ }⟩
  · intro s hs
    exact (hheight s (hsf.trans hs)).2
  · intro s hs a π
    simpa only [mul_assoc,episodeScaleRadius] using hstages s (hsf.trans hs) a π

end DirectionalTransience

end

end OAI
