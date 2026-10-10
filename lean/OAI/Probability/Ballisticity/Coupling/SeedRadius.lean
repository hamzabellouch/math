import Mathlib
import OAI.Probability.Ballisticity.Coupling.SeedUniform

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def fluctuationRadius {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (s : ℝ) : ℝ :=
  if h : ∃ r : ℝ, 0<r ∧ fluctuationScale μ S r=s then h.choose else 1

lemma fluctuationRadius_spec {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) (hne : 0<μ {x | S x≠0}) {R s : ℝ} (hR : 0<R)
    (hs : fluctuationScale μ S R<s) :
    R<fluctuationRadius μ S s ∧ fluctuationScale μ S (fluctuationRadius μ S s)=s := by
  have hcont := (continuousOn_fluctuationScale μ S hS hne).mono
    (show Set.Ici R ⊆ Set.Ioi 0 from fun r hr => hR.trans_le hr)
  obtain ⟨r,hr,he⟩ := intermediate_value_Ici hcont (fluctuationScale_tendsto μ S hS hI hne) hs.le
  have hex : ∃ r : ℝ, 0<r ∧ fluctuationScale μ S r=s := ⟨r,hR.trans_le hr,he⟩
  have hpos : 0<fluctuationRadius μ S s := by simp only [fluctuationRadius,dite_eq_left hex]; exact hex.choose_spec.1
  have heq : fluctuationScale μ S (fluctuationRadius μ S s)=s := by simp only [fluctuationRadius,dite_eq_left hex]; exact hex.choose_spec.2
  refine ⟨?_,heq⟩
  by_contra hn
  have hh := fluctuationScale_mono μ S hS hne hpos (not_lt.mp hn)
  rw [heq] at hh
  exact (not_le_of_gt hs) hh

lemma fluctuationRadius_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) (hne : 0<μ {x | S x≠0}) :
    Tendsto (fluctuationRadius μ S) atTop atTop := by
  apply tendsto_atTop.mpr
  intro bound
  filter_upwards [eventually_gt_atTop (fluctuationScale μ S (max bound 1))] with s hs
  exact (le_max_left bound 1).trans
    (fluctuationRadius_spec μ S hS hI hne (lt_of_lt_of_le (by norm_num) (le_max_right _ _)) hs).1.le

lemma fluctuationRadius_eventual_unique {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) (hne : 0<μ {x | S x≠0}) :
    ∀ᶠ s in atTop, ∀ r : ℝ, 0<r → fluctuationScale μ S r=s → r=fluctuationRadius μ S s := by
  obtain ⟨R,hR,hstrict⟩ := fluctuationScale_eventually_strictMono μ S hS hne
  filter_upwards [eventually_gt_atTop (fluctuationScale μ S R)] with s hs r hr he
  obtain ⟨hRR,hRspec⟩ := fluctuationRadius_spec μ S hS hI hne hR hs
  have hrR : R≤r := by
    by_contra hn
    have hh := fluctuationScale_mono μ S hS hne hr (not_le.mp hn).le
    rw [he] at hh
    exact (not_le_of_gt hs) hh
  exact hstrict.injOn hrR hRR.le (he.trans hRspec.symm)

theorem separated_seeds {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (k : ℕ) (hk : 2≤k) (p : ℝ) (hp : 0<p) :
    ∃ C c₀ g₀ : ℝ, 0<C ∧ 0<c₀ ∧ 0<g₀ ∧ ∃ H₀ : ℕ, ∀ H≥H₀,
      ∀ π : ProbabilityMeasure (Fin k → Lattice d),
        1-p < (environmentLaw ν).real {ω | ENNReal.ofReal g₀≤
          rawTupleMixture (realPosition (step e)) H π.toMeasure ω {v | TupleSeparated f
            (c₀*fluctuationRadius (independentConditionedPairLaw ν (realPosition (step e)))
              (commonIncrementProcess (realPosition (step e)) f 0) (H/C)) v}} := by
  obtain ⟨C,c₀,g₀,R,hC,hc,hg,hR,hseed⟩ := seed_mass_at_scale ν hue e f hef htrans k hk p hp
  let μ := independentConditionedPairLaw ν (realPosition (step e))
  let S := commonIncrementProcess (realPosition (step e)) f 0
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν _
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν _ htrans))
  have hS : Measurable S := measurable_commonIncrementProcess _ _ _
  have hI : Integrable S μ := independent_commonWordIncrement_integrable ν hue _ (signed_direction_unit e) htrans
    (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f
  have hne : 0<μ {x | S x≠0} := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have hlim : Tendsto (fun H : ℕ => (H:ℝ)/C) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hC
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp (hlim.eventually (eventually_gt_atTop (fluctuationScale μ S R)))
  refine ⟨C,c₀,g₀,hC,hc,hg,H₀,fun H hH π => ?_⟩
  obtain ⟨hr,hspec⟩ := fluctuationRadius_spec μ S hS hI hne hR (hH₀ H hH)
  apply hseed _ hr.le H _ π
  change (H:ℝ)=C*fluctuationScale μ S (fluctuationRadius μ S ((H:ℝ)/C))
  rw [hspec]
  field_simp

end DirectionalTransience

end

end OAI
