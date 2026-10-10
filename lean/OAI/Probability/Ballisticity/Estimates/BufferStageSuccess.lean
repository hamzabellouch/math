import Mathlib
import OAI.Probability.Ballisticity.Estimates.RawPairEndpoint

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma rawPairEndpoint_integrand_measurable {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) : Measurable (fun p : Environment d × (Lattice d × Lattice d) =>
      ((quenchedKernel (p.1,p.2.1)).prod (quenchedKernel (p.1,p.2.2))).real
        (PairEndpointEvent ℓ f p.2.1 p.2.2 H z)) := by
  apply measurable_from_prod_countable_left
  intro x
  have hh := Kernel.measurable_coe (sharedPairKernel x.1 x.2)
    (measurableSet_pairEndpointEvent ℓ f x.1 x.2 H z)
  simpa only [sharedPairKernel,Kernel.prod_apply,fixedQuenchedKernel,Kernel.comap_apply,Measure.real] using hh.ennreal_toReal

lemma measurable_rawPairEndpointMass {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (π : Measure (Lattice d × Lattice d)) [SFinite π] :
    Measurable (rawPairEndpointMass ℓ f H z π) :=
  (rawPairEndpoint_integrand_measurable ℓ f H z).stronglyMeasurable.integral_prod_right.measurable

lemma central_retained_le_rawPair {d : ℕ} (e f : Direction d) (θ z b : ℝ)
    {h H : ℕ} (hh : 0 < h) (hhH : h ≤ H) (ω : Environment d)
    (π : Measure (Lattice d × Lattice d)) [IsProbabilityMeasure π]
    (hgap : ∀ᵐ x ∂π, b+2*z ≤ signedCoordinate f (x.2-x.1)) :
    pairCentralRetainedMass (realPosition (step e)) f θ z H π ω ≤
      rawPairEndpointMass (realPosition (step e)) f h b π ω := by
  have hC (x) := centralPrefixMass_bounds (realPosition (step e)) f θ z H ω x
  have hI : Integrable (fun x : Lattice d × Lattice d =>
      centralPrefixMass (realPosition (step e)) f θ z H ω x.1*
      centralPrefixMass (realPosition (step e)) f θ z H ω x.2) π :=
    (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hC _).1 (hC _).1)]
        exact (mul_le_of_le_one_left (hC _).1 (hC _).2).trans (hC _).2)
  have hJ : Integrable (fun x : Lattice d × Lattice d =>
      ((quenchedKernel (ω,x.1)).prod (quenchedKernel (ω,x.2))).real
        (PairEndpointEvent (realPosition (step e)) f x.1 x.2 h b)) π :=
    (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
  apply integral_mono_ae hI hJ
  filter_upwards [hgap] with x hx
  have hm (w : Lattice d) : centralPrefixMass (realPosition (step e)) f θ z H ω w ≤
      centralPrefixMass (realPosition (step e)) f θ z h ω w :=
    ENNReal.toReal_mono (measure_ne_top _ _) (quenchedTube_mono_height e f w θ z hh hhH ω)
  exact (mul_le_mul (hm x.1) (hm x.2) (hC x.2).1
    (centralPrefixMass_bounds _ _ _ _ _ _ _).1).trans
      (central_pair_mass_le e f x.1 x.2 θ z b hh ω hx)

lemma jump_retained_le_rawPair {d : ℕ} (e f : Direction d) (θ z a s b : ℝ)
    (hs : s=1 ∨ s= -1) {H : ℕ} (hH : 0 < H) (ω : Environment d)
    (π : Measure (Lattice d × Lattice d)) [IsProbabilityMeasure π]
    (hgap : ∀ᵐ x ∂π, b+z-a ≤ signedCoordinate f (x.2-x.1)) :
    pairJumpRetainedMass (realPosition (step e)) f θ z a s H π ω ≤
      rawPairEndpointMass (realPosition (step e)) f H b π ω := by
  have hC (x) := centralPrefixMass_bounds (realPosition (step e)) f θ z H ω x
  have hJ (x) := jumpPrefixMass_bounds (realPosition (step e)) f ((H:ℝ)*θ) a s H ω x
  have hI : Integrable (fun x : Lattice d × Lattice d =>
      jumpPrefixMass (realPosition (step e)) f ((H:ℝ)*θ) a s H ω (if s=1 then x.2 else x.1)*
      centralPrefixMass (realPosition (step e)) f θ z H ω (if s=1 then x.1 else x.2)) π :=
    (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hJ _).1 (hC _).1)]
        exact (mul_le_of_le_one_left (hC _).1 (hJ _).2).trans (hC _).2)
  have hK : Integrable (fun x : Lattice d × Lattice d =>
      ((quenchedKernel (ω,x.1)).prod (quenchedKernel (ω,x.2))).real
        (PairEndpointEvent (realPosition (step e)) f x.1 x.2 H b)) π :=
    (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
  apply integral_mono_ae hI hK
  filter_upwards [hgap] with x hx
  exact jump_central_pair_mass_le e f x.1 x.2 θ z a s b hs hH ω hx

def BufferStageSuccess {d : ℕ} (ℓ : Vector d) (f : Direction d) (H : ℕ)
    (z₀ r ε a g : ℝ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) : Prop :=
  (∀ h : ℕ, 0 < h → h ≤ H → g ≤ rawPairEndpointMass ℓ f h (z₀+(1-ε)*r) π ω) ∧
    g ≤ rawPairEndpointMass ℓ f H (z₀+(1+a)*r) π ω

lemma measurableSet_bufferStageSuccess {d : ℕ} (ℓ : Vector d) (f : Direction d) (H : ℕ)
    (z₀ r ε a g : ℝ) (π : Measure (Lattice d × Lattice d)) [SFinite π] :
    MeasurableSet {ω | BufferStageSuccess ℓ f H z₀ r ε a g π ω} := by
  unfold BufferStageSuccess
  apply MeasurableSet.inter
  · change MeasurableSet {ω | ∀ h : ℕ, 0 < h → h ≤ H → g ≤ rawPairEndpointMass ℓ f h (z₀+(1-ε)*r) π ω}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun h => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => measurableSet_le measurable_const
        (measurable_rawPairEndpointMass ℓ f h _ π)
  · exact measurableSet_le measurable_const (measurable_rawPairEndpointMass ℓ f H _ π)

theorem buffer_stage_success_probability {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ ε : ℝ, 0 < ε →
      ∃ g R : ℝ, 0 < g ∧ 0 < R ∧ ∀ r : ℝ, R ≤ r →
        let H := ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊
        0 < H ∧ ∀ z₀ : ℝ, ∀ π : Measure (Lattice d × Lattice d), IsProbabilityMeasure π →
          (∀ᵐ x ∂π, z₀+r ≤ signedCoordinate f (x.2-x.1)) →
          c ≤ (environmentLaw ν).real {ω | BufferStageSuccess (realPosition (step e)) f H z₀ r ε a g π ω} := by
  obtain ⟨a,j,c,ha,hj,hc,hfair⟩ := clipped_pair_favorable_fraction ν hue e f hef htrans
  refine ⟨a/4,c,by positivity,hc,fun ε hε => ?_⟩
  let δ := min (ε/4) (a/4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨d₀,R,hd,hR,hr⟩ := hfair δ hδ
  refine ⟨min (c*d₀^2) (c*(j*d₀)),R,lt_min (by positivity) (by positivity),hR,fun r hrr => ?_⟩
  obtain ⟨hH,θ,s,hs,hfrac⟩ := hr r hrr
  refine ⟨hH,fun z₀ π hπ hgap => ?_⟩
  have := hπ
  have hr0 : 0 ≤ r := (hR.trans_le hrr).le
  have heps : 2*δ ≤ ε := by have := min_le_left (ε/4) (a/4); dsimp [δ]; linarith
  have haδ : a/4+δ ≤ a := by have := min_le_right (ε/4) (a/4); dsimp [δ]; linarith
  refine (hfrac π hπ).trans (measureReal_mono ?_)
  intro ω hω
  obtain ⟨hcentral,hjump⟩ := pair_retained_mass_of_favorable_fraction (realPosition (step e)) f
    θ (δ*r) (a*r) s _ π ω hj.le hd.le hω
  constructor
  · intro h hh hhH
    refine (min_le_left _ _).trans (hcentral.trans
      (central_retained_le_rawPair e f θ (δ*r) (z₀+(1-ε)*r) hh hhH ω π ?_))
    filter_upwards [hgap] with x hx
    have := mul_le_mul_of_nonneg_right heps hr0
    linarith
  · refine (min_le_right _ _).trans (hjump.trans
      (jump_retained_le_rawPair e f θ (δ*r) (a*r) s (z₀+(1+a/4)*r) hs hH ω π ?_))
    filter_upwards [hgap] with x hx
    have := mul_le_mul_of_nonneg_right haδ hr0
    linarith
end DirectionalTransience

end

end

end OAI
