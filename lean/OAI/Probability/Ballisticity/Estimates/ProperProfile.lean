import Mathlib
import OAI.Probability.Ballisticity.Stationary.ArrayMarkedEntropy
import OAI.Probability.Ballisticity.Walk.ProfileGrowth2

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def horizontalLayerEquiv {d : ℕ} (e : Direction d) : HorizontalSpace e ≃ HorizontalLayer e where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def IsProperProfile {d : ℕ} (e : Direction d) (w : HorizontalSpace e → ℝ≥0∞) : Prop :=
  (∀ z, 0<w z) ∧ (∑' z, w z)≤1

lemma isProperProfile_measurable {d : ℕ} (e : Direction d) :
    MeasurableSet {w | IsProperProfile e w} := by
  simp only [IsProperProfile,Set.ofPred_and,Set.ofPred_forall]
  exact (MeasurableSet.iInter fun z => measurableSet_lt measurable_const (measurable_pi_apply z)).inter
    (measurableSet_le (Measurable.tsum fun z => measurable_pi_apply z) measurable_const)

abbrev ProperProfile {d : ℕ} (e : Direction d) := {w : HorizontalSpace e → ℝ≥0∞ // IsProperProfile e w}

noncomputable def properProfileKernel {d : ℕ} (e : Direction d) : Kernel (ProperProfile e) (HorizontalLayer e) :=
  Kernel.mk (fun w => Measure.sum (fun z : HorizontalSpace e => w.1 z • Measure.dirac (horizontalLayerEquiv e z))) (by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.sum_apply _ hs,Measure.smul_apply,smul_eq_mul]
    exact Measurable.tsum fun z => ((measurable_pi_apply z).comp measurable_subtype_coe).mul_const _)

lemma properProfileKernel_apply {d : ℕ} (e : Direction d) (w : ProperProfile e) (z : HorizontalSpace e) :
    properProfileKernel e w {horizontalLayerEquiv e z}=w.1 z := by
  change (Measure.sum (fun y : HorizontalSpace e => w.1 y • Measure.dirac (horizontalLayerEquiv e y))) {horizontalLayerEquiv e z}=_
  rw [Measure.sum_apply _ (measurableSet_singleton _)]
  simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply' _ (measurableSet_singleton _)]
  rw [tsum_eq_single z]
  · simp
  · intro y hy
    simp [hy,(horizontalLayerEquiv e).injective.eq_iff]

lemma properProfileKernel_total {d : ℕ} (e : Direction d) (w : ProperProfile e) :
    properProfileKernel e w Set.univ≤1 := by
  change (Measure.sum (fun z : HorizontalSpace e => w.1 z • Measure.dirac (horizontalLayerEquiv e z))) Set.univ≤1
  simpa only [Measure.sum_apply _ MeasurableSet.univ,Measure.smul_apply,smul_eq_mul,Measure.dirac_apply_of_mem (Set.mem_univ _),mul_one] using w.2.2

instance properProfileKernel_finite {d : ℕ} (e : Direction d) : IsFiniteKernel (properProfileKernel e) :=
  ⟨⟨1,ENNReal.one_lt_top,properProfileKernel_total e⟩⟩

lemma properProfileKernel_full {d : ℕ} (e : Direction d) (w : ProperProfile e) (z : HorizontalLayer e) :
    0<(properProfileKernel e w).real {z} := by
  change 0<(properProfileKernel e w {z}).toReal
  rw [←(horizontalLayerEquiv e).apply_symm_apply z,properProfileKernel_apply]
  exact ENNReal.toReal_pos (w.2.1 _).ne' (ne_top_of_le_ne_top ENNReal.one_ne_top ((ENNReal.le_tsum _).trans w.2.2))

noncomputable def markedProfile {d : ℕ} (e : Direction d) (p : MarkedCurrentData e) : HorizontalSpace e → ℝ≥0∞ :=
  fun z => ENNReal.ofReal (p.1.2 (p.2,z):ℝ)

lemma markedProfile_measurable {d : ℕ} (e : Direction d) : Measurable (markedProfile e) := by
  apply Measurable.of_eval
  intro z
  exact Measurable.ennreal_ofReal ((measurable_from_prod_countable_left fun a =>
    ((measurable_pi_apply (a,z)).comp measurable_snd).subtype_val))

noncomputable def properData {d : ℕ} (e : Direction d) (w₀ : ProperProfile e) (p : MarkedCurrentData e) : ProperProfile e :=
  if h : IsProperProfile e (markedProfile e p) then ⟨markedProfile e p,h⟩ else w₀

lemma properData_measurable {d : ℕ} (e : Direction d) (w₀ : ProperProfile e) : Measurable (properData e w₀) := by
  apply Measurable.subtype_mk
  have he : (fun p => (properData e w₀ p).val)=(fun p => if IsProperProfile e (markedProfile e p) then markedProfile e p else w₀.1) := by
    funext p
    by_cases hp : IsProperProfile e (markedProfile e p) <;> simp [properData,hp]
  change Measurable (fun p => (properData e w₀ p).val)
  rw [he]
  exact Measurable.ite ((isProperProfile_measurable e).preimage (markedProfile_measurable e))
    (markedProfile_measurable e) measurable_const

lemma properData_eq {d : ℕ} (e : Direction d) (w₀ : ProperProfile e) (p : MarkedCurrentData e)
    (hp : IsProperProfile e (markedProfile e p)) : (properData e w₀ p).1=markedProfile e p := by
  simp only [properData,dite_eq_left hp]

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma marked_profile_proper (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) :
    ∀ᵐ p ∂markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event,
      IsProperProfile e (markedProfile e (markedData e p)) := by
  have h := markedArrayLaw_ae e (L.law : Measure (ActualEpisodeArray e)) G.event G.measurable_event
    (show ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), Y∈G.event →
      ArrayProfilesConsistent e Y ∧ ∀ i a z, 0<(Y.2.2.1 (i,(i,a),z):ℝ) from by
        filter_upwards [L.consistent,L.full_profiles hue htrans G] with Y hO hF hY
        exact ⟨hO.2,hF hY⟩)
  filter_upwards [h] with p hp
  exact ⟨fun z => ENNReal.ofReal_pos.mpr (hp.2 0 p.2 z),arrayProfileMass_total_le_one e p.1 hp.1 0 (0,p.2)⟩

lemma properProfile_nonempty (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) : Nonempty (ProperProfile e) := by
  have := markedArrayLaw_probability e (L.law : Measure (ActualEpisodeArray e)) G.event G.positive_event.ne'
  obtain ⟨p,hp⟩ := (L.marked_profile_proper hue htrans G).exists
  exact ⟨⟨_,hp⟩⟩

end StationaryArrayLaw
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

noncomputable def fillUpper {d : ℕ} (e : Direction d) (p : UpperRows e × Environment d) : Environment d :=
  rowGraft {x | 0 ≤ signedHeight e x} (upperEnvironment e p.1) p.2

lemma fillUpper_measurable {d : ℕ} (e : Direction d) : Measurable (fillUpper e) :=
  (rowGraft_measurable _).comp (((upperEnvironment_continuous e).measurable.comp measurable_fst).prodMk measurable_snd)

lemma fillUpper_eq {d : ℕ} (e : Direction d) (ξ : UpperRows e) (ω : Environment d)
    (x : Lattice d) (hx : 0 ≤ signedHeight e x) :
    fillUpper e (ξ,ω) x=upperEnvironment e ξ x := by simp [fillUpper,rowGraft,hx]

lemma fillUpper_reference {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν] :
    ((Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν)).prod (environmentLaw ν)).map (fillUpper e)=
      environmentLaw ν := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (fillUpper_measurable e),lintegral_prod _ (show Measurable (fun p => f (fillUpper e p)) from hf.comp (fillUpper_measurable e)).aemeasurable,
    ←upperField_map e ν 0]
  rw [lintegral_map ((show Measurable (fun p => f (fillUpper e p)) from hf.comp (fillUpper_measurable e)).lintegral_prod_right') ((upperField_measurable_rows e 0).mono (rowSigma_le _) le_rfl)]
  have he (η ξ : Environment d) : fillUpper e (upperField e 0 η,ξ)=rowGraft {x | 0 ≤ signedHeight e x} η ξ := by
    funext x
    by_cases hx : 0 ≤ signedHeight e x
    · simp only [fillUpper,rowGraft,Set.mem_ofPred_eq,ite_eq_left hx,upperEnvironment_restrict_eq e η x (by rw [signedHeight_projection]; exact_mod_cast hx)]
    · simp only [fillUpper,rowGraft,Set.mem_ofPred_eq,ite_eq_right hx]
  simp_rw [he]
  simpa only [Set.indicator_univ] using rowGraft_event_lintegral ν {x | 0 ≤ signedHeight e x}
    Set.univ MeasurableSet.univ f hf

lemma fillUpper_joint_reference {d : ℕ} {D : Type*} [MeasurableSpace D]
    (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (δ : Measure D) [IsFiniteMeasure δ] :
    ((δ.prod (Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν))).prod (environmentLaw ν)).map
      (fun p => (p.1.1,fillUpper e (p.1.2,p.2)))=δ.prod (environmentLaw ν) := by
  have hp : Measurable (fun p : (D × UpperRows e) × Environment d => (p.1.1,fillUpper e (p.1.2,p.2))) :=
    measurable_fst.fst.prodMk ((fillUpper_measurable e).comp (measurable_fst.snd.prodMk measurable_snd))
  apply Measure.ext_of_lintegral
  intro f hf
  have hfp : Measurable (fun p : (D × UpperRows e) × Environment d => f (p.1.1,fillUpper e (p.1.2,p.2))) := hf.comp hp
  rw [lintegral_map hf hp,lintegral_prod _ hfp.aemeasurable,
    lintegral_prod _ hfp.lintegral_prod_right'.aemeasurable,
    lintegral_prod _ hf.aemeasurable]
  apply lintegral_congr
  intro a
  have hm : Measurable (fun p : UpperRows e × Environment d => f (a,fillUpper e p)) :=
    hf.comp (measurable_const.prodMk (fillUpper_measurable e))
  rw [←lintegral_prod _ hm.aemeasurable]
  simpa only [Function.comp_apply,id_eq,fillUpper_reference e ν] using
    (lintegral_map (μ := (Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν)).prod (environmentLaw ν))
      (hf.comp (measurable_const.prodMk measurable_id)) (fillUpper_measurable e)).symm

lemma fillUpper_finite_entropy {d : ℕ} {Ω D : Type*} [MeasurableSpace Ω] [MeasurableSpace D]
    (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u : Ω → D) (hu : Measurable u) (ξ : Ω → UpperRows e) (hξ : Measurable ξ)
    (hkl : klDiv (μ.map (fun ω => (u ω,ξ ω)))
      ((μ.map u).prod (Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν)))≠∞) :
    klDiv ((μ.prod (environmentLaw ν)).map (fun p => (u p.1,fillUpper e (ξ p.1,p.2))))
      ((μ.map u).prod (environmentLaw ν))≠∞ := by
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let W := μ.map (fun ω => (u ω,ξ ω))
  let R := (μ.map u).prod (Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν))
  have : IsProbabilityMeasure W :=
    (Measure.isProbabilityMeasure_map_iff (hu.prodMk hξ).aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (μ.map u) :=
    (Measure.isProbabilityMeasure_map_iff hu.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure R := by dsimp only [R]; infer_instance
  have hp : Measurable (fun p : (D × UpperRows e) × Environment d => (p.1.1,fillUpper e (p.1.2,p.2))) :=
    measurable_fst.fst.prodMk ((fillUpper_measurable e).comp (measurable_fst.snd.prodMk measurable_snd))
  have hh := klDiv_map_le (W.prod (environmentLaw ν)) (R.prod (environmentLaw ν)) hp
  rw [StoppedWindow.same_auxiliary_cost] at hh
  have he : (W.prod (environmentLaw ν)).map (fun p => (p.1.1,fillUpper e (p.1.2,p.2)))=
      (μ.prod (environmentLaw ν)).map (fun p => (u p.1,fillUpper e (ξ p.1,p.2))) := by
    have hmap := Measure.map_prod_map μ (environmentLaw ν) (hu.prodMk hξ) measurable_id
    simp only [Measure.map_id] at hmap
    rw [show W.prod (environmentLaw ν)=_ from hmap,Measure.map_map hp ((hu.prodMk hξ).prodMap measurable_id)]
    rfl
  rw [he,fillUpper_joint_reference] at hh
  exact ne_top_of_le_ne_top hkl hh

end DirectionalTransience

end

end OAI
