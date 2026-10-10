import Mathlib
import OAI.Analysis.HardSphere.Allocation.GroupJoint
import OAI.Analysis.HardSphere.Allocation.TaggedReference
import OAI.Analysis.HardSphere.Allocation.NearLift
import OAI.Analysis.HardSphere.Allocation.PhysicalTargets

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma physicalDatum_home {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (g : Fin G) (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (ω : ConfigurationPath N L) (a : GridAllocation N K (G*M))
    (v : Fin 3 → Fin K) (i : Fin N) (hi : Eligible m r R C S s₀ u v i ω) :
    datumHome hL (physicalDatum g m r R C S s₀ u (ω,a)) i=v :=
  (gridHome_eq_iff hL hK (ω 0 i) v).mpr hi.1.1

lemma full_success_datum {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (g : Fin G) (n : ℕ) (t r R C S s₀ : ℝ) (w : Time)
    (ω : ConfigurationPath N L) (a : GridAllocation N K (G*M))
    (v : Fin 3 → Fin K) (i : Fin N)
    (hi : Eligible (n+n) r R C S s₀ (prefixTime midpointTime w) v i ω)
    (his : i∈groupUnion g a)
    (hs : StrongExcept n t r R C S w
      (nearestLift L (anchorPoint v) (ω 0 i)) (nearestLift L (anchorPoint v) (ω 1 i))
      (anchorPoint v) (fun j ↦ onePathAt j ω) i (fun j ↦ unitTarget (anchorPoint v+targetStep j))) :
    datumAccessible hL g (n+n) t r R C S (prefixTime midpointTime w) i
      (physicalDatum g (n+n) r R C S s₀ (prefixTime midpointTime w) (ω,a)) := by
  let d := physicalDatum g (n+n) r R C S s₀ (prefixTime midpointTime w) (ω,a)
  have hh : datumHome hL d i=v := physicalDatum_home hL hK g _ _ _ _ _ _ _ ω a v i hi
  have hy : datumStart hL d i=nearestLift L (anchorPoint v) (ω 0 i) := by
    unfold datumStart
    rw [hh]
    rfl
  have hz : datumEnd hL d i=nearestLift L (anchorPoint v) (ω 1 i) := by
    unfold datumEnd
    rw [hh]
    rfl
  change ∀j : Fin 7, _ ≤ volume (Prod.mk d ⁻¹' datumTarget hL g (n+n) t r R C S (prefixTime midpointTime w) i j)
  intro j
  have hsj := hs j
  rw [Measure.restrict_apply₀] at hsj
  · refine hsj.trans (measure_mono ?_)
    intro U hU
    refine ⟨?_,?_⟩
    · change U∈unitTarget (anchorPoint (datumHome hL d i)+targetStep j)
      simpa only [hh] using hU.2
    · change ENNReal.ofReal (9/10:ℝ)≤datumSuccess hL g (n+n) t r R C S (prefixTime midpointTime w) i (d,U)
      refine hU.1.trans ?_
      unfold datumSuccess
      rw [hy,hz]
      rw [←trialKernel_pin]
      apply measure_mono
      intro f hf
      change Regular (n+n) r R C (prefixTime midpointTime w) S (projectCurve L f) ∧
        TrialConfined L (anchorPoint (datumHome hL d i)) f ∧
        f∈fixedEndpoints (datumStart hL d i) (datumEnd hL d i) ∧ _
      rw [hh,hy,hz]
      refine ⟨hf.1.1.1,hf.1.1.2,hf.2,?_⟩
      intro k hk
      have hk' : k∉groupUnion g a := hk
      have hki : k≠i := by intro he; exact hk' (he ▸ his)
      simpa only [d,physicalDatum,ite_eq_right hk'] using hf.1.2 k hki
  · exact (measurableSet_le measurable_const ((trialKernel t _ _).measurable_coe
      (successExcept_measurable n r R C S w (anchorPoint v) (fun j ↦ onePathAt j ω) i))).nullMeasurableSet

def fullFailure {N K : ℕ} {L : Length} (n : ℕ) (t r R C S : ℝ) (w : Time)
    (v : Fin 3 → Fin K) (ω : ConfigurationPath N L) : Finset (Fin N) :=
  Finset.univ.filter fun i ↦ ¬StrongExcept n t r R C S w
    (nearestLift L (anchorPoint v) (ω 0 i)) (nearestLift L (anchorPoint v) (ω 1 i))
    (anchorPoint v) (fun j ↦ onePathAt j ω) i (fun j ↦ unitTarget (anchorPoint v+targetStep j))

lemma allocation_some_of_supported {I : Type*} [Fintype I] [DecidableEq I]
    (E : Finset I) (total : ℕ) (hE : total≤E.card) (a : Allocation total I)
    (ha : a∈(allocationPMF E total).support) : ∃f,a=some f := by
  have : Nonempty (Fin total↪E) := Function.Embedding.nonempty_of_card_le (by simpa using hE)
  rw [allocationPMF_large E total hE,PMF.support_map] at ha
  obtain ⟨f,_,rfl⟩ := ha
  exact ⟨_,rfl⟩

lemma datumBad_forces_half_failure {N K G q : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (g : Fin G)
    (n : ℕ) (t r R C S s₀ : ℝ) (w : Time) (v : Fin 3 → Fin K)
    (ω : ConfigurationPath N L) (a : GridAllocation N K (G*(2*q)))
    (ha : a v∈(allocationPMF (eligibleList (n+n) r R C S s₀ (prefixTime midpointTime w) v ω) (G*(2*q))).support)
    (hE : G*(2*q)≤(eligibleList (n+n) r R C S s₀ (prefixTime midpointTime w) v ω).card)
    (hb : v∈datumBad hL g (n+n) t r R C S (prefixTime midpointTime w)
      (physicalDatum g (n+n) r R C S s₀ (prefixTime midpointTime w) (ω,a))) :
    ∃f,a v=some f ∧ q≤(Finset.univ.filter fun k ↦
      f (groupPosition (2*q) G g k)∈fullFailure n t r R C S w v ω).card := by
  obtain ⟨f,hf⟩ := allocation_some_of_supported _ _ hE (a v) ha
  refine ⟨f,hf,?_⟩
  let d := physicalDatum g (n+n) r R C S s₀ (prefixTime midpointTime w) (ω,a)
  let P : Fin (2*q) → Prop := fun k ↦ f (groupPosition (2*q) G g k)∈fullFailure n t r R C S w v ω
  let good := Finset.univ.filter fun k ↦ ¬P k
  have hinj : Function.Injective (fun k ↦ f (groupPosition (2*q) G g k)) :=
    f.injective.comp (groupPosition (2*q) G g).injective
  have hsub : good.image (fun k ↦ f (groupPosition (2*q) G g k))⊆
      datumAccessibleLabels hL g (n+n) t r R C S (prefixTime midpointTime w) v d := by
    intro i hi
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hi
    have hiE := allocationPMF_support _ _ _ ha f hf (groupPosition (2*q) G g k)
    have hel := (Finset.mem_filter.mp hiE).2
    have hsel : f (groupPosition (2*q) G g k)∈groupUnion g a :=
      Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ v,by simp [groupAt,hf]⟩
    have hstrong : StrongExcept n t r R C S w
        (nearestLift L (anchorPoint v) (ω 0 (f (groupPosition (2*q) G g k))))
        (nearestLift L (anchorPoint v) (ω 1 (f (groupPosition (2*q) G g k))))
        (anchorPoint v) (fun j ↦ onePathAt j ω) (f (groupPosition (2*q) G g k))
        (fun j ↦ unitTarget (anchorPoint v+targetStep j)) := by
      have hh := (Finset.mem_filter.mp hk).2
      simpa only [P,fullFailure,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hh
    exact Finset.mem_filter.mpr ⟨hsel,physicalDatum_home hL hK g _ _ _ _ _ _ _ ω a v _ hel,
      full_success_datum hL hK g n t r R C S s₀ w ω a v _ hel hsel hstrong⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hcard
  have hbad := (Finset.mem_filter.mp hb).2
  have hc := Finset.card_filter_add_card_filter_not (s:=Finset.univ) P
  simp only [Finset.card_univ,Fintype.card_fin] at hc
  change (Finset.univ.filter P).card+good.card=2*q at hc
  change q≤(Finset.univ.filter P).card
  change 2*(datumAccessibleLabels hL g (n+n) t r R C S (prefixTime midpointTime w) v d).card<2*q at hbad
  omega

theorem physicalDatum_joint_half_failure {N K G q : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (g : Fin G)
    (n : ℕ) (t r R C S s₀ : ℝ) (w : Time) (ω : ConfigurationPath N L)
    (T : Finset (Fin 3 → Fin K))
    (hE : ∀v∈T,G*(2*q)≤(eligibleList (n+n) r R C S s₀ (prefixTime midpointTime w) v ω).card)
    (hB : ∀v∈T,10*((eligibleList (n+n) r R C S s₀ (prefixTime midpointTime w) v ω)∩
      fullFailure n t r R C S w v ω).card≤(eligibleList (n+n) r R C S s₀ (prefixTime midpointTime w) v ω).card) :
    physicalAllocationKernel (n+n) (G*(2*q)) r R C S s₀ (prefixTime midpointTime w) ω
      {a | ∀v∈T,v∈datumBad hL g (n+n) t r R C S (prefixTime midpointTime w)
        (physicalDatum g (n+n) r R C S s₀ (prefixTime midpointTime w) (ω,a))}≤
      ENNReal.ofReal ((2/5:ℝ)^q)^T.card := by
  let E := fun v : Fin 3 → Fin K ↦ eligibleList (n+n) r R C S s₀ (prefixTime midpointTime w) v ω
  change siteAllocationKernel (G*(2*q)) E _≤_
  have hs : ∀ᵐa ∂siteAllocationKernel (G*(2*q)) E,
      ∀v,a v∈(allocationPMF (E v) (G*(2*q))).support := by
    rw [ae_iff_measure_eq (MeasurableSet.of_discrete : MeasurableSet {a : GridAllocation N K (G*(2*q)) | ∀v,a v∈(allocationPMF (E v) (G*(2*q))).support}).nullMeasurableSet]
    simpa only [measure_univ] using siteAllocation_supported E (G*(2*q))
  refine (measure_mono_ae ?_).trans
    (siteAllocation_joint_half_bad E (fun v ↦ fullFailure n t r R C S w v ω)
      (G*(2*q)) q (groupPosition (2*q) G g) T hE hB)
  filter_upwards [hs] with a ha
  intro hb v hv
  exact datumBad_forces_half_failure hL hK g n t r R C S s₀ w v ω a (ha v) (hE v hv) (hb v hv)

theorem canonical_supply_counts {ell b Alo A H : ℝ}
    (hell : 0<ell) (hb : 0<b) (hAlo : 0<Alo) (hA : 0<A) (hH : 0<H) :
    ∃t₀ : ℝ,0<t₀ ∧ ∀t : ℝ,0<t → t≤t₀ →
    ∃D₀ : ℝ,1≤D₀ ∧ ∀D α : ℝ,D₀≤D → Alo≤α → α≤A →
    ∀(N K n : ℕ) [Nontrivial (Fin N)] (L : Length),50<L.val →
    n=⌈t/(α/D)^2⌉₊ → ∀w : Time,t*(w:ℝ)=D⁻¹ →
    ∀θ : ℝ,θ≤ell/6 → ∀v : Fin 3→Fin K,∀ω : ConfigurationPath N L,
    Certificate (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) ell θ H D (prefixTime midpointTime w) v ω →
    let E := eligibleList (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (prefixTime midpointTime w) v ω
    ell*D/2≤(E.card:ℝ) ∧ 10*(E∩fullFailure n t (α/D) (D^(1/12:ℝ))
      (64*(meanCost+1)) (b*D^(-(1/3):ℝ)/8) w v ω).card≤E.card := by
  obtain ⟨t₀,ht₀,hs⟩ := canonical_certificate_useful_list hell hb hAlo hA hH
  refine ⟨t₀,ht₀,?_⟩
  intro t ht htt
  obtain ⟨D₀,hD₀,hs⟩ := hs t ht htt
  refine ⟨D₀,hD₀,?_⟩
  intro D α hD hαlo hαhi N K n _ L hL hn w hw θ hθ v ω hc
  let E := eligibleList (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (prefixTime midpointTime w) v ω
  let e := (E.equivFinOfCardEq rfl).symm
  let f : Fin E.card → Fin N := fun k ↦ (e k).val
  have hinj : Function.Injective f := fun i j h ↦ e.injective (Subtype.ext h)
  have himage : Finset.univ.image f=E := by
    ext i
    constructor
    · intro hi
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
      exact (e k).property
    · intro hi
      exact Finset.mem_image.mpr ⟨e.symm ⟨i,hi⟩,Finset.mem_univ _,by simp [f]⟩
  have hh := hs D α hD hαlo hαhi N K E.card n L hL hn w hw θ hθ v (anchorPoint v)
    (anchorPoint_project L v) ω hc f hinj himage
    (fun j ↦ unitTarget (anchorPoint v+targetStep j))
    (fun j ↦ unitTarget_measurable _) (fun j ↦ unitTarget_volume _) (targetCell_radius (anchorPoint v))
  have hlo := (eligible_list_size (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) ell θ H D
      (by linarith) hθ (prefixTime midpointTime w) v ω hc f hinj himage).1
  refine ⟨hlo,?_⟩
  let B := fullFailure n t (α/D) (D^(1/12:ℝ)) (64*(meanCost+1)) (b*D^(-(1/3):ℝ)/8) w v ω
  have he : (Finset.univ.filter fun k ↦ f k∈B).image f=E∩B := by
    ext i
    constructor
    · intro hi
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_inter.mpr ⟨(e k).property,(Finset.mem_filter.mp hk).2⟩
    · intro hi
      obtain ⟨hiE,hiB⟩ := Finset.mem_inter.mp hi
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp (himage.symm ▸ hiE)
      exact Finset.mem_image.mpr ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hiB⟩,rfl⟩
  have hcard := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ hinj] at hcard
  have hbnd : ((E∩B).card:ℝ)≤(E.card:ℝ)/10 := by
    rw [←hcard]
    simpa only [B,fullFailure,Finset.mem_filter,Finset.mem_univ,true_and] using hh
  have hreal : (10:ℝ)*((E∩B).card:ℝ)≤(E.card:ℝ) := by linarith
  exact_mod_cast hreal

lemma physical_bad_joint_of_certified_counts {N K G q : ℕ} [NeZero K]
    [Nontrivial (Fin N)] {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (n : ℕ) (t r R C S s₀ ell θ H D : ℝ) (w : Time)
    (μ : Measure (ConfigurationPath N L)) [SFinite μ] (p : ℝ≥0∞)
    (hjoint : ∀A : Finset (Fin 3→Fin K),μ {ω | ∀v∈A,
      ¬Certificate (n+n) r R C S s₀ ell θ H D (prefixTime midpointTime w) v ω}≤p^A.card)
    (hcount : ∀v : Fin 3→Fin K,∀ω : ConfigurationPath N L,
      Certificate (n+n) r R C S s₀ ell θ H D (prefixTime midpointTime w) v ω →
      G*(2*q)≤(eligibleList (n+n) r R C S s₀ (prefixTime midpointTime w) v ω).card ∧
      10*((eligibleList (n+n) r R C S s₀ (prefixTime midpointTime w) v ω)∩
        fullFailure n t r R C S w v ω).card≤
        (eligibleList (n+n) r R C S s₀ (prefixTime midpointTime w) v ω).card)
    (A : Finset (Fin 3→Fin K)) :
    ((μ.compProd (physicalAllocationKernel (n+n) (G*(2*q)) r R C S s₀ (prefixTime midpointTime w))).map
      (physicalDatum g (n+n) r R C S s₀ (prefixTime midpointTime w)))
      {d | A⊆datumBad hL g (n+n) t r R C S (prefixTime midpointTime w) d}≤
      (p+ENNReal.ofReal ((2/5:ℝ)^q))^A.card := by
  have hK : 1≤K := Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)
  have hbad (v : Fin 3→Fin K) : MeasurableSet {z : ConfigurationPath N L×GridAllocation N K (G*(2*q)) |
      v∈datumBad hL g (n+n) t r R C S (prefixTime midpointTime w)
        (physicalDatum g (n+n) r R C S s₀ (prefixTime midpointTime w) z)} :=
    ((datumBad_measurable (M:=2*q) hL g (n+n) t r R C S (prefixTime midpointTime w)).comp
      (physicalDatum_measurable g (n+n) r R C S s₀ (prefixTime midpointTime w)))
      ((Set.to_countable {B : Finset (Fin 3→Fin K) | v∈B}).measurableSet)
  have hEvent : MeasurableSet {d : PhysicalDatum N K (2*q) G L |
      A⊆datumBad hL g (n+n) t r R C S (prefixTime midpointTime w) d} :=
    (datumBad_measurable hL g (n+n) t r R C S (prefixTime midpointTime w))
      ((Set.to_countable {B : Finset (Fin 3→Fin K) | A⊆B}).measurableSet)
  rw [Measure.map_apply (physicalDatum_measurable g (n+n) r R C S s₀ (prefixTime midpointTime w)) hEvent]
  have H := certified_allocated_joint μ (physicalAllocationKernel (K:=K) (n+n) (G*(2*q)) r R C S s₀ (prefixTime midpointTime w))
    (fun v ω ↦ Certificate (n+n) r R C S s₀ ell θ H D (prefixTime midpointTime w) v ω)
    (fun v z ↦ v∈datumBad hL g (n+n) t r R C S (prefixTime midpointTime w)
      (physicalDatum g (n+n) r R C S s₀ (prefixTime midpointTime w) z))
    (fun v ↦ certificate_measurable _ _ _ _ _ _ _ _ _ _ _ v) hbad p
    (ENNReal.ofReal ((2/5:ℝ)^q)) hjoint
    (fun ω T hc ↦ physicalDatum_joint_half_failure hL hK g n t r R C S s₀ w ω T
      (fun v hv ↦ (hcount v ω (hc v hv)).1) (fun v hv ↦ (hcount v ω (hc v hv)).2)) A
  refine (measure_mono ?_).trans H
  intro z hz v hv
  exact Or.inr (hz hv)

end HardSphere.Groups
end
end

end OAI
