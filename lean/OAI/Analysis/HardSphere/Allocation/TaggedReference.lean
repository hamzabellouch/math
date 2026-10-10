import Mathlib
import OAI.Analysis.HardSphere.Geometry.SiteGroups

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {Ω A G Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
  [Fintype A] [DecidableEq A] [Fintype G] [DecidableEq G]

def allocatedTagLaw (μ : Measure Ω) (I : G→Ω→Finset A) (κ : A→Kernel Ω Y)
    (g : G) : Measure Y := ∑i,κ i ∘ₘ (μ.restrict {ω | i∈I g ω})

lemma sum_allocatedTagLaw_le (μ : Measure Ω) (I : G→Ω→Finset A)
    (hI : ∀g i,MeasurableSet {ω | i∈I g ω}) (κ : A→Kernel Ω Y)
    (hd : ∀ω g g',g≠g' → Disjoint (I g ω) (I g' ω)) :
    ∑g,allocatedTagLaw μ I κ g ≤ ∑i,κ i ∘ₘ μ := by
  classical
  apply Measure.le_iff.2
  intro s hs
  have hbind (i : A) (ν : Measure Ω) : (κ i ∘ₘ ν) s=∫⁻ω,κ i ω s ∂ν :=
    Measure.bind_apply hs (κ i).aemeasurable
  simp only [allocatedTagLaw,Measure.finsetSum_apply,hbind]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  simp_rw [←lintegral_indicator (hI _ i)]
  rw [←lintegral_finsetSum _ (fun g _ ↦ ((κ i).measurable_coe hs).indicator (hI g i))]
  apply lintegral_mono
  intro ω
  let T : Finset G := Finset.univ.filter (fun g ↦ i∈I g ω)
  have hT : T.card≤1 := by
    rw [Finset.card_le_one]
    intro g hg g' hg'
    by_contra h
    exact Finset.disjoint_left.mp (hd ω g g' h) (Finset.mem_filter.mp hg).2 (Finset.mem_filter.mp hg').2
  calc
    (∑g,({ω | i∈I g ω}.indicator (fun ω ↦ κ i ω s)) ω)=∑g∈T,κ i ω s := by
      change _=∑g∈Finset.univ.filter (fun g ↦ i∈I g ω),κ i ω s
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro g _
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    _ ≤ κ i ω s := by
      rw [Finset.sum_const]
      simpa only [one_nsmul] using nsmul_le_nsmul_left (show 0≤κ i ω s from bot_le) hT
end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Sampling
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def groupSlot (M G : ℕ) (g : Fin G) : Fin M↪Fin (M*G) where
  toFun i := (finCongr (Nat.mul_comm G M)) (finProdFinEquiv (g,i))
  inj' := by
    intro i j h
    exact congrArg Prod.snd (finProdFinEquiv.injective ((finCongr _).injective h))

lemma groupSlot_ne {M G : ℕ} {g h : Fin G} (hgh : g≠h) (i j : Fin M) :
    groupSlot M G g i≠groupSlot M G h j := by
  intro he
  exact hgh (congrArg Prod.fst (finProdFinEquiv.injective ((finCongr _).injective he)))

def groupLabels {M G : ℕ} (a : Allocation (M*G) I) (g : Fin G) : Finset I :=
  match a with
  | none => ∅
  | some f => Finset.univ.image (fun i ↦ f (groupSlot M G g i))

omit [Fintype I] in
lemma groupLabels_disjoint {M G : ℕ} (a : Allocation (M*G) I)
    {g h : Fin G} (hgh : g≠h) : Disjoint (groupLabels a g) (groupLabels a h) := by
  cases a with
  | none => simp [groupLabels]
  | some f =>
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hj
    exact groupSlot_ne hgh j k (f.injective hk.symm)

def fieldGroup {M G : ℕ} (E : V→Finset I) (a : V→Allocation (M*G) I)
    (g : Fin G) : Finset I :=
  Finset.univ.biUnion (fun v ↦ groupLabels (a v) g∩E v)

omit [Fintype I] in
lemma fieldGroup_disjoint {M G : ℕ} (E : V→Finset I)
    (hd : ∀v w,v≠w→Disjoint (E v) (E w)) (a : V→Allocation (M*G) I)
    {g h : Fin G} (hgh : g≠h) : Disjoint (fieldGroup E a g) (fieldGroup E a h) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨w,_,hw⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨hvg,hvE⟩ := Finset.mem_inter.mp hv
  obtain ⟨hwh,hwE⟩ := Finset.mem_inter.mp hw
  by_cases hvw : v=w
  · subst w
    exact Finset.disjoint_left.mp (groupLabels_disjoint (a v) hgh) hvg hwh
  · exact Finset.disjoint_left.mp (hd v w hvw) hvE hwE

omit [DecidableEq V] in
lemma fieldGroup_measurable {M G : ℕ} (g : Fin G) :
    Measurable (fun p : (V→Finset I)×(V→Allocation (M*G) I) ↦ fieldGroup p.1 p.2 g) :=
  measurable_of_countable _

omit [Fintype I] in
lemma groupLabels_subset_supported {M G : ℕ} (E : Finset I)
    (a : Allocation (M*G) I) (ha : a∈(allocationPMF E (M*G)).support) (g : Fin G) :
    groupLabels a g⊆E := by
  cases a with
  | none => simp [groupLabels]
  | some f =>
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact allocationPMF_support E (M*G) (some f) ha f rfl _

omit [Fintype I] [DecidableEq V] in
lemma fieldGroup_eq_raw_supported {M G : ℕ} (E : V→Finset I)
    (a : V→Allocation (M*G) I) (ha : ∀v,a v∈(allocationPMF (E v) (M*G)).support)
    (g : Fin G) :
    fieldGroup E a g=Finset.univ.biUnion (fun v ↦ groupLabels (a v) g) := by
  unfold fieldGroup
  congr 1
  funext v
  exact Finset.inter_eq_left.mpr (groupLabels_subset_supported (E v) (a v) (ha v) g)

omit [DecidableEq I] [DecidableEq V] in
lemma siteAllocation_supported (E : V→Finset I) (total : ℕ) :
    siteAllocationKernel total E {a | ∀v,a v∈(allocationPMF (E v) total).support}=1 := by
  change Measure.pi (fun v ↦ (allocationPMF (E v) total).toMeasure) _=1
  have he : {a : V→Allocation total I | ∀v,a v∈(allocationPMF (E v) total).support}=
      Set.univ.pi (fun v ↦ (allocationPMF (E v) total).support) := by ext a; simp
  rw [he,Measure.pi_pi]
  apply Finset.prod_eq_one
  intro v _
  exact (PMF.toMeasure_apply_eq_one_iff _ (MeasurableSet.of_discrete)).mpr (Subset.refl _)

end HardSphere.Sampling

namespace HardSphere.Groups
open Sampling Wiener PathCutoff Comparison

def allocatedPhysicalGroup {N K M G : ℕ} {L : Length} (m : ℕ)
    (r R C S s₀ : ℝ) (u : Time) (g : Fin G)
    (p : ConfigurationPath N L×((Fin 3→Fin K)→Allocation (M*G) (Fin N))) : Finset (Fin N) :=
  fieldGroup (fun v ↦ eligibleList m r R C S s₀ u v p.1) p.2 g

lemma allocatedPhysicalGroup_mem_measurable {N K M G : ℕ} {L : Length} (m : ℕ)
    (r R C S s₀ : ℝ) (u : Time) (g : Fin G) (i : Fin N) :
    MeasurableSet {p : ConfigurationPath N L×((Fin 3→Fin K)→Allocation (M*G) (Fin N)) |
      i∈allocatedPhysicalGroup m r R C S s₀ u g p} := by
  have he : {p : ConfigurationPath N L×((Fin 3→Fin K)→Allocation (M*G) (Fin N)) |
      i∈allocatedPhysicalGroup m r R C S s₀ u g p}=
      ⋃v : Fin 3→Fin K, {p | i∈groupLabels (p.2 v) g}∩
        {p | Eligible m r R C S s₀ u v i p.1} := by
    ext p
    simp [allocatedPhysicalGroup,fieldGroup,eligibleList]
  rw [he]
  apply MeasurableSet.iUnion
  intro v
  have ha : MeasurableSet {a : (Fin 3→Fin K)→Allocation (M*G) (Fin N) | i∈groupLabels (a v) g} :=
    MeasurableSet.of_discrete
  exact (ha.preimage measurable_snd).inter ((eligible_measurable m r R C S s₀ u v i).preimage measurable_fst)

lemma allocatedPhysicalGroup_disjoint {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (p : ConfigurationPath N L×((Fin 3→Fin K)→Allocation (M*G) (Fin N)))
    {g h : Fin G} (hgh : g≠h) :
    Disjoint (allocatedPhysicalGroup m r R C S s₀ u g p)
      (allocatedPhysicalGroup m r R C S s₀ u h p) :=
  fieldGroup_disjoint _ (fun _ _ hh ↦ eligibleList_disjoint hL hK m r R C S s₀ u p.1 hh) _ hgh

lemma allocatedPhysicalTag_sum_le {N K M G : ℕ} {L : Length}
    {Y : Type*} [MeasurableSpace Y]
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (μ : Measure (ConfigurationPath N L×((Fin 3→Fin K)→Allocation (M*G) (Fin N))))
    (κ : Fin N→Kernel (ConfigurationPath N L×((Fin 3→Fin K)→Allocation (M*G) (Fin N))) Y) :
    (∑g,allocatedTagLaw μ (allocatedPhysicalGroup m r R C S s₀ u) κ g)≤∑i,κ i ∘ₘ μ := by
  apply sum_allocatedTagLaw_le
  · intro g i
    exact allocatedPhysicalGroup_mem_measurable (N:=N) (K:=K) (M:=M) (L:=L) m r R C S s₀ u g i
  · intro p g h hgh
    exact allocatedPhysicalGroup_disjoint hL hK m r R C S s₀ u p hgh

end HardSphere.Groups

end
end

end

end OAI
