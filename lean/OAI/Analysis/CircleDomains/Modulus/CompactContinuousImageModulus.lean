import OAI.Analysis.CircleDomains.Probability.CompactMeasureContinuity
import OAI.Analysis.CircleDomains.Modulus.ModulusFiniteMesh

namespace OAI

/-! A continuous presentation inside a compact family avoiding zero has a
compact subfamily retaining every prescribed strict modulus threshold. -/
open Set Function Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

lemma measureFamilyModulus_zero_of_isEmpty
    {A Z : Type*} [IsEmpty A] [MeasurableSpace Z]
    (σ : Measure Z) (K : A → FiniteMeasure Z) : measureFamilyModulus A Z σ K = 0 := by
  apply le_antisymm _ bot_le
  have h := measureFamilyModulus_le_admissible σ K
    (h := fun _ => 0) measurable_const (fun a => isEmptyElim a)
  change measureFamilyModulus A Z σ K ≤ 0
  simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0),lintegral_zero] using h

lemma exists_compact_subfamily_of_continuous_image
    {X Z : Type*} [MetricSpace X] [CompleteSpace X] [SeparableSpace X] [Nonempty X]
    [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] {T : Set (FiniteMeasure Z)}
    (hT : IsCompact T) (hz : (0 : FiniteMeasure Z) ∉ T)
    (f : X → T) (hf : Continuous f) {c : ℝ≥0∞}
    (hc : c < measureFamilyModulus X Z σ (fun x => (f x).val)) :
    ∃ S : Set (FiniteMeasure Z), IsCompact S ∧ S ⊆ range (fun x => (f x).val) ∧
      c < measureFamilyModulus S Z σ (fun v => v.val) := by
  classical
  let : CompactSpace T := isCompact_iff_compactSpace.mp hT
  let : PolishSpace T := compact_finiteMeasure_polish hT
  let : MetricSpace T := metrizableSpaceMetric T
  obtain ⟨d,hcd,hd⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hc
  have hd0 : 0 < d := by
    have hp : (0 : ℝ≥0∞) < d := (show (0 : ℝ≥0∞) ≤ c from zero_le).trans_lt hcd
    exact_mod_cast hp
  have heq : measureFamilyModulus (univ : Set X) Z σ (fun x => (f x.val).val) =
      measureFamilyModulus X Z σ (fun x => (f x).val) := by
    apply measureFamilyModulus_eq_of_range_eq
    ext v
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.val,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x,mem_univ x⟩,rfl⟩
  obtain ⟨C,F,_,hC,hanti,hmesh,hlarge⟩ := exists_modulus_finite_mesh σ
    (fun x => (f x).val) isClosed_univ (c := (d : ℝ≥0∞)) (heq.symm ▸ hd)
  have hne (n : ℕ) : (C n).Nonempty := by
    by_contra hn
    let : IsEmpty (C n) := ⟨fun x => hn ⟨x.val,x.property⟩⟩
    have hm := hlarge n
    rw [measureFamilyModulus_zero_of_isEmpty] at hm
    exact (not_lt_of_ge bot_le) hm
  let U (n : ℕ) : Set (FiniteMeasure Z) := Subtype.val '' closure (f '' C n)
  have hUc (n : ℕ) : IsCompact (U n) := isClosed_closure.isCompact.image continuous_subtype_val
  have hUn (n : ℕ) : (U n).Nonempty := by
    obtain ⟨x,hx⟩ := hne n
    exact ⟨(f x).val,⟨f x,subset_closure (mem_image_of_mem f hx),rfl⟩⟩
  have hUa : Antitone U := fun n m hnm => image_mono (closure_mono (image_mono (hanti hnm)))
  have hUz : (0 : FiniteMeasure Z) ∉ U 0 := by
    rintro ⟨w,_,hw⟩
    exact hz (hw ▸ w.property)
  have hUl (n : ℕ) : (d : ℝ≥0∞) < measureFamilyModulus (U n) Z σ (fun v => v.val) := by
    apply (hlarge n).trans_le
    apply measureFamilyModulus_mono_range
    rintro _ ⟨x,rfl⟩
    exact ⟨⟨(f x.val).val,⟨f x.val,subset_closure (mem_image_of_mem f x.property),rfl⟩⟩,rfl⟩
  have hlow := compact_intersection_modulus_lower σ U hUc hUn hUa hUz hd0 hUl
  let S : Set (FiniteMeasure Z) := (fun x => (f x).val) '' (⋂ n, C n)
  have hSc : IsCompact S := (compact_iInter_of_finite_mesh C hC F hmesh).image
    (continuous_subtype_val.comp hf)
  have hIS : (⋂ n, U n) ⊆ S := by
    intro v hv
    obtain ⟨w,_,hwv⟩ := mem_iInter.mp hv 0
    have hw : w ∈ ⋂ n, closure (f '' C n) := by
      apply mem_iInter.mpr
      intro n
      obtain ⟨w',hw',he⟩ := mem_iInter.mp hv n
      have heq : w' = w := Subtype.ext (he.trans hwv.symm)
      exact heq ▸ hw'
    rw [← image_iInter_eq_iInter_closure_of_finite_mesh C hC hanti F hmesh f hf] at hw
    obtain ⟨x,hx,hfx⟩ := hw
    exact ⟨x,hx,(congrArg Subtype.val hfx).trans hwv⟩
  refine ⟨S,hSc,?_ ,hcd.trans_le (hlow.trans ?_)⟩
  · rintro v ⟨x,_,rfl⟩
    exact mem_range_self x
  · apply measureFamilyModulus_mono_range
    rintro _ ⟨v,rfl⟩
    exact ⟨⟨v.val,hIS v.property⟩,rfl⟩

end CircleDomainRigidity

end

end OAI
