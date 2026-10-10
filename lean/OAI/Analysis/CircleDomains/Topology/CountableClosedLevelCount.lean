import OAI.Analysis.CircleDomains.Topology.CompactLevelCount
import Mathlib.Topology.Compactness.SigmaCompact

namespace OAI

/-! Joint Borel measurability of distinct path intersections with a
countable union of closed level relations. Paths may retrace themselves.
-/

open Set Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X T : Type*} [MetricSpace X]
  [TopologicalSpace T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

private def indexedSeparatedHits (H : ℕ → Set (X × T)) (n : ℕ)
    (a : Fin n → ℕ) (r : ℝ) : Set (C(PathTime, X) × T) :=
  {p | ∃ s : Fin n → PathTime,
    (∀ i j, i ≠ j → r ≤ dist (p.1 (s i)) (p.1 (s j))) ∧
    ∀ i, (p.1 (s i), p.2) ∈ H (a i)}

omit [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
private theorem isClosed_indexedSeparatedHits
    {H : ℕ → Set (X × T)} (hH : ∀ n, IsClosed (H n))
    (n : ℕ) (a : Fin n → ℕ) (r : ℝ) : IsClosed (indexedSeparatedHits H n a r) := by
  let E : Set ((C(PathTime, X) × T) × (Fin n → PathTime)) :=
    {p | (∀ i j, i ≠ j → r ≤ dist (p.1.1 (p.2 i)) (p.1.1 (p.2 j))) ∧
      ∀ i, (p.1.1 (p.2 i), p.1.2) ∈ H (a i)}
  have he (i : Fin n) : Continuous
      (fun p : (C(PathTime, X) × T) × (Fin n → PathTime) => p.1.1 (p.2 i)) :=
    continuous_eval.comp (continuous_fst.fst.prodMk ((continuous_apply i).comp continuous_snd))
  have hE : IsClosed E := by
    have hs : IsClosed {p : (C(PathTime, X) × T) × (Fin n → PathTime) |
        ∀ i j, i ≠ j → r ≤ dist (p.1.1 (p.2 i)) (p.1.1 (p.2 j))} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_le continuous_const ((he i).dist (he j))
    have hm : IsClosed {p : (C(PathTime, X) × T) × (Fin n → PathTime) |
        ∀ i, (p.1.1 (p.2 i), p.1.2) ∈ H (a i)} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun i => (hH (a i)).preimage ((he i).prodMk continuous_fst.snd)
    exact hs.inter hm
  have hp : Prod.fst '' E = indexedSeparatedHits H n a r := by
    ext p
    constructor
    · rintro ⟨⟨_, s⟩, hs, rfl⟩
      exact ⟨s, hs⟩
    · rintro ⟨s, hs⟩
      exact ⟨(p, s), hs, rfl⟩
  rw [← hp]
  exact isClosedMap_fst_of_compactSpace E hE

theorem measurable_countable_closed_relation_path_count
    {H : ℕ → Set (X × T)} (hH : ∀ n, IsClosed (H n)) :
    Measurable (fun p : C(PathTime, X) × T =>
      pathImageCount {x | ∃ n, (x, p.2) ∈ H n} p.1) := by
  simp_rw [pathImageCount_eq_iSup]
  apply Measurable.iSup
  intro n
  apply measurable_const.piecewise _ measurable_const
  have he : {p : C(PathTime, X) × T |
      p.1 ∈ imageHitAtLeast {x | ∃ n, (x, p.2) ∈ H n} n} =
      ⋃ a : Fin n → ℕ, ⋃ m : ℕ, indexedSeparatedHits H n a (1 / ((m : ℝ) + 1)) := by
    ext p
    constructor
    · rintro ⟨s, hs, hmem⟩
      choose a ha using hmem
      obtain ⟨m, hm⟩ := exists_reciprocal_separation (p.1 ∘ s) hs
      exact mem_iUnion₂.mpr ⟨a, m, s, hm, ha⟩
    · intro hp
      obtain ⟨a, m, s, hsep, ha⟩ := mem_iUnion₂.mp hp
      refine ⟨s, ?_, fun i => ⟨a i, ha i⟩⟩
      intro i j hij
      by_contra hne
      have h := hsep i j hne
      change p.1 (s i) = p.1 (s j) at hij
      rw [hij, dist_self] at h
      have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      linarith
  change MeasurableSet {p : C(PathTime, X) × T |
    p.1 ∈ imageHitAtLeast {x | ∃ n, (x, p.2) ∈ H n} n}
  rw [he]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun m =>
    (isClosed_indexedSeparatedHits hH n a (1 / ((m : ℝ) + 1))).measurableSet

theorem measurable_sigmaCompact_chart_circle_count
    (π : ℂ → X) (hπ : Continuous π) {A : Set ℂ} (hA : IsSigmaCompact A)
    (f : ℂ → ℝ) (hf : ContinuousOn f A) :
    Measurable (fun p : C(PathTime, X) × UnitAddCircle =>
      pathImageCount (π '' (A ∩ {z | (f z : UnitAddCircle) = p.2})) p.1) := by
  obtain ⟨K, hK, hcover⟩ := hA
  let H : ℕ → Set (X × UnitAddCircle) := fun n =>
    (fun z => (π z, (f z : UnitAddCircle))) '' K n
  have hKA (n : ℕ) : K n ⊆ A := hcover ▸ subset_iUnion K n
  have hH (n : ℕ) : IsClosed (H n) :=
    ((hK n).image_of_continuousOn (hπ.continuousOn.prodMk
      ((AddCircle.continuous_mk' (1 : ℝ)).comp_continuousOn (hf.mono (hKA n))))).isClosed
  have hs (t : UnitAddCircle) : {x | ∃ n, (x, t) ∈ H n} =
      π '' (A ∩ {z | (f z : UnitAddCircle) = t}) := by
    ext x
    constructor
    · rintro ⟨n, z, hz, heq⟩
      exact ⟨z, ⟨hKA n hz, (Prod.mk.inj heq).2⟩, (Prod.mk.inj heq).1⟩
    · rintro ⟨z, ⟨hz, hzt⟩, rfl⟩
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ hz)
      exact ⟨n, z, hn, Prod.ext rfl hzt⟩
  simpa only [hs] using measurable_countable_closed_relation_path_count hH

theorem measurable_sigmaCompact_restricted_relation_path_count
    {A : Set X} (hA : IsSigmaCompact A) {H : Set (X × T)} (hH : IsClosed H) :
    Measurable (fun p : C(PathTime, X) × T =>
      pathImageCount (A ∩ {x | (x, p.2) ∈ H}) p.1) := by
  obtain ⟨K, hK, hcover⟩ := hA
  let R : ℕ → Set (X × T) := fun n => (K n ×ˢ univ) ∩ H
  have hR (n : ℕ) : IsClosed (R n) := ((hK n).isClosed.prod isClosed_univ).inter hH
  have hs (t : T) : {x | ∃ n, (x, t) ∈ R n} = A ∩ {x | (x, t) ∈ H} := by
    ext x
    change (∃ n, (x ∈ K n ∧ t ∈ (univ : Set T)) ∧ (x, t) ∈ H) ↔ _
    rw [← hcover]
    simp only [mem_univ, and_true, mem_inter_iff, mem_iUnion, mem_ofPred_eq, exists_and_right]
  simpa only [hs] using measurable_countable_closed_relation_path_count hR

end CircleDomainRigidity

end

end OAI
