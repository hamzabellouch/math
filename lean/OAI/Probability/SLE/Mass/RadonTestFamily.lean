import OAI.Probability.SLE.Mass.RadonTestLimit
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UrysohnsLemma

namespace OAI

/-! A countable determining family on a second-countable locally compact
space, constructed from compact exhaustion and separability on compacts. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology CompactlySupported

namespace SLEExactGauge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

omit [LocallyCompactSpace X] in
/-- Compact support in a fixed compact set admits a countable uniformly
dense family, with the same support constraint. -/
theorem exists_compact_test_sequence (K : Set X) (hK : IsCompact K) :
    ∃ f : ℕ → C_c(X, ℝ), (∀ j, tsupport (f j) ⊆ K) ∧
      ∀ g : C_c(X, ℝ), tsupport g ⊆ K → ∀ ε : ℝ, 0 < ε →
        ∃ j, ∀ x, |g x-f j x| ≤ ε := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S : Set C(K, ℝ) := {g | ∃ f : C_c(X, ℝ), tsupport f ⊆ K ∧ ∀ x : K, g x=f x}
  have hzero : (0 : C(K, ℝ)) ∈ S := by
    refine ⟨0, ?_, fun _ => rfl⟩
    simp
  let : Nonempty S := ⟨⟨0,hzero⟩⟩
  obtain ⟨d,hd⟩ := TopologicalSpace.exists_dense_seq S
  have hrep (j : ℕ) : ∃ f : C_c(X, ℝ), tsupport f ⊆ K ∧ ∀ x : K, (d j).1 x=f x :=
    (d j).2
  choose f hf hrep using hrep
  refine ⟨f,hf,fun g hg ε hε => ?_⟩
  let r : C(K, ℝ) := ⟨fun x => g x, g.continuous.comp continuous_subtype_val⟩
  have hr : r ∈ S := ⟨g,hg,fun _ => rfl⟩
  obtain ⟨j,hj⟩ := Metric.denseRange_iff.mp hd ⟨r,hr⟩ ε hε
  refine ⟨j,fun x => ?_⟩
  by_cases hx : x ∈ K
  · have hb := ContinuousMap.norm_coe_le_norm (r-(d j).1) ⟨x,hx⟩
    have hb' : |g x-f j x| ≤ dist (⟨r,hr⟩ : S) (d j) := by
      change |g x-f j x| ≤ dist r (d j).1
      rw [dist_eq_norm]
      simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs, hrep j ⟨x,hx⟩, r,
        ContinuousMap.coe_mk] using hb
    exact hb'.trans hj.le
  · have hgx : g x=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hg h))
    have hfx : f j x=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hf j h))
    simpa only [hgx,hfx,sub_self,abs_zero] using hε.le

omit [SecondCountableTopology X] in
/-- One nonnegative compactly supported cutoff dominates one on a given
compact set. -/
theorem exists_compact_test_cutoff (K : Set X) (hK : IsCompact K) :
    ∃ f : C_c(X, ℝ), (∀ x, 0 ≤ f x) ∧ ∀ x ∈ K, 1 ≤ f x := by
  obtain ⟨f,hf,hfc,_,h01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    hK isOpen_univ (subset_univ K)
  refine ⟨⟨f,hfc⟩,fun x => (h01 x).1,fun x hx => ?_⟩
  change 1 ≤ f x
  rw [hf hx]
  rfl

/-- The determining family required by Radon reconstruction exists
without an additional density or cutoff hypothesis. -/
theorem exists_localTestFamily : Nonempty (LocalTestFamily X) := by
  classical
  let K := CompactExhaustion.choice X
  have hdense (n : ℕ) := exists_compact_test_sequence (K n) (K.isCompact n)
  choose f hf hfdense using hdense
  have hcut (n : ℕ) := exists_compact_test_cutoff (K n) (K.isCompact n)
  choose ψ hψ0 hψ1 using hcut
  let test (j : ℕ) : C_c(X, ℝ) :=
    match Encodable.decode (α := ℕ ⊕ (ℕ × ℕ)) j with
    | some (.inl n) => ψ n
    | some (.inr (n,k)) => f n k
    | none => 0
  have htest_cut (n : ℕ) : test (Encodable.encode (Sum.inl n : ℕ ⊕ (ℕ × ℕ)))=ψ n := by
    simp only [test, Encodable.encodek]
  have htest_dense (n j : ℕ) :
      test (Encodable.encode (Sum.inr (n,j) : ℕ ⊕ (ℕ × ℕ)))=f n j := by
    simp only [test, Encodable.encodek]
  refine ⟨{
    compactSet := K
    isCompact := K.isCompact
    exhaustive := fun _ h => K.exists_superset_of_isCompact h
    test := test
    cutoffIndex := fun n => Encodable.encode (Sum.inl n : ℕ ⊕ (ℕ × ℕ))
    cutoff_nonneg := ?_
    cutoff_one_le := ?_
    dense := ?_ }⟩
  · intro n x
    rw [htest_cut]
    exact hψ0 n x
  · intro n x hx
    rw [htest_cut]
    exact hψ1 n x hx
  · intro n g hg ε hε
    obtain ⟨j,hj⟩ := hfdense n g hg ε hε
    refine ⟨Encodable.encode (Sum.inr (n,j) : ℕ ⊕ (ℕ × ℕ)), ?_, ?_⟩
    · rw [htest_dense]
      exact hf n j
    · rw [htest_dense]
      exact hj

/-- A chosen countable family can be used for all times and all random
outcomes of a measure-valued construction. -/
def localTestFamily (X : Type*) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] : LocalTestFamily X :=
  Classical.choice exists_localTestFamily

end SLEExactGauge

end

end OAI
