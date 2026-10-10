import Mathlib
import OAI.Probability.Ballisticity.Estimates.CommonTrueRecord

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def FirstHighRecord {d : ℕ} (ℓ : Vector d) (J : ℝ) (X : Path d) (n : ℕ) : Prop :=
  TrueRecord ℓ X n ∧ J < dot (realPosition (X n)) ℓ ∧
    ∀ j < n, J < dot (realPosition (X j)) ℓ → ¬ TrueRecord ℓ X j

lemma measurableSet_firstHighRecord {d : ℕ} (ℓ : Vector d) (J : ℝ) (n : ℕ) :
    MeasurableSet {X : Path d | FirstHighRecord ℓ J X n} := by
  have hm j : MeasurableSet {X : Path d | J < dot (realPosition (X j)) ℓ} :=
    measurableSet_lt measurable_const ((measurable_of_countable (fun x : Lattice d => dot (realPosition x) ℓ)).comp (measurable_pi_apply j))
  simp only [FirstHighRecord, Set.ofPred_and, Set.ofPred_forall]
  exact (measurableSet_trueRecord ℓ n).inter ((hm n).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => by
      simpa only [imp_iff_not_or,Set.ofPred_or,Set.compl_ofPred] using
        (hm j).compl.union (measurableSet_trueRecord ℓ j).compl))

lemma firstHighRecord_unique {d : ℕ} (ℓ : Vector d) (J : ℝ) (X : Path d)
    {m n : ℕ} (hm : FirstHighRecord ℓ J X m) (hn : FirstHighRecord ℓ J X n) : m = n := by
  rcases lt_trichotomy m n with h | h | h
  · exact False.elim (hn.2.2 m h hm.2.1 hm.1)
  · exact h
  · exact False.elim (hm.2.2 n h hn.2.1 hn.1)

lemma annealed_exists_firstHighRecord {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (J : ℝ) :
    ∀ᵐ X ∂annealedLaw ν, ∃ n, FirstHighRecord ℓ J X n := by
  filter_upwards [htrans, annealed_trueRecords_unbounded ν ℓ htrans] with X ht hu
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (eventually_gt_atTop J))
  obtain ⟨n,hn,htrue⟩ := hu N
  have he : ∃ n, TrueRecord ℓ X n ∧ J < dot (realPosition (X n)) ℓ :=
    ⟨n,htrue,hN n hn.le⟩
  exact ⟨Nat.find he, (Nat.find_spec he).1, (Nat.find_spec he).2,
    fun j hj hjJ hjT => Nat.find_min he hj ⟨hjT,hjJ⟩⟩

def AdmissibleHighWord {d : ℕ} (ℓ : Vector d) (J : ℝ) (w : List (Direction d)) : Prop :=
  StrictRecord ℓ (wordPath 0 w) w.length ∧
  J < dot (realPosition (wordPath 0 w w.length)) ℓ ∧
  (∀ j ≤ w.length, 0 ≤ dot (realPosition (wordPath 0 w j)) ℓ) ∧
  ∀ j < w.length, J < dot (realPosition (wordPath 0 w j)) ℓ →
    StrictRecord ℓ (wordPath 0 w) j →
      ∃ k, j < k ∧ k < w.length ∧ dot (realPosition (wordPath 0 w k)) ℓ <
        dot (realPosition (wordPath 0 w j)) ℓ

lemma highWord_characterization {d : ℕ} (ℓ : Vector d) (J : ℝ)
    (w : List (Direction d)) (X : Path d) (hX : X ∈ wordCylinder 0 w) :
    (X ∈ NoDrop ℓ 0 ∧ FirstHighRecord ℓ J X w.length) ↔
      AdmissibleHighWord ℓ J w ∧
        (fun j => X (w.length+j)-wordPath 0 w w.length) ∈ NoDrop ℓ 0 := by
  have hzero : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot,realPosition]
  have hrec (j : ℕ) (hj : j ≤ w.length) := strictRecord_congr_prefix ℓ hj hX
  have hsuf : (fun j => X (w.length+j)-wordPath 0 w w.length) ∈ NoDrop ℓ 0 ↔
      X ∈ FutureNoDrop ℓ w.length := by
    rw [← hX w.length le_rfl]
    exact suffix_noDrop_iff ℓ X w.length
  constructor
  · rintro ⟨hD,hT,hJ,hfirst⟩
    refine ⟨⟨(hrec _ le_rfl).mp hT.1, ?_, ?_, ?_⟩, hsuf.mpr hT.2⟩
    · simpa only [hX _ le_rfl] using hJ
    · intro j hj
      simpa only [hzero,hX j hj] using hD j
    · intro j hj hjJ hjR
      have hfail := hfirst j hj (by simpa only [hX j hj.le] using hjJ)
      obtain ⟨k,hjk,hkn,hdrop⟩ := (not_trueRecord_before_true_iff ℓ X hj
        ((hrec j hj.le).mpr hjR) hT).mp hfail
      exact ⟨k,hjk,hkn,by simpa only [hX k hkn.le,hX j hj.le] using hdrop⟩
  · rintro ⟨⟨hR,hJ,hprefix,hfail⟩,hD⟩
    have ht : TrueRecord ℓ X w.length := ⟨(hrec _ le_rfl).mpr hR,hsuf.mp hD⟩
    refine ⟨(noDrop_iff_prefix_and_future ℓ 0 X w.length ht.2).mpr ?_, ht, ?_, ?_⟩
    · intro j hj
      simpa only [hzero,hX j hj] using hprefix j hj
    · simpa only [hX _ le_rfl] using hJ
    · intro j hj hjJ hjT
      obtain ⟨k,hjk,hkn,hk⟩ := hfail j hj (by simpa only [hX j hj.le] using hjJ)
        ((hrec j hj.le).mp hjT.1)
      have hd := hjT.2 (k-j)
      change dot (realPosition (X j)) ℓ ≤ dot (realPosition (X (j+(k-j)))) ℓ at hd
      rw [Nat.add_sub_of_le hjk.le] at hd
      have hk' := hk
      rw [← hX k hkn.le, ← hX j hj.le] at hk'
      exact (not_lt_of_ge hd) hk'

def HighWordEvent {d : ℕ} (ℓ : Vector d) (J : ℝ) (w : List (Direction d)) : Set (Path d) :=
  {X | X ∈ NoDrop ℓ 0 ∧ X ∈ wordCylinder 0 w ∧ FirstHighRecord ℓ J X w.length}

lemma measurableSet_highWordEvent {d : ℕ} (ℓ : Vector d) (J : ℝ) (w : List (Direction d)) :
    MeasurableSet (HighWordEvent ℓ J w) :=
  (measurableSet_noDrop ℓ 0).inter ((measurableSet_wordCylinder 0 w).inter
    (measurableSet_firstHighRecord ℓ J w.length))

lemma highWordEvent_disjoint {d : ℕ} (ℓ : Vector d) (J : ℝ) :
    Pairwise (fun u v : List (Direction d) => Disjoint (HighWordEvent ℓ J u) (HighWordEvent ℓ J v)) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  rintro X ⟨_,hcu,hu⟩ ⟨_,hcv,hv⟩
  have hlen := firstHighRecord_unique ℓ J X hu hv
  apply huv (word_eq_of_paths 0 u v hlen ?_)
  intro j hj
  exact (hcu j hj).symm.trans (hcv j (hlen ▸ hj))

lemma highWordEvent_nil {d : ℕ} (ℓ : Vector d) (J : ℝ) (hJ : 0 ≤ J) :
    HighWordEvent ℓ J ([] : List (Direction d)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro X ⟨_,hc,hT⟩
  have h0 := hc 0 (by simp)
  have hj := hT.2.1
  simp only [List.length_nil,h0,wordPath_zero] at hj
  have hz : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot,realPosition]
  rw [hz] at hj
  exact (not_lt_of_ge hJ) hj

lemma highWordEvent_eq {d : ℕ} (ℓ : Vector d) (J : ℝ) (w : List (Direction d))
    (hw : AdmissibleHighWord ℓ J w) :
    HighWordEvent ℓ J w = (fun X : Path d => fun j => X (w.length+j)-
      wordPath 0 w w.length) ⁻¹' NoDrop ℓ 0 ∩ wordCylinder 0 w := by
  ext X
  constructor
  · rintro ⟨hD,hc,hT⟩
    exact ⟨((highWord_characterization ℓ J w X hc).mp ⟨hD,hT⟩).2,hc⟩
  · rintro ⟨hD,hc⟩
    have h := (highWord_characterization ℓ J w X hc).mpr ⟨hw,hD⟩
    exact ⟨h.1,hc,h.2⟩

lemma highWordEvent_empty {d : ℕ} (ℓ : Vector d) (J : ℝ) (w : List (Direction d))
    (hw : ¬ AdmissibleHighWord ℓ J w) : HighWordEvent ℓ J w = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro X ⟨hD,hc,hT⟩
  exact hw ((highWord_characterization ℓ J w X hc).mp ⟨hD,hT⟩).1

noncomputable def highWord {d : ℕ} (ℓ : Vector d) (J : ℝ) (X : Path d) : List (Direction d) :=
  if h : ∃ w, X ∈ HighWordEvent ℓ J w then h.choose else []

lemma highWord_eq_iff {d : ℕ} (ℓ : Vector d) (J : ℝ) (X : Path d) (w : List (Direction d))
    (hw : w ≠ []) : highWord ℓ J X = w ↔ X ∈ HighWordEvent ℓ J w := by
  unfold highWord
  split_ifs with h
  · constructor
    · intro he
      exact he ▸ h.choose_spec
    · intro hX
      by_contra hne
      exact (Set.disjoint_left.mp (highWordEvent_disjoint ℓ J hne)) h.choose_spec hX
  · simp only [eq_comm (a := ([] : List (Direction d))), hw, false_iff]
    exact fun hX => h ⟨w,hX⟩

lemma highWord_nil_iff {d : ℕ} (ℓ : Vector d) (J : ℝ) (hJ : 0 ≤ J) (X : Path d) :
    highWord ℓ J X = [] ↔ ¬ ∃ w, X ∈ HighWordEvent ℓ J w := by
  unfold highWord
  split_ifs with h
  · simp only [h,not_true_eq_false,iff_false]
    intro he
    have hh := h.choose_spec
    rw [he,highWordEvent_nil ℓ J hJ] at hh
    exact hh
  · simp [h]

lemma measurable_highWord {d : ℕ} (ℓ : Vector d) (J : ℝ) (hJ : 0 ≤ J) :
    Measurable (highWord ℓ J) := by
  apply measurable_to_countable'
  intro w
  by_cases hw : w = []
  · subst w
    have he : highWord ℓ J ⁻¹' {[]} = (⋃ w, HighWordEvent ℓ J w)ᶜ := by
      ext X
      simp only [Set.mem_preimage,Set.mem_singleton_iff,highWord_nil_iff ℓ J hJ,
        Set.mem_compl_iff,Set.mem_iUnion]
    rw [he]
    exact (MeasurableSet.iUnion (measurableSet_highWordEvent ℓ J)).compl
  · have he : highWord ℓ J ⁻¹' {w} = HighWordEvent ℓ J w := by
      ext X
      exact highWord_eq_iff ℓ J X w hw
    rw [he]
    exact measurableSet_highWordEvent ℓ J w

noncomputable def highSuffix {d : ℕ} (ℓ : Vector d) (J : ℝ) (X : Path d) : Path d :=
  fun j => X ((highWord ℓ J X).length+j)-X (highWord ℓ J X).length

lemma measurable_highSuffix {d : ℕ} (ℓ : Vector d) (J : ℝ) (hJ : 0 ≤ J) :
    Measurable (highSuffix ℓ J) := by
  apply Measurable.of_eval
  intro j
  have hf : Measurable (fun X : Path d => (highWord ℓ J X).length) :=
    (measurable_of_countable List.length).comp (measurable_highWord ℓ J hJ)
  have heval : Measurable (fun p : Path d × ℕ => p.1 p.2) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply n
  exact (heval.comp (measurable_id.prodMk (hf.add_const j))).sub
    (heval.comp (measurable_id.prodMk hf))

lemma highSuffix_on_highWordEvent {d : ℕ} (ℓ : Vector d) (J : ℝ) (hJ : 0 ≤ J)
    (w : List (Direction d)) (X : Path d) (hX : X ∈ HighWordEvent ℓ J w) :
    highSuffix ℓ J X = fun j => X (w.length+j)-wordPath 0 w w.length := by
  have hw : w ≠ [] := by
    intro he
    rw [he,highWordEvent_nil ℓ J hJ] at hX
    exact hX
  unfold highSuffix
  rw [(highWord_eq_iff ℓ J X w hw).mpr hX,hX.2.1 w.length le_rfl]

lemma conditioned_highWord_exists {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (J : ℝ) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, ∃ w, X ∈ HighWordEvent ℓ J w := by
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  filter_upwards [conditionedLaw_noDrop ν ℓ,hac.ae_le (annealed_initial ν),
    hac.ae_le (annealed_nearest_neighbor ν),hac.ae_le (annealed_exists_firstHighRecord ν ℓ htrans J)]
    with X hD h0 hNN hT
  obtain ⟨n,hn⟩ := hT
  obtain ⟨w,hw,hc⟩ := exists_word_prefix X hNN n
  exact ⟨w,hD,by simpa only [h0] using hc,hw.symm ▸ hn⟩

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
