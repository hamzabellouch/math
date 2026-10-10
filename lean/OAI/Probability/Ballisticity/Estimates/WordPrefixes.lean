import Mathlib
import OAI.Probability.Ballisticity.Estimates.RelativeBudget

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma wordPath_take {d : ℕ} (x : Lattice d) (w : List (Direction d)) (n i : ℕ)
    (hi : i≤n) : wordPath x (w.take n) i=wordPath x w i := by
  by_cases hn : n≤w.length
  · have hp := wordPath_append_prefix x (w.take n) (w.drop n)
      (n:=i) (by simpa only [List.length_take,Nat.min_eq_left hn] using hi)
    simpa only [List.take_append_drop] using hp.symm
  · rw [List.take_of_length_le (by omega)]

noncomputable def wordPrefix {d : ℕ} (e : Direction d) (x : Lattice d) (h : ℕ)
    (w : List (Direction d)) := w.take (wordFirstHitTime e x h w)

lemma wordFirstHitTime_le_end {d : ℕ} (e : Direction d) (x : Lattice d) (h H : ℕ)
    (hh : h≤H) (w : CoordinateWord e x H) : wordFirstHitTime e x h w.val≤w.val.length := by
  apply wordFirstHitTime_le
  rw [wordPath_hit_exact]
  omega

lemma wordPrefix_length {d : ℕ} (e : Direction d) (x : Lattice d) (h H : ℕ)
    (hh : h≤H) (w : CoordinateWord e x H) : (wordPrefix e x h w.val).length=wordFirstHitTime e x h w.val := by
  simp only [wordPrefix,List.length_take,Nat.min_eq_left (wordFirstHitTime_le_end e x h H hh w)]

lemma wordPrefix_hit {d : ℕ} (e : Direction d) (x : Lattice d) (h H : ℕ)
    (hh : h≤H) (w : CoordinateWord e x H) :
    wordPath x (wordPrefix e x h w.val)∈HitAt (Strip (realPosition (step e)) x h)
      (Upper (realPosition (step e)) x h) (wordPrefix e x h w.val).length := by
  rw [wordPrefix_length e x h H hh w]
  constructor
  · rw [coordinate_mem_upper_iff]
    unfold wordPrefix
    rw [wordPath_take x w.val _ _ le_rfl]
    exact wordFirstHitTime_spec e x h w.val ⟨w.val.length,by
      rw [wordPath_hit_exact]; omega⟩
  · intro i hi
    rw [coordinate_mem_strip_iff]
    unfold wordPrefix
    rw [wordPath_take x w.val _ i hi.le]
    refine ⟨?_,wordFirstHitTime_min e x h w.val hi⟩
    have h := (coordinate_mem_strip_iff e x _ H).mp
      (w.property.2 i (hi.trans_le (wordFirstHitTime_le_end e x h H hh w)))
    exact h.1

noncomputable def coordinateWordPrefix {d : ℕ} (e : Direction d) (x : Lattice d)
    (h H : ℕ) (hh : h≤H) (w : CoordinateWord e x H) : CoordinateWord e x h :=
  ⟨wordPrefix e x h w.val,wordPrefix_hit e x h H hh w⟩

lemma wordCylinder_prefix {d : ℕ} (e : Direction d) (x : Lattice d) (h : ℕ)
    (w : List (Direction d)) : wordCylinder x w ⊆ wordCylinder x (wordPrefix e x h w) := by
  intro X hX i hi
  have hlen : (wordPrefix e x h w).length≤w.length := by
    simp only [wordPrefix,List.length_take]; exact min_le_right _ _
  have hin : i≤wordFirstHitTime e x h w := by
    exact hi.trans (by simp only [wordPrefix,List.length_take]; exact min_le_left _ _)
  exact (hX i (hi.trans hlen)).trans (wordPath_take x w _ i hin).symm

lemma successfulWordLaw_prefix_le {d : ℕ} (e : Direction d) (ω : Environment d)
    (x : Lattice d) (h H : ℕ) (hh : h≤H) :
    (successfulWordLaw ω x (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H)).map
      (coordinateWordPrefix e x h H hh) ≤
    successfulWordLaw ω x (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h) := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.map_apply (measurable_of_countable _) hE,
    successfulWordLaw_event _ _ _ _ (disjoint_strip_upper _ _ _),
    successfulWordLaw_event _ _ _ _ (disjoint_strip_upper _ _ _)]
  apply measure_mono
  intro X hX
  obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hX
  exact Set.mem_iUnion.mpr ⟨⟨coordinateWordPrefix e x h H hh w.val,w.property⟩,
    wordCylinder_prefix e x h w.val.val hw⟩

lemma rawWordLaw_prefix_le {d : ℕ} (e : Direction d) (ω : Environment d)
    (x : Lattice d) (h H : ℕ) (hh : h≤H) :
    (rawWordLaw (realPosition (step e)) H ω x).map (wordPrefix e x h)≤
    rawWordLaw (realPosition (step e)) h ω x := by
  let μ : Measure (CoordinateWord e x H) := successfulWordLaw ω x
    (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H)
  let μ' : Measure (CoordinateWord e x h) := successfulWordLaw ω x
    (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h)
  have hf : (μ.map (coordinateWordPrefix e x h H hh)).map Subtype.val≤μ'.map Subtype.val :=
    Measure.map_mono (successfulWordLaw_prefix_le e ω x h H hh) measurable_subtype_coe
  rw [Measure.map_map measurable_subtype_coe (measurable_of_countable _)] at hf
  change (μ.map Subtype.val).map (wordPrefix e x h)≤μ'.map Subtype.val
  rw [Measure.map_map (measurable_of_countable _) measurable_subtype_coe]
  exact hf

noncomputable def tupleWordPrefix {d k : ℕ} (e : Direction d) (x : Fin k → Lattice d) (h : ℕ)
    (w : Fin k → List (Direction d)) : Fin k → List (Direction d) := fun j => wordPrefix e (x j) h (w j)

lemma rawTupleWordLaw_prefix_le {d k : ℕ} (e : Direction d) (ω : Environment d)
    (x : Fin k → Lattice d) (h H : ℕ) (hh : h≤H) :
    (rawTupleWordLaw (realPosition (step e)) H ω x).map (tupleWordPrefix e x h)≤
    rawTupleWordLaw (realPosition (step e)) h ω x := by
  change (Measure.pi (fun j => rawWordLaw (realPosition (step e)) H ω (x j))).map
    (fun w j => wordPrefix e (x j) h (w j))≤_
  rw [Measure.pi_map_pi (fun _ => (measurable_of_countable _).aemeasurable)]
  exact TupleKernel.countable_pi_mono k _ _ fun j => rawWordLaw_prefix_le e ω (x j) h H hh

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma relativeWordDisplacement_prefix {d : ℕ} (e f : Direction d) (x : Lattice d)
    (h H : ℕ) (hh : h≤H) (s : ℕ) (hs : s≤h) (w : CoordinateWord e x H) :
    relativeWordDisplacement e f x s (wordPrefix e x h w.val)=relativeWordDisplacement e f x s w.val := by
  have he := relativeWordDisplacement_append_prefix e f x h s hs
    (coordinateWordPrefix e x h H hh w) (w.val.drop (wordFirstHitTime e x h w.val))
  change relativeWordDisplacement e f x s (w.val.take (wordFirstHitTime e x h w.val)++
    w.val.drop (wordFirstHitTime e x h w.val))=_ at he
  rw [List.take_append_drop] at he
  exact he.symm

lemma tupleRelativeBudget_prefix {d k : ℕ} (e f : Direction d) (x : Fin k → Lattice d)
    (h H : ℕ) (hh : h≤H) (r : ℝ) (w : ∀ j, CoordinateWord e (x j) H)
    (hw : TupleRelativeBudget e f x H r (fun j => (w j).val)) :
    TupleRelativeBudget e f x h r (tupleWordPrefix e x h (fun j => (w j).val)) := by
  intro s hs i j
  change |relativeWordDisplacement e f (x i) s (wordPrefix e (x i) h (w i).val)-
    relativeWordDisplacement e f (x j) s (wordPrefix e (x j) h (w j).val)|≤r
  rw [relativeWordDisplacement_prefix e f (x i) h H hh s hs (w i),
    relativeWordDisplacement_prefix e f (x j) h H hh s hs (w j)]
  exact hw s (hs.trans hh) i j

lemma tupleRelativeBudget_prefix_separation {d k : ℕ} (e f : Direction d)
    (x : Fin k → Lattice d) (h H : ℕ) (hh : h≤H) (G r : ℝ)
    (w : ∀ j, CoordinateWord e (x j) H) (hG : TupleSeparated f G x)
    (hw : TupleRelativeBudget e f x H r (fun j => (w j).val)) :
    TupleSeparated f (G-r) (tupleWordEndpoint x (tupleWordPrefix e x h (fun j => (w j).val))) :=
  tupleRelativeBudget_separation e f x h G r (fun j => coordinateWordPrefix e (x j) h H hh (w j))
    hG (tupleRelativeBudget_prefix e f x h H hh r w hw)

lemma rawTupleWordLaw_valid_ae {d k : ℕ} (e : Direction d) (ω : Environment d)
    (x : Fin k → Lattice d) (H : ℕ) :
    ∀ᵐ w ∂rawTupleWordLaw (realPosition (step e)) H ω x, ∀ j,
      wordPath (x j) (w j)∈HitAt (Strip (realPosition (step e)) (x j) H)
        (Upper (realPosition (step e)) (x j) H) (w j).length := by
  apply ae_iff_of_countable.mpr
  intro w hw j
  by_contra hj
  apply hw
  rw [rawTupleWordLaw_singleton]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [rawWordLaw_singleton,ite_eq_right hj]

lemma relativeBudgetWordLaw_prefix_separation_ae {d k : ℕ} (e f : Direction d)
    (ω : Environment d) (x : Fin k → Lattice d) (h H : ℕ) (hh : h≤H) (G r : ℝ)
    (hG : TupleSeparated f G x) :
    ∀ᵐ w ∂relativeBudgetWordLaw e f H r ω x,
    TupleSeparated f (G-r) (tupleWordEndpoint x (tupleWordPrefix e x h w)) := by
  have hv := (rawTupleWordLaw_valid_ae e ω x H).filter_mono
    (ae_mono (show relativeBudgetWordLaw e f H r ω x≤rawTupleWordLaw (realPosition (step e)) H ω x from
      Measure.restrict_le_self))
  have hb : ∀ᵐ w ∂relativeBudgetWordLaw e f H r ω x,TupleRelativeBudget e f x H r w :=
    ae_restrict_mem (Set.to_countable _).measurableSet
  filter_upwards [hv,hb] with w hw hb
  exact tupleRelativeBudget_prefix_separation e f x h H hh G r (fun j => ⟨w j,hw j⟩) hG hb

theorem budget_prefix_certificate {d k : ℕ} (e f : Direction d) (ω : Environment d)
    (x : Fin k → Lattice d) (h H : ℕ) (hh : h≤H) (G r : ℝ)
    (hG : TupleSeparated f G x) :
    relativeBudgetWordLaw e f H r ω x Set.univ ≤
      rawTupleEndpointLaw (realPosition (step e)) h ω x {y | TupleSeparated f (G-r) y} := by
  let P := fun w : Fin k → List (Direction d) => tupleWordEndpoint x (tupleWordPrefix e x h w)
  have hle : (relativeBudgetWordLaw e f H r ω x).map P≤rawTupleEndpointLaw (realPosition (step e)) h ω x := by
    rw [←rawTupleWordLaw_endpoint (realPosition (step e)) h ω x]
    have hp := (Measure.map_mono (show relativeBudgetWordLaw e f H r ω x≤
      rawTupleWordLaw (realPosition (step e)) H ω x from Measure.restrict_le_self)
        (measurable_of_countable (tupleWordPrefix e x h))).trans (rawTupleWordLaw_prefix_le e ω x h H hh)
    have he := Measure.map_mono hp (measurable_of_countable (tupleWordEndpoint x))
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at he
    exact he
  have he : (relativeBudgetWordLaw e f H r ω x).map P {y | TupleSeparated f (G-r) y}=
      relativeBudgetWordLaw e f H r ω x Set.univ := by
    rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
    apply measure_congr
    filter_upwards [relativeBudgetWordLaw_prefix_separation_ae e f ω x h H hh G r hG] with w hw
    apply propext
    exact iff_true_intro hw
  rw [←he]
  exact hle _

end DirectionalTransience

end

end OAI
