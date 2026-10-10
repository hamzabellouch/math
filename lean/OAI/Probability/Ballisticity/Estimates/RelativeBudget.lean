import Mathlib
import OAI.Probability.Ballisticity.Estimates.WordConcatenation

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def relativeWordDisplacement {d : ℕ} (e f : Direction d) (x : Lattice d)
    (s : ℕ) (w : List (Direction d)) : ℝ :=
  signedCoordinate f (wordFirstHitPosition e x s w - x)

def TupleRelativeBudget {d k : ℕ} (e f : Direction d) (x : Fin k → Lattice d)
    (H : ℕ) (r : ℝ) (w : Fin k → List (Direction d)) : Prop :=
  ∀ s ≤ H, ∀ i j, |relativeWordDisplacement e f (x i) s (w i) -
    relativeWordDisplacement e f (x j) s (w j)| ≤ r

def TupleSeparated {d k : ℕ} (f : Direction d) (G : ℝ) (x : Fin k → Lattice d) : Prop :=
  ∀ i j, i ≠ j → G ≤ |signedCoordinate f (x i) - signedCoordinate f (x j)|

def tupleWordEndpoint {d k : ℕ} (x : Fin k → Lattice d)
    (w : Fin k → List (Direction d)) : Fin k → Lattice d :=
  fun j => wordPath (x j) (w j) (w j).length

lemma relativeWordDisplacement_endpoint {d : ℕ} (e f : Direction d) (x : Lattice d)
    (H : ℕ) (w : HitWord x (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H)) :
    relativeWordDisplacement e f x H w.val = signedCoordinate f (wordPath x w.val w.val.length - x) := by
  unfold relativeWordDisplacement wordFirstHitPosition
  rw [wordFirstHitTime_endpoint]

lemma relativeWordDisplacement_append_prefix {d : ℕ} (e f : Direction d) (x : Lattice d)
    (h s : ℕ) (hs : s ≤ h)
    (u : HitWord x (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h))
    (v : List (Direction d)) :
    relativeWordDisplacement e f x s (u.val++v) = relativeWordDisplacement e f x s u.val := by
  unfold relativeWordDisplacement
  rw [wordFirstHitPosition_append_prefix e x h s hs u v]

lemma relativeWordDisplacement_append_suffix {d : ℕ} (e f : Direction d) (x : Lattice d)
    (h m t : ℕ) (ht : t ≤ m)
    (u : HitWord x (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h))
    (v : HitWord (wordPath x u.val u.val.length)
      (Strip (realPosition (step e)) (wordPath x u.val u.val.length) m)
      (Upper (realPosition (step e)) (wordPath x u.val u.val.length) m)) :
    relativeWordDisplacement e f x (h+t) (u.val++v.val) =
      relativeWordDisplacement e f x h u.val +
        relativeWordDisplacement e f (wordPath x u.val u.val.length) t v.val := by
  rw [relativeWordDisplacement_endpoint e f x h u]
  unfold relativeWordDisplacement
  rw [wordFirstHitPosition_append_suffix e x h m t ht u v]
  simp only [signedCoordinate_sub]
  ring

lemma tupleRelativeBudget_append {d k : ℕ} (e f : Direction d) (x : Fin k → Lattice d)
    (h m : ℕ) (r q : ℝ) (hq : 0 ≤ q)
    (u : ∀ j, HitWord (x j) (Strip (realPosition (step e)) (x j) h) (Upper (realPosition (step e)) (x j) h))
    (v : ∀ j, HitWord (wordPath (x j) (u j).val (u j).val.length)
      (Strip (realPosition (step e)) (wordPath (x j) (u j).val (u j).val.length) m)
      (Upper (realPosition (step e)) (wordPath (x j) (u j).val (u j).val.length) m))
    (hu : TupleRelativeBudget e f x h r (fun j => (u j).val))
    (hv : TupleRelativeBudget e f (fun j => wordPath (x j) (u j).val (u j).val.length)
      m q (fun j => (v j).val)) :
    TupleRelativeBudget e f x (h+m) (r+q) (fun j => (u j).val++(v j).val) := by
  intro s hs i j
  by_cases hsh : s ≤ h
  · rw [relativeWordDisplacement_append_prefix e f (x i) h s hsh (u i) (v i).val,
      relativeWordDisplacement_append_prefix e f (x j) h s hsh (u j) (v j).val]
    exact (hu s hsh i j).trans (le_add_of_nonneg_right hq)
  · have he : s = h+(s-h) := by omega
    have ht : s-h ≤ m := by omega
    rw [he,relativeWordDisplacement_append_suffix e f (x i) h m (s-h) ht (u i) (v i),
      relativeWordDisplacement_append_suffix e f (x j) h m (s-h) ht (u j) (v j)]
    have h1 := hu h le_rfl i j
    have h2 := hv (s-h) ht i j
    calc
      _ = |(relativeWordDisplacement e f (x i) h (u i).val -
        relativeWordDisplacement e f (x j) h (u j).val) +
        (relativeWordDisplacement e f (wordPath (x i) (u i).val (u i).val.length) (s-h) (v i).val -
        relativeWordDisplacement e f (wordPath (x j) (u j).val (u j).val.length) (s-h) (v j).val)| := by
          congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 h2)

lemma tupleRelativeBudget_separation {d k : ℕ} (e f : Direction d) (x : Fin k → Lattice d)
    (H : ℕ) (G r : ℝ)
    (w : ∀ j, HitWord (x j) (Strip (realPosition (step e)) (x j) H) (Upper (realPosition (step e)) (x j) H))
    (hG : TupleSeparated f G x)
    (hw : TupleRelativeBudget e f x H r (fun j => (w j).val)) :
    TupleSeparated f (G-r) (tupleWordEndpoint x (fun j => (w j).val)) := by
  intro i j hij
  have hb := hw H le_rfl i j
  rw [relativeWordDisplacement_endpoint e f (x i) H (w i),
    relativeWordDisplacement_endpoint e f (x j) H (w j)] at hb
  apply sub_le_iff_le_add.mpr
  change G ≤ |signedCoordinate f (wordPath (x i) (w i).val (w i).val.length) -
    signedCoordinate f (wordPath (x j) (w j).val (w j).val.length)| + r
  calc
    G ≤ |signedCoordinate f (x i)-signedCoordinate f (x j)| := hG i j hij
    _ = |(signedCoordinate f (wordPath (x i) (w i).val (w i).val.length) -
        signedCoordinate f (wordPath (x j) (w j).val (w j).val.length)) -
      (signedCoordinate f (wordPath (x i) (w i).val (w i).val.length - x i) -
        signedCoordinate f (wordPath (x j) (w j).val (w j).val.length - x j))| := by
          simp only [signedCoordinate_sub]; congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans (add_le_add le_rfl hb)

noncomputable def relativeBudgetWordLaw {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (ω : Environment d) (x : Fin k → Lattice d) :
    Measure (Fin k → List (Direction d)) :=
  (rawTupleWordLaw (realPosition (step e)) H ω x).restrict {w | TupleRelativeBudget e f x H r w}

noncomputable def relativeBudgetEndpointLaw {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (ω : Environment d) (x : Fin k → Lattice d) :
    Measure (Fin k → Lattice d) :=
  (relativeBudgetWordLaw e f H r ω x).map (tupleWordEndpoint x)

instance relativeBudgetWordLaw_finite {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (ω : Environment d) (x : Fin k → Lattice d) :
    IsFiniteMeasure (relativeBudgetWordLaw e f H r ω x) := by
  unfold relativeBudgetWordLaw
  infer_instance

instance relativeBudgetEndpointLaw_finite {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (ω : Environment d) (x : Fin k → Lattice d) :
    IsFiniteMeasure (relativeBudgetEndpointLaw e f H r ω x) := by
  unfold relativeBudgetEndpointLaw
  infer_instance

lemma relativeBudgetEndpointLaw_le {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (ω : Environment d) (x : Fin k → Lattice d) :
    relativeBudgetEndpointLaw e f H r ω x ≤ rawTupleEndpointLaw (realPosition (step e)) H ω x := by
  rw [← rawTupleWordLaw_endpoint (realPosition (step e)) H ω x]
  exact Measure.map_mono Measure.restrict_le_self (measurable_of_countable _)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience
namespace TupleKernel

noncomputable def dependentPair {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (K : A → Measure B) : Measure (A × B) :=
  μ.bind (fun a => (K a).map (fun b => (a,b)))

lemma dependentPair_singleton {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (K : A → Measure B) (a : A) (b : B) :
    dependentPair μ K {(a,b)} = μ {a} * K a {b} := by
  rw [dependentPair,Measure.bind_apply (measurableSet_singleton _) (measurable_of_countable _).aemeasurable,
    lintegral_countable']
  have he (c : A) : ((K c).map (fun b => (c,b))) {(a,b)} = if c=a then K c {b} else 0 := by
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    by_cases hc : c=a
    · subst c
      rw [ite_eq_left rfl]
      congr 1
      ext y
      simp
    · rw [ite_eq_right hc]
      have hset : (fun y => (c,y)) ⁻¹' {(a,b)} = (∅ : Set B) := by
        ext y
        simp [hc]
      rw [hset,measure_empty]
  simp_rw [he]
  rw [tsum_eq_single a]
  · simp [mul_comm]
  · intro c hc
    simp [hc]

lemma restrict_singleton {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure A) (S : Set A) (a : A) :
    μ.restrict S {a} = if a ∈ S then μ {a} else 0 := by
  rw [Measure.restrict_apply (measurableSet_singleton a)]
  by_cases ha : a ∈ S
  · rw [ite_eq_left ha,Set.singleton_inter_of_mem ha]
  · rw [ite_eq_right ha,Set.singleton_inter_of_notMem ha,measure_empty]

end TupleKernel

noncomputable def rawTupleSplitLaw {d k : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) :
    Measure ((Fin k → List (Direction d)) × (Fin k → List (Direction d))) :=
  TupleKernel.dependentPair (rawTupleWordLaw (realPosition (step e)) h ω x)
    (fun u => rawTupleWordLaw (realPosition (step e)) m ω (tupleWordEndpoint x u))

lemma rawTupleSplitLaw_singleton {d k : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) (u v : Fin k → List (Direction d)) :
    rawTupleSplitLaw e h m ω x {(u,v)} = ∏ j, rawWordPairLaw e h m ω (x j) {(u j,v j)} := by
  rw [rawTupleSplitLaw,TupleKernel.dependentPair_singleton]
  simp only [rawTupleWordLaw_singleton,rawWordPairLaw_singleton,tupleWordEndpoint,Finset.prod_mul_distrib]

def ValidTupleSplit {d k : ℕ} (e : Direction d) (x : Fin k → Lattice d) (h m : ℕ)
    (p : (Fin k → List (Direction d)) × (Fin k → List (Direction d))) : Prop :=
  ∀ j, ValidWordSplit e (x j) h m (p.1 j,p.2 j)

def tupleWordConcat {d k : ℕ}
    (p : (Fin k → List (Direction d)) × (Fin k → List (Direction d))) : Fin k → List (Direction d) :=
  fun j => p.1 j++p.2 j

lemma tupleWordConcat_injOn {d k : ℕ} (e : Direction d) (x : Fin k → Lattice d) (h m : ℕ) :
    Set.InjOn (tupleWordConcat (d := d) (k := k)) {p | ValidTupleSplit e x h m p} := by
  intro u hu v hv he
  have hi (j) : (u.1 j,u.2 j) = (v.1 j,v.2 j) := by
    apply congrArg Subtype.val
      (coordinateWordConcat_injective e (x j) h m (a₁ := ⟨(u.1 j,u.2 j),hu j⟩)
        (a₂ := ⟨(v.1 j,v.2 j),hv j⟩) _)
    exact Subtype.ext (congrFun he j)
  exact Prod.ext (funext fun j => congrArg Prod.fst (hi j)) (funext fun j => congrArg Prod.snd (hi j))

lemma rawTupleSplitLaw_invalid {d k : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d)
    (p : (Fin k → List (Direction d)) × (Fin k → List (Direction d)))
    (hp : ¬ ValidTupleSplit e x h m p) : rawTupleSplitLaw e h m ω x {p} = 0 := by
  rw [← Prod.eta p,rawTupleSplitLaw_singleton]
  obtain ⟨j,hj⟩ := not_forall.mp hp
  exact Finset.prod_eq_zero (Finset.mem_univ j)
    (rawWordPairLaw_invalid e h m ω (x j) (p.1 j,p.2 j) hj)

lemma rawTupleSplitLaw_valid {d k : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d)
    (p : (Fin k → List (Direction d)) × (Fin k → List (Direction d)))
    (hp : ValidTupleSplit e x h m p) : rawTupleSplitLaw e h m ω x {p} =
      rawTupleWordLaw (realPosition (step e)) (h+m) ω x {tupleWordConcat p} := by
  rw [← Prod.eta p,rawTupleSplitLaw_singleton,rawTupleWordLaw_singleton]
  apply Finset.prod_congr rfl
  intro j _
  exact rawWordPairLaw_valid e h m ω (x j) ⟨(p.1 j,p.2 j),hp j⟩

lemma rawTupleWordLaw_comp_le {d k : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) :
    (rawTupleSplitLaw e h m ω x).map tupleWordConcat ≤
      rawTupleWordLaw (realPosition (step e)) (h+m) ω x := by
  apply TupleKernel.countable_restricted_map_le _ _ {p | ValidTupleSplit e x h m p}
    tupleWordConcat (tupleWordConcat_injOn e x h m)
  · exact fun p hp => rawTupleSplitLaw_invalid e h m ω x p hp
  · exact fun p hp => (rawTupleSplitLaw_valid e h m ω x p hp).le

noncomputable def relativeBudgetSplitLaw {d k : ℕ} (e f : Direction d) (h m : ℕ)
    (r q : ℝ) (ω : Environment d) (x : Fin k → Lattice d) :
    Measure ((Fin k → List (Direction d)) × (Fin k → List (Direction d))) :=
  TupleKernel.dependentPair (relativeBudgetWordLaw e f h r ω x)
    (fun u => relativeBudgetWordLaw e f m q ω (tupleWordEndpoint x u))

lemma relativeBudgetWordLaw_singleton {d k : ℕ} (e f : Direction d) (H : ℕ)
    (r : ℝ) (ω : Environment d) (x : Fin k → Lattice d) (w : Fin k → List (Direction d)) :
    relativeBudgetWordLaw e f H r ω x {w} =
      if TupleRelativeBudget e f x H r w then rawTupleWordLaw (realPosition (step e)) H ω x {w} else 0 := by
  exact TupleKernel.restrict_singleton _ _ _

lemma relativeBudgetSplitLaw_singleton {d k : ℕ} (e f : Direction d) (h m : ℕ)
    (r q : ℝ) (ω : Environment d) (x : Fin k → Lattice d)
    (p : (Fin k → List (Direction d)) × (Fin k → List (Direction d))) :
    relativeBudgetSplitLaw e f h m r q ω x {p} =
      if TupleRelativeBudget e f x h r p.1 ∧
        TupleRelativeBudget e f (tupleWordEndpoint x p.1) m q p.2
      then rawTupleSplitLaw e h m ω x {p} else 0 := by
  rw [← Prod.eta p,relativeBudgetSplitLaw,TupleKernel.dependentPair_singleton,
    rawTupleSplitLaw,TupleKernel.dependentPair_singleton]
  simp only [relativeBudgetWordLaw_singleton]
  split_ifs <;> simp_all

lemma relativeBudgetWordLaw_comp_le {d k : ℕ} (e f : Direction d) (h m : ℕ)
    (r q : ℝ) (hq : 0 ≤ q) (ω : Environment d) (x : Fin k → Lattice d) :
    (relativeBudgetSplitLaw e f h m r q ω x).map tupleWordConcat ≤
      relativeBudgetWordLaw e f (h+m) (r+q) ω x := by
  let S := {p | ValidTupleSplit e x h m p ∧ TupleRelativeBudget e f x h r p.1 ∧
    TupleRelativeBudget e f (tupleWordEndpoint x p.1) m q p.2}
  apply TupleKernel.countable_restricted_map_le _ _ S
  · intro a ha b hb he
    exact tupleWordConcat_injOn e x h m ha.1 hb.1 he
  · intro p hp
    rw [relativeBudgetSplitLaw_singleton]
    by_cases hbudget : TupleRelativeBudget e f x h r p.1 ∧
        TupleRelativeBudget e f (tupleWordEndpoint x p.1) m q p.2
    · rw [ite_eq_left hbudget]
      exact rawTupleSplitLaw_invalid e h m ω x p (fun hval => hp ⟨hval,hbudget⟩)
    · exact ite_eq_right hbudget
  · intro p hp
    rw [relativeBudgetSplitLaw_singleton,ite_eq_left hp.2,rawTupleSplitLaw_valid e h m ω x p hp.1,
      relativeBudgetWordLaw_singleton]
    have hc : TupleRelativeBudget e f x (h+m) (r+q) (tupleWordConcat p) :=
      tupleRelativeBudget_append e f x h m r q hq
        (fun j => coordinateSplitFirst e (x j) h m ⟨(p.1 j,p.2 j),hp.1 j⟩)
        (fun j => coordinateSplitSecond e (x j) h m ⟨(p.1 j,p.2 j),hp.1 j⟩) hp.2.1 hp.2.2
    rw [ite_eq_left hc]

end DirectionalTransience

end

end OAI
