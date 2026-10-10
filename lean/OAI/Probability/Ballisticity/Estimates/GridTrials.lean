import Mathlib
import OAI.Probability.Ballisticity.Crossings.CrossingGap

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def DropBetween {d : ℕ} (ℓ : Vector d) (n m : ℕ) : Set (Path d) :=
  {X | ∃ r, n ≤ r ∧ r < m ∧ dot (realPosition (X r)) ℓ < dot (realPosition (X n)) ℓ}

lemma measurableSet_dropBetween {d : ℕ} (ℓ : Vector d) (n m : ℕ) :
    MeasurableSet (DropBetween ℓ n m) := by
  simp only [DropBetween,Set.ofPred_exists,Set.ofPred_and]
  exact MeasurableSet.iUnion fun r => (MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter (measurableSet_lt
      ((measurable_of_countable (fun x : Lattice d => dot (realPosition x) ℓ)).comp (measurable_pi_apply r))
      ((measurable_of_countable (fun x : Lattice d => dot (realPosition x) ℓ)).comp (measurable_pi_apply n))))

lemma dropBetween_prefix {d : ℕ} (ℓ : Vector d) (n m : ℕ) (hn : n ≤ m) :
    PrefixDetermined m (DropBetween ℓ n m) := by
  intro X Y hXY
  constructor <;> rintro ⟨r,h1,h2,h3⟩
  · exact ⟨r,h1,h2,by simpa only [← hXY r h2.le,← hXY n hn] using h3⟩
  · exact ⟨r,h1,h2,by simpa only [hXY r h2.le,hXY n hn] using h3⟩

lemma dropBetween_not_futureNoDrop {d : ℕ} (ℓ : Vector d) (n m : ℕ) (X : Path d)
    (h : X ∈ DropBetween ℓ n m) : X ∉ FutureNoDrop ℓ n := by
  rintro hD
  obtain ⟨r,hnr,hrm,hr⟩ := h
  have hh := hD (r-n)
  rw [Nat.add_sub_of_le hnr] at hh
  exact (not_lt_of_ge hh) hr

def GridPrefix {d : ℕ} (e : Direction d) (B : ℕ) : ℕ → ℕ → Set (Path d)
  | 0,n => {X | X 0=0} ∩ FirstLayerHit (signedHeight e) B n
  | k+1,m => ({X | X 0=0} ∩ FirstLayerHit (signedHeight e) (((k+2)*B:ℕ):ℤ) m) ∩
      ⋃ n < m, GridPrefix e B k n ∩ DropBetween (realPosition (step e)) n m

def GridReached {d : ℕ} (e : Direction d) (B k : ℕ) : Set (Path d) :=
  ⋃ n, GridPrefix e B k n

lemma gridPrefix_hit {d : ℕ} (e : Direction d) (B k n : ℕ) :
    GridPrefix e B k n ⊆ {X | X 0=0} ∩ FirstLayerHit (signedHeight e) (((k+1)*B:ℕ):ℤ) n := by
  cases k with
  | zero => simpa only [GridPrefix,Nat.zero_add,one_mul] using (Set.Subset.refl (GridPrefix e B 0 n))
  | succ k => exact Set.inter_subset_left

lemma measurableSet_gridPrefix {d : ℕ} (e : Direction d) (B k n : ℕ) :
    MeasurableSet (GridPrefix e B k n) := by
  induction k generalizing n with
  | zero =>
    exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
      (measurableSet_firstLayerHit _ _ _)
  | succ k ih =>
    exact ((measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
      (measurableSet_firstLayerHit _ _ _)).inter (MeasurableSet.iUnion fun j =>
        MeasurableSet.iUnion fun _ => (ih j).inter (measurableSet_dropBetween _ _ _))

lemma measurableSet_gridReached {d : ℕ} (e : Direction d) (B k : ℕ) :
    MeasurableSet (GridReached e B k) := MeasurableSet.iUnion (measurableSet_gridPrefix e B k)

lemma gridPrefix_prefix {d : ℕ} (e : Direction d) (B k n : ℕ) :
    PrefixDetermined n (GridPrefix e B k n) := by
  have hz (m : ℕ) : PrefixDetermined m {X : Path d | X 0=0} := by
    intro X Y hXY
    simp only [Set.mem_ofPred_eq,hXY 0 (Nat.zero_le _)]
  induction k generalizing n with
  | zero => exact prefixDetermined_inter (hz _) (firstLayerHit_prefix _ _ _)
  | succ k ih =>
    apply prefixDetermined_inter (prefixDetermined_inter (hz _) (firstLayerHit_prefix _ _ _))
    intro X Y hXY
    simp only [Set.mem_iUnion,Set.mem_inter_iff]
    apply exists_congr
    intro j
    apply exists_congr
    intro hj
    exact and_congr ((prefixDetermined_mono hj.le (ih j)) X Y hXY)
      ((dropBetween_prefix _ j n hj.le) X Y hXY)

lemma gridPrefix_disjoint {d : ℕ} (e : Direction d) (B k : ℕ) :
    Pairwise (fun n m => Disjoint (GridPrefix e B k n) (GridPrefix e B k m)) := by
  intro n m hnm
  exact (firstLayerHit_disjoint (signedHeight e) (((k+1)*B:ℕ):ℤ) hnm).mono
    (fun X hX => (gridPrefix_hit e B k n hX).2)
    (fun X hX => (gridPrefix_hit e B k m hX).2)

lemma gridPrefix_record {d : ℕ} (e : Direction d) (B k n : ℕ) (hB : 0<B)
    (X : Path d) (hX : X ∈ GridPrefix e B k n) :
    0<n ∧ StrictRecord (realPosition (step e)) X n := by
  have hh := gridPrefix_hit e B k n hX
  refine ⟨?_,firstLayerHit_record _ _ (signedHeight_projection e) _ _ X hh.2⟩
  by_contra hn
  have hn0 : n=0 := by omega
  have he := hh.2.1
  rw [hn0,hh.1,signedHeight_zero] at he
  have hpos : (0:ℤ)<((k+1)*B:ℕ) := by exact_mod_cast (Nat.mul_pos (Nat.succ_pos k) hB)
  omega

lemma gridReached_succ_subset {d : ℕ} (e : Direction d) (B k : ℕ) :
    GridReached e B (k+1) ⊆ GridReached e B k := by
  intro X hX
  obtain ⟨m,hm⟩ := Set.mem_iUnion.mp hX
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hm.2
  obtain ⟨_,hn⟩ := Set.mem_iUnion.mp hn
  exact Set.mem_iUnion.mpr ⟨n,hn.1⟩

lemma gridReached_succ_failure {d : ℕ} (e : Direction d) (B k n : ℕ) (X : Path d)
    (hX : X ∈ GridReached e B (k+1)) (hn : X ∈ GridPrefix e B k n) :
    X ∉ FutureNoDrop (realPosition (step e)) n := by
  obtain ⟨m,hm⟩ := Set.mem_iUnion.mp hX
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hm.2
  obtain ⟨_,hj⟩ := Set.mem_iUnion.mp hj
  have heq : j=n := by
    by_contra hh
    exact Set.disjoint_left.mp (gridPrefix_disjoint e B k hh) hj.1 hn
  subst j
  exact dropBetween_not_futureNoDrop _ n m X hj.2

lemma gridReached_contraction {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (B k : ℕ) (hB : 0<B) :
    (annealedLaw ν).real (GridReached e B (k+1)) ≤
      (1-(annealedLaw ν).real (NoDrop (realPosition (step e)) 0))*
        (annealedLaw ν).real (GridReached e B k) := by
  let ℓ := realPosition (step e)
  let μ := annealedLaw ν
  have hg := stopping_prefix_favourable_gain μ (GridPrefix e B k) (GridReached e B (k+1))
    (μ (NoDrop ℓ 0)) (gridPrefix_prefix e B k) (measurableSet_gridPrefix e B k)
    (gridPrefix_disjoint e B k) (measurableSet_gridReached e B (k+1))
    (gridReached_succ_subset e B k) (by
      intro n f hf
      have hr := gridPrefix_record e B k n hB f hf
      let A := (fun X : Path d => fun j => X (n+j)) ⁻¹' NoDrop ℓ (f n) ∩ pathCylinder f n
      refine ⟨A,(measurableSet_noDrop ℓ (f n)).preimage (by fun_prop) |>.inter
        (measurableSet_pathCylinder f n),Set.inter_subset_right,?_,?_⟩
      · apply Set.disjoint_left.mpr
        intro X hX hA
        apply gridReached_succ_failure e B k n X hX ((gridPrefix_prefix e B k n X f hA.2).mpr hf)
        change ∀ j, dot (realPosition (X n)) ℓ ≤ dot (realPosition (X (n+j))) ℓ
        have hh : ∀ j, dot (realPosition (f n)) ℓ ≤ dot (realPosition (X (n+j))) ℓ := hA.1
        simpa only [hA.2 n le_rfl] using hh
      · exact annealed_record_cylinder_noDrop ν ℓ f n hr.1 hr.2)
  have hr := ENNReal.toReal_mono (measure_ne_top μ _) hg
  rw [ENNReal.toReal_add (measure_ne_top μ _)
    (ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _)),ENNReal.toReal_mul] at hr
  change μ.real (GridReached e B (k+1))+μ.real (GridReached e B k)*μ.real (NoDrop ℓ 0) ≤
    μ.real (GridReached e B k) at hr
  change μ.real _≤(1-μ.real (NoDrop ℓ 0))*μ.real _
  nlinarith

lemma gridReached_geometric {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (B k : ℕ) (hB : 0<B) :
    (annealedLaw ν).real (GridReached e B k) ≤
      (1-(annealedLaw ν).real (NoDrop (realPosition (step e)) 0))^k := by
  have hp : (annealedLaw ν).real (NoDrop (realPosition (step e)) 0) ≤ 1 := measureReal_le_one
  induction k with
  | zero =>
    rw [pow_zero]
    exact measureReal_le_one
  | succ k ih =>
    exact (gridReached_contraction ν e B k hB).trans (by
      simpa only [pow_succ,mul_comm] using mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hp))

end DirectionalTransience

end

end OAI
