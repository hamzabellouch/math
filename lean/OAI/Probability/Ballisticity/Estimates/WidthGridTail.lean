import Mathlib
import OAI.Probability.Ballisticity.Estimates.GridTrials
import OAI.Probability.Ballisticity.Crossings.CrossingSurplus

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def LateGridFailure {d : ℕ} (e : Direction d) (B j : ℕ) : Set (Path d) :=
  ⋃ n, (({X : Path d | X 0=0} ∩ FirstLayerHit (signedHeight e) (j*B:ℕ) n) ∩
    FutureEvent (fun x => Cross (realPosition (step e)) x B) n) \ FutureNoDrop (realPosition (step e)) n

lemma measurableSet_lateGridFailure {d : ℕ} (e : Direction d) (B j : ℕ) :
    MeasurableSet (LateGridFailure e B j) := by
  apply MeasurableSet.iUnion
  intro n
  exact (((measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
    (measurableSet_firstLayerHit _ _ _)).inter
      (measurableSet_futureEvent _ (fun x => measurableSet_cross _ _ _) _)).diff
        (measurableSet_futureNoDrop _ _)

lemma measureReal_iUnion_disjoint {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (A : ℕ → Set α) (hm : ∀ n, MeasurableSet (A n))
    (hd : Pairwise (fun n m => Disjoint (A n) (A m))) :
    μ.real (⋃ n,A n)=∑' n,μ.real (A n) := by
  rw [measureReal_def,measure_iUnion hd hm]
  exact ENNReal.tsum_toReal_eq (fun n => measure_ne_top μ (A n))

lemma lateGridFailure_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (B j : ℕ) (hB : 0 < B) (hj : 0 < j) :
    (annealedLaw ν).real (LateGridFailure e B j)  ≤
      (annealedLaw ν).real (Cross (realPosition (step e)) 0 B \ NoDrop (realPosition (step e)) 0) := by
  let ℓ := realPosition (step e)
  let μ := annealedLaw ν
  let A := fun n => {X : Path d | X 0=0} ∩ FirstLayerHit (signedHeight e) (j*B:ℕ) n
  let F := fun n => (A n ∩ FutureEvent (fun x => Cross ℓ x B) n) \ FutureNoDrop ℓ n
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter (measurableSet_firstLayerHit _ _ _)
  have hFm (n : ℕ) : MeasurableSet (F n) :=
    ((hAm n).inter (measurableSet_futureEvent _ (fun _ => measurableSet_cross _ _ _) _)).diff
      (measurableSet_futureNoDrop _ _)
  have hAd : Pairwise (fun n m => Disjoint (A n) (A m)) :=
    fun n m hnm => (firstLayerHit_disjoint (signedHeight e) (j*B:ℕ) hnm).mono
      Set.inter_subset_right Set.inter_subset_right
  have hFd : Pairwise (fun n m => Disjoint (F n) (F m)) :=
    fun n m hnm => (hAd hnm).mono (Set.Subset.trans Set.sdiff_subset Set.inter_subset_left)
      (Set.Subset.trans Set.sdiff_subset Set.inter_subset_left)
  have hf (n : ℕ) : μ.real (F n)=μ.real (A n)*μ.real (Cross ℓ 0 B \ NoDrop ℓ 0) := by
    by_cases hn : 0 < n
    · apply annealed_record_event_cross_failure ν ℓ htrans n hn (A n) (hAm n)
      · apply prefixDetermined_inter
        · intro X Y hXY
          simp only [Set.mem_ofPred_eq,hXY 0 (Nat.zero_le n)]
        · exact firstLayerHit_prefix _ _ _
      · exact fun X hX => firstLayerHit_record _ _ (signedHeight_projection e) _ _ X hX.2
      · exact_mod_cast hB
    · have hz : n=0 := by omega
      have hAe : A n=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro X hX
        have hh := hX.2.1
        rw [hz,hX.1,signedHeight_zero] at hh
        have hpos : 0 < j*B := Nat.mul_pos hj hB
        exact (Nat.ne_of_gt hpos) (by exact_mod_cast hh.symm)
      have hFe : F n=∅ := by simp [F,hAe]
      simp only [hAe,hFe,measureReal_empty,zero_mul]
  change μ.real (⋃ n,F n) ≤ _
  rw [measureReal_iUnion_disjoint μ F hFm hFd]
  simp_rw [hf]
  rw [tsum_mul_right,← measureReal_iUnion_disjoint μ A hAm hAd]
  exact mul_le_of_le_one_left measureReal_nonneg measureReal_le_one

def NoTruePastHeight {d : ℕ} (e : Direction d) (H : ℕ) : Set (Path d) :=
  {X | X 0=0 ∧ ∃ n, X ∈ FirstLayerHit (signedHeight e) H n ∧
    ∀ t, 0 < t → t ≤ n → ¬TrueRecord (realPosition (step e)) X t}

lemma measurableSet_noTruePastHeight {d : ℕ} (e : Direction d) (H : ℕ) :
    MeasurableSet (NoTruePastHeight e H) := by
  simp only [NoTruePastHeight,Set.ofPred_and,Set.ofPred_exists,Set.ofPred_forall]
  exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
    (MeasurableSet.iUnion fun n => (measurableSet_firstLayerHit _ _ _).inter
      (MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
        (measurableSet_trueRecord _ _).compl))

lemma firstLayerHit_time_lt {d : ℕ} (h : Lattice d → ℤ) (H K : ℤ) (hHK : H < K)
    (X : Path d) (n m : ℕ) (hn : X ∈ FirstLayerHit h H n) (hm : X ∈ FirstLayerHit h K m) : n < m := by
  by_contra hh
  rcases lt_or_eq_of_le (Nat.le_of_not_lt hh) with hlt | rfl
  · have hk := hn.2 m hlt
    rw [hm.1] at hk
    omega
  · have hh := hm.1
    rw [hn.1] at hh
    exact (ne_of_lt hHK) hh

lemma noTruePastHeight_grid_cover {d : ℕ} (e : Direction d) (B k : ℕ) (hB : 0 < B)
    (X : Path d) (hNN : ∀ n, ∃ f, X (n+1)=X n+step f)
    (ht : X ∈ TransientPaths (realPosition (step e)))
    (hX : X ∈ NoTruePastHeight e ((k+1)*B)) :
    X ∈ GridReached e B k ∪ ⋃ j ∈ Finset.range k, LateGridFailure e B (j+1) := by
  induction k with
  | zero =>
    obtain ⟨h0,n,hn,_⟩ := hX
    exact Or.inl (Set.mem_iUnion.mpr ⟨n,h0,by simpa using hn⟩)
  | succ k ih =>
    obtain ⟨h0,m,hm,hnot⟩ := hX
    obtain ⟨n,hn⟩ := noDrop_firstLayerHit_exists e X h0 hNN ht
      (show 0 < (k+1)*B by positivity)
    have hnm : n < m := firstLayerHit_time_lt _ _ _ (by exact_mod_cast
      (show (k+1)*B < (k+1+1)*B by nlinarith)) X n m hn hm
    have hprev : X ∈ NoTruePastHeight e ((k+1)*B) :=
      ⟨h0,n,hn,fun t ht htn => hnot t ht (htn.trans hnm.le)⟩
    rcases ih hprev with hg | hbad
    · obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hg
      have hqn : q=n := by
        by_contra hh
        exact Set.disjoint_left.mp (firstLayerHit_disjoint (signedHeight e) ((k+1)*B:ℕ) hh)
          (gridPrefix_hit e B k q hq).2 hn
      subst q
      by_cases hdrop : X ∈ DropBetween (realPosition (step e)) n m
      · exact Or.inl (Set.mem_iUnion.mpr ⟨m,⟨h0,by simpa [Nat.add_assoc] using hm⟩,
          Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨hnm,hq,hdrop⟩⟩⟩)
      · apply Or.inr
        refine Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self k),?_⟩⟩
        apply Set.mem_iUnion.mpr
        refine ⟨n,⟨⟨h0,hn⟩,?_⟩,?_⟩
        · refine ⟨m-n,?_,?_⟩
          · change dot (realPosition (X n)) (realPosition (step e))+B ≤ dot (realPosition (X (n+(m-n)))) (realPosition (step e))
            rw [Nat.add_sub_of_le hnm.le,signedHeight_projection,signedHeight_projection,hn.1,hm.1]
            push_cast
            ring_nf
            exact le_rfl
          · intro i hi
            rw [signedHeight_projection,signedHeight_projection]
            by_contra hh
            apply hdrop
            exact ⟨n+i,by omega,by omega,by simpa only [signedHeight_projection] using lt_of_not_ge hh⟩
        · have hr := gridPrefix_record e B k n hB X hq
          exact fun hD => hnot n hr.1 hnm.le ⟨hr.2,hD⟩
    · apply Or.inr
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hbad
      obtain ⟨hj,hbad⟩ := Set.mem_iUnion.mp hj
      exact Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr
        ((Finset.mem_range.mp hj).trans (Nat.lt_succ_self k)),hbad⟩⟩

lemma noTruePastHeight_grid_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (B k : ℕ) (hB : 0 < B) :
    (annealedLaw ν).real (NoTruePastHeight e ((k+1)*B))  ≤
      (1-(annealedLaw ν).real (NoDrop (realPosition (step e)) 0))^k +
      k*(annealedLaw ν).real (Cross (realPosition (step e)) 0 B \ NoDrop (realPosition (step e)) 0) := by
  calc
    _  ≤  (annealedLaw ν).real (GridReached e B k ∪ ⋃ j ∈ Finset.range k, LateGridFailure e B (j+1)) := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono_ae
      filter_upwards [annealed_nearest_neighbor ν,htrans] with X hNN ht
      exact noTruePastHeight_grid_cover e B k hB X hNN ht
    _  ≤  (annealedLaw ν).real (GridReached e B k)+
        ∑ j ∈ Finset.range k, (annealedLaw ν).real (LateGridFailure e B (j+1)) :=
      (measureReal_union_le _ _).trans (add_le_add le_rfl
        (measureReal_biUnion_finset_le (μ := annealedLaw ν) (Finset.range k) (fun j => LateGridFailure e B (j+1))))
    _  ≤  _ := add_le_add (gridReached_geometric ν e B k hB) (by
      simpa using Finset.sum_le_sum (s := Finset.range k) (fun j _ => lateGridFailure_bound ν e htrans B (j+1) hB (by omega)))

lemma noTruePastSquare_rapidDecay {d : ℕ} (hd : 2 ≤ d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    RapidDecay (fun N => (annealedLaw ν).real (NoTruePastHeight e ((N+1)^2))) := by
  have hp := noDrop_positive_of_directionallyTransient ν (realPosition (step e)) htrans
  have hp' : 0 < (annealedLaw ν).real (NoDrop (realPosition (step e)) 0) :=
    ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  have hgeom := rapidDecay_geometric (1-(annealedLaw ν).real (NoDrop (realPosition (step e)) 0))
    (sub_nonneg.mpr measureReal_le_one) (by linarith)
  have hbad := ((crossing_failure_rapidDecay hd ν hue e htrans).shift
    (fun _ => measureReal_nonneg) 1).pow_mul 1
  apply (hgeom.add hbad).of_le (fun _ => measureReal_nonneg)
  apply Eventually.of_forall
  intro N
  have hh := noTruePastHeight_grid_bound ν e htrans (N+1) N (by omega)
  simp only [pow_two,pow_one] at hh ⊢
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by linarith : (N:ℝ) ≤ N+1)
    measureReal_nonneg))

end DirectionalTransience

end

end OAI
