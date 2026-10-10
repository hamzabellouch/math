import Mathlib
import OAI.Probability.Ballisticity.Estimates.GlobalProfile

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

abbrev UpperRows {d : ℕ} (e : Direction d) := (ℕ×HorizontalSpace e) → Row d

noncomputable def upperEnvironment {d : ℕ} (e : Direction d) (ξ : UpperRows e) : Environment d :=
  fun x => ξ ((signedHeight e x).toNat,horizontalProjection e x)

lemma upperEnvironment_continuous {d : ℕ} (e : Direction d) : Continuous (upperEnvironment e) := by
  unfold upperEnvironment
  fun_prop

lemma upperEnvironment_lift {d : ℕ} (e : Direction d) (ξ : UpperRows e)
    (l : ℕ) (z : HorizontalSpace e) :
    upperEnvironment e ξ (horizontalLift e l z)=ξ (l,z) := by
  simp only [upperEnvironment,signedHeight_horizontalLift,horizontalProjection_lift,Int.toNat_natCast]

lemma continuous_wordWeight {d : ℕ} (x : Lattice d) (w : List (Direction d)) :
    Continuous (fun ω : Environment d => wordWeight ω x w) := by
  induction w generalizing x with
  | nil => exact continuous_const
  | cons u w ih =>
    change Continuous (fun ω : Environment d => ((ω x).1 u:ℝ)*wordWeight ω (x+step u) w)
    exact (NNReal.continuous_coe.comp ((continuous_apply u).comp (continuous_subtype_val.comp (continuous_apply x)))).mul (ih _)

lemma hitKernel_eq_tsum_words {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (hST : Disjoint S T) (A : Set (Lattice d)) :
    hitKernel S T (ω,x) A =
      ∑' w : {w : HitWord x S T // wordPath x w.val w.val.length∈A},
        ENNReal.ofReal (wordWeight ω x w.val.val) := by
  rw [←successfulWordLaw_endpoint ω x S T hST,
    Measure.map_apply (measurable_of_countable _) (Set.to_countable A).measurableSet,
    successfulWordLaw_apply]
  rfl

lemma hitKernel_lowerSemicontinuous {d : ℕ} (x : Lattice d)
    (S T : Set (Lattice d)) (hST : Disjoint S T) (A : Set (Lattice d)) :
    LowerSemicontinuous (fun ω : Environment d => hitKernel S T (ω,x) A) := by
  simp_rw [hitKernel_eq_tsum_words _ x S T hST A]
  exact lowerSemicontinuous_tsum fun w =>
    (ENNReal.continuous_ofReal.comp (continuous_wordWeight x w.val.val)).lowerSemicontinuous

noncomputable def upperHorizontalKernel {d : ℕ} (e : Direction d) (H : ℕ) (ξ : UpperRows e) :
    Kernel (HorizontalSpace e) (HorizontalSpace e) :=
  Kernel.mk (fun z => (variableHitKernel (realPosition (step e)) H (upperEnvironment e ξ,horizontalLift e 0 z)).map
    (horizontalProjection e)) (measurable_of_countable _)

lemma upperHorizontalKernel_apply {d : ℕ} (e : Direction d) (H : ℕ) (ξ : UpperRows e)
    (z : HorizontalSpace e) (A : Set (HorizontalSpace e)) :
    upperHorizontalKernel e H ξ z A =
      hitKernel (Strip (realPosition (step e)) (horizontalLift e 0 z) H)
        (Upper (realPosition (step e)) (horizontalLift e 0 z) H)
        (upperEnvironment e ξ,horizontalLift e 0 z) (horizontalProjection e ⁻¹' A) := by
  rw [upperHorizontalKernel,Kernel.coe_mk,Measure.map_apply (measurable_of_countable _) (Set.to_countable A).measurableSet]
  rfl

lemma upperHorizontalKernel_lowerSemicontinuous {d : ℕ} (e : Direction d) (H : ℕ)
    (z : HorizontalSpace e) (A : Set (HorizontalSpace e)) :
    LowerSemicontinuous (fun ξ : UpperRows e => upperHorizontalKernel e H ξ z A) := by
  simp_rw [upperHorizontalKernel_apply]
  exact (hitKernel_lowerSemicontinuous _ _ _ (disjoint_strip_upper _ _ _) _).comp
    (upperEnvironment_continuous e)

lemma upperHorizontalKernel_mass_le_one {d : ℕ} (e : Direction d) (H : ℕ) (ξ : UpperRows e)
    (z : HorizontalSpace e) : upperHorizontalKernel e H ξ z Set.univ ≤ 1 := by
  rw [upperHorizontalKernel_apply,Set.preimage_univ]
  exact hitKernel_total_le_one (disjoint_strip_upper _ _ _) _

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical BigOperators
namespace DirectionalTransience

lemma wordPath_endpoint_sum {d : ℕ} (x : Lattice d) (w : List (Direction d)) :
    wordPath x w w.length=x+(w.map step).sum := by
  induction w generalizing x with
  | nil => simp [wordPath]
  | cons u w ih => simp [wordPath,ih,add_assoc]

lemma wordPath_replicate_min {d : ℕ} (x : Lattice d) (u : Direction d) (k n : ℕ) :
    wordPath x (List.replicate k u) n=x+(min n k:ℕ) • step u := by
  induction k generalizing x n with
  | zero => simp [wordPath]
  | succ k ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [List.replicate_succ,wordPath,ih,min_add_add_right,succ_nsmul]
      abel

lemma exists_horizontal_word {d : ℕ} (e : Direction d) (z : HorizontalSpace e) :
    ∃ w : List (Direction d), (w.map step).sum=z.val ∧ ∀ u∈w, u.1≠e.1 := by
  have hsingle (i : Fin d) : ∃ w : List (Direction d),
      (w.map step).sum=Pi.single i (z.val i) ∧ ∀ u∈w, u.1≠e.1 := by
    by_cases hi : i=e.1
    · subst i
      refine ⟨[],?_,by simp⟩
      have hz : z.val e.1=0 := z.property
      simp [hz]
    · cases hz : z.val i with
      | ofNat n =>
        refine ⟨List.replicate n (i,true),?_,?_⟩
        · simp only [List.map_replicate,List.sum_replicate]
          funext j
          by_cases hj : j=i
          · subst j; simp [step]
          · simp [step,hj]
        · intro u hu
          have he := List.eq_of_mem_replicate hu
          simpa only [he] using hi
      | negSucc n =>
        refine ⟨List.replicate (n+1) (i,false),?_,?_⟩
        · simp only [List.map_replicate,List.sum_replicate]
          funext j
          by_cases hj : j=i
          · subst j; simp [step]; omega
          · simp [step,hj]
        · intro u hu
          have he := List.eq_of_mem_replicate hu
          simpa only [he] using hi
  have hf (s : Finset (Fin d)) : ∃ w : List (Direction d),
      (w.map step).sum=∑ i∈s, Pi.single i (z.val i) ∧ ∀ u∈w, u.1≠e.1 := by
    induction s using Finset.induction_on with
    | empty => exact ⟨[],by simp,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨v,hv,hve⟩ := hsingle i
      obtain ⟨w,hw,hwe⟩ := ih
      refine ⟨v++w,by simp [hv,hw,hi],?_⟩
      intro u hu
      rcases List.mem_append.mp hu with hu|hu
      · exact hve u hu
      · exact hwe u hu
  obtain ⟨w,hw,hwe⟩ := hf Finset.univ
  refine ⟨w,hw.trans ?_,hwe⟩
  funext j
  simp

lemma wordPath_horizontal {d : ℕ} (e : Direction d) (x : Lattice d)
    (w : List (Direction d)) (hw : ∀ u∈w, u.1≠e.1) (n : ℕ) :
    signedHeight e (wordPath x w n)=signedHeight e x := by
  induction w generalizing x n with
  | nil => rfl
  | cons u w ih =>
    cases n with
    | zero => rfl
    | succ n =>
      rw [wordPath,ih (x+step u) (fun g hg => hw g (by simp [hg]))]
      have hu := hw u (by simp)
      rw [signedHeight_add]
      simp [signedHeight, step,Ne.symm hu]

lemma positive_wordWeight {d : ℕ} (ω : Environment d)
    (hω : ∀ x u, 0<(ω x).val u) (x : Lattice d) (w : List (Direction d)) :
    0<wordWeight ω x w := by
  induction w generalizing x with
  | nil => norm_num [wordWeight]
  | cons u w ih =>
    exact mul_pos (NNReal.coe_pos.mpr (hω x u)) (ih _)

lemma upperHorizontalKernel_pos {d : ℕ} (e : Direction d) (H : ℕ) (hH : 0<H)
    (ξ : UpperRows e) (hξ : ∀ p u, 0<(ξ p).val u) (x y : HorizontalSpace e) :
    0<upperHorizontalKernel e H ξ x {y} := by
  obtain ⟨v,hv,hve⟩ := exists_horizontal_word e (y-x)
  let w := v++List.replicate H e
  have hend : wordPath (horizontalLift e 0 x) v v.length=horizontalLift e 0 y := by
    rw [wordPath_endpoint_sum,hv]
    simp only [horizontalLift,zero_zsmul,add_zero,AddSubgroup.coe_sub]
    abel
  have hy : wordPath (horizontalLift e 0 x) w w.length=horizontalLift e H y := by
    simp only [w,List.length_append,List.length_replicate]
    rw [wordPath_append_suffix,hend,wordPath_replicate_min,Nat.min_self]
    simp [horizontalLift]
  have hh : wordPath (horizontalLift e 0 x) w∈HitAt
      (Strip (realPosition (step e)) (horizontalLift e 0 x) H)
      (Upper (realPosition (step e)) (horizontalLift e 0 x) H) w.length := by
    constructor
    · rw [coordinate_mem_upper_iff,hy,signedHeight_horizontalLift,signedHeight_horizontalLift]
      omega
    · intro n hn
      rw [coordinate_mem_strip_iff,signedHeight_horizontalLift]
      by_cases hnv : n≤v.length
      · have he := wordPath_append_prefix (horizontalLift e 0 x) v (List.replicate H e) hnv
        rw [he,wordPath_horizontal e _ v hve,signedHeight_horizontalLift]
        omega
      · have hn' : n=v.length+(n-v.length) := by omega
        rw [hn',wordPath_append_suffix,hend,wordPath_replicate_min,signedHeight_add,
          signedHeight_horizontalLift]
        have hmin : min (n-v.length) H=n-v.length := by
          have hh : n<v.length+H := by simpa only [w,List.length_append,List.length_replicate] using hn
          omega
        rw [hmin]
        have he : signedHeight e ((n-v.length) • step e)=(n-v.length:ℕ) := by
          exact_mod_cast signedHeight_zsmul_step e (n-v.length:ℕ)
        rw [he]
        have hh : n<v.length+H := by simpa only [w,List.length_append,List.length_replicate] using hn
        omega
  rw [upperHorizontalKernel_apply,hitKernel_eq_tsum_words _ _ _ _ (disjoint_strip_upper _ _ _) _]
  let a : {w : HitWord (horizontalLift e 0 x)
      (Strip (realPosition (step e)) (horizontalLift e 0 x) H)
      (Upper (realPosition (step e)) (horizontalLift e 0 x) H) //
      wordPath (horizontalLift e 0 x) w.val w.val.length∈horizontalProjection e ⁻¹' {y}} :=
    ⟨⟨w,hh⟩,by change horizontalProjection e (wordPath _ w w.length)=y; rw [hy,horizontalProjection_lift]⟩
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (positive_wordWeight (upperEnvironment e ξ)
    (fun z u => hξ _ u) (horizontalLift e 0 x) w))
    (ENNReal.le_tsum (f := fun term => ENNReal.ofReal
      (wordWeight (upperEnvironment e ξ) (horizontalLift e 0 x) term.val.val)) a)

end DirectionalTransience

end

end OAI
