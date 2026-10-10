import Mathlib
import OAI.Probability.Ballisticity.Renewal.Regeneration

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def visitCount {d : ℕ} (X : Path d) (y : Lattice d) (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, if X j=y then 1 else 0

lemma visitCount_succ {d : ℕ} (X : Path d) (y : Lattice d) (n : ℕ) :
    visitCount X y (n+1)=visitCount X y n+(if X n=y then 1 else 0) := by
  exact Finset.sum_range_succ _ n

lemma visitCount_mono {d : ℕ} (X : Path d) (y : Lattice d) : Monotone (visitCount X y) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [visitCount_succ]
  omega

lemma visitCount_exists {d : ℕ} (X : Path d) (y : Lattice d) (n k : ℕ)
    (hk : k < visitCount X y n) : ∃ j < n, X j=y ∧ visitCount X y j=k := by
  induction n with
  | zero => simp [visitCount] at hk
  | succ n ih =>
    by_cases hh : k < visitCount X y n
    · obtain ⟨j,hj,hX,hc⟩ := ih hh
      exact ⟨j,by omega,hX,hc⟩
    · rw [visitCount_succ] at hk
      split_ifs at hk with hX
      · exact ⟨n,by omega,hX,by omega⟩
      · omega

lemma measurable_visitCount {d : ℕ} (y : Lattice d) (n : ℕ) :
    Measurable (fun X : Path d => visitCount X y n) := by
  unfold visitCount
  exact Finset.measurable_sum _ fun j _ => measurable_const.ite
    (measurableSet_eq_fun (measurable_pi_apply j) measurable_const) measurable_const

lemma visitCount_prefix {d : ℕ} (X Y : Path d) (y : Lattice d) (n : ℕ)
    (h : ∀ j < n, X j=Y j) : visitCount X y n=visitCount Y y n := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (Finset.mem_range.mp hj)]

def VisitPrefix {d : ℕ} (x : Lattice d) (S : Set (Lattice d)) (y : Lattice d) (k n : ℕ) :
    Set (Path d) := {X | X 0=x ∧ X n=y ∧ (∀ j ≤ n, X j∈S) ∧ visitCount X y n=k}

def VisitReached {d : ℕ} (x : Lattice d) (S : Set (Lattice d)) (y : Lattice d) (k : ℕ) :
    Set (Path d) := ⋃ n, VisitPrefix x S y k n

lemma measurableSet_visitPrefix {d : ℕ} (x : Lattice d) (S : Set (Lattice d)) (y : Lattice d) (k n : ℕ) :
    MeasurableSet (VisitPrefix x S y k n) := by
  unfold VisitPrefix
  simp only [Set.ofPred_and,Set.ofPred_forall]
  exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
    ((measurableSet_eq_fun (measurable_pi_apply n) measurable_const).inter
      ((MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (measurable_pi_apply j) ((Set.to_countable S).measurableSet)).inter
        (measurableSet_eq_fun (measurable_visitCount y n) measurable_const)))

lemma visitPrefix_prefix {d : ℕ} (x : Lattice d) (S : Set (Lattice d)) (y : Lattice d) (k n : ℕ) :
    PrefixDetermined n (VisitPrefix x S y k n) := by
  intro X Y hXY
  have hc := visitCount_prefix X Y y n (fun j hj => hXY j hj.le)
  simp only [VisitPrefix,Set.mem_ofPred_eq,hXY 0 (Nat.zero_le n),hXY n le_rfl,hc]
  have hh : (∀ j ≤ n, X j∈S) ↔ ∀ j ≤ n, Y j∈S := by
    apply forall_congr'; intro j
    apply forall_congr'; intro hj
    rw [hXY j hj]
  rw [hh]

lemma measurableSet_visitReached {d : ℕ} (x : Lattice d) (S : Set (Lattice d)) (y : Lattice d) (k : ℕ) :
    MeasurableSet (VisitReached x S y k) := MeasurableSet.iUnion (measurableSet_visitPrefix x S y k)

lemma visitPrefix_disjoint {d : ℕ} (x : Lattice d) (S : Set (Lattice d)) (y : Lattice d) (k : ℕ) :
    Pairwise (fun n m => Disjoint (VisitPrefix x S y k n) (VisitPrefix x S y k m)) := by
  have hh (n m : ℕ) (hnm : n < m) (X : Path d) (hn : X ∈ VisitPrefix x S y k n)
      (hm : X ∈ VisitPrefix x S y k m) : False := by
    have hc := visitCount_mono X y (show n+1 ≤ m by omega)
    rw [visitCount_succ,hn.2.1,ite_eq_left rfl,hn.2.2.2,hm.2.2.2] at hc
    omega
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro X hn hm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact hh n m hlt X hn hm
  · exact hh m n hgt X hm hn

lemma visitReached_succ_subset {d : ℕ} (x : Lattice d) (S : Set (Lattice d)) (y : Lattice d) (k : ℕ) :
    VisitReached x S y (k+1) ⊆ VisitReached x S y k := by
  intro X hX
  obtain ⟨m,hm⟩ := Set.mem_iUnion.mp hX
  obtain ⟨n,hn,hny,hc⟩ := visitCount_exists X y m k (by rw [hm.2.2.2]; omega)
  exact Set.mem_iUnion.mpr ⟨n,hm.1,hny,fun j hj => hm.2.2.1 j (hj.trans hn.le),hc⟩

def ReturnIn {d : ℕ} (S : Set (Lattice d)) (y : Lattice d) : Set (Path d) :=
  {X | ∃ n, 0 < n ∧ X n=y ∧ ∀ j ≤ n, X j∈S}

lemma measurableSet_returnIn {d : ℕ} (S : Set (Lattice d)) (y : Lattice d) :
    MeasurableSet (ReturnIn S y) := by
  unfold ReturnIn
  simp only [Set.ofPred_exists,Set.ofPred_and,Set.ofPred_forall]
  exact MeasurableSet.iUnion fun n => (MeasurableSet.const _).inter
    ((measurableSet_eq_fun (measurable_pi_apply n) measurable_const).inter
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        (measurable_pi_apply j) ((Set.to_countable S).measurableSet)))

lemma visitReached_succ_return {d : ℕ} (x : Lattice d) (S : Set (Lattice d)) (y : Lattice d)
    (k n : ℕ) (X : Path d) (hn : X ∈ VisitPrefix x S y k n)
    (hnext : X ∈ VisitReached x S y (k+1)) :
    (fun j => X (n+j)) ∈ ReturnIn S y := by
  obtain ⟨m,hm⟩ := Set.mem_iUnion.mp hnext
  have hnm : n < m := by
    by_contra hh
    have hc := visitCount_mono X y (by omega : m ≤ n)
    rw [hn.2.2.2,hm.2.2.2] at hc
    omega
  refine ⟨m-n,by omega,by simpa only [Nat.add_sub_of_le hnm.le] using hm.2.1,?_⟩
  intro j hj
  exact hm.2.2.1 (n+j) (by omega)

lemma visitReached_contraction {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S : Set (Lattice d)) (y : Lattice d) (k : ℕ) (A : Set (Path d))
    (hA : MeasurableSet A) (hdis : Disjoint A (ReturnIn S y)) :
    (quenchedKernel (ω,x)).real (VisitReached x S y (k+1))  ≤
      (1-(quenchedKernel (ω,y)).real A)*(quenchedKernel (ω,x)).real (VisitReached x S y k) := by
  let μ := quenchedKernel (ω,x)
  have hg := stopping_prefix_favourable_gain μ (VisitPrefix x S y k) (VisitReached x S y (k+1))
    (quenchedKernel (ω,y) A) (visitPrefix_prefix x S y k) (measurableSet_visitPrefix x S y k)
    (visitPrefix_disjoint x S y k) (measurableSet_visitReached x S y (k+1))
    (visitReached_succ_subset x S y k) (by
      intro n f hf
      let F := (fun X : Path d => fun i => X (n+i)) ⁻¹' A ∩ pathCylinder f n
      refine ⟨F,(hA.preimage (by fun_prop)).inter (measurableSet_pathCylinder f n),Set.inter_subset_right,?_,?_⟩
      · apply Set.disjoint_left.mpr
        intro X hnext hF
        have hpre := (visitPrefix_prefix x S y k n X f hF.2).mpr hf
        exact Set.disjoint_left.mp hdis hF.1 (visitReached_succ_return x S y k n X hpre hnext)
      · simpa only [hf.2.1] using quenched_prefix_future ω x f hf.1 n hA)
  have hr := ENNReal.toReal_mono (measure_ne_top μ _) hg
  rw [ENNReal.toReal_add (measure_ne_top μ _)
    (ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top (quenchedKernel (ω,y)) _)),ENNReal.toReal_mul] at hr
  change μ.real (VisitReached x S y (k+1))+μ.real (VisitReached x S y k)*(quenchedKernel (ω,y)).real A  ≤
    μ.real (VisitReached x S y k) at hr
  change μ.real _ ≤ (1-(quenchedKernel (ω,y)).real A)*μ.real _
  nlinarith

lemma visitReached_geometric {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S : Set (Lattice d)) (y : Lattice d) (k : ℕ) (A : Set (Path d))
    (hA : MeasurableSet A) (hdis : Disjoint A (ReturnIn S y)) (δ : ℝ)
    (hδ : δ ≤ (quenchedKernel (ω,y)).real A) :
    (quenchedKernel (ω,x)).real (VisitReached x S y k)  ≤  (1-δ)^k := by
  have hp : (quenchedKernel (ω,y)).real A ≤ 1 := measureReal_le_one
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _  ≤  (1-(quenchedKernel (ω,y)).real A)*(quenchedKernel (ω,x)).real (VisitReached x S y k) :=
        visitReached_contraction ω x S y k A hA hdis
      _  ≤  (1-δ)*(1-δ)^k := mul_le_mul (by linarith) ih measureReal_nonneg (by linarith)
      _ = _ := by rw [pow_succ]; ring

end DirectionalTransience

end

end OAI
