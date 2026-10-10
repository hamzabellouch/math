import Mathlib
import OAI.Probability.ParisiFinite.BranchNumerator

namespace OAI

/-! Hierarchy Numerator. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open scoped BigOperators Topology NNReal
open scoped BigOperators NNReal Topology
open scoped BigOperators NNReal
open scoped NNReal Topology
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace
open MeasureTheory ProbabilityTheory Filter TopologicalSpace Set MeasurableSpace
open scoped BigOperators Topology NNReal ENNReal MatrixOrder
open scoped BigOperators Topology NNReal ENNReal ContDiff
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def hierarchyNumerator {d r : ℕ} (a : Fin (d+1) → ℝ) (c : Fin (d+1) → Fin r → ℕ) : ℝ :=
  (∏ k : Fin d,edgeFactor (a k.succ) (a k.castSucc) (c k.castSucc) (c k.succ))*
    leafFactor (a (Fin.last d)) (c (Fin.last d))

lemma hierarchyNumerator_existing {d r : ℕ} (a : Fin (d+1) → ℝ)
    (c : Fin (d+1) → Fin (r+1) → ℕ) (hc : NestedCodes c)
    (i : Fin r) (hi : restrictCode (c (Fin.last d)) i=c (Fin.last d) (Fin.last r)) :
    hierarchyNumerator a c=
      ((clusterCount (restrictCode (c (Fin.last d))) i:ℝ)-a (Fin.last d))*
        hierarchyNumerator a (fun k => restrictCode (c k)) := by
  have he : (∏ k : Fin d,edgeFactor (a k.succ) (a k.castSucc) (c k.castSucc) (c k.succ))=
      ∏ k : Fin d,edgeFactor (a k.succ) (a k.castSucc) (restrictCode (c k.castSucc)) (restrictCode (c k.succ)) := by
    apply Finset.prod_congr rfl
    intro k _
    apply edgeFactor_existing _ _ _ _ (hc _ _ (by change (k:ℕ)≤(k:ℕ)+1; omega)) i
    exact hc k.succ (Fin.last d) (Fin.le_last _) _ _ hi
  unfold hierarchyNumerator
  rw [he,leafFactor_existing _ _ i hi]
  ring

lemma hierarchyNumerator_fresh {d r : ℕ} (a : Fin (d+1) → ℝ)
    (c : Fin (d+1) → Fin (r+1) → ℕ) (hc : NestedCodes c)
    (k : Fin d) (i : Fin r) (hi : restrictCode (c k.castSucc) i=c k.castSucc (Fin.last r))
    (hn : ∀ j,restrictCode (c k.succ) j≠c k.succ (Fin.last r)) :
    hierarchyNumerator a c=
      (a k.succ*((childLabels (restrictCode (c k.castSucc)) (restrictCode (c k.succ))
        (restrictCode (c k.castSucc) i)).card:ℝ)-a k.castSucc)*
          hierarchyNumerator a (fun l => restrictCode (c l)) := by
  let e (l : Fin d) := edgeFactor (a l.succ) (a l.castSucc) (c l.castSucc) (c l.succ)
  let e' (l : Fin d) := edgeFactor (a l.succ) (a l.castSucc) (restrictCode (c l.castSucc)) (restrictCode (c l.succ))
  let A := a k.succ*((childLabels (restrictCode (c k.castSucc)) (restrictCode (c k.succ))
      (restrictCode (c k.castSucc) i)).card:ℝ)-a k.castSucc
  have hek : e k=A*e' k := edgeFactor_fresh_child _ _ _ _ i hi hn
  have hel : ∀ l,l≠k → e l=e' l := by
    intro l hl
    rcases lt_or_gt_of_ne hl with hl | hl
    · apply edgeFactor_existing _ _ _ _ (hc _ _ (by change (l:ℕ)≤(l:ℕ)+1; omega)) i
      apply hc l.succ k.castSucc (by change (l:ℕ)+1≤(k:ℕ); exact hl) _ _ hi
    · apply edgeFactor_fresh_parent
      intro j hj
      apply hn j
      exact hc k.succ l.castSucc (by change (k:ℕ)+1≤(l:ℕ); exact hl) _ _ hj
  have hprod : (∏ l,e l)=A*∏ l,e' l := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
    have hh : (∏ l∈Finset.univ.erase k,e l)=∏ l∈Finset.univ.erase k,e' l :=
      Finset.prod_congr rfl (fun l hl => hel l (Finset.mem_erase.mp hl).1)
    rw [hek,hh]
    ring
  have hleaf : leafFactor (a (Fin.last d)) (c (Fin.last d))=
      leafFactor (a (Fin.last d)) (restrictCode (c (Fin.last d))) := by
    apply leafFactor_fresh
    intro j hj
    exact hn j (hc k.succ (Fin.last d) (Fin.le_last _) _ _ hj)
  change (∏ l,e l)*_=A*((∏ l,e' l)*_)
  rw [hprod,hleaf]
  ring

lemma codeLabels_one (c : Fin 1 → ℕ) : codeLabels c={c 0} := by
  ext x
  simp only [codeLabels_mem,Finset.mem_singleton]
  exact ⟨fun ⟨i,hi⟩ => by fin_cases i; exact hi.symm,fun h => ⟨0,h.symm⟩⟩

lemma childLabels_one (p c : Fin 1 → ℕ) : childLabels p c (p 0)={c 0} := by
  ext y
  simp only [mem_childLabels,Finset.mem_singleton]
  exact ⟨fun ⟨i,_,hi⟩ => by fin_cases i; exact hi.symm,fun h => ⟨0,rfl,h.symm⟩⟩

lemma edgeFactor_one (a b : ℝ) (p c : Fin 1 → ℕ) : edgeFactor a b p c=1 := by
  simp [edgeFactor,codeLabels_one,childLabels_one]

lemma leafFactor_one (a : ℝ) (c : Fin 1 → ℕ) : leafFactor a c=1 := by
  have hn : labelCount c (c 0)=1 := by simp [labelCount,Finset.filter_singleton]
  simp [leafFactor,codeLabels_one,hn]

lemma hierarchyNumerator_one {d : ℕ} (a : Fin (d+1) → ℝ) (c : Fin (d+1) → Fin 1 → ℕ) :
    hierarchyNumerator a c=1 := by simp [hierarchyNumerator,edgeFactor_one,leafFactor_one]

lemma exists_hierarchy_branch {d r : ℕ} (hr : 0<r) (c : Fin (d+1) → Fin (r+1) → ℕ)
    (hroot : ∀ i j,c 0 i=c 0 j)
    (hleaf : ∀ i,restrictCode (c (Fin.last d)) i≠c (Fin.last d) (Fin.last r)) :
    ∃ (k : Fin d) (i : Fin r),restrictCode (c k.castSucc) i=c k.castSucc (Fin.last r) ∧
      ∀ j,restrictCode (c k.succ) j≠c k.succ (Fin.last r) := by
  let S := Finset.univ.filter (fun k => ∃ i,restrictCode (c k) i=c k (Fin.last r))
  have hS : S.Nonempty := ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨⟨0,hr⟩,hroot _ _⟩⟩⟩
  let l := S.max' hS
  have hl : ∃ i,restrictCode (c l) i=c l (Fin.last r) := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
  have hne : l≠Fin.last d := by
    intro hh
    obtain ⟨i,hi⟩ := hl
    rw [hh] at hi
    exact hleaf i hi
  have hlt : (l:ℕ)<d := by have := l.isLt; have hh := Fin.val_injective.ne hne; simp only [Fin.val_last] at hh; omega
  let k : Fin d := ⟨l.val,hlt⟩
  have hk : k.castSucc=l := Fin.ext rfl
  obtain ⟨i,hi⟩ := hl
  refine ⟨k,i,by rwa [hk],?_⟩
  intro j hj
  have hs : k.succ∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨j,hj⟩⟩
  have hm : k.succ≤l := Finset.le_max' S k.succ hs
  change (l:ℕ)+1≤(l:ℕ) at hm
  omega

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma hierarchy_one_real {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) {d : ℕ}
    (c : Fin (d+1) → Fin 1 → ℕ) (q : Fin (d+1) → ℝ) (hq : ∀ k,q k<1) :
    (μ:Measure OverlapArray).real (hierarchyEvent c q)=1 := by
  have he : hierarchyEvent c q =ᵐ[(μ:Measure OverlapArray)] Set.univ := by
    filter_upwards [ae_full_probability μ isClosed_GramArrays.measurableSet hG] with R hg
    apply propext
    change (∀ k,∀ i j : Fin 1,q k<(R i j:ℝ) ↔ c k i=c k j) ↔ True
    rw [iff_true]
    intro k i j
    fin_cases i; fin_cases j
    change q k<(R 0 0:ℝ) ↔ _
    rw [hg.2.1]
    simp [hq k]
  rw [measureReal_congr he,probReal_univ]

 

theorem GG_hierarchy_EPPF {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d r : ℕ} (hr : 0<r) (c : Fin (d+1) → Fin r → ℕ) (hc : NestedCodes c)
    (hroot : ∀ i j,c 0 i=c 0 j)
    (q : Fin (d+1) → ℝ) (hq : Monotone q) (h1 : q (Fin.last d)<1) :
    ((r-1).factorial:ℝ)*(μ:Measure OverlapArray).real (hierarchyEvent c q)=
      hierarchyNumerator (fun k => overlapDiscount μ (q k)) c := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hr0 : r=0
    · subst r
      rw [hierarchy_one_real hG c q (fun k => (hq (Fin.le_last _)).trans_lt h1),hierarchyNumerator_one]
      norm_num
    have hr' : 0<r := Nat.pos_of_ne_zero hr0
    have hold := ih hr' (fun k => restrictCode (c k)) (nestedCodes_restrict hc)
      (fun i j => hroot i.castSucc j.castSucc)
    have hf : (r.factorial:ℝ)=(r:ℝ)*((r-1).factorial:ℝ) := by
      exact_mod_cast (Nat.mul_factorial_pred hr0).symm
    simp only [Nat.add_sub_cancel] at *
    by_cases hleaf : ∃ i,restrictCode (c (Fin.last d)) i=c (Fin.last d) (Fin.last r)
    · obtain ⟨i,hi⟩ := hleaf
      rw [hierarchyNumerator_existing _ c hc i hi,hf]
      have he := GG_hierarchy_existing hG hgg hu c hc q hq h1 i hi
      linear_combination ((r-1).factorial:ℝ)*he+
        ((clusterCount (restrictCode (c (Fin.last d))) i:ℝ)-overlapDiscount μ (q (Fin.last d)))*hold
    · obtain ⟨k,i,hi,hn⟩ := exists_hierarchy_branch hr' c hroot (not_exists.mp hleaf)
      obtain ⟨T,hT⟩ := exists_parentReps ((nestedCodes_restrict hc) k.castSucc k.succ
        (by change (k:ℕ)≤(k:ℕ)+1; omega)) i
      rw [hierarchyNumerator_fresh _ c hc k i hi hn,hf]
      have he := GG_hierarchy_fresh hG hgg hu c hc q hq h1 k i hi hn hT
      rw [hT.card_childLabels] at he
      linear_combination ((r-1).factorial:ℝ)*he+
        (overlapDiscount μ (q k.succ)*
          ((childLabels (restrictCode (c k.castSucc)) (restrictCode (c k.succ))
            (restrictCode (c k.castSucc) i)).card:ℝ)-overlapDiscount μ (q k.castSucc))*hold

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def splitCode {r : ℕ} (P : OrderedFinpartition r) (c : ∀ i,Fin (P.partSize i) → ℕ) : Fin r → ℕ :=
  fun j => let s := P.equivSigma.symm j; Nat.pair s.1.val (c s.1 s.2)

lemma splitCode_emb {r : ℕ} (P : OrderedFinpartition r) (c : ∀ i,Fin (P.partSize i) → ℕ)
    (i : Fin P.length) (j : Fin (P.partSize i)) : splitCode P c (P.emb i j)=Nat.pair i.val (c i j) := by
  change (fun s : Σ i,Fin (P.partSize i) => Nat.pair s.1.val (c s.1 s.2))
    (P.equivSigma.symm (P.equivSigma ⟨i,j⟩))=_
  rw [P.equivSigma.symm_apply_apply]

lemma pair_left_injective (i : ℕ) : Function.Injective (Nat.pair i) :=
  fun _ _ h => (Nat.pair_eq_pair.mp h).2

lemma codeLabels_split {r : ℕ} (P : OrderedFinpartition r) (c : ∀ i,Fin (P.partSize i) → ℕ) :
    codeLabels (splitCode P c)=Finset.univ.biUnion
      (fun i => (codeLabels (c i)).image (Nat.pair i.val)) := by
  ext y
  simp only [codeLabels_mem,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_image]
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨⟨i,k⟩,rfl⟩ := P.equivSigma.surjective j
    change splitCode P c (P.emb i k)=y at hj
    rw [splitCode_emb] at hj
    exact ⟨i,c i k,⟨k,rfl⟩,hj⟩
  · rintro ⟨i,x,hx,hy⟩
    obtain ⟨j,hj⟩ := hx
    refine ⟨P.emb i j,?_⟩
    rw [splitCode_emb,hj,hy]

lemma prod_codeLabels_split {r : ℕ} (P : OrderedFinpartition r) (c : ∀ i,Fin (P.partSize i) → ℕ)
    (F : ℕ → ℝ) :
    (∏ y∈codeLabels (splitCode P c),F y)=∏ i,∏ y∈codeLabels (c i),F (Nat.pair i.val y) := by
  rw [codeLabels_split,Finset.prod_biUnion]
  · apply Finset.prod_congr rfl
    intro i _
    exact Finset.prod_image (pair_left_injective i.val).injOn
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro y hi hj
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hi
    obtain ⟨z,_,hz⟩ := Finset.mem_image.mp hj
    exact hij (Fin.ext (Nat.pair_eq_pair.mp (hx.trans hz.symm)).1)

lemma labelCount_split {r : ℕ} (P : OrderedFinpartition r) (c : ∀ i,Fin (P.partSize i) → ℕ)
    (i : Fin P.length) (x : ℕ) : labelCount (splitCode P c) (Nat.pair i.val x)=labelCount (c i) x := by
  have hcnt {n : ℕ} (f : Fin n → ℕ) (y : ℕ) : labelCount f y=∑ j,if f j=y then 1 else 0 := by
    simp [labelCount]
  rw [hcnt,← P.sum_sigma_eq_sum]
  simp only [splitCode_emb,Nat.pair_eq_pair,Fin.val_inj]
  rw [Finset.sum_eq_single i]
  · simp only [true_and]
    exact (hcnt _ _).symm
  · intro j _ hji
    simp [hji]
  · simp

lemma childLabels_split {r : ℕ} (P : OrderedFinpartition r)
    (p c : ∀ i,Fin (P.partSize i) → ℕ) (i : Fin P.length) (x : ℕ) :
    childLabels (splitCode P p) (splitCode P c) (Nat.pair i.val x)=
      (childLabels (p i) (c i) x).image (Nat.pair i.val) := by
  ext y
  simp only [mem_childLabels,Finset.mem_image]
  constructor
  · rintro ⟨j,hp,hc⟩
    obtain ⟨⟨k,l⟩,rfl⟩ := P.equivSigma.surjective j
    change splitCode P p (P.emb k l)=_ at hp
    change splitCode P c (P.emb k l)=_ at hc
    rw [splitCode_emb] at hp hc
    have hki : k=i := Fin.ext (Nat.pair_eq_pair.mp hp).1
    subst k
    exact ⟨c i l,⟨l,(Nat.pair_eq_pair.mp hp).2,rfl⟩,hc⟩
  · rintro ⟨z,hz,hy⟩
    obtain ⟨j,hp,hc⟩ := hz
    refine ⟨P.emb i j,?_,?_⟩
    · rw [splitCode_emb,hp]
    · rw [splitCode_emb,hc,hy]

lemma leafFactor_split {r : ℕ} (a : ℝ) (P : OrderedFinpartition r)
    (c : ∀ i,Fin (P.partSize i) → ℕ) :
    leafFactor a (splitCode P c)=∏ i,leafFactor a (c i) := by
  unfold leafFactor
  rw [prod_codeLabels_split]
  simp_rw [labelCount_split]

lemma edgeFactor_split {r : ℕ} (a b : ℝ) (P : OrderedFinpartition r)
    (p c : ∀ i,Fin (P.partSize i) → ℕ) :
    edgeFactor a b (splitCode P p) (splitCode P c)=∏ i,edgeFactor a b (p i) (c i) := by
  unfold edgeFactor
  rw [prod_codeLabels_split]
  simp_rw [childLabels_split,Finset.card_image_of_injective _ (pair_left_injective _)]

lemma codeLabels_const {r : ℕ} (hr : 0<r) (x : ℕ) : codeLabels (fun _ : Fin r => x)={x} := by
  ext y
  simp only [codeLabels_mem,Finset.mem_singleton]
  exact ⟨fun ⟨_,h⟩ => h.symm,fun h => ⟨⟨0,hr⟩,h.symm⟩⟩

lemma labelCount_const (r x : ℕ) : labelCount (fun _ : Fin r => x) x=r := by
  simp [labelCount]

lemma leafFactor_const (a : ℝ) (r x : ℕ) : leafFactor a (fun _ : Fin r => x)=blockFactor a r := by
  by_cases hr : r=0
  · subst r
    simp [leafFactor,codeLabels,blockFactor]
  · unfold leafFactor
    rw [codeLabels_const (Nat.pos_of_ne_zero hr),Finset.prod_singleton,labelCount_const]

lemma edgeFactor_root {r : ℕ} (a b : ℝ) (P : OrderedFinpartition r) :
    edgeFactor a b (fun _ : Fin r => 0) (splitCode P (fun _ _ => 0))=branchFactor a b P.length := by
  by_cases hr : r=0
  · subst r
    have hl : P.length=0 := Nat.eq_zero_of_not_pos fun h => by
      have hh := P.length_le
      omega
    simp [edgeFactor,codeLabels,hl,branchFactor]
  have he : codeLabels (splitCode P (fun _ _ => 0))=
      Finset.univ.image (fun i : Fin P.length => Nat.pair i.val 0) := by
    rw [codeLabels_split]
    ext y
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_image]
    simp_rw [codeLabels_const (P.partSize_pos _),Finset.mem_singleton]
    aesop
  have hcard : (codeLabels (splitCode P (fun _ _ => 0))).card=P.length := by
    rw [he,Finset.card_image_of_injective]
    · simp
    · intro i j hij
      exact Fin.ext (Nat.pair_eq_pair.mp hij).1
  have hchild : childLabels (fun _ : Fin r => 0) (splitCode P (fun _ _ => 0)) 0=
      codeLabels (splitCode P (fun _ _ => 0)) := by simp [childLabels,codeLabels]
  unfold edgeFactor
  rw [codeLabels_const (Nat.pos_of_ne_zero hr),Finset.prod_singleton,hchild,hcard]

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal ContDiff
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

@[reducible] def PartitionTree : ℕ → ℕ → Type
  | 0,_ => Unit
  | d+1,r => Σ P : OrderedFinpartition r, ∀ i : Fin P.length,PartitionTree d (P.partSize i)

instance partitionTreeFintype (d r : ℕ) : Fintype (PartitionTree d r) := by
  induction d generalizing r with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ d ih =>
    letI : ∀ n,Fintype (PartitionTree d n) := ih
    exact inferInstanceAs (Fintype (Σ P : OrderedFinpartition r,∀ i : Fin P.length,PartitionTree d (P.partSize i)))

instance partitionTreeDecidableEq (d r : ℕ) : DecidableEq (PartitionTree d r) := Classical.decEq _

def treeCodes : {d r : ℕ} → PartitionTree d r → Fin (d+1) → Fin r → ℕ
  | 0,_,_ => fun _ _ => 0
  | _+1,_,⟨P,T⟩ => Fin.cases (fun _ => 0) (fun k => splitCode P (fun i => treeCodes (T i) k))

@[simp] lemma treeCodes_root {d r : ℕ} (T : PartitionTree d r) : treeCodes T 0=fun _ => 0 := by
  cases d with
  | zero => rfl
  | succ d => rcases T with ⟨P,T⟩; rfl

@[simp] lemma treeCodes_succ {d r : ℕ} (P : OrderedFinpartition r)
    (T : ∀ i,PartitionTree d (P.partSize i)) (k : Fin (d+1)) :
    treeCodes (⟨P,T⟩ : PartitionTree (d+1) r) k.succ=splitCode P (fun i => treeCodes (T i) k) := rfl

lemma splitCode_refines {r : ℕ} (P : OrderedFinpartition r)
    (p c : ∀ i,Fin (P.partSize i) → ℕ) (h : ∀ i,Refines (p i) (c i)) :
    Refines (splitCode P p) (splitCode P c) := by
  intro j k hjk
  obtain ⟨⟨i,j⟩,rfl⟩ := P.equivSigma.surjective j
  obtain ⟨⟨l,k⟩,rfl⟩ := P.equivSigma.surjective k
  change splitCode P c (P.emb i j)=splitCode P c (P.emb l k) at hjk
  change splitCode P p (P.emb i j)=splitCode P p (P.emb l k)
  simp only [splitCode_emb,Nat.pair_eq_pair] at hjk ⊢
  have hi : i=l := Fin.ext hjk.1
  subst l
  exact ⟨rfl,h i j k hjk.2⟩

lemma treeCodes_nested {d r : ℕ} (T : PartitionTree d r) : NestedCodes (treeCodes T) := by
  induction d generalizing r with
  | zero => intro k l hkl i j hij; rfl
  | succ d ih =>
    rcases T with ⟨P,T⟩
    intro k
    induction k using Fin.cases with
    | zero => intro l hkl i j hij; rfl
    | succ k =>
      intro l hkl
      have hl0 : l≠0 := by intro hl; subst l; have := k.isLt; change (k:ℕ)+1≤0 at hkl; omega
      obtain ⟨l,rfl⟩ := Fin.exists_succ_eq.mpr hl0
      exact splitCode_refines P _ _ (fun i => ih (T i) k l (Fin.succ_le_succ_iff.mp hkl))

lemma hierarchyNumerator_tree_zero {r : ℕ} (a : Fin 1 → ℝ) (T : PartitionTree 0 r) :
    hierarchyNumerator a (treeCodes T)=blockFactor (a 0) r := by
  simp [hierarchyNumerator,treeCodes,leafFactor_const]

lemma hierarchyNumerator_tree_succ {d r : ℕ} (a : Fin (d+2) → ℝ)
    (P : OrderedFinpartition r) (T : ∀ i,PartitionTree d (P.partSize i)) :
    hierarchyNumerator a (treeCodes (⟨P,T⟩ : PartitionTree (d+1) r))=
      branchFactor (a 1) (a 0) P.length*
        ∏ i,hierarchyNumerator (fun k => a k.succ) (treeCodes (T i)) := by
  unfold hierarchyNumerator
  rw [Fin.prod_univ_succ]
  change (edgeFactor (a 1) (a 0) (fun _ => 0)
      (splitCode P (fun i => treeCodes (T i) 0)) *
      (∏ k : Fin d,edgeFactor (a k.succ.succ) (a k.castSucc.succ)
        (splitCode P (fun i => treeCodes (T i) k.castSucc))
        (splitCode P (fun i => treeCodes (T i) k.succ)))) *
      leafFactor (a (Fin.last d).succ) (splitCode P (fun i => treeCodes (T i) (Fin.last d))) = _
  simp_rw [treeCodes_root]
  rw [edgeFactor_root]
  have he : (∏ k : Fin d,
      edgeFactor (a k.succ.succ) (a k.castSucc.succ)
        (splitCode P (fun i => treeCodes (T i) k.castSucc))
        (splitCode P (fun i => treeCodes (T i) k.succ)))=
      ∏ i,∏ k : Fin d,edgeFactor (a k.succ.succ) (a k.castSucc.succ)
        (treeCodes (T i) k.castSucc) (treeCodes (T i) k.succ) := by
    simp_rw [edgeFactor_split]
    exact Finset.prod_comm
  change branchFactor (a 1) (a 0) P.length * _ * _ = _
  rw [he,leafFactor_split,Finset.prod_mul_distrib]
  ring

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal ContDiff
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {ι : Type*} [Fintype ι]

def hierarchyMark (w : ι → ℝ) : (d : ℕ) → (Fin (d+1) → ℝ) → ((Fin d → ι) → ℝ) → ℝ → ℝ
  | 0,a,x,z => (1-z*x (fun k => Fin.elim0 k))^(a 0)
  | d+1,a,x,z => (∑ i,w i*hierarchyMark w d (fun k => a k.succ) (fun s => x (Fin.cons i s)) z)^(a 0/a 1)

def treeMarkMoment (w : ι → ℝ) : {d r : ℕ} → ((Fin d → ι) → ℝ) → PartitionTree d r → ℝ
  | 0,r,x,_ => x (fun k => Fin.elim0 k)^r
  | _+1,_,x,⟨P,T⟩ => ∏ j : Fin P.length,∑ i,w i*treeMarkMoment w (fun s => x (Fin.cons i s)) (T j)

def hierarchyCoefficient {d : ℕ} (w : ι → ℝ) (a : Fin (d+1) → ℝ)
    (x : (Fin d → ι) → ℝ) (r : ℕ) : ℝ :=
  ∑ T : PartitionTree d r,hierarchyNumerator a (treeCodes T)*treeMarkMoment w x T

lemma hierarchyCoefficient_zero (w : ι → ℝ) (a : Fin 1 → ℝ) (x : (Fin 0 → ι) → ℝ) (r : ℕ) :
    hierarchyCoefficient w a x r=blockFactor (a 0) r*x (fun k => Fin.elim0 k)^r := by
  unfold hierarchyCoefficient
  simp only [hierarchyNumerator_tree_zero,treeMarkMoment]
  change (∑ _ : Unit,blockFactor (a 0) r*x (fun k => Fin.elim0 k)^r)=_
  simp

lemma hierarchyCoefficient_succ {d : ℕ} (w : ι → ℝ) (a : Fin (d+2) → ℝ)
    (x : (Fin (d+1) → ι) → ℝ) (r : ℕ) :
    hierarchyCoefficient w a x r=
      ∑ P : OrderedFinpartition r,branchFactor (a 1) (a 0) P.length *
        ∏ j,∑ i,w i*hierarchyCoefficient w (fun k => a k.succ) (fun s => x (Fin.cons i s)) (P.partSize j) := by
  unfold hierarchyCoefficient
  change (∑ PT : (Σ P : OrderedFinpartition r,∀ j,PartitionTree d (P.partSize j)),
    hierarchyNumerator a (treeCodes (PT : PartitionTree (d+1) r))*treeMarkMoment w x PT)=_
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro P _
  simp only [hierarchyNumerator_tree_succ,treeMarkMoment]
  simp_rw [Finset.mul_sum]
  have he (j : Fin P.length) :
      (∑ i,∑ T : PartitionTree d (P.partSize j),w i*
        (hierarchyNumerator (fun k => a k.succ) (treeCodes T)*treeMarkMoment w (fun s => x (Fin.cons i s)) T))=
      ∑ T : PartitionTree d (P.partSize j),hierarchyNumerator (fun k => a k.succ) (treeCodes T)*
        ∑ i,w i*treeMarkMoment w (fun s => x (Fin.cons i s)) T := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  rw [Fintype.prod_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.prod_mul_distrib]
  ring

lemma hierarchyMark_zero {d : ℕ} (w : ι → ℝ) (hw : ∑ i,w i=1)
    (a : Fin (d+1) → ℝ) (x : (Fin d → ι) → ℝ) : hierarchyMark w d a x 0=1 := by
  induction d with
  | zero => simp [hierarchyMark]
  | succ d ih => simp only [hierarchyMark,ih,mul_one,hw,Real.one_rpow]

lemma hierarchyMark_contDiffAt_zero {d : ℕ} (w : ι → ℝ) (hw : ∑ i,w i=1)
    (a : Fin (d+1) → ℝ) (x : (Fin d → ι) → ℝ) (n : ℕ∞ω) :
    ContDiffAt ℝ n (hierarchyMark w d a x) 0 := by
  induction d with
  | zero =>
    apply ContDiffAt.rpow_const_of_ne
    · fun_prop
    · simp
  | succ d ih =>
    apply ContDiffAt.rpow_const_of_ne
    · exact ContDiffAt.sum fun i _ => contDiffAt_const.mul (ih _ _)
    · simp only [hierarchyMark_zero w hw,mul_one,hw]; norm_num

lemma hierarchyMean_derivative {d : ℕ} (w : ι → ℝ) (hw : ∑ i,w i=1)
    (a : Fin (d+1) → ℝ) (x : ι → (Fin d → ι) → ℝ) {n : ℕ} (_hn : 0<n)
    (h : ∀ y,iteratedDeriv n (hierarchyMark w d a y) 0= -a 0*hierarchyCoefficient w a y n) :
    iteratedDeriv n (fun z => ∑ i,w i*hierarchyMark w d a (x i) z) 0=
      -a 0*∑ i,w i*hierarchyCoefficient w a (x i) n := by
  rw [iteratedDeriv_fun_sum]
  · simp only [iteratedDeriv_const_mul_field,h,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro i _
    exact contDiffAt_const.mul (hierarchyMark_contDiffAt_zero w hw a (x i) n)

 

theorem hierarchyMark_derivative {d : ℕ} (w : ι → ℝ) (hw : ∑ i,w i=1)
    (a : Fin (d+1) → ℝ) (ha : ∀ k : Fin d,a k.succ≠0)
    (x : (Fin d → ι) → ℝ) {n : ℕ} (hn : 0<n) :
    iteratedDeriv n (hierarchyMark w d a x) 0= -a 0*hierarchyCoefficient w a x n := by
  induction d generalizing n with
  | zero =>
    rw [hierarchyCoefficient_zero]
    simpa only [hierarchyMark,mul_assoc] using iteratedDeriv_affine_rpow_zero_pos (a 0) (x (fun k => Fin.elim0 k)) hn
  | succ d ih =>
    let A : ℝ → ℝ := fun z => ∑ i,w i*hierarchyMark w d (fun k => a k.succ) (fun s => x (Fin.cons i s)) z
    have hA : ContDiffAt ℝ n A 0 := ContDiffAt.sum fun i _ => contDiffAt_const.mul
      (hierarchyMark_contDiffAt_zero w hw _ _ n)
    have hAz : A 0=1 := by simp [A,hierarchyMark_zero w hw,hw]
    have hg : ContDiffAt ℝ n (fun y : ℝ => y^(a 0/a 1)) (A 0) := by
      apply ContDiffAt.rpow_const_of_ne
      · fun_prop
      · rw [hAz]; norm_num
    have hf := iteratedDeriv_scomp_eq_sum_orderedFinpartition hg hA (i:=n) le_rfl
    change iteratedDeriv n (hierarchyMark w (d+1) a x) 0=_ at hf
    rw [hf,hierarchyCoefficient_succ,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P _
    have hd (j : Fin P.length) : iteratedDeriv (P.partSize j) A 0=
        -a 1*∑ i,w i*hierarchyCoefficient w (fun k => a k.succ)
          (fun s => x (Fin.cons i s)) (P.partSize j) :=
      hierarchyMean_derivative w hw _ _ (P.partSize_pos j)
        (fun y => ih _ (fun k => ha k.succ) y (P.partSize_pos j))
    simp only [hd,hAz,iteratedDeriv_rpow_one,smul_eq_mul]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    have hh := signed_power_factor (ha 0) (a 0) (P.length_pos hn)
    simp only [Fin.succ_zero_eq_one] at hh
    linear_combination (∏ j,∑ i,w i*hierarchyCoefficient w (fun k => a k.succ)
      (fun s => x (Fin.cons i s)) (P.partSize j))*hh

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal ContDiff
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {ι : Type*} [Fintype ι]

def hierarchyLog (w : ι → ℝ) {d : ℕ} (a : Fin (d+1) → ℝ)
    (x : (Fin (d+1) → ι) → ℝ) (z : ℝ) : ℝ :=
  (a 0)⁻¹*Real.log (∑ i,w i*hierarchyMark w d a (fun s => x (Fin.cons i s)) z)

lemma hierarchyLog_derivative {d : ℕ} (w : ι → ℝ) (hw : ∑ i,w i=1)
    (a : Fin (d+1) → ℝ) (ha : ∀ k,a k≠0) (x : (Fin (d+1) → ι) → ℝ)
    {n : ℕ} (hn : 0<n) :
    iteratedDeriv n (hierarchyLog w a x) 0= -hierarchyCoefficient w (Fin.cons 0 a) x n := by
  let A : ℝ → ℝ := fun z => ∑ i,w i*hierarchyMark w d a (fun s => x (Fin.cons i s)) z
  have hA : ContDiffAt ℝ n A 0 := ContDiffAt.sum fun i _ => contDiffAt_const.mul
    (hierarchyMark_contDiffAt_zero w hw _ _ n)
  have hAz : A 0=1 := by simp [A,hierarchyMark_zero w hw,hw]
  have hg : ContDiffAt ℝ n Real.log (A 0) := by
    rw [hAz]; exact Real.contDiffAt_log.mpr (by norm_num)
  have hf := iteratedDeriv_scomp_eq_sum_orderedFinpartition hg hA (i:=n) le_rfl
  change iteratedDeriv n (fun z => Real.log (A z)) 0=_ at hf
  change iteratedDeriv n (fun z => (a 0)⁻¹*Real.log (A z)) 0=_
  rw [iteratedDeriv_const_mul_field,hf,hierarchyCoefficient_succ,Finset.mul_sum,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro P _
  have hd (j : Fin P.length) : iteratedDeriv (P.partSize j) A 0=
      -a 0*∑ i,w i*hierarchyCoefficient w a (fun s => x (Fin.cons i s)) (P.partSize j) :=
    hierarchyMean_derivative w hw _ _ (P.partSize_pos j)
      (fun y => hierarchyMark_derivative w hw a (fun k => ha k.succ) y (P.partSize_pos j))
  simp only [hd,hAz,iteratedDeriv_log_one (P.length_pos hn),smul_eq_mul,
    Fin.cons_zero,Fin.cons_succ]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hh := signed_log_factor (ha 0) (P.length_pos hn)
  rw [branchFactor_zero]
  change (a 0)⁻¹*(((-a 0)^P.length * _)*_)= -(tableFactor (a 0) P.length * _)
  linear_combination (∏ j,∑ i,w i*hierarchyCoefficient w a
    (fun s => x (Fin.cons i s)) (P.partSize j))*hh

def hierarchyMarkedMoment {d : ℕ} (μ : ProbabilityMeasure OverlapArray)
    (q : Fin (d+1) → ℝ) (w : ι → ℝ) (x : (Fin d → ι) → ℝ) (r : ℕ) : ℝ :=
  ∑ T : PartitionTree d r,(μ:Measure OverlapArray).real (hierarchyEvent (treeCodes T) q)*
    treeMarkMoment w x T

lemma GG_hierarchy_coefficient {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d : ℕ} (q : Fin (d+1) → ℝ) (hq : Monotone q) (h1 : q (Fin.last d)<1)
    (w : ι → ℝ) (x : (Fin d → ι) → ℝ) {n : ℕ} (hn : 0<n) :
    hierarchyCoefficient w (fun k => overlapDiscount μ (q k)) x n=
      ((n-1).factorial:ℝ)*hierarchyMarkedMoment μ q w x n := by
  unfold hierarchyCoefficient hierarchyMarkedMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [← GG_hierarchy_EPPF hG hgg hu hn (treeCodes T) (treeCodes_nested T)
    (fun i j => by simp) q hq h1]
  ring

lemma overlapDiscount_below (μ : ProbabilityMeasure OverlapArray) {q : ℝ} (hq : q < -1) :
    overlapDiscount μ q=0 := by
  have he : {x : OverlapEntry | (x:ℝ)≤q}=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (not_lt_of_ge x.property.1) (hx.trans_lt hq)
  simp only [overlapDiscount,he,measureReal_empty]

 

theorem GG_hierarchy_log_derivative {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1) (ha : ∀ k : Fin (d+1),overlapDiscount μ (q k.succ)≠0)
    (w : ι → ℝ) (hw : ∑ i,w i=1) (x : (Fin (d+1) → ι) → ℝ)
    {n : ℕ} (hn : 0<n) :
    iteratedDeriv n (hierarchyLog w (fun k => overlapDiscount μ (q k.succ)) x) 0=
      -((n-1).factorial:ℝ)*hierarchyMarkedMoment μ q w x n := by
  rw [hierarchyLog_derivative w hw _ ha x hn]
  have he : Fin.cons 0 (fun k => overlapDiscount μ (q k.succ))=(fun k => overlapDiscount μ (q k)) := by
    funext k
    induction k using Fin.cases with
    | zero => exact (overlapDiscount_below μ h0).symm
    | succ k => rfl
  rw [he,GG_hierarchy_coefficient hG hgg hu q hq h1 w x hn]
  ring

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal ContDiff
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma splitCode_zero_index {r : ℕ} (P : OrderedFinpartition r) (j : Fin r) :
    splitCode P (fun _ _ => 0) j=Nat.pair (P.index j).val 0 := by
  obtain ⟨⟨i,k⟩,rfl⟩ := P.equivSigma.surjective j
  change splitCode P (fun _ _ => 0) (P.emb i k)=_
  rw [splitCode_emb]
  change _=Nat.pair (P.index (P.emb i k)).val 0
  rw [orderedIndex_emb]

lemma treeCodes_level_one_relation {d r : ℕ} (P : OrderedFinpartition r)
    (T : ∀ i,PartitionTree d (P.partSize i)) (i j : Fin r) :
    treeCodes (d:=d+1) (⟨P,T⟩ : PartitionTree (d+1) r) 1 i=
      treeCodes (d:=d+1) (⟨P,T⟩ : PartitionTree (d+1) r) 1 j ↔ P.index i=P.index j := by
  change splitCode P (fun k => treeCodes (T k) 0) i=splitCode P (fun k => treeCodes (T k) 0) j ↔ _
  simp [treeCodes_root,splitCode_zero_index,Nat.pair_eq_pair,Fin.val_inj]

 
theorem tree_eq_of_same_relations {d r : ℕ} (T U : PartitionTree d r)
    (h : ∀ k i j,treeCodes T k i=treeCodes T k j ↔ treeCodes U k i=treeCodes U k j) : T=U := by
  induction d generalizing r with
  | zero => exact Subsingleton.elim _ _
  | succ d ih =>
    rcases T with ⟨P,T⟩
    rcases U with ⟨Q,U⟩
    have hPQ : P=Q := ordered_eq_of_same_relation P Q (fun i j => by
      simpa only [treeCodes_level_one_relation] using h 1 i j)
    subst Q
    suffices he : T=U from congrArg (fun V => (⟨P,V⟩ : PartitionTree (d+1) r)) he
    funext i
    apply ih
    intro k j l
    have hh := h k.succ (P.emb i j) (P.emb i l)
    simpa only [treeCodes_succ,splitCode_emb,Nat.pair_eq_pair,true_and] using hh

lemma tree_hierarchy_disjoint {d r : ℕ} {T U : PartitionTree d r} (hTU : T≠U)
    (q : Fin (d+1) → ℝ) :
    Disjoint (hierarchyEvent (treeCodes T) q) (hierarchyEvent (treeCodes U) q) := by
  apply Set.disjoint_left.mpr
  intro R hT hU
  apply hTU
  exact tree_eq_of_same_relations T U (fun k i j => ((hT k) i j).symm.trans ((hU k) i j))

lemma hierarchyEvent_measurable {d r : ℕ} (c : Fin (d+1) → Fin r → ℕ) (q : Fin (d+1) → ℝ) :
    MeasurableSet (hierarchyEvent c q) := by
  change MeasurableSet {R | ∀ k,R∈partitionEvent (c k) (q k)}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => measurableSet_partitionEvent _ _

end SKCavity

end

end OAI
