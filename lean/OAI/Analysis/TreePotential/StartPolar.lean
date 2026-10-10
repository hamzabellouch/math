import OAI.Analysis.TreePotential.StartEnergy

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials.Segments

lemma enn_sqrt_sq (x : ℝ≥0∞) : (x^2)^(1/2:ℝ)=x := by
  rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
  norm_num

lemma enn_sq_sqrt (x : ℝ≥0∞) : (x^(1/2:ℝ))^2=x := by
  rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
  norm_num

lemma startCost_finset_sum {I : Type*} (n : ℕ) (E : Finset I) (m : I → List ℕ → ℝ≥0∞) :
    startCost n (∑ i ∈ E,m i)≤∑ i ∈ E,startCost n (m i) := by
  induction E using Finset.induction_on with
  | empty => simp
  | @insert i E hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (startCost_add n _ _).trans (add_le_add le_rfl ih)

lemma treeSum_fintype_sum {I : Type*} [Fintype I] (n : ℕ) (m : I → List ℕ → ℝ≥0∞) :
    treeSum n (fun s => ∑ i,m i s)=∑ i,treeSum n (m i) := by
  simpa only [tsum_fintype] using treeSum_tsum n m

def layerMass (d : ℕ) (m : List ℕ → ℝ≥0∞) : List ℕ → ℝ≥0∞ :=
  fun s => if s.length=d then m s else 0

def layerNorm (n d : ℕ) (m : List ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  (treeSum n (fun s => (layerMass d m s)^2))^(1/2:ℝ)

lemma layerMass_antichain (n d : ℕ) (m : List ℕ → ℝ≥0∞) : AntichainMass n (layerMass d m) := by
  intro s t hs ht hms hmt hst
  have hs' : s.length=d := by by_contra h; simp [layerMass,h] at hms
  have ht' : t.length=d := by by_contra h; simp [layerMass,h] at hmt
  exact hst.eq_of_length (hs'.trans ht'.symm)

lemma layerCost_eq_norm (n d : ℕ) (m : List ℕ → ℝ≥0∞) : startCost n (layerMass d m)=layerNorm n d m := by
  rw [layerNorm,← startCost_antichain_sq n _ (layerMass_antichain n d m),enn_sqrt_sq]

lemma sum_layers (n : ℕ) (m : List ℕ → ℝ≥0∞) (s : List ℕ) (hs : s.length≤ n) :
    (∑ d : Fin (n+1),layerMass d m s)=m s := by
  let j : Fin (n+1) := ⟨s.length,by omega⟩
  rw [Finset.sum_eq_single j]
  · simp [layerMass,j]
  · intro i hi hij
    have hn : s.length≠i.val := by intro he; exact hij (Fin.ext he.symm)
    simp [layerMass,hn]
  · simp

lemma sum_layerNorm_sq (n : ℕ) (m : List ℕ → ℝ≥0∞) :
    (∑ d : Fin (n+1),(layerNorm n d m)^2)=treeSum n (fun s => (m s)^2) := by
  simp only [layerNorm,enn_sq_sqrt]
  rw [← treeSum_fintype_sum]
  apply treeSum_congr
  intro s hs
  have he : ∀ d : Fin (n+1),(layerMass d m s)^2=layerMass d (fun t => (m t)^2) s := by
    intro d
    unfold layerMass
    split_ifs <;> simp
  simp_rw [he]
  exact sum_layers n _ s hs

/-- Exact level estimate on countably branching trees, allowing either side to be infinite. -/

lemma startCost_le_sum_layers (n : ℕ) (m : List ℕ → ℝ≥0∞) :
    startCost n m≤∑ d : Fin (n+1),layerNorm n d m := by
  calc
    _ = startCost n (∑ d : Fin (n+1),layerMass d m) := by
      apply startCost_congr
      intro s hs
      simpa only [Finset.sum_apply] using (sum_layers n m s hs).symm
    _ ≤ ∑ d : Fin (n+1),startCost n (layerMass d m) := startCost_finset_sum n Finset.univ _
    _ = _ := by simp_rw [layerCost_eq_norm]

lemma sum_layers_le_hilbert (n : ℕ) (m : List ℕ → ℝ≥0∞) :
    (∑ d : Fin (n+1),layerNorm n d m)≤
      ((n+1 : ℕ):ℝ≥0∞)^(1/2:ℝ)*(treeSum n (fun s => (m s)^2))^(1/2:ℝ) := by
  have h := eTwo_inner_le (fun _ : Fin (n+1) => (1:ℝ≥0∞)) (fun d => layerNorm n d m)
  simpa only [one_mul,tsum_fintype,eTwo,one_pow,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one,sum_layerNorm_sq] using h

lemma startCost_hilbert_comparisons (n : ℕ) (m : List ℕ → ℝ≥0∞) :
    (treeSum n (fun s => (m s)^2))^(1/2:ℝ)≤ startCost n m ∧
    startCost n m≤∑ d : Fin (n+1),layerNorm n d m ∧
    (∑ d : Fin (n+1),layerNorm n d m)≤
      ((n+1 : ℕ):ℝ≥0∞)^(1/2:ℝ)*(treeSum n (fun s => (m s)^2))^(1/2:ℝ) := by
  refine ⟨?_,startCost_le_sum_layers n m,sum_layers_le_hilbert n m⟩
  have hh := ENNReal.rpow_le_rpow (treeSum_sq_le_startCost_sq n m) (by norm_num : (0:ℝ)≤1/2)
  simpa only [enn_sqrt_sq] using hh

end BoundedTreePotentials.Segments

/-! Start-cost polar identification. -/





namespace BoundedTreePotentials.Segments

/-- Finite incomparable tests wholly contained in a specified descendant cone.
The component index, prefix, root and endpoint conventions are unchanged. -/
def ConeFamily (n : ℕ) (s : List ℕ) :=
  {F : Finset Segment // Incomparable F ∧ ∀ S ∈ F, S.start.1=n ∧ s <+: S.start.2.val}

instance coneFamilyNonempty (n : ℕ) (s : List ℕ) : Nonempty (ConeFamily n s) :=
  ⟨⟨∅,by constructor <;> intro S hS <;> simp at hS⟩⟩

/-- Squared local polar budget. Supremums in ENNReal avoid any assumption of
an optimizing antichain or endpoint. -/
def coneEnergy (g : Node → ℝ) (n : ℕ) (s : List ℕ) : ℝ≥0∞ :=
  ⨆ F : ConeFamily n s, ∑ S ∈ F.val, (ENNReal.ofReal |S.eval g|)^2

def coneBudget (g : Node → ℝ) (n : ℕ) (s : List ℕ) : ℝ≥0∞ :=
  (coneEnergy g n s)^(1/2:ℝ)

lemma coneBudget_sq (g : Node → ℝ) (n : ℕ) (s : List ℕ) :
    (coneBudget g n s)^2=coneEnergy g n s := by
  rw [coneBudget,← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
  norm_num

lemma branch_index_eq {s u v : List ℕ} {i j : ℕ}
    (hu : s++[i] <+: u) (hv : s++[j] <+: v) (huv : u <+: v) : i=j := by
  have h : s++[i] <+: s++[j] :=
    List.prefix_of_prefix_length_le (hu.trans huv) hv (by simp)
  have he : s++[i]=s++[j] := h.eq_of_length (by simp)
  simpa only [List.append_cancel_left_eq,List.cons.injEq,and_true] using he

lemma cone_children_union (n : ℕ) (s : List ℕ) (E : Finset ℕ)
    (F : (j : ℕ) → ConeFamily n (s++[j])) :
    Incomparable (E.biUnion (fun j => (F j).val)) ∧
    (∀ S ∈ E.biUnion (fun j => (F j).val), S.start.1=n ∧ s <+: S.start.2.val) ∧
    (E : Set ℕ).PairwiseDisjoint (fun j => (F j).val) := by
  have hbranch {i j : ℕ} {S T : Segment} (hS : S ∈ (F i).val) (hT : T ∈ (F j).val)
      (hST : Prefix S.start T.start) : i=j :=
    branch_index_eq ((F i).property.2 S hS).2 ((F j).property.2 T hT).2 hST.2
  refine ⟨?_,?_,?_⟩
  · intro S hS T hT hne
    obtain ⟨i,hi,hSi⟩ := Finset.mem_biUnion.mp hS
    obtain ⟨j,hj,hTj⟩ := Finset.mem_biUnion.mp hT
    by_cases hij : i=j
    · subst j
      exact (F i).property.1 S hSi T hTj hne
    · exact ⟨fun h => hij (hbranch hSi hTj h),fun h => hij (hbranch hTj hSi h).symm⟩
  · intro S hS
    obtain ⟨i,hi,hSi⟩ := Finset.mem_biUnion.mp hS
    exact ⟨((F i).property.2 S hSi).1,(List.prefix_append s [i]).trans ((F i).property.2 S hSi).2⟩
  · intro i hi j hj hne
    apply Finset.disjoint_left.mpr
    intro S hSi hSj
    exact hne (hbranch hSi hSj (prefix_refl _))

lemma coneEnergy_children (g : Node → ℝ) (n : ℕ) (s : List ℕ) :
    (∑' j : ℕ,coneEnergy g n (s++[j])) ≤ coneEnergy g n s := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro E
  apply enn_sum_iSup_le E (fun j (F : ConeFamily n (s++[j])) => ∑ S ∈ F.val,(ENNReal.ofReal |S.eval g|)^2)
  intro F
  obtain ⟨hinc,hcone,hdisj⟩ := cone_children_union n s E F
  let U : ConeFamily n s := ⟨E.biUnion (fun j => (F j).val),hinc,hcone⟩
  apply le_iSup_of_le U
  exact le_of_eq (Finset.sum_biUnion hdisj).symm

lemma coneBudget_children (g : Node → ℝ) (n : ℕ) (s : List ℕ) :
    eTwo (fun j : ℕ => coneBudget g n (s++[j])) ≤ coneBudget g n s := by
  unfold eTwo
  simp only [coneBudget_sq]
  exact ENNReal.rpow_le_rpow (coneEnergy_children g n s) (by norm_num : (0:ℝ) ≤ 1/2)

lemma coneBudget_potential (g : Node → ℝ) (n h : ℕ) (s : List ℕ) :
    IsPotential h (fun t => coneBudget g n (s++t)) := by
  induction h generalizing s with
  | zero => trivial
  | succ h ih =>
    refine ⟨?_,?_⟩
    · simpa only [List.append_nil] using coneBudget_children g n s
    · intro j
      simpa only [List.append_assoc,List.singleton_append] using ih (s++[j])

lemma coneEnergy_roots (g : Node → ℝ) (hg : IsUnitTest g) :
    (∑' n : ℕ,coneEnergy g n []) ≤ 1 := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro H
  apply enn_sum_iSup_le H (fun n (F : ConeFamily n []) => ∑ S ∈ F.val,(ENNReal.ofReal |S.eval g|)^2)
  intro F
  have hc : ∀ n ∈ H, ∀ S ∈ (F n).val, S.start.1=n := fun n hn S hS => ((F n).property.2 S hS).1
  have hi := component_families_incomparable H (fun n => (F n).val) (fun n hn => (F n).property.1) hc
  have hd := component_families_disjoint H (fun n => (F n).val) hc
  rw [← Finset.sum_biUnion hd]
  have hh := hg _ hi
  have he : (∑ S ∈ H.biUnion (fun n => (F n).val),(ENNReal.ofReal |S.eval g|)^2) =
      ENNReal.ofReal (∑ S ∈ H.biUnion (fun n => (F n).val),(S.eval g)^2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun S hS => sq_nonneg _)]
    apply Finset.sum_congr rfl
    intro S hS
    rw [← ENNReal.ofReal_pow (abs_nonneg _),sq_abs]
  rw [he]
  simpa using ENNReal.ofReal_le_ofReal hh

lemma coneBudget_roots (g : Node → ℝ) (hg : IsUnitTest g) :
    eTwo (fun n => coneBudget g n []) ≤ 1 := by
  unfold eTwo
  simp only [coneBudget_sq]
  have h := ENNReal.rpow_le_rpow (coneEnergy_roots g hg) (by norm_num : (0:ℝ) ≤ 1/2)
  simpa using h

lemma segment_le_coneBudget (g : Node → ℝ) (S : Segment) :
    ENNReal.ofReal |S.eval g| ≤ coneBudget g S.start.1 S.start.2.val := by
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0:ℝ)<2)).mp
  simp only [ENNReal.rpow_two,coneBudget_sq]
  let F : ConeFamily S.start.1 S.start.2.val := ⟨{S},by
    constructor
    · intro U hU V hV hne
      simp only [Finset.mem_singleton] at hU hV
      exact (hne (hU.trans hV.symm)).elim
    · intro U hU
      obtain rfl := Finset.mem_singleton.mp hU
      exact ⟨rfl,List.prefix_refl _⟩⟩
  apply le_iSup_of_le F
  simp [F]

/-- The polar estimate for an arbitrary nonnegative start array, allowing
infinite costs. Its local budgets were obtained from actual incomparable tests. -/
lemma forest_pair_budget_le (m : (n : ℕ) → List ℕ → ℝ≥0∞)
    (g : Node → ℝ) (hg : IsUnitTest g) :
    (∑' n : ℕ,treeSum (n+1) (fun s => m n s*coneBudget g n s)) ≤ forestCost m := by
  calc
    _ ≤ ∑' n : ℕ,startCost (n+1) (m n)*coneBudget g n [] := by
      apply ENNReal.tsum_le_tsum
      intro n
      simpa only [List.nil_append] using treeSum_pair_le (n+1) (m n) _ (coneBudget_potential g n (n+1) [])
    _ ≤ eTwo (fun n => startCost (n+1) (m n))*eTwo (fun n => coneBudget g n []) := eTwo_inner_le _ _
    _ ≤ forestCost m*1 := mul_le_mul le_rfl (coneBudget_roots g hg) zero_le zero_le
    _ = _ := mul_one _

end BoundedTreePotentials.Segments

end

end OAI
