import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.GroupedEntropyPartition
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.PairConditionalEntropy
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ComplementSums
import Mathlib.Data.List.NodupEquivFin

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldNativeGroupedRates

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open JointNativeGroupedEntropy JointGroupedEntropyPartition
open AllFieldNativeCapacity AllFieldPairConditionalEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

section Reindex

variable {U K A : Type*} [Fintype U] [Fintype K] [Fintype A]

omit [Fintype U] [Fintype K] in
theorem singletonResidualGroup_transport (e : U ≃ U) (c : K ≃ K)
    (d : U → Prop) (weight : U → K)
    (hw : ∀ u, c (weight u) = weight (e u)) :
    (Equiv.sumCongr e c) ∘ singletonResidualGroup (d ∘ e) weight =
      singletonResidualGroup d weight ∘ e := by
  funext u
  by_cases hu : d (e u) <;>
    simp [singletonResidualGroup, Function.comp_apply, hu, hw]

theorem singletonResidual_groupedEntropy_reindex (e : U ≃ U) (c : K ≃ K)
    (p : U → ℝ) (d : U → Prop) (weight : U → K) (q : U → A → ℝ)
    (hp : ∀ u, p (e u) = p u) (hw : ∀ u, c (weight u) = weight (e u)) :
    JointCompatibilityIncidence.groupedEntropy p
      (singletonResidualGroup (d ∘ e) weight) (q ∘ e) =
      JointCompatibilityIncidence.groupedEntropy p (singletonResidualGroup d weight) q := by
  calc
    _ = JointCompatibilityIncidence.groupedEntropy p
        ((Equiv.sumCongr e c) ∘ singletonResidualGroup (d ∘ e) weight) (q ∘ e) :=
      (JointCompatibilityIncidence.groupedEntropy_relabel (Equiv.sumCongr e c) p _ _).symm
    _ = JointCompatibilityIncidence.groupedEntropy p
        (singletonResidualGroup d weight ∘ e) (q ∘ e) := by
      rw [singletonResidualGroup_transport e c d weight hw]
    _ = _ := JointCompatibilityIncidence.groupedEntropy_reindex e p _ q hp

theorem right_conditional_sum_eq (e : U ≃ U) (c : K ≃ K)
    (p : FiniteLaw U) (d : U → Prop) (weight : U → K) (q : U → A → ℝ)
    (hp : ∀ u, p.mass (e u) = p.mass u)
    (hw : ∀ u, c (weight u) = weight (e u)) (hq : ∀ u, ∑ a, q u a = 1) :
    (∑ k, (p.map weight).mass k *
      JointCompatibilityIncidence.groupedEntropy (p.conditional weight k).mass
        (JointCompatibilityIncidence.designatedGroup (d ∘ e)) (q ∘ e)) =
      JointCompatibilityIncidence.groupedEntropy p.mass (singletonResidualGroup d weight) q := by
  rw [← groupedEntropy_conditional_partition p (d ∘ e) weight (q ∘ e)
    (fun u => hq (e u))]
  exact singletonResidual_groupedEntropy_reindex e c p.mass d weight q hp hw

end Reindex

def supportSubtypeEquiv {α : Type*} (xs : List α) (f : α → α)
    (hm : ∀ x ∈ xs, f x ∈ xs) (hi : ∀ x ∈ xs, f (f x) = x) :
    Equiv.Perm {x // x ∈ xs} where
  toFun x := ⟨f x.val, hm x.val x.property⟩
  invFun x := ⟨f x.val, hm x.val x.property⟩
  left_inv x := Subtype.ext (hi x.val x.property)
  right_inv x := Subtype.ext (hi x.val x.property)

def supportIndexEquiv {α : Type*} [DecidableEq α] (xs : List α) (hn : xs.Nodup)
    (f : α → α) (hm : ∀ x ∈ xs, f x ∈ xs) (hi : ∀ x ∈ xs, f (f x) = x) :
    Equiv.Perm (Fin xs.length) :=
  ((hn.getEquiv xs).trans (supportSubtypeEquiv xs f hm hi)).trans (hn.getEquiv xs).symm

theorem supportIndexEquiv_get {α : Type*} [DecidableEq α] (xs : List α)
    (hn : xs.Nodup) (f : α → α) (hm : ∀ x ∈ xs, f x ∈ xs)
    (hi : ∀ x ∈ xs, f (f x) = x) (i : Fin xs.length) :
    xs.get (supportIndexEquiv xs hn f hm hi i) = f (xs.get i) := by
  exact congrArg Subtype.val ((hn.getEquiv xs).apply_symm_apply
    ((supportSubtypeEquiv xs f hm hi) ((hn.getEquiv xs) i)))

def boundedComplement (s : ℕ) (hs : s < 17) (k : Fin 17) : Fin 17 :=
  ⟨if k.val ≤ s then s - k.val else k.val, by
    split_ifs
    · exact lt_of_le_of_lt (Nat.sub_le _ _) hs
    · exact k.isLt⟩

theorem boundedComplement_involutive (s : ℕ) (hs : s < 17) :
    Function.Involutive (boundedComplement s hs) := by
  intro k
  apply Fin.ext
  dsimp only [boundedComplement]
  split_ifs <;> omega

def boundedComplementEquiv (s : ℕ) (hs : s < 17) : Equiv.Perm (Fin 17) where
  toFun := boundedComplement s hs
  invFun := boundedComplement s hs
  left_inv := boundedComplement_involutive s hs
  right_inv := boundedComplement_involutive s hs

section NativeSupport

variable {A : Type*} [Fintype A]

theorem native_right_conditional_sum_eq (support : List Shape) (s : Shape)
    (p : Shape → ℝ) (priority : Placement) (position : Fin 3) (q : Shape → A → ℝ)
    (hn : support.Nodup) (hm : ∀ u ∈ support, complement s u ∈ support)
    (hsupp : ∀ u ∈ support, ∀ side, u side ≤ s side)
    (hs : s (priority position) < 17)
    (hbound : ∀ i : SupportIndex support, support[i.val] (priority position) < 17)
    (law : FiniteLaw (SupportIndex support))
    (hlaw : ∀ i : SupportIndex support, law.mass i = p support[i.val])
    (hp : ∀ u ∈ support, p (complement s u) = p u)
    (hq : ∀ i : SupportIndex support, ∑ a, q support[i.val] a = 1) :
    (∑ k : Fin 17, (law.map (ownWeight support priority position hbound)).mass k *
      JointCompatibilityIncidence.groupedEntropy
        (law.conditional (ownWeight support priority position hbound) k).mass
        (JointCompatibilityIncidence.designatedGroup (fun i =>
          AllFieldNativeCapacity.designated priority position (complement s support[i.val])))
        (fun i => q (complement s support[i.val]))) =
      AllFieldNativeCapacity.groupedEntropy support p priority position q := by
  let hi : ∀ u ∈ support, complement s (complement s u) = u :=
    fun u hu => complement_involution_of_le s u (hsupp u hu)
  let e := supportIndexEquiv support hn (complement s) hm hi
  let c := boundedComplementEquiv (s (priority position)) hs
  let weight := ownWeight support priority position hbound
  let d : SupportIndex support → Prop :=
    fun i => AllFieldNativeCapacity.designated priority position support[i.val]
  let q₀ : SupportIndex support → A → ℝ := fun i => q support[i.val]
  have he (i : SupportIndex support) :
      support[(e i).val] = complement s support[i.val] := by
    simpa only [List.get_eq_getElem] using
      supportIndexEquiv_get support hn (complement s) hm hi i
  have hmass (i : SupportIndex support) : law.mass (e i) = law.mass i := by
    simp only [hlaw, he]
    exact hp _ (List.getElem_mem i.isLt)
  have hw (i : SupportIndex support) : c (weight i) = weight (e i) := by
    apply Fin.ext
    change (if support[i.val] (priority position) ≤ s (priority position)
      then s (priority position) - support[i.val] (priority position)
      else support[i.val] (priority position)) = support[(e i).val] (priority position)
    rw [ite_eq_left (hsupp _ (List.getElem_mem i.isLt) _), he]
    rfl
  have hright := right_conditional_sum_eq e c law d weight q₀ hmass hw hq
  have hd : d ∘ e = fun i =>
      AllFieldNativeCapacity.designated priority position (complement s support[i.val]) := by
    funext i
    dsimp only [d, Function.comp_apply]
    rw [he]
  have hqr : q₀ ∘ e = fun i => q (complement s support[i.val]) := by
    funext i
    dsimp only [q₀, Function.comp_apply]
    rw [he]
  rw [hd, hqr] at hright
  have hnonneg (i : SupportIndex support) : 0 ≤ p support[i.val] := by
    rw [← hlaw i]
    exact law.nonneg i
  have hmassfun : law.mass = fun i : SupportIndex support => p support[i.val] := funext hlaw
  calc
    _ = JointCompatibilityIncidence.groupedEntropy law.mass
        (nativeGroup support priority position hbound) (fun i => q support[i.val]) := by
      simpa only [d, q₀, weight, nativeGroup] using hright
    _ = _ := by
      rw [hmassfun]
      exact groupedEntropy_eq_native support p priority position q hbound hnonneg hq

theorem native_two_conditional_sums_eq (support : List Shape) (s : Shape)
    (p : Shape → ℝ) (priority : Placement) (position : Fin 3) (q : Shape → A → ℝ)
    (hn : support.Nodup) (hm : ∀ u ∈ support, complement s u ∈ support)
    (hsupp : ∀ u ∈ support, ∀ side, u side ≤ s side)
    (hs : s (priority position) < 17)
    (hbound : ∀ i : SupportIndex support, support[i.val] (priority position) < 17)
    (law : FiniteLaw (SupportIndex support))
    (hlaw : ∀ i : SupportIndex support, law.mass i = p support[i.val])
    (hp : ∀ u ∈ support, p (complement s u) = p u)
    (hq : ∀ i : SupportIndex support, ∑ a, q support[i.val] a = 1) :
    (∑ k : Fin 17, (law.map (ownWeight support priority position hbound)).mass k *
      (JointCompatibilityIncidence.groupedEntropy
        (law.conditional (ownWeight support priority position hbound) k).mass
        (JointCompatibilityIncidence.designatedGroup (fun i =>
          AllFieldNativeCapacity.designated priority position support[i.val]))
        (fun i => q support[i.val]) +
      JointCompatibilityIncidence.groupedEntropy
        (law.conditional (ownWeight support priority position hbound) k).mass
        (JointCompatibilityIncidence.designatedGroup (fun i =>
          AllFieldNativeCapacity.designated priority position (complement s support[i.val])))
        (fun i => q (complement s support[i.val])))) =
      2 * AllFieldNativeCapacity.groupedEntropy support p priority position q := by
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← native_groupedEntropy_eq_sum_conditional support p priority position q hbound law hlaw hq,
    native_right_conditional_sum_eq support s p priority position q hn hm hsupp hs
      hbound law hlaw hp hq]
  ring

end NativeSupport

def twoHalfConditionalCost {A : Type*} [Fintype A]
    (support : List Shape) (s : Shape) (priority : Placement) (position : Fin 3)
    (q : Shape → A → ℝ) (law : FiniteLaw (SupportIndex support))
    (weight : SupportIndex support → Fin 17) : ℝ :=
  ∑ k : Fin 17, (law.map weight).mass k *
    (JointCompatibilityIncidence.groupedEntropy (law.conditional weight k).mass
      (JointCompatibilityIncidence.designatedGroup (fun i =>
        AllFieldNativeCapacity.designated priority position support[i.val]))
      (fun i => q support[i.val]) +
    JointCompatibilityIncidence.groupedEntropy (law.conditional weight k).mass
      (JointCompatibilityIncidence.designatedGroup (fun i =>
        AllFieldNativeCapacity.designated priority position (complement s support[i.val])))
      (fun i => q (complement s support[i.val])))

theorem stageA_twoHalfConditionalCost_eq (g : Shape) (hg : g ∈ positiveInitial)
    (priority : Placement) (position : Fin 3) :
    twoHalfConditionalCost (below g) g priority position
      (fun u a => (halfLaw u (priority position) a : ℝ)) (stageASplitLaw g hg)
      (stageASplitWeight g hg (priority position)) =
      2 * AllFieldNativeCapacity.groupedEntropy (below g)
        (fun u => (stageALaw g u : ℝ)) priority position
        (fun u a => (halfLaw u (priority position) a : ℝ)) := by
  have hs : g (priority position) < 17 :=
    Nat.lt_succ_of_le ((positiveInitial_shape_spec g hg).1 (priority position))
  let hb : ∀ i : SupportIndex (below g), (below g)[i.val] (priority position) < 17 :=
    fun i => lt_of_le_of_lt (below_le (List.getElem_mem i.isLt) _) hs
  have hq (i : SupportIndex (below g)) :
      ∑ a, (halfLaw (below g)[i.val] (priority position) a : ℝ) = 1 :=
    (halfFiniteLaw _ (stageA_children_size g hg _ (List.getElem_mem i.isLt))
      (priority position)).total
  have hh := native_two_conditional_sums_eq (below g) g
    (fun u => (stageALaw g u : ℝ)) priority position
    (fun u a => (halfLaw u (priority position) a : ℝ))
    (stageA_below_nodup g hg) (fun u hu => (stageA_support_complement g hg u hu).1)
    (fun _ hu => below_le hu) hs hb (stageASplitLaw g hg) (fun _ => rfl)
    (fun u hu => by rw [stageALaw_complement g u hg hu]) hq
  have hw : ownWeight (below g) priority position hb =
      stageASplitWeight g hg (priority position) := by
    funext i
    apply Fin.ext
    simp only [ownWeight, stageASplitWeight, List.get_eq_getElem]
  rw [hw] at hh
  simpa only [twoHalfConditionalCost] using hh

theorem stageB_twoHalfConditionalCost_eq (t : Shape) (ht : t ∈ positiveSecond)
    (priority : Placement) (position : Fin 3) :
    twoHalfConditionalCost (below t) t priority position
      (fun u a => (littleLaw t u (priority position) a : ℝ)) (stageBSplitLaw t ht)
      (stageBSplitWeight t ht (priority position)) =
      2 * AllFieldNativeCapacity.groupedEntropy (below t)
        (fun u => (stageBLaw t u : ℝ)) priority position
        (fun u a => (littleLaw t u (priority position) a : ℝ)) := by
  have hs : t (priority position) < 17 :=
    Nat.lt_succ_of_le ((positiveSecond_shape_spec t ht).1 (priority position))
  let hb : ∀ i : SupportIndex (below t), (below t)[i.val] (priority position) < 17 :=
    fun i => lt_of_le_of_lt (below_le (List.getElem_mem i.isLt) _) hs
  have hq (i : SupportIndex (below t)) :
      ∑ a, (littleLaw t (below t)[i.val] (priority position) a : ℝ) = 1 :=
    (littleFiniteLaw t _ (priority position)).total
  have hh := native_two_conditional_sums_eq (below t) t
    (fun u => (stageBLaw t u : ℝ)) priority position
    (fun u a => (littleLaw t u (priority position) a : ℝ))
    (stageB_below_nodup t ht) (fun u hu => (stageB_support_complement t ht u hu).1)
    (fun _ hu => below_le hu) hs hb (stageBSplitLaw t ht) (fun _ => rfl)
    (fun u hu => by rw [stageBLaw_complement t u ht hu]) hq
  have hw : ownWeight (below t) priority position hb =
      stageBSplitWeight t ht (priority position) := by
    funext i
    apply Fin.ext
    simp only [ownWeight, stageBSplitWeight, List.get_eq_getElem]
  rw [hw] at hh
  simpa only [twoHalfConditionalCost] using hh

theorem stageA_twoHalfConditionalCost_eq_entropy_sub_capacity
    (g : Shape) (hg : g ∈ positiveInitial) (side : Fin 3) (hside : side ≠ 0) :
    twoHalfConditionalCost (below g) g (Equiv.refl (Fin 3)) side
      (fun u a => (halfLaw u side a : ℝ)) (stageASplitLaw g hg)
      (stageASplitWeight g hg side) =
      finiteEntropy (stageAPairLaw g hg side).mass - stageACapacity g side := by
  rw [stageACapacity_sharing g hg side hside]
  have hh := stageA_twoHalfConditionalCost_eq g hg (Equiv.refl (Fin 3)) side
  simpa only [Equiv.refl_apply, sub_sub_cancel] using hh

theorem stageB_twoHalfConditionalCost_eq_entropy_sub_capacity
    (t : Shape) (ht : t ∈ positiveSecond) (side : Fin 3) (hside : side ≠ 0) :
    twoHalfConditionalCost (below t) t (stageBPriority t) side
      (fun u a => (littleLaw t u (stageBPriority t side) a : ℝ)) (stageBSplitLaw t ht)
      (stageBSplitWeight t ht (stageBPriority t side)) =
      finiteEntropy (stageBPairLaw t ht (stageBPriority t side)).mass -
        stageBCapacity t side := by
  rw [stageBCapacity_sharing t ht side hside]
  have hh := stageB_twoHalfConditionalCost_eq t ht (stageBPriority t) side
  simpa only [sub_sub_cancel] using hh

end MatrixMultiplication.AllFieldNativeGroupedRates

end

end OAI
