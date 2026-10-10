import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FixedCharges
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RecordedTops
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SingleEdgeWeight

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma treeOccurrences_empty_of_free_core (w : ClosedLine h ℓ) (p : S.FreeCoreIndex w) :
    treeOccurrences w p.val.val = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact p.val.property ⟨⟨i,(mem_filter.mp hi).2⟩, Or.inl p.property⟩

lemma treeOccurrences_singleton_of_free (w : ClosedLine h ℓ) (p : S.FreeIndex w)
    (e : Fin ℓ) (he : e ∈ treeOccurrences w p.val) :
    treeOccurrences w p.val = {e} := by
  ext i
  constructor
  · intro hi
    exact mem_singleton.mpr ((unique_occurrence_of_free w p.val p.property e
      (mem_filter.mp he).2 i).mp (mem_filter.mp hi).2)
  · intro hi
    simpa only [mem_singleton.mp hi] using he

def freeTreeWeight (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) (p : S.Index) : ℝ :=
  ∏ e ∈ treeOccurrences w p, singletonTokenWeight w 𝔏 p e

lemma freeTreeWeight_nonneg (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) : 0 ≤ freeTreeWeight w 𝔏 p :=
  prod_nonneg (fun _ _ => singletonTokenWeight_nonneg w 𝔏 p _)

def primeBound (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) (U : Finset ℤ)
    (E : S.Index → Finset (Fin ℓ)) (p : S.Index) : ℝ :=
  if (treeOccurrences w p).Nonempty then
    (if S.IsFixed w p then fixedTreeWeight w p (E p) else freeTreeWeight w 𝔏 p) / (p : ℝ)
  else outsideTreeBound w 𝔏 U p

lemma primeBound_nonneg (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (E : S.Index → Finset (Fin ℓ)) (p : S.Index) :
    0 ≤ primeBound w 𝔏 U E p := by
  unfold primeBound
  split_ifs
  · exact div_nonneg (fixedTreeWeight_nonneg w p _) (Nat.cast_nonneg _)
  · exact div_nonneg (freeTreeWeight_nonneg w 𝔏 p) (Nat.cast_nonneg _)
  · exact outsideTreeBound_nonneg w 𝔏 U p

lemma no_tree_of_not_nonempty (w : ClosedLine h ℓ) (p : S.Index)
    (hn : ¬(treeOccurrences w p).Nonempty) :
    ∀ i ∈ w.treeSteps, ¬(p : ℕ) ∣ w.label i := by
  intro i hi hd
  exact hn ⟨i, mem_filter.mpr ⟨hi,hd⟩⟩

lemma fixed_mean_le_primeBound (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (U : Finset ℤ) (hU : U ⊆ goodOrigins w) (E : S.Index → Finset (Fin ℓ))
    (p : S.FixedIndex w) (htop : NoComponentTop w U p.val (E p.val)) :
    avg (recordPrime w 𝔏 U p.val (E p.val)) ≤ primeBound w 𝔏 U E p.val := by
  by_cases ho : (treeOccurrences w p.val).Nonempty
  · rw [primeBound, ite_eq_left ho, ite_eq_left p.property]
    exact fixed_tree_mean w 𝔏 U hU p.val (E p.val) htop ho
  · rw [primeBound, ite_eq_right ho]
    exact (avg_mono (recordPrime_le_charged_local w 𝔏 U p.val (E p.val))).trans
      (outside_tree_mean w 𝔏 U hU p.val (no_tree_of_not_nonempty w p.val ho))

lemma free_core_mean_le_primeBound (w : ClosedLine h ℓ)
    (𝔏 : List (AttachedSpec w D L)) (U : Finset ℤ) (hU : U ⊆ goodOrigins w)
    (E : S.Index → Finset (Fin ℓ)) (p : S.FreeCoreIndex w) :
    avg (fun a => |localWithList w 𝔏 p.val.val a| * allPrimeCharges w U p.val.val a) ≤
      primeBound w 𝔏 U E p.val.val := by
  have ho : ¬(treeOccurrences w p.val.val).Nonempty := by
    rw [treeOccurrences_empty_of_free_core w p]
    exact not_nonempty_empty
  rw [primeBound, ite_eq_right ho]
  exact outside_tree_mean w 𝔏 U hU p.val.val (no_tree_of_not_nonempty w p.val.val ho)

lemma free_center_mean_le_primeBound (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (U : Finset ℤ) (hU : U ⊆ goodOrigins w)
    (E : S.Index → Finset (Fin ℓ)) (p : S.FreeCenterIndex w)
    (hlarge : 2 * (ℓ+1) ≤ (p.val.val : ℕ)) :
    |avg (localWithList w 𝔏 p.val.val)| ≤ primeBound w 𝔏 U E p.val.val := by
  by_cases ho : (treeOccurrences w p.val.val).Nonempty
  · rw [primeBound, ite_eq_left ho, ite_eq_right p.val.property]
    obtain ⟨e,he⟩ := ho
    rw [freeTreeWeight, treeOccurrences_singleton_of_free w p.val e he, prod_singleton]
    exact free_center_tree_mean w hh 𝔏 p e (mem_filter.mp he).2 hlarge
  · rw [primeBound, ite_eq_right ho]
    have hc := outside_tree_mean w 𝔏 U hU p.val.val
      (no_tree_of_not_nonempty w p.val.val ho)
    simp only [allPrimeCharges_center w U p.val.val p.property, mul_one] at hc
    exact (abs_avg_le _).trans hc

lemma product_index_split (w : ClosedLine h ℓ) (f : S.Index → ℝ) :
    (∏ p : S.FixedIndex w, f p.val) *
      ((∏ p : S.FreeCoreIndex w, f p.val.val) *
       (∏ p : S.FreeCenterIndex w, f p.val.val)) = ∏ p : S.Index, f p := by
  rw [Fintype.prod_subtype_mul_prod_subtype (fun p : S.FreeIndex w => S.IsCore p.val)
    (fun p : S.FreeIndex w => f p.val)]
  exact Fintype.prod_subtype_mul_prod_subtype (S.IsFixed w) f

theorem assignedKernelIntegral_le_all_prime_bounds (w : ClosedLine h ℓ) (hh : 0 < h)
    {T : ℝ} (cut : S.Cutoffs T) (𝔏 : List (AttachedSpec w D L))
    (E : S.Index → Finset (Fin ℓ)) (hE : ∀ p, E p ⊆ treeOccurrences w p)
    (group : S.FixedResidues w → Prop)
    (hgroup : ∀ a, group a → ∀ p : S.FixedIndex w, litEdges w p.val (a p) = E p.val)
    (hlarge : ∀ p : S.Index, 2 * (ℓ+1) ≤ (p : ℕ)) :
    assignedKernelIntegral w cut 𝔏 group ≤
      chargeConstant (S := S) w T (recordU w E) *
        ∏ p : S.Index, primeBound w 𝔏 (recordU w E) E p := by
  let U := recordU w E
  have hU := recordU_subset w E
  have hh' := assignedKernelIntegral_le_prime_means w cut 𝔏 U hU group
    (fun p => E p.val) hgroup
  apply hh'.trans
  calc
    _ ≤ chargeConstant (S := S) w T U *
        (∏ p : S.FreeCenterIndex w, primeBound w 𝔏 U E p.val.val) *
        (∏ p : S.FixedIndex w, primeBound w 𝔏 U E p.val) *
        ∏ p : S.FreeCoreIndex w, primeBound w 𝔏 U E p.val.val := by
      have hZ := prod_le_prod₀ (s := univ) (fun (p : S.FreeCenterIndex w) _ => abs_nonneg
          (avg (localWithList w 𝔏 p.val.val)))
        (fun p _ => free_center_mean_le_primeBound w hh 𝔏 U hU E p (hlarge _))
      have hF := prod_le_prod₀ (s := univ) (fun (p : S.FixedIndex w) _ =>
          avg_nonneg (recordPrime_nonneg w 𝔏 U p.val (E p.val)))
        (fun p _ => fixed_mean_le_primeBound w 𝔏 U hU E p
          (recordU_noComponentTop w E hE _))
      have hC := prod_le_prod₀ (s := univ) (fun (p : S.FreeCoreIndex w) _ => avg_nonneg (fun a =>
          mul_nonneg (abs_nonneg _) (allPrimeCharges_nonneg w U p.val.val a)))
        (fun p _ => free_core_mean_le_primeBound w 𝔏 U hU E p)
      have hZF := mul_le_mul hZ hF
        (prod_nonneg (fun p _ => avg_nonneg (recordPrime_nonneg w 𝔏 U p.val _)))
        (prod_nonneg (fun p _ => primeBound_nonneg w 𝔏 U E p.val.val))
      have hZFC := mul_le_mul hZF hC
        (prod_nonneg (fun p _ => avg_nonneg (fun a =>
          mul_nonneg (abs_nonneg _) (allPrimeCharges_nonneg w U p.val.val a))))
        (mul_nonneg (prod_nonneg (fun p _ => primeBound_nonneg w 𝔏 U E p.val.val))
          (prod_nonneg (fun p _ => primeBound_nonneg w 𝔏 U E p.val)))
      simpa only [chargeConstant, mul_assoc] using mul_le_mul_of_nonneg_left hZFC
        ((Real.exp_pos _).le : 0 ≤ chargeConstant (S := S) w T U)
    _ = _ := by
      rw [← product_index_split w]
      ring

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
