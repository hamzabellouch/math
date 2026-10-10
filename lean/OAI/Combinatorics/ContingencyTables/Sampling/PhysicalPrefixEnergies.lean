import OAI.Combinatorics.ContingencyTables.Transport.ContextGraphEnergy
import OAI.Combinatorics.ContingencyTables.Transport.FiniteExposureVariance

namespace OAI

/-! # Physical prefix contexts use each exchange edge at most once -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def prefixExtension (small : I → J → Bool) (s : I×J) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) : I×J → ℕ := fun a =>
  if h : small a.1 a.2=true ∧ RowMajorBefore a s then (τ ⟨⟨a,h.1⟩,h.2⟩).val else 0

omit [Fintype I] [Fintype J] in
lemma prefixExtension_at (small : I → J → Bool) (s : I×J) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) (a : Earlier small s) :
    prefixExtension small s U τ a.val.val=(τ a).val := by
  unfold prefixExtension
  rw [dite_eq_left ⟨a.val.property,a.property⟩]
  exact congrArg (fun b : Earlier small s => (τ b).val) (Subtype.ext (Subtype.ext rfl))

omit [Fintype I] [Fintype J] in
lemma prefixExtension_bounded (small : I → J → Bool) (s : I×J) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) (a : Earlier small s) :
    prefixExtension small s U τ a.val.val ≤ U := by
  rw [prefixExtension_at]
  exact Nat.le_of_lt_succ (τ a).isLt

noncomputable def prefixValues (small : I → J → Bool) (s : I×J) (U : ℕ)
    (z : SmallProfile small) : Earlier small s → Fin (U+1) :=
  fun a => ⟨min (z (a.val,false)) U,Nat.lt_succ_of_le (min_le_right _ _)⟩

omit [Fintype I] [Fintype J] in
lemma physicalPrefix_iff_values (small : I → J → Bool) (s : I×J) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) (z : SmallProfile small)
    (hz : ∀ a : Earlier small s,z (a.val,false) ≤ U) :
    PhysicalPrefix small s (prefixExtension small s U τ) z ↔ prefixValues small s U z=τ := by
  constructor
  · intro hp
    funext a
    apply Fin.ext
    change min (z (a.val,false)) U=(τ a).val
    rw [min_eq_left (hz a),hp a,prefixExtension_at]
  · intro hp a
    have h := congrArg Fin.val (congrFun hp a)
    change min (z (a.val,false)) U=(τ a).val at h
    rw [min_eq_left (hz a)] at h
    rw [prefixExtension_at]
    exact h

noncomputable def physicalEdges (small : I → J → Bool) (B : I → J → ℕ) :
    Finset (SmallProfile small×SmallProfile small) :=
  ((vertices small B) ×ˢ (vertices small B)).filter (fun p => IntegerExchangeAdjacent p.1 p.2)

noncomputable def physicalEnergy (small : I → J → Bool) (B : I → J → ℕ)
    (f H : SmallProfile small → ℝ) : ℝ :=
  (∑ p ∈ physicalEdges small B,edgeTerm f H p)/2

lemma physicalContextEdges_eq_filter (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (U : ℕ) (hB : ∀ i j,small i j=true → B i j=U)
    (τ : Earlier small s → Fin (U+1)) :
    physicalContextEdges small B s (prefixExtension small s U τ)=
      (physicalEdges small B).filter (fun p =>
        prefixValues small s U p.1=prefixValues small s U p.2 ∧ prefixValues small s U p.1=τ) := by
  ext p
  simp only [physicalContextEdges,physicalEdges,Finset.mem_filter,Finset.mem_product]
  constructor
  · rintro ⟨⟨hx,hy⟩,ha,hpx,hpy⟩
    have hxb := (mem_vertices_iff small B p.1).mp hx
    have hyb := (mem_vertices_iff small B p.2).mp hy
    have hvx := (physicalPrefix_iff_values small s U τ p.1 (fun a => by
      simpa only [hB _ _ a.val.property] using hxb.1 (a.val,false))).mp hpx
    have hvy := (physicalPrefix_iff_values small s U τ p.2 (fun a => by
      simpa only [hB _ _ a.val.property] using hyb.1 (a.val,false))).mp hpy
    exact ⟨⟨⟨hx,hy⟩,ha⟩,hvx.trans hvy.symm,hvx⟩
  · rintro ⟨⟨⟨hx,hy⟩,ha⟩,hv,hτ⟩
    have hxb := (mem_vertices_iff small B p.1).mp hx
    have hyb := (mem_vertices_iff small B p.2).mp hy
    refine ⟨⟨hx,hy⟩,ha,?_,?_⟩
    · exact (physicalPrefix_iff_values small s U τ p.1 (fun a => by
        simpa only [hB _ _ a.val.property] using hxb.1 (a.val,false))).mpr hτ
    · exact (physicalPrefix_iff_values small s U τ p.2 (fun a => by
        simpa only [hB _ _ a.val.property] using hyb.1 (a.val,false))).mpr (hv.symm.trans hτ)

lemma sum_physicalContextEdgeTerms_le (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (U : ℕ) (hB : ∀ i j,small i j=true → B i j=U)
    (f H : SmallProfile small → ℝ) (hf : ∀ z,0 ≤ f z) :
    (∑ τ : Earlier small s → Fin (U+1), ∑ p ∈
      physicalContextEdges small B s (prefixExtension small s U τ), edgeTerm f H p) ≤
      ∑ p ∈ physicalEdges small B,edgeTerm f H p := by
  simp_rw [physicalContextEdges_eq_filter small B s U hB]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro p _
  by_cases h : prefixValues small s U p.1=prefixValues small s U p.2
  · simp only [h,true_and,Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte]
    exact le_rfl
  · simpa only [h,false_and,↓reduceIte,Finset.sum_const_zero,edgeTerm] using
      mul_nonneg (le_min (hf p.1) (hf p.2)) (sq_nonneg (H p.1-H p.2))

/-- At a fixed exposed cell, prefix contexts partition eligible physical
edges. Nonnegative exchange energy is therefore counted at most once. -/
theorem sum_physicalContextEnergy_le (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (U : ℕ) (hB : ∀ i j,small i j=true → B i j=U)
    (f H : SmallProfile small → ℝ) (hf : ∀ z,0 ≤ f z) :
    (∑ τ : Earlier small s → Fin (U+1),
      physicalContextEnergy small B s (prefixExtension small s U τ) f H) ≤
      physicalEnergy small B f H := by
  unfold physicalContextEnergy physicalEnergy
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right
    (sum_physicalContextEdgeTerms_le small B s U hB f H hf) (by norm_num)

end ContingencyTables.SmallGraphProfiles

end OAI
