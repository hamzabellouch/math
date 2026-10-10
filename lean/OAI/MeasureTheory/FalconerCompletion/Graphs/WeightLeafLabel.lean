import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.IntervalRamp

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
variable {d : ℕ}

noncomputable def weightLeafLabel (M : ℕ) (w : CellPath d → ℝ) (p : CellPath d) : List ℕ :=
  [leafMassBin M (w p)]

lemma weightLeafLabel_card_le (L : Finset (CellPath d)) (M : ℕ) (w : CellPath d → ℝ) :
    (L.image (weightLeafLabel M w)).card ≤ M+1 := by
  classical
  have hs : L.image (weightLeafLabel M w) ⊆
      (Finset.range (M+1)).image (fun k => [k]) := by
    intro T hT
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_image.mpr ⟨leafMassBin M (w p),
      Finset.mem_range.mpr (Nat.lt_succ_of_le (leafMassBin_le M _)),rfl⟩
  exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans (by simp))

lemma weighted_class_bin_bounds {N M B K : ℕ} {L : Finset (CellPath d)}
    (w : CellPath d → ℝ) (hw : ∀ q ∈ L, 1 ≤ (2:ℝ)^M*w q ∧ w q ≤ 1)
    {p : CellPath d} :
    let F := blockLabel L N B (weightLeafLabel M w) K
    let s := leafBinEndpoint M (leafMassBin M (w p))
    0 < s ∧ ∀ q ∈ classLeaves L F (F p), s ≤ w q ∧ w q ≤ 2*s := by
  refine ⟨leafBinEndpoint_pos _ _,?_⟩
  intro q hq
  obtain ⟨hq,he⟩ := Finset.mem_filter.mp hq
  have hold := blockLabel_old L N B (weightLeafLabel M w) (Nat.zero_le K) he
  have heq : leafMassBin M (w q) = leafMassBin M (w p) := by
    simpa only [blockLabel,weightLeafLabel,List.singleton_inj] using hold
  have hh := leaf_mass_bin_bounds (hw q hq).1 (hw q hq).2
  rw [heq] at hh
  exact ⟨hh.1,hh.2.le⟩

lemma sum_weight_bounds {C : Finset (CellPath d)} {w : CellPath d → ℝ} {s : ℝ}
    (hw : ∀ q ∈ C, s ≤ w q ∧ w q ≤ 2*s) :
    (C.card:ℝ)*s ≤ ∑ q ∈ C, w q ∧ ∑ q ∈ C, w q ≤ (C.card:ℝ)*(2*s) := by
  constructor
  · calc
      _ = ∑ _q ∈ C, s := by simp
      _ ≤ _ := Finset.sum_le_sum fun q hq => (hw q hq).1
  · calc
      _ ≤ ∑ _q ∈ C, 2*s := Finset.sum_le_sum fun q hq => (hw q hq).2
      _ = _ := by simp

theorem weighted_class_grid_bounds {N M : ℕ} {L : Finset (CellPath d)}
    (hL : L ⊆ dyadicPaths N) (w : CellPath d → ℝ)
    (hw : ∀ q ∈ L, 1 ≤ (2:ℝ)^M*w q ∧ w q ≤ 1)
    {B : ℕ} (hB : 0 < B) {p : CellPath d} (hp : p ∈ L)
    {i : ℕ} (hi : i ≤ N/B+1) {P : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B (weightLeafLabel M w) (N/B+1))
      (blockLabel L N B (weightLeafLabel M w) (N/B+1) p)).image
      (List.take (blockDepth N B i))) :
    let K := N/B+1
    let F := blockLabel L N B (weightLeafLabel M w) K
    let C := classLeaves L F (F p)
    let ref := (blockProduct L F N B i p : ℝ)/(blockProduct L F N B K p : ℝ)
    ref/(2:ℝ)^(K+1) ≤ (∑ q ∈ prefixFiber C (blockDepth N B i) P, w q)/(∑ q ∈ C, w q) ∧
      (∑ q ∈ prefixFiber C (blockDepth N B i) P, w q)/(∑ q ∈ C, w q) ≤ (2:ℝ)^(K+1)*ref := by
  classical
  let K := N/B+1
  let F := blockLabel L N B (weightLeafLabel M w) K
  let C := classLeaves L F (F p)
  let s := leafBinEndpoint M (leafMassBin M (w p))
  have hbin := weighted_class_bin_bounds (N := N) (B := B) (K := K) (p := p) w hw
  have hs : 0 < s := hbin.1
  have hm : ∀ q ∈ C, s ≤ w q ∧ w q ≤ 2*s := hbin.2
  have hmass := sum_weight_bounds (C := prefixFiber C (blockDepth N B i) P)
    (fun q hq => hm q (Finset.mem_filter.mp hq).1)
  have htotal := sum_weight_bounds hm
  have hc := blockClass_leaf_count hL B (weightLeafLabel M w) K p hi hP
  have hr := blockClass_root_count hL hB (weightLeafLabel M w) hp
  change blockProduct L F N B i p ≤ (prefixFiber C (blockDepth N B i) P).card ∧
    (prefixFiber C (blockDepth N B i) P).card ≤ 2^i*blockProduct L F N B i p at hc
  change blockProduct L F N B K p ≤ C.card ∧ C.card ≤ 2^K*blockProduct L F N B K p at hr
  have hpow : (2:ℝ)^i ≤ (2:ℝ)^K := pow_le_pow_right₀ (by norm_num) hi
  have hu : 0 < (blockProduct L F N B i p : ℝ) := by exact_mod_cast blockProduct_pos L F N B i p
  have hv : 0 < (blockProduct L F N B K p : ℝ) := by exact_mod_cast blockProduct_pos L F N B K p
  have hci : (blockProduct L F N B i p:ℝ) ≤ (prefixFiber C (blockDepth N B i) P).card ∧
      ((prefixFiber C (blockDepth N B i) P).card:ℝ) ≤ (2:ℝ)^i*(blockProduct L F N B i p:ℝ) := by
    exact_mod_cast hc
  have hcr : (blockProduct L F N B K p:ℝ) ≤ (C.card:ℝ) ∧
      (C.card:ℝ) ≤ (2:ℝ)^K*(blockProduct L F N B K p:ℝ) := by exact_mod_cast hr
  have hx : (blockProduct L F N B i p:ℝ)*s ≤
      ∑ q ∈ prefixFiber C (blockDepth N B i) P, w q ∧
      (∑ q ∈ prefixFiber C (blockDepth N B i) P, w q) ≤
        (2:ℝ)^(K+1)*(blockProduct L F N B i p:ℝ)*s := by
    constructor
    · exact (mul_le_mul_of_nonneg_right hci.1 hs.le).trans hmass.1
    · have hc' := hci.2.trans (mul_le_mul_of_nonneg_right hpow hu.le)
      have hh := hmass.2.trans (mul_le_mul_of_nonneg_right hc' (by positivity : 0 ≤ 2*s))
      simpa only [pow_succ,mul_assoc,mul_left_comm,mul_comm] using hh
  have ht : (blockProduct L F N B K p:ℝ)*s ≤ (∑ q ∈ C, w q) ∧
      (∑ q ∈ C, w q) ≤ (2:ℝ)^(K+1)*(blockProduct L F N B K p:ℝ)*s := by
    constructor
    · exact (mul_le_mul_of_nonneg_right hcr.1 hs.le).trans htotal.1
    · have hh := htotal.2.trans (mul_le_mul_of_nonneg_right hcr.2 (by positivity : 0 ≤ 2*s))
      simpa only [pow_succ,mul_assoc,mul_left_comm,mul_comm] using hh
  exact ratio_bounds_of_mass_bounds hs hu hv (by positivity) hx ht

theorem weighted_class_profile_grid {N M : ℕ} (hN : 0 < N) {L : Finset (CellPath d)}
    (hL : L ⊆ dyadicPaths N) (w : CellPath d → ℝ)
    (hw : ∀ q ∈ L, 1 ≤ (2:ℝ)^M*w q ∧ w q ≤ 1)
    {B : ℕ} (hB : 0 < B) {p : CellPath d} (hp : p ∈ L)
    {i : ℕ} (hi : i ≤ N/B+1) {P : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B (weightLeafLabel M w) (N/B+1))
      (blockLabel L N B (weightLeafLabel M w) (N/B+1) p)).image
      (List.take (blockDepth N B i))) :
    let K := N/B+1
    let F := blockLabel L N B (weightLeafLabel M w) K
    let C := classLeaves L F (F p)
    let ref := ((2:ℝ)^N)^(-regularizedProfile L F N B K p (blockDepth N B i))
    ref/(2:ℝ)^(K+1) ≤ (∑ q ∈ prefixFiber C (blockDepth N B i) P, w q)/(∑ q ∈ C, w q) ∧
      (∑ q ∈ prefixFiber C (blockDepth N B i) P, w q)/(∑ q ∈ C, w q) ≤ (2:ℝ)^(K+1)*ref := by
  dsimp only
  rw [regularizedProfile_reference_grid hN hL _ hB p hi]
  exact weighted_class_grid_bounds hL w hw hB hp hi hP

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
