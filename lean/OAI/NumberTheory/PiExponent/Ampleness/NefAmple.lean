import Mathlib

namespace OAI

open Set
open scoped Pointwise

namespace PiExponent.NefAmple

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E]

def nonnegativeCone {ι : Type*} (degree : ι → E →L[ℝ] ℝ) : ConvexCone ℝ E where
  carrier := {x | ∀ i, 0 ≤ degree i x}
  smul_mem' := by
    intro c hc x hx i
    simpa only [map_smul, smul_eq_mul] using mul_nonneg hc.le (hx i)
  add_mem' := by
    intro x hx y hy i
    simpa only [map_add] using add_nonneg (hx i) (hy i)

omit [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E] in
@[simp] theorem mem_nonnegativeCone {ι : Type*} (degree : ι → E →L[ℝ] ℝ) (x : E) :
    x ∈ nonnegativeCone degree ↔ ∀ i, 0 ≤ degree i x := Iff.rfl

omit [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E] in
theorem isClosed_nonnegativeCone {ι : Type*} (degree : ι → E →L[ℝ] ℝ) :
    IsClosed (nonnegativeCone degree : Set E) := by
  have heq : (nonnegativeCone degree : Set E) = ⋂ i, {x | 0 ≤ degree i x} := by
    ext x
    simp
  rw [heq]
  exact isClosed_iInter (fun i => isClosed_le continuous_const (degree i).continuous)

omit [IsTopologicalAddGroup E] in

theorem pos_smul_mem_interior (C : ConvexCone ℝ E) {x : E}
    (hx : x ∈ interior (C : Set E)) {c : ℝ} (hc : 0 < c) :
    c • x ∈ interior (C : Set E) := by
  have hs : c • (C : Set E) ⊆ (C : Set E) := by
    rintro _ ⟨y, hy, rfl⟩
    exact C.smul_mem hc hy
  apply interior_mono hs
  rw [interior_smul₀ hc.ne']
  exact smul_mem_smul_set hx

omit [ContinuousConstSMul ℝ E] in

theorem add_mem_interior (C : ConvexCone ℝ E) {x y : E}
    (hx : x ∈ C) (hy : y ∈ interior (C : Set E)) :
    x + y ∈ interior (C : Set E) := by
  have hm : x + y ∈ (C : Set E) + interior (C : Set E) := add_mem_add hx hy
  have hi : x + y ∈ interior ((C : Set E) + (C : Set E)) :=
    subset_interior_add_right hm
  apply interior_mono (s := (C : Set E) + (C : Set E)) ?_ hi
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact C.add_mem ha hb

theorem positive_combination_mem_interior (C : ConvexCone ℝ E) {x y : E}
    (hx : x ∈ C) (hy : y ∈ interior (C : Set E)) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    a • x + b • y ∈ interior (C : Set E) :=
  add_mem_interior C (C.smul_mem ha hx) (pos_smul_mem_interior C hy hb)

theorem combination_denominator_pos {a σ : ℝ} (ha : 1 < a) (hσ : 0 < σ) :
    0 < a * (1 + σ) - 1 := by
  have hp : 0 < a * σ := mul_pos (zero_lt_one.trans ha) hσ
  nlinarith

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E] in

theorem interpolation_divisor_identity (A F : E) {a σ : ℝ}
    (ha : 1 < a) (hσ : 0 < σ) :
    ((a - 1) / (a * (1 + σ) - 1)) • (A - (1 + σ) • F) +
      (σ / (a * (1 + σ) - 1)) • (a • A - F) = A - F := by
  have hd : a * (1 + σ) - 1 ≠ 0 := (combination_denominator_pos ha hσ).ne'
  have hA : (a - 1) / (a * (1 + σ) - 1) +
      σ / (a * (1 + σ) - 1) * a = 1 := by field_simp; ring
  have hF : ((a - 1) / (a * (1 + σ) - 1)) * (1 + σ) +
      σ / (a * (1 + σ) - 1) = 1 := by field_simp; ring
  calc
    _ = ((a - 1) / (a * (1 + σ) - 1) + σ / (a * (1 + σ) - 1) * a) • A -
        (((a - 1) / (a * (1 + σ) - 1)) * (1 + σ) + σ / (a * (1 + σ) - 1)) • F := by
          simp only [smul_sub, smul_smul]
          rw [add_smul, add_smul]
          abel
    _ = A - F := by rw [hA, hF, one_smul, one_smul]

theorem interpolation_divisor_mem_interior (C : ConvexCone ℝ E) (A F : E)
    {a σ : ℝ} (ha : 1 < a) (hσ : 0 < σ)
    (hne : A - (1 + σ) • F ∈ C)
    (hin : a • A - F ∈ interior (C : Set E)) :
    A - F ∈ interior (C : Set E) := by
  have hd := combination_denominator_pos ha hσ
  rw [← interpolation_divisor_identity A F ha hσ]
  exact positive_combination_mem_interior C hne hin
    (div_pos (sub_pos.mpr ha) hd) (div_pos hσ hd)

omit [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E] in

theorem interpolation_degree_margin (degree : E →L[ℝ] ℝ) (A F : E)
    {a σ : ℝ} (ha : 1 < a) (hσ : 0 < σ)
    (hne : 0 ≤ degree (A - (1 + σ) • F)) :
    (σ / (a * (1 + σ) - 1)) * degree (a • A - F) ≤ degree (A - F) := by
  have hcoef : 0 < (a - 1) / (a * (1 + σ) - 1) :=
    div_pos (sub_pos.mpr ha) (combination_denominator_pos ha hσ)
  have he := congrArg degree (interpolation_divisor_identity A F ha hσ)
  simp only [map_add, map_smul, smul_eq_mul] at he
  have hn := mul_nonneg hcoef.le hne
  linarith

omit [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E] in

theorem interpolation_degree_pos (degree : E →L[ℝ] ℝ) (A F : E)
    {a σ : ℝ} (ha : 1 < a) (hσ : 0 < σ)
    (hne : 0 ≤ degree (A - (1 + σ) • F))
    (hpos : 0 < degree (a • A - F)) : 0 < degree (A - F) :=
  (mul_pos (div_pos hσ (combination_denominator_pos ha hσ)) hpos).trans_le
    (interpolation_degree_margin degree A F ha hσ hne)

end PiExponent.NefAmple

end OAI
