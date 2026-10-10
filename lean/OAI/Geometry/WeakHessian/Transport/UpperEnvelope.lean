import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set

namespace WeakHessianTransport
variable {A E : Type*} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup E] [Module ℝ E]

lemma exists_sublinear_support (N : E → ℝ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, N (r • x) = r * N x)
    (hadd : ∀ x y, N (x+y) ≤ N x + N y) (x : E) :
    ∃ g : E →ₗ[ℝ] ℝ, g x = N x ∧ ∀ y, g y ≤ N y := by
  have hzero : N 0 = 0 := by
    have H := hhom 2 (by norm_num) 0
    simp only [smul_zero] at H
    linarith
  have hcompat : ∀ r : ℝ, r • x = 0 → r • N x = 0 := by
    intro r hr
    rcases smul_eq_zero.mp hr with hr | hx
    · simp [hr]
    · simp [hx,hzero]
  let p : E →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' x (N x) hcompat
  have hdom : ∀ y : p.domain, p y ≤ N y := by
    rintro ⟨y,hy⟩
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hy
    change LinearPMap.mkSpanSingleton' x (N x) hcompat ⟨r • x, _⟩ ≤ N (r • x)
    rw [LinearPMap.mkSpanSingleton'_apply]
    simp only [RingHom.id_apply, smul_eq_mul]
    rcases lt_trichotomy 0 r with hr | hr | hr
    · rw [hhom r hr x]
    · simp [← hr,hzero]
    · have H := hadd x (-x)
      rw [add_neg_cancel, hzero] at H
      have heq : r • x = (-r) • (-x) := by simp
      rw [heq, hhom (-r) (by linarith) (-x)]
      have H' := mul_le_mul_of_nonneg_left H (show 0 ≤ -r by linarith)
      nlinarith
  obtain ⟨g,hgp,hg⟩ := exists_extension_of_le_sublinear p N hhom hadd hdom
  refine ⟨g, ?_, hg⟩
  have hx : x ∈ p.domain := Submodule.mem_span_singleton_self x
  have H := hgp ⟨x,hx⟩
  simpa only [p, LinearPMap.mkSpanSingleton'_apply_self] using H

variable [PartialOrder E] [IsOrderedAddMonoid E] [PosSMulMono ℝ E]

def upperEnvelope (T : A →ₗ[ℝ] E) (c : A →ₗ[ℝ] ℝ) (x : E) : ℝ :=
  sInf {r | ∃ a : A, x ≤ T a ∧ r = c a}

variable (T : A →ₗ[ℝ] E) (c : A →ₗ[ℝ] ℝ) (l : E →ₗ[ℝ] ℝ)
  (hl : Monotone l) (hcomp : ∀ a, l (T a) = c a)
  (hmajor : ∀ x : E, ∃ a : A, x ≤ T a)

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hmajor in
lemma envelope_nonempty (x : E) : {r | ∃ a : A, x ≤ T a ∧ r = c a}.Nonempty := by
  obtain ⟨a,ha⟩ := hmajor x
  exact ⟨c a, a, ha, rfl⟩

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hl hcomp in
lemma envelope_bddBelow (x : E) : BddBelow {r | ∃ a : A, x ≤ T a ∧ r = c a} := by
  refine ⟨l x, ?_⟩
  rintro r ⟨a,ha,rfl⟩
  simpa only [hcomp] using hl ha

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hl hcomp hmajor in
lemma lower_le_envelope (x : E) : l x ≤ upperEnvelope T c x := by
  apply le_csInf (envelope_nonempty T c hmajor x)
  rintro r ⟨a,ha,rfl⟩
  simpa only [hcomp] using hl ha

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hl hcomp in
lemma envelope_le (x : E) (a : A) (ha : x ≤ T a) : upperEnvelope T c x ≤ c a :=
  csInf_le (envelope_bddBelow T c l hl hcomp x) ⟨a,ha,rfl⟩

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hl hcomp hmajor in
lemma envelope_image (a : A) : upperEnvelope T c (T a) = c a := by
  exact le_antisymm (envelope_le T c l hl hcomp _ a le_rfl)
    (by simpa only [hcomp] using lower_le_envelope T c l hl hcomp hmajor (T a))

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hl hcomp hmajor in
lemma envelope_zero : upperEnvelope T c (0 : E) = 0 := by
  simpa only [map_zero] using envelope_image T c l hl hcomp hmajor 0

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hl hcomp hmajor in
lemma envelope_mono : Monotone (upperEnvelope T c) := by
  intro x y hxy
  apply le_csInf (envelope_nonempty T c hmajor y)
  rintro r ⟨a,ha,rfl⟩
  exact envelope_le T c l hl hcomp x a (hxy.trans ha)

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hmajor in
lemma envelope_lt {x : E} {r : ℝ} (hr : upperEnvelope T c x < r) :
    ∃ a : A, x ≤ T a ∧ c a < r := by
  obtain ⟨s,⟨a,ha,rfl⟩,hs⟩ := exists_lt_of_csInf_lt (envelope_nonempty T c hmajor x) hr
  exact ⟨a,ha,hs⟩

omit [PosSMulMono ℝ E] in
include hl hcomp hmajor in
lemma envelope_add (x y : E) :
    upperEnvelope T c (x+y) ≤ upperEnvelope T c x + upperEnvelope T c y := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a,ha,har⟩ := envelope_lt T c hmajor (x := x) (r := upperEnvelope T c x+ε/2) (by linarith)
  obtain ⟨b,hb,hbr⟩ := envelope_lt T c hmajor (x := y) (r := upperEnvelope T c y+ε/2) (by linarith)
  have H := envelope_le T c l hl hcomp (x+y) (a+b) (by simpa only [map_add] using add_le_add ha hb)
  rw [map_add] at H
  linarith

omit [IsOrderedAddMonoid E] in
include hl hcomp hmajor in
lemma envelope_smul (r : ℝ) (hr : 0 < r) (x : E) :
    upperEnvelope T c (r • x) = r * upperEnvelope T c x := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨a,ha,har⟩ := envelope_lt T c hmajor (x := x)
      (r := upperEnvelope T c x+ε/r) (lt_add_of_pos_right _ (div_pos hε hr))
    have H := envelope_le T c l hl hcomp (r • x) (r • a)
      (by simpa only [map_smul] using smul_le_smul_of_nonneg_left ha hr.le)
    rw [map_smul, smul_eq_mul] at H
    have H' := mul_lt_mul_of_pos_left har hr
    have heq : r*(upperEnvelope T c x+ε/r) = r*upperEnvelope T c x+ε := by field_simp
    rw [heq] at H'
    linarith
  · apply le_csInf (envelope_nonempty T c hmajor (r • x))
    rintro s ⟨a,ha,rfl⟩
    have hax : x ≤ T (r⁻¹ • a) := by
      have H := smul_le_smul_of_nonneg_left ha (inv_nonneg.mpr hr.le)
      simpa only [map_smul, smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using H
    have H := envelope_le T c l hl hcomp x (r⁻¹ • a) hax
    rw [map_smul, smul_eq_mul] at H
    have H' := mul_le_mul_of_nonneg_left H hr.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] using H'

include hl hcomp hmajor in

lemma exists_envelope_support (x : E) :
    ∃ g : E →ₗ[ℝ] ℝ, Monotone g ∧ (∀ a, g (T a) = c a) ∧
      g x = upperEnvelope T c x := by
  obtain ⟨g,hgx,hg⟩ := exists_sublinear_support (upperEnvelope T c)
    (envelope_smul T c l hl hcomp hmajor) (envelope_add T c l hl hcomp hmajor) x
  have hpos : ∀ y : E, 0 ≤ y → 0 ≤ g y := by
    intro y hy
    have H := hg (-y)
    have H' := envelope_mono T c l hl hcomp hmajor (neg_nonpos.mpr hy)
    rw [envelope_zero T c l hl hcomp hmajor] at H'
    rw [map_neg] at H
    linarith
  refine ⟨g, ?_, ?_, hgx⟩
  · intro y z hyz
    have H := hpos (z-y) (sub_nonneg.mpr hyz)
    rw [map_sub] at H
    linarith
  · intro a
    have H := hg (T a)
    have H' := hg (T (-a))
    rw [envelope_image T c l hl hcomp hmajor] at H H'
    rw [map_neg, map_neg, map_neg] at H'
    linarith

end WeakHessianTransport

open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology

end
end InlinedFile0

end OAI
