import Mathlib
import OAI.Geometry.SmoothYau.Limits.CoordinateForm

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance hmoDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance hmoDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance hmoFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance hmoFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance
local instance hmoDerivNorm : NormedAddCommGroup (E →L[ℝ] CoordinateForm E) := inferInstance
local instance hmoDerivSpace : NormedSpace ℝ (E →L[ℝ] CoordinateForm E) := inferInstance

def positiveFormOn (P : Submodule ℝ E) (T : CoordinateForm E) : Prop :=
  ∀ v ∈ P, v ≠ 0 → 0 < T v v

omit [FiniteDimensional ℝ E] in
lemma positiveFormOn_iff_unit (P : Submodule ℝ E) (T : CoordinateForm E) :
    positiveFormOn P T ↔ ∀ v ∈ P, ‖v‖ = 1 → 0 < T v v := by
  constructor
  · intro h v hv hn
    exact h v hv (norm_ne_zero_iff.mp (by rw [hn]; norm_num))
  · intro h v hv hv0
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    let w := ‖v‖⁻¹ • v
    have hw : ‖w‖ = 1 := by simp [w, norm_smul, hn]
    have hp := h w (P.smul_mem _ hv) hw
    have he : ‖v‖ • w = v := by simp [w, smul_smul, hn]
    have heq : T v v = ‖v‖^2 * T w w := by
      conv_lhs => rw [← he]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact mul_pos (sq_pos_of_ne_zero hn) hp

theorem isOpen_positiveFormOn (P : Submodule ℝ E) :
    IsOpen {T : CoordinateForm E | positiveFormOn P T} := by
  let S : Set E := {v | v ∈ P ∧ ‖v‖ = 1}
  have hS : IsCompact S := by
    have he : S = (P : Set E) ∩ sphere (0 : E) 1 := by
      ext v
      simp only [S, mem_ofPred_eq, mem_inter_iff, mem_sphere_zero_iff_norm]
      rfl
    rw [he]
    exact (isCompact_sphere 0 1).inter_left P.closed_of_finiteDimensional
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let B : Set (CoordinateForm E × S) := {p | p.1 p.2 p.2 ≤ 0}
  have hT : Continuous (fun p : CoordinateForm E × S => p.1) := continuous_fst
  have hv : Continuous (fun p : CoordinateForm E × S => (p.2 : E)) :=
    continuous_subtype_val.comp continuous_snd
  have hB : IsClosed B := isClosed_le ((hT.clm_apply hv).clm_apply hv) continuous_const
  have hC : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace _ hB
  convert hC.isOpen_compl using 1
  ext T
  rw [mem_ofPred_eq, positiveFormOn_iff_unit]
  simp only [mem_compl_iff, mem_image, B, mem_ofPred_eq]
  constructor
  · intro h
    rintro ⟨q,hq,hqT⟩
    subst T
    exact (not_le_of_gt (h q.2 q.2.property.1 q.2.property.2)) hq
  · intro h v hv hn
    by_contra hh
    apply h
    exact ⟨(T,⟨v,hv,hn⟩),not_lt.mp hh,rfl⟩

def hessianMargins (B H : CoordinateForm E) : Prop :=
  positiveFormOn ⊤ ((1/2 : ℝ) • B + H) ∧
  ∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧ positiveFormOn P (H-B)

theorem isOpen_hessianMargins :
    IsOpen {p : CoordinateForm E × CoordinateForm E | hessianMargins p.1 p.2} := by
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨h₁,P,hP,h₂⟩
  have hb : Continuous (fun p : CoordinateForm E × CoordinateForm E => p.1) := continuous_fst
  have hh : Continuous (fun p : CoordinateForm E × CoordinateForm E => p.2) := continuous_snd
  have hc₁ : Continuous (fun p : CoordinateForm E × CoordinateForm E => (1/2 : ℝ) • p.1+p.2) :=
    (hb.const_smul (1/2 : ℝ)).add hh
  have hc₂ : Continuous (fun p : CoordinateForm E × CoordinateForm E => p.2-p.1) :=
    continuous_snd.sub continuous_fst
  have h₁' := ((isOpen_positiveFormOn (⊤ : Submodule ℝ E)).preimage hc₁).mem_nhds h₁
  have h₂' := ((isOpen_positiveFormOn P).preimage hc₂).mem_nhds h₂
  filter_upwards [h₁',h₂'] with q hq₁ hq₂
  exact ⟨hq₁,P,hP,hq₂⟩

omit [FiniteDimensional ℝ E] in
lemma hessianMargins_of_strong (B H : CoordinateForm E)
    (hB : ∀ v, v ≠ 0 → 0 < B v v)
    (h₁ : ∀ v, -(1/4 : ℝ)*B v v ≤ H v v)
    (h₂ : ∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, (3/2 : ℝ)*B v v ≤ H v v) : hessianMargins B H := by
  refine ⟨?_,?_⟩
  · intro v _ hv
    change 0 < (1/2 : ℝ)*B v v+H v v
    nlinarith [h₁ v,hB v hv]
  · obtain ⟨P,hP,hp⟩ := h₂
    refine ⟨P,hP,?_⟩
    intro v hv hv0
    change 0 < H v v-B v v
    nlinarith [hp v hv,hB v hv0]

omit [FiniteDimensional ℝ E] in
lemma hessianMargins_lower {B H : CoordinateForm E} (h : hessianMargins B H) :
    ∀ v, -(1/2 : ℝ)*B v v ≤ H v v := by
  intro v
  by_cases hv : v = 0
  · simp [hv]
  · have hh := h.1 v (by trivial) hv
    change 0 < (1/2 : ℝ)*B v v+H v v at hh
    linarith

omit [FiniteDimensional ℝ E] in
lemma hessianMargins_plane {B H : CoordinateForm E} (h : hessianMargins B H) :
    ∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧ ∀ v ∈ P, B v v ≤ H v v := by
  obtain ⟨P,hP,hp⟩ := h.2
  refine ⟨P,hP,?_⟩
  intro v hv
  by_cases hv0 : v = 0
  · simp [hv0]
  · have hh := hp v hv hv0
    change 0 < H v v-B v v at hh
    linarith

end YauCounterexamples

end

end OAI
