import OAI.Analysis.ForestSpace.Distortion

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section Exhaustions
variable {V : Type} [PartialOrder V]

/-- Every increasing ancestral exhaustion converges by coordinate density
and tail contractivity, without reflexivity. -/
theorem ancestral_exhaustion_tendsto (H : ℕ → Finset V)
    (hH : ∀ n, IsLowerSet (H n : Set V)) (hmono : Monotone H)
    (hcover : ∀ v : V, ∃ n, v ∈ H n) (x : X V) :
    Filter.Tendsto (fun n => PX (H n) (hH n) x) Filter.atTop (nhds x) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hx : (x : FullDual V) ∈ closure
      (Submodule.span ℝ (Set.range (eStar (V := V))) : Set (FullDual V)) := x.property
  obtain ⟨z,hz,hclose⟩ := Metric.mem_closure_iff.mp hx ε hε
  obtain ⟨S,hS⟩ := finite_span_support hz
  let n : V → ℕ := fun v => (hcover v).choose
  refine ⟨S.sup n,?_⟩
  intro m hm
  have hSm : S ⊆ H m := by
    intro v hv
    have hvm : n v ≤ m := (Finset.le_sup hv).trans hm
    exact hmono hvm (hcover v).choose_spec
  have hzP := hS (H m) (hH m) hSm
  have hzQ : Q (H m : Set V) (hH m) z = 0 := by rw [Q_eq_sub,hzP,sub_self]
  have hh := norm_Q_le (H m : Set V) (hH m) ((x : FullDual V)-z)
  rw [map_sub,hzQ,sub_zero,Q_eq_sub] at hh
  have he : ‖(x : FullDual V)-P (H m : Set V) (hH m) x‖ < ε :=
    hh.trans_lt (by simpa only [dist_eq_norm] using hclose)
  rw [dist_eq_norm]
  change ‖((PX (H m) (hH m) x : FullDual V)-(x : FullDual V))‖ < ε
  rw [PX_val,norm_sub_rev]
  exact he

/-- Completed tails are approximated by finite coordinate combinations outside
the ancestral head. -/
theorem approximate_tail_outside (H : Finset V) (hH : IsLowerSet (H : Set V))
    (y : X V) (hy : y = QX H hH y) (ε : ℝ) (hε : 0 < ε) :
    ∃ z : FullDual V, z ∈ Submodule.span ℝ (eStar '' (H : Set V)ᶜ) ∧
      ‖(y : FullDual V)-z‖ < ε := by
  have hycl : (y : FullDual V) ∈ closure
      (Submodule.span ℝ (Set.range (eStar (V := V))) : Set (FullDual V)) := y.property
  obtain ⟨z,hz,hclose⟩ := Metric.mem_closure_iff.mp hycl ε hε
  refine ⟨Q (H : Set V) hH z,?_,?_⟩
  · obtain ⟨c,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hz
    change Q (H : Set V) hH (∑ v ∈ c.support, c v • eStar v) ∈ _
    rw [map_sum]
    apply Submodule.sum_mem
    intro v hv
    rw [map_smul,Q_eq_sub,P_eStar]
    by_cases hvH : v ∈ (H : Set V)
    · simp [hvH]
    · rw [ite_eq_right hvH,sub_zero]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v,hvH,rfl⟩)
  · have hy' : Q (H : Set V) hH (y : FullDual V) = y := by
      have he := congrArg Subtype.val hy
      simpa only [QX_val] using he.symm
    have hh := norm_Q_le (H : Set V) hH ((y : FullDual V)-z)
    rw [map_sub,hy'] at hh
    exact hh.trans_lt (by simpa only [dist_eq_norm] using hclose)

end Exhaustions

end

end ForestSpace

end OAI
