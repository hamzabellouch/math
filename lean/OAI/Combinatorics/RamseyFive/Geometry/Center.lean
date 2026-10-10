import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.ProjectiveReduction
open Module Submodule
open scoped BigOperators

variable {K V : Type*} [Field K] [Infinite K] [AddCommGroup V] [Module K V]

theorem exists_center {ι : Type*} [Finite ι] (W : ι → Submodule K V)
    (hW : ∀ i, W i ≠ ⊤) : ∃ v : V, ∀ i, v ∉ W i :=
  Submodule.exists_forall_notMem_of_forall_ne_top W hW

omit [Infinite K] in

theorem quotient_injOn {W : Submodule K V} {v : V} (hv : v ∉ W) :
    Set.InjOn (Submodule.mkQ (K ∙ v)) W := by
  intro x hx y hy hxy
  have hmem : x - y ∈ K ∙ v := by
    exact (Submodule.Quotient.eq (K ∙ v)).mp hxy
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  have haw : a • v ∈ W := ha ▸ W.sub_mem hx hy
  have ha0 : a = 0 := by
    by_contra ha0
    exact hv ((W.smul_mem_iff ha0).mp haw)
  simpa [ha0, eq_comm, sub_eq_zero] using ha

theorem exists_projection [FiniteDimensional K V] {ι : Type*} [Finite ι]
    [Nonempty ι] (n : ℕ) (hdim : finrank K V = n + 1)
    (W : ι → Submodule K V) (hW : ∀ i, W i ≠ ⊤) :
    ∃ f : V →ₗ[K] (Fin n → K), Function.Surjective f ∧
      ∀ i, Set.InjOn f (W i) := by
  classical
  obtain ⟨v, hv⟩ := exists_center W hW
  have hv0 : v ≠ 0 := by
    intro he
    exact hv (Classical.arbitrary ι) (he ▸ (W _).zero_mem)
  have hr : finrank K (V ⧸ (K ∙ v)) = n := by
    have he := Submodule.finrank_quotient_add_finrank (K ∙ v)
    rw [finrank_span_singleton hv0, hdim] at he
    omega
  let e : (V ⧸ (K ∙ v)) ≃ₗ[K] (Fin n → K) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hr)
  refine ⟨e.toLinearMap.comp (Submodule.mkQ (K ∙ v)), ?_, ?_⟩
  · exact e.surjective.comp (Submodule.mkQ_surjective _)
  · intro i x hx y hy hxy
    exact quotient_injOn (hv i) hx hy (e.injective hxy)

theorem exists_projection_preserving_spans [FiniteDimensional K V]
    (n : ℕ) (hdim : finrank K V = n + 1) (X : Finset V) :
    ∃ f : V →ₗ[K] (Fin n → K), Function.Surjective f ∧
      ∀ Y : Finset V, Y ⊆ X → Submodule.span K (Y : Set V) ≠ ⊤ →
        Set.InjOn f (Submodule.span K (Y : Set V)) := by
  classical
  let I := {Y : Finset V // Y ∈ X.powerset}
  let : Nonempty I := ⟨⟨∅, by simp⟩⟩
  have hb : (⊥ : Submodule K V) ≠ ⊤ := by
    intro he
    have hr := congrArg (fun W : Submodule K V => finrank K W) he
    simp [hdim] at hr
  let W : I → Submodule K V := fun Y =>
    if Submodule.span K (Y.val : Set V) = ⊤ then ⊥ else
      Submodule.span K (Y.val : Set V)
  have hW : ∀ i, W i ≠ ⊤ := by
    intro i
    dsimp [W]
    split_ifs with hi
    · exact hb
    · exact hi
  obtain ⟨f, hf, hfi⟩ := exists_projection n hdim W hW
  refine ⟨f, hf, ?_⟩
  intro Y hY hY'
  have H := hfi ⟨Y, Finset.mem_powerset.mpr hY⟩
  simpa [W, hY'] using H

omit [Infinite K] in

theorem finrank_map_of_injOn {U : Type*} [AddCommGroup U] [Module K U]
    (f : V →ₗ[K] U) (W : Submodule K V) (hf : Set.InjOn f W) :
    finrank K (W.map f) = finrank K W := by
  have hi : Function.Injective (f.comp W.subtype) := by
    intro x y hxy
    exact Subtype.ext (hf x.property y.property hxy)
  have hr := LinearMap.finrank_range_of_inj hi
  have he : (f.comp W.subtype).range = W.map f := by
    ext y
    simp [LinearMap.mem_range, Submodule.mem_map]
  rwa [he] at hr

end SharpRamseyFive.ProjectiveReduction

end OAI
