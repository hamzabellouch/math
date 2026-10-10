import Lean.Elab.Tactic.Omega
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.HyperplaneNormal

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

def normalMap (f : E →ₗ[K] K) (V : Submodule K E) : f.ker →ₗ[K] E ⧸ V :=
  V.mkQ.comp f.ker.subtype

theorem exists_kernel_decomposition (f : E →ₗ[K] K) {v : E} (hv : f v ≠ 0)
    (x : E) : ∃ w : E, w ∈ f.ker ∧ x = w + (f x / f v) • v := by
  refine ⟨x - (f x / f v) • v, ?_, ?_⟩
  · rw [LinearMap.mem_ker, map_sub, map_smul]
    change f x - (f x / f v) * f v = 0
    rw [div_mul_cancel₀ _ hv, sub_self]
  · simp

theorem ker_sup_eq_top (f : E →ₗ[K] K) (V : Submodule K E)
    (hV : ¬ V ≤ f.ker) : f.ker ⊔ V = ⊤ := by
  classical
  obtain ⟨v, hv, hfv⟩ : ∃ v, v ∈ V ∧ f v ≠ 0 := by
    by_contra h
    apply hV
    intro v hv
    rw [LinearMap.mem_ker]
    by_contra hfv
    exact h ⟨v, hv, hfv⟩
  apply top_unique
  intro x _
  obtain ⟨w, hw, hx⟩ := exists_kernel_decomposition f hfv x
  exact Submodule.mem_sup.mpr ⟨w, hw, (f x / f v) • v, V.smul_mem _ hv, hx.symm⟩

theorem normalMap_surjective (f : E →ₗ[K] K) (V : Submodule K E)
    (hV : ¬ V ≤ f.ker) : Function.Surjective (normalMap f V) := by
  rw [← LinearMap.range_eq_top]
  change LinearMap.range (V.mkQ.comp f.ker.subtype) = ⊤
  rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_mkQ_eq_top,
    sup_comm]
  exact ker_sup_eq_top f V hV

theorem normalMap_rank (f : E →ₗ[K] K) (V : Submodule K E)
    (hV : ¬ V ≤ f.ker) :
    Module.finrank K (LinearMap.range (normalMap f V)) = Module.finrank K (E ⧸ V) := by
  rw [LinearMap.range_eq_top.mpr (normalMap_surjective f V hV), finrank_top]

theorem normalMap_rank_eq_codimension [FiniteDimensional K E]
    (f : E →ₗ[K] K) (V : Submodule K E) (hV : ¬ V ≤ f.ker) :
    Module.finrank K (LinearMap.range (normalMap f V)) =
      Module.finrank K E - Module.finrank K V := by
  rw [normalMap_rank f V hV]
  have h := V.finrank_quotient_add_finrank
  omega

theorem kernel_finrank_three [FiniteDimensional K E] (hE : Module.finrank K E = 4)
    (f : E →ₗ[K] K) (hf : f ≠ 0) : Module.finrank K f.ker = 3 := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  omega

theorem point_normalMap_injective (f : E →ₗ[K] K) :
    Function.Injective (normalMap f (⊥ : Submodule K E)) := by
  rw [← LinearMap.ker_eq_bot]
  simp [normalMap, LinearMap.ker_comp]

theorem point_normalMap_rank_three [FiniteDimensional K E]
    (hE : Module.finrank K E = 4) (f : E →ₗ[K] K) (hf : f ≠ 0) :
    Module.finrank K (LinearMap.range (normalMap f (⊥ : Submodule K E))) = 3 := by
  rw [LinearMap.finrank_range_of_inj (point_normalMap_injective f)]
  exact kernel_finrank_three hE f hf

end WeightedTorusJets.HyperplaneNormal

end

section

namespace WeightedTorusJets.HyperplaneNormal

variable {K E Q : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup Q] [Module K Q]

theorem select_three_directions (v : Fin 3 → Q) :
    ∃ I : Set (Fin 3),
      LinearIndependent K (fun i : I => v i) ∧
      Submodule.span K (v '' I) = Submodule.span K (Set.range v) ∧
      Nat.card I = Module.finrank K (Submodule.span K (Set.range v)) := by
  classical
  obtain ⟨I, _, _, hspan, hli⟩ :=
    exists_linearIndepOn_extension (K := K) (v := v) (linearIndepOn_empty K v)
      (Set.empty_subset (Set.univ : Set (Fin 3)))
  have hspan' : Submodule.span K (v '' I) = Submodule.span K (Set.range v) := by
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨i, _, rfl⟩
      exact ⟨i, rfl⟩
    · apply Submodule.span_le.mpr
      simpa only [Set.image_univ] using hspan
  refine ⟨I, hli, hspan', ?_⟩
  have hcard := finrank_span_eq_card hli
  rw [← Set.image_eq_range, hspan'] at hcard
  simpa only [Nat.card_eq_fintype_card] using hcard.symm

theorem span_normal_basis (f : E →ₗ[K] K) (V : Submodule K E)
    (b : Module.Basis (Fin 3) K f.ker) :
    Submodule.span K (Set.range (fun i => normalMap f V (b i))) =
      LinearMap.range (normalMap f V) := by
  rw [show (fun i => normalMap f V (b i)) = normalMap f V ∘ b from rfl,
    Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top]

theorem select_normal_directions (f : E →ₗ[K] K) (V : Submodule K E)
    (b : Module.Basis (Fin 3) K f.ker) :
    ∃ I : Set (Fin 3),
      LinearIndependent K (fun i : I => normalMap f V (b i)) ∧
      Submodule.span K ((fun i => normalMap f V (b i)) '' I) =
        LinearMap.range (normalMap f V) ∧
      Nat.card I = Module.finrank K (LinearMap.range (normalMap f V)) := by
  obtain ⟨I, hli, hspan, hcard⟩ :=
    select_three_directions (K := K) (fun i => normalMap f V (b i))
  exact ⟨I, hli, hspan.trans (span_normal_basis f V b),
    hcard.trans (congrArg (fun P : Submodule K (E ⧸ V) => Module.finrank K P)
      (span_normal_basis f V b))⟩

theorem normal_rank_le_three (f : E →ₗ[K] K) (V : Submodule K E)
    (b : Module.Basis (Fin 3) K f.ker) :
    Module.finrank K (LinearMap.range (normalMap f V)) ≤ 3 := by
  classical
  obtain ⟨I, _, _, hcard⟩ := select_normal_directions f V b
  rw [← hcard]
  simpa only [Nat.card_fin] using
    Nat.card_le_card_of_injective (Subtype.val : I → Fin 3) Subtype.val_injective

theorem select_min_codimension_directions [FiniteDimensional K E]
    (hE : Module.finrank K E = 4) (f : E →ₗ[K] K) (hf : f ≠ 0)
    (V : Submodule K E) (b : Module.Basis (Fin 3) K f.ker)
    (hV : (¬ V ≤ f.ker) ∨ V = ⊥) :
    ∃ I : Set (Fin 3),
      LinearIndependent K (fun i : I => normalMap f V (b i)) ∧
      Submodule.span K ((fun i => normalMap f V (b i)) '' I) =
        LinearMap.range (normalMap f V) ∧
      Nat.card I = min (4 - Module.finrank K V) 3 := by
  obtain ⟨I, hli, hspan, hcard⟩ := select_normal_directions f V b
  refine ⟨I, hli, hspan, hcard.trans ?_⟩
  rcases hV with hV | rfl
  · have hrank := normalMap_rank_eq_codimension f V hV
    have hbound := normal_rank_le_three f V b
    rw [hE] at hrank
    omega
  · rw [point_normalMap_rank_three hE f hf]
    simp

end WeightedTorusJets.HyperplaneNormal

end

end SiegelZeros

end OAI
