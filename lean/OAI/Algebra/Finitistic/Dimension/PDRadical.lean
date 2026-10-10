import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.SimpleModule.Basic

namespace OAI
noncomputable section
namespace LittleFinitistic.PDRadical
open Module LinearMap Submodule
universe u v
variable {A : Type u} [Ring A]
variable (P : Type v) [AddCommGroup P] [Module A P]

/-- For a finitely generated projective module the module radical is exactly
multiplication by the ring Jacobson radical. No commutativity is assumed. -/
theorem jacobson_eq_smul [Module.Finite A P] [Module.Projective A P] :
    Module.jacobson A P = Ring.jacobson A • (⊤ : Submodule A P) := by
  apply le_antisymm _ (Ring.jacobson_smul_top_le A P)
  intro x hx
  obtain ⟨n, f, g, hf, hg, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  have hcoord (i : Fin n) : g x i ∈ Ring.jacobson A :=
    Module.le_comap_jacobson ((LinearMap.proj i).comp g) hx
  have hsum : g x = ∑ i : Fin n, Pi.single i (g x i) := by
    classical
    ext j
    simp
  have hxsum : x = ∑ i : Fin n, (g x i) • f (Pi.single i 1) := by
    classical
    calc
      x = f (g x) := (DFunLike.congr_fun hfg x).symm
      _ = ∑ i : Fin n, f (Pi.single i (g x i)) := by conv_lhs => rw [hsum, map_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        have he : Pi.single i (g x i) = (g x i) • (Pi.single i 1 : Fin n → A) := by
          ext j
          by_cases hj : i = j
          · subst j; simp
          · simp [Ne.symm hj]
        rw [he, map_smul]
  rw [hxsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hcoord i) mem_top

/-- The noncommutative Nakayama step used in the manuscript. -/
theorem quotient_radical_nontrivial [Module.Finite A P] [Nontrivial P] :
    Nontrivial (P ⧸ (Ring.jacobson A • (⊤ : Submodule A P))) := by
  apply Submodule.Quotient.nontrivial_iff.mpr
  exact ne_of_lt (Submodule.jacobson_smul_lt_top (R := A) (M := P) ⊤)

/-- Any map into a simple module annihilates the radical of its domain. -/
theorem simple_map_radical_zero
    {S : Type v} [AddCommGroup S] [Module A S] [IsSimpleModule A S]
    (f : P →ₗ[A] S) (x : P) (hx : x ∈ Module.jacobson A P) : f x = 0 := by
  have h := Module.le_comap_jacobson f hx
  have hs : Module.jacobson A S = ⊥ := by
    apply bot_unique
    exact sInf_le isCoatom_bot
  simpa [hs] using h
end LittleFinitistic.PDRadical

end

end OAI
