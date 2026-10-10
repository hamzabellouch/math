import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommonEigenspaceCommutators
import Mathlib.GroupTheory.FiniteAbelian.Basic

namespace OAI

/-! # Torsion characters of common eigenspaces

A nonzero common eigenspace gives a genuine character into the units of the
field. If each operator has a unipotent positive power, this character has
finite image on a finitely generated group.
-/

noncomputable section
namespace PolycyclicRecognition

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

theorem commonEigenspace_units_character
    (ρ : G →* (V ≃ₗ[K] V)) (χ : G → K)
    (hχ : commonEigenspace (fun g => (ρ g).toLinearMap) χ ≠ ⊥) :
    ∃ ξ : G →* Kˣ, ∀ g, (ξ g : K) = χ g := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have he (g : G) : ρ g v = χ g • v := (mem_commonEigenspace _ _ _).mp hv g
  have hn (g : G) : χ g ≠ 0 := by
    intro hz
    have hzv : ρ g v = 0 := by rw [he, hz, zero_smul]
    exact hv0 ((ρ g).injective (hzv.trans (map_zero (ρ g)).symm))
  refine ⟨{ toFun := fun g => Units.mk0 (χ g) (hn g)
            map_one' := ?_
            map_mul' := ?_ }, fun _ => rfl⟩
  · apply Units.ext
    change χ 1 = 1
    apply smul_left_injective K hv0
    have hh := he 1
    rw [map_one] at hh
    change v = χ 1 • v at hh
    simpa only [one_smul] using hh.symm
  · intro g h
    apply Units.ext
    change χ (g * h) = χ g * χ h
    apply smul_left_injective K hv0
    calc
      χ (g * h) • v = ρ (g * h) v := (he _).symm
      _ = ρ g (ρ h v) := by rw [map_mul]; rfl
      _ = χ h • (χ g • v) := by rw [he h, map_smul, he g]
      _ = (χ g * χ h) • v := by rw [smul_smul, mul_comm]

theorem eigenvalue_torsion_of_unipotent_power (T : Module.End K V)
    (hT : ∃ m : ℕ, 0 < m ∧ IsNilpotent (T ^ m - 1))
    {z : K} (hz : T.HasEigenvalue z) : ∃ m : ℕ, 0 < m ∧ z ^ m = 1 := by
  obtain ⟨m, hm, hnil⟩ := hT
  obtain ⟨v, hv, hv0⟩ := hz.exists_hasEigenvector
  have hpow := (show T.HasEigenvector z v from ⟨hv, hv0⟩).pow_apply m
  have he : (T ^ m - 1).HasEigenvector (z ^ m - 1) v := by
    refine ⟨?_, hv0⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change (T ^ m) v - v = (z ^ m - 1) • v
    rw [hpow, sub_smul, one_smul]
  have hn := (Module.End.hasEigenvalue_of_hasEigenvector he).isNilpotent_of_isNilpotent hnil
  exact ⟨m, hm, sub_eq_zero.mp (isNilpotent_iff_eq_zero.mp hn)⟩

theorem commonEigenspace_finite_character [Group.FG G]
    (ρ : G →* (V ≃ₗ[K] V)) (χ : G → K)
    (hχ : commonEigenspace (fun g => (ρ g).toLinearMap) χ ≠ ⊥)
    (hρ : ∀ g, ∃ m : ℕ, 0 < m ∧ IsNilpotent ((ρ g).toLinearMap ^ m - 1)) :
    ∃ ξ : G →* Kˣ, (∀ g, (ξ g : K) = χ g) ∧ Finite ξ.range := by
  obtain ⟨ξ, hξ⟩ := commonEigenspace_units_character ρ χ hχ
  refine ⟨ξ, hξ, CommGroup.finite_of_fg_isMulTorsion ξ.range ?_⟩
  intro a
  obtain ⟨g, hg⟩ := a.property
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have hz : Module.End.HasEigenvalue (ρ g).toLinearMap (χ g) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨(Module.End.mem_eigenspace_iff).mpr ((mem_commonEigenspace _ _ _).mp hv g), hv0⟩
  obtain ⟨m, hm, he⟩ := eigenvalue_torsion_of_unipotent_power _ (hρ g) hz
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨m, hm, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change (a.val : K) ^ m = 1
  rw [← hg, hξ, he]

end PolycyclicRecognition

end

end OAI
