import Mathlib.LinearAlgebra.Dual.Defs

namespace OAI

noncomputable section
namespace ArExplicit
universe u v w
variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V]
variable {W : Type w} [AddCommGroup W] [Module k W]

theorem scalarChart_eq_smul (e : V ≃ₗ[k] k) (x : V) : x = e x • e.symm 1 := by
  apply e.injective
  rw [map_smul, e.apply_symm_apply]
  exact (mul_one _).symm

theorem scalarDetector_injective (e : V ≃ₗ[k] k) (d : V →ₗ[k] W)
    (x : V) (hx : d x ≠ 0) : Function.Injective d := by
  have hg : d (e.symm 1) ≠ 0 := by
    intro hz
    apply hx
    rw [scalarChart_eq_smul e x, map_smul, hz, smul_zero]
  apply (injective_iff_map_eq_zero d).mpr
  intro z hz
  have hs : e z = 0 := by
    have h := hz
    rw [scalarChart_eq_smul e z, map_smul] at h
    by_contra he
    apply hg
    calc
      d (e.symm 1) = (e z)⁻¹ • (e z • d (e.symm 1)) := by
        rw [← mul_smul, inv_mul_cancel₀ he, one_smul]
      _ = 0 := by rw [h, smul_zero]
  exact e.injective (hs.trans (map_zero e).symm)

theorem scalarDetector_common (e : V ≃ₗ[k] k) (d : V →ₗ[k] W)
    (x y : V) (b : W) (hb : b ≠ 0) (hx : d x = b) (hy : d y = b) :
    x = y ∧ x ≠ 0 := by
  have hdx : d x ≠ 0 := hx ▸ hb
  refine ⟨scalarDetector_injective e d x hdx (hx.trans hy.symm), ?_⟩
  intro hz
  exact hdx (hz ▸ map_zero d)

end ArExplicit

end

end OAI
