import OAI.Analysis.KadisonKastler.BoundaryBoundedTransport
import OAI.Analysis.KadisonKastler.Intertwiner
import OAI.Analysis.KadisonKastler.SpectralClipping
import Mathlib.Algebra.Star.UnitaryStarAlgAut

namespace OAI

/-! # Averaging and polar normalization of a boundary intertwiner

A supplied equivariant bimodule mean gives a near-identity semilinear
intertwiner. Continuous functional calculus passes its transformation law
to the unitary polar factor.
-/

namespace KadisonKastler

open scoped CStarAlgebra BoundedContinuousFunction

noncomputable section

variable {B : Type*} [CStarAlgebra B]
local instance boundaryIntertwinerOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance boundaryIntertwinerStarOrder : StarOrderedRing B :=
  CStarAlgebra.spectralOrderedRing B

/-- Left multiplication by a unitary does not change the absolute value. -/
theorem abs_unitary_mul (u : unitary B) (b : B) :
    CFC.abs ((u : B) * b) = CFC.abs b := by
  unfold CFC.abs
  congr 1
  rw [star_mul]
  calc
    star b * star (u : B) * ((u : B) * b) =
        star b * (star (u : B) * (u : B)) * b := by noncomm_ring
    _ = star b * b := by
      rw [Unitary.star_mul_self_of_mem u.property, mul_one]

/-- Right multiplication by a unitary conjugates the absolute value. -/
theorem abs_mul_unitary (b : B) (u : unitary B) :
    CFC.abs (b * (u : B)) = star (u : B) * CFC.abs b * (u : B) := by
  have hm := starAlgHom_map_abs
    (Unitary.conjStarAlgAut ℂ B (star u)).toStarAlgHom b
  have hr : CFC.abs (star (u : B) * b * (u : B)) = CFC.abs (b * (u : B)) := by
    rw [mul_assoc]
    exact abs_unitary_mul (star u) (b * (u : B))
  simpa only [StarAlgEquiv.toStarAlgHom_apply, Unitary.conjStarAlgAut_star_apply, hr]
    using hm.symm

/-- The absolute value satisfies the semilinear covariance forced by an
invertible intertwiner of unitaries. -/
theorem abs_semilinear_intertwines (a : B ≃⋆ₐ[ℂ] B) (b : B)
    (u v : unitary B) (hb : b * (u : B) = (v : B) * a b) :
    CFC.abs b * (u : B) = (u : B) * a (CFC.abs b) := by
  have hconj : star (u : B) * CFC.abs b * (u : B) = a (CFC.abs b) := by
    calc
      _ = CFC.abs (b * (u : B)) := (abs_mul_unitary b u).symm
      _ = CFC.abs ((v : B) * a b) := congrArg CFC.abs hb
      _ = CFC.abs (a b) := abs_unitary_mul v (a b)
      _ = a (CFC.abs b) := (starAlgHom_map_abs a.toStarAlgHom b).symm
  calc
    CFC.abs b * (u : B) =
        (u : B) * (star (u : B) * CFC.abs b * (u : B)) := by
      simp only [← mul_assoc, Unitary.mul_star_self_of_mem u.property, one_mul]
    _ = (u : B) * a (CFC.abs b) := by rw [hconj]

/-- An invertible semilinear intertwiner passes its law to its polar unitary. -/
theorem polar_unitary_semilinear_intertwines (a : B ≃⋆ₐ[ℂ] B) (b : B)
    (hunit : IsUnit b) (u v L : unitary B)
    (hb : b * (u : B) = (v : B) * a b)
    (hL : (L : B) * CFC.abs b = b) :
    (L : B) * (u : B) = (v : B) * a (L : B) := by
  have ha : IsUnit (CFC.abs b) := by
    obtain ⟨t, rfl⟩ := hunit
    exact isUnit_abs t
  have haa : IsUnit (a (CFC.abs b)) := ha.map a.toMonoidHom
  apply haa.mul_right_cancel
  calc
    ((L : B) * (u : B)) * a (CFC.abs b) =
        (L : B) * ((u : B) * a (CFC.abs b)) := mul_assoc _ _ _
    _ = (L : B) * (CFC.abs b * (u : B)) := by
      rw [abs_semilinear_intertwines a b u v hb]
    _ = b * (u : B) := by rw [← mul_assoc, hL]
    _ = (v : B) * a b := hb
    _ = ((v : B) * a (L : B)) * a (CFC.abs b) := by rw [mul_assoc, ← map_mul, hL]

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
local instance boundaryIntertwinerFunctionCStar : CStarAlgebra (G →ᵇ B) where

/-- Averaging the genuine field `S_t U_t*` produces the semilinear intertwiner. -/
theorem averaged_boundary_intertwiner
    (α : G →* (B ≃⋆ₐ[ℂ] B))
    (m : BimoduleMean (boundaryConstant (G := G) (B := B)))
    (hm : ∀ g f, m.toCLM (boundaryTranslate α g f) = α g (m.toCLM f))
    (S : unitary (G →ᵇ B))
    (hS : ∀ g h, S.val g * α g (S.val h) = S.val (g * h))
    (U : G →* unitary B) (hU : ∀ g t, α g (U t : B) = (U t : B))
    {δ : ℝ} (hclose : ∀ g, ‖S.val g - (U g : B)‖ ≤ δ) :
    ∃ b : B, ‖b - 1‖ ≤ δ ∧
      ∀ g, b * (U g : B) = S.val g * α g b := by
  let H : unitary (G →ᵇ B) := S * star (boundedUnitaryFamily U)
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hclose 1)
  have hH : ‖(H : G →ᵇ B) - 1‖ ≤ δ := by
    apply (BoundedContinuousFunction.norm_le hδ).mpr
    intro t
    have heq : S.val t * star (U t : B) - 1 =
        (S.val t - (U t : B)) * star (U t : B) := by
      rw [sub_mul, Unitary.mul_star_self_of_mem (U t).property]
    change ‖S.val t * star (U t : B) - 1‖ ≤ δ
    rw [heq]
    simpa only [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary] using hclose t
  have hfield (g : G) :
      boundaryConstant (G := G) (S.val g) * boundaryTranslate α g (H : G →ᵇ B) =
        (H : G →ᵇ B) * boundaryConstant (G := G) (U g : B) := by
    ext t
    have hUg : star (U (g⁻¹ * t)) = star (U t) * U g := by
      simp only [map_mul, map_inv, Unitary.star_eq_inv, mul_inv_rev, inv_inv]
    have hUgB : star (U (g⁻¹ * t) : B) = star (U t : B) * (U g : B) := by
      simpa only [Unitary.coe_star, Submonoid.coe_mul] using
        congrArg (fun w : unitary B => (w : B)) hUg
    have hc : S.val g * α g (S.val (g⁻¹ * t)) = S.val t := by
      simpa only [mul_inv_cancel_left] using hS g (g⁻¹ * t)
    change S.val g * α g (S.val (g⁻¹ * t) * star (U (g⁻¹ * t) : B)) =
      (S.val t * star (U t : B)) * (U g : B)
    rw [map_mul, map_star, hU, ← mul_assoc, hc, hUgB, mul_assoc]
  refine ⟨m.toCLM (H : G →ᵇ B), ?_, ?_⟩
  · apply m.norm_sub_le (H : G →ᵇ B) 1
    simpa only [map_one] using hH
  · intro g
    have he := congrArg m.toCLM (hfield g)
    rw [m.map_left, m.map_right, hm] at he
    exact he.symm

/-- The averaged boundary intertwiner has a near-identity unitary polar
factor satisfying the same semilinear intertwining equation. -/
theorem exists_unitary_boundary_intertwiner
    (α : G →* (B ≃⋆ₐ[ℂ] B))
    (m : BimoduleMean (boundaryConstant (G := G) (B := B)))
    (hm : ∀ g f, m.toCLM (boundaryTranslate α g f) = α g (m.toCLM f))
    (S : unitary (G →ᵇ B))
    (hS : ∀ g h, S.val g * α g (S.val h) = S.val (g * h))
    (U : G →* unitary B) (hU : ∀ g t, α g (U t : B) = (U t : B))
    {δ : ℝ} (hδ : δ < 1) (hclose : ∀ g, ‖S.val g - (U g : B)‖ ≤ δ) :
    ∃ L : unitary B, (∀ g, (L : B) * (U g : B) = S.val g * α g (L : B)) ∧
      ‖(L : B) - 1‖ ≤ 2 * δ := by
  obtain ⟨b, hb, hbi⟩ := averaged_boundary_intertwiner α m hm S hS U hU hclose
  have hnear : ‖b - 1‖ < 1 := hb.trans_lt hδ
  have hunit : IsUnit b := by
    nontriviality B
    exact (Units.ofNearby 1 b (by simpa using hnear)).isUnit
  obtain ⟨L, hL, hLn⟩ := exists_polar_unitary_near_one b hnear
  refine ⟨L, ?_, hLn.trans (mul_le_mul_of_nonneg_left hb (by norm_num))⟩
  intro g
  exact polar_unitary_semilinear_intertwines (α g) b hunit (U g)
    (unitaryFamilyEval S g) L (hbi g) hL

end

end KadisonKastler

end OAI
