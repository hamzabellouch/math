import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace

namespace WeakPureInfiniteness

abbrev GroupHilbert (G : Type*) : Type _ := lp (fun _ : G => ℂ) 2

variable {G K : Type*}

lemma mem_l2_reindex (e : G ≃ K) (ξ : GroupHilbert K) :
    Memℓp (fun g => ξ (e g)) 2 := by
  apply (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mpr
  have hs : Summable (fun k => ‖ξ k‖ ^ (2 : ℝ≥0∞).toReal) :=
    Memℓp.summable (by norm_num) ξ.property
  exact e.summable_iff.mpr hs

def l2Reindex (e : G ≃ K) : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert K where
  toFun ξ := ⟨fun k => ξ (e.symm k), mem_l2_reindex e.symm ξ⟩
  invFun ξ := ⟨fun g => ξ (e g), mem_l2_reindex e ξ⟩
  left_inv ξ := by ext g; simp
  right_inv ξ := by ext k; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' ξ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
    congr 1
    exact e.symm.tsum_eq (fun g => ‖ξ g‖ ^ (2 : ℝ≥0∞).toReal)

@[simp]
lemma l2Reindex_apply (e : G ≃ K) (ξ : GroupHilbert G) (k : K) :
    l2Reindex e ξ k = ξ (e.symm k) := rfl

lemma l2Reindex_single [DecidableEq G] [DecidableEq K] (e : G ≃ K) (g : G) (c : ℂ) :
    l2Reindex e (lp.single 2 g c) = lp.single 2 (e g) c := by
  classical
  ext k
  simp only [l2Reindex_apply, lp.single_apply, Pi.single_apply]
  have he : e.symm k = g ↔ k = e g := e.symm_apply_eq
  simp only [he]

variable [Group G]

def leftRegularIsometry : G →* (GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert G) where
  toFun s := l2Reindex (Equiv.mulLeft s)
  map_one' := by
    ext ξ g
    change ξ ((1 : G)⁻¹ * g) = ξ g
    simp
  map_mul' s t := by
    ext ξ g
    change ξ ((s * t)⁻¹ * g) = ξ (t⁻¹ * (s⁻¹ * g))
    simp [mul_assoc]

def rightRegularIsometry : G →* (GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert G) where
  toFun s := l2Reindex (Equiv.mulRight s⁻¹)
  map_one' := by
    ext ξ g
    change ξ (g * ((1 : G)⁻¹)⁻¹) = ξ g
    simp
  map_mul' s t := by
    ext ξ g
    change ξ (g * ((s * t)⁻¹)⁻¹) = ξ ((g * (s⁻¹)⁻¹) * (t⁻¹)⁻¹)
    simp [mul_assoc]

def leftRegular : G →* unitary (GroupHilbert G →L[ℂ] GroupHilbert G) :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp leftRegularIsometry

def rightRegular : G →* unitary (GroupHilbert G →L[ℂ] GroupHilbert G) :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp rightRegularIsometry

@[simp]
lemma leftRegular_apply (s g : G) (ξ : GroupHilbert G) :
    (leftRegular s : GroupHilbert G →L[ℂ] GroupHilbert G) ξ g = ξ (s⁻¹ * g) := rfl

@[simp]
lemma rightRegular_apply (s g : G) (ξ : GroupHilbert G) :
    (rightRegular s : GroupHilbert G →L[ℂ] GroupHilbert G) ξ g = ξ (g * s) := by
  change ξ (g * (s⁻¹)⁻¹) = _
  rw [inv_inv]

lemma leftRegular_single [DecidableEq G] (s g : G) (c : ℂ) :
    (leftRegular s : GroupHilbert G →L[ℂ] GroupHilbert G) (lp.single 2 g c) =
      lp.single 2 (s * g) c := l2Reindex_single (Equiv.mulLeft s) g c

lemma rightRegular_single [DecidableEq G] (s g : G) (c : ℂ) :
    (rightRegular s : GroupHilbert G →L[ℂ] GroupHilbert G) (lp.single 2 g c) =
      lp.single 2 (g * s⁻¹) c := l2Reindex_single (Equiv.mulRight s⁻¹) g c

lemma leftRegular_commute_right (s t : G) :
    Commute (leftRegular s : GroupHilbert G →L[ℂ] GroupHilbert G)
      (rightRegular t : GroupHilbert G →L[ℂ] GroupHilbert G) := by
  ext ξ g
  simp [mul_assoc]

def groupInversion : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert G := l2Reindex (Equiv.inv G)

lemma groupInversion_intertwines (s : G) (ξ : GroupHilbert G) :
    groupInversion ((leftRegular s : GroupHilbert G →L[ℂ] GroupHilbert G) ξ) =
      (rightRegular s : GroupHilbert G →L[ℂ] GroupHilbert G) (groupInversion ξ) := by
  ext g
  simp [groupInversion]

lemma inner_leftRight_regular_base [DecidableEq G] (s t : G) :
    inner ℂ (lp.single (E := fun _ : G => ℂ) 2 1 1)
      (((leftRegular s : GroupHilbert G →L[ℂ] GroupHilbert G) * rightRegular t)
        (lp.single 2 1 1)) = if s = t then 1 else 0 := by
  classical
  rw [mul_apply_eq_comp, rightRegular_single, leftRegular_single]
  simp only [one_mul, lp.inner_single_left, RCLike.inner_apply,
    map_one, one_mul, lp.single_apply]
  simp [Pi.single_apply, eq_comm, mul_inv_eq_one]

end WeakPureInfiniteness
end

end OAI
