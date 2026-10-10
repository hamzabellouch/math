import OAI.Analysis.Cotype.WalshExactPairing
import Mathlib.Algebra.Group.Subgroup.Basic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype

def walshSymmetryGroup (n : ℕ) : Subgroup (Equiv.Perm (Cube n) × Equiv.Perm (Cube n)) where
  carrier := {g | ∀ u v, character (g.2 v) (g.1 u) = character v u}
  one_mem' := by intro u v; rfl
  mul_mem' := by
    intro g h hg hh u v
    change character (g.2 (h.2 v)) (g.1 (h.1 u)) = _
    rw [hg, hh]
  inv_mem' := by
    intro g hg u v
    have h := hg (g.1⁻¹ u) (g.2⁻¹ v)
    simpa using h.symm

abbrev WalshSymmetry (n : ℕ) : Type := walshSymmetryGroup n
instance (n : ℕ) : Fintype (WalshSymmetry n) := Fintype.ofFinite _
instance (n : ℕ) : DecidableEq (WalshSymmetry n) := Classical.decEq _

def primalSymmetry {n : ℕ} (g : WalshSymmetry n) : Equiv.Perm (Cube n) := g.val.1
def dualSymmetry {n : ℕ} (g : WalshSymmetry n) : Equiv.Perm (Cube n) := g.val.2

theorem symmetry_pairing {n : ℕ} (g : WalshSymmetry n) (u v : Cube n) :
    character (dualSymmetry g v) (primalSymmetry g u) = character v u := g.property u v

theorem character_separates {n : ℕ} {u v : Cube n}
    (h : ∀ a, character a u = character a v) : u = v := by
  funext i
  have he := h (unitIndex i)
  rw [character_unitIndex, character_unitIndex] at he
  cases hu : u i <;> cases hv : v i <;> simp_all [sign] <;> norm_num at he

theorem primalSymmetry_xor {n : ℕ} (g : WalshSymmetry n) (u v : Cube n) :
    primalSymmetry g (xorCube u v) = xorCube (primalSymmetry g u) (primalSymmetry g v) := by
  apply character_separates
  intro a
  obtain ⟨b,rfl⟩ := (dualSymmetry g).surjective a
  rw [symmetry_pairing, character_xor, character_xor, symmetry_pairing, symmetry_pairing]

theorem dualSymmetry_xor {n : ℕ} (g : WalshSymmetry n) (u v : Cube n) :
    dualSymmetry g (xorCube u v) = xorCube (dualSymmetry g u) (dualSymmetry g v) := by
  apply character_separates
  intro a
  obtain ⟨b,rfl⟩ := (primalSymmetry g).surjective a
  rw [character_symm, symmetry_pairing, character_xor_left]
  rw [character_xor, character_symm (primalSymmetry g b) (dualSymmetry g u),
    character_symm (primalSymmetry g b) (dualSymmetry g v), symmetry_pairing, symmetry_pairing]

variable {Γ Ω X : Type*} [Fintype Ω] [NormedAddCommGroup X] [NormedSpace ℝ X]
open WithLp

def l2Reindex (e : Ω ≃ Ω) : PiLp 2 (fun _ : Ω => X) ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Ω => X) where
  toFun z := toLp 2 (fun a => z (e a))
  invFun z := toLp 2 (fun a => z (e.symm a))
  left_inv z := by ext a; simp
  right_inv z := by ext a; simp
  map_add' z w := by ext a; rfl
  map_smul' c z := by ext a; rfl
  norm_map' z := by
    simp only [PiLp.norm_eq_of_L2]
    congr 1
    exact Equiv.sum_comp e (fun a => ‖z a‖^2)

@[simp] theorem l2Reindex_apply (e : Ω ≃ Ω) (z : PiLp 2 (fun _ : Ω => X)) (a : Ω) :
    l2Reindex e z a = z (e a) := rfl

variable [Group Γ] [Fintype Γ]

def rightTranslation : Γ →* (PiLp 2 (fun _ : Γ => X) ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Γ => X)) where
  toFun h := l2Reindex (Equiv.mulRight h)
  map_one' := by ext z a; simp
  map_mul' g h := by ext z a; simp [mul_assoc]

@[simp] theorem rightTranslation_apply (h : Γ) (z : PiLp 2 (fun _ : Γ => X)) (a : Γ) :
    rightTranslation h z a = z (a*h) := rfl

end Cotype

end

end OAI
