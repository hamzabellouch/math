import OAI.Analysis.Laughlin.Operators.CAR
import OAI.Analysis.Laughlin.Pair.Conjugation

namespace OAI

namespace Laughlin.Fock

theorem contraction_map {Q : ℕ} (f : Orbital Q →ₗ[ℂ] Orbital Q)
    (d : Module.Dual ℂ (Orbital Q)) (x : Space Q) :
    CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f x) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d.comp f) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    change CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f (ExteriorAlgebra.ι ℂ m*x)) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d.comp f) (ExteriorAlgebra.ι ℂ m*x))
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      LinearMap.comp_apply, map_sub, map_smul, hx]

noncomputable def orbitalScaling (Q : ℕ) (d : Fin (Q+1) → ℂ) : Orbital Q →ₗ[ℂ] Orbital Q where
  toFun v i := d i*v i
  map_add' v w := by ext i; simp [mul_add]
  map_smul' c v := by ext i; simp [mul_left_comm]

noncomputable def exteriorScaling (Q : ℕ) (d : Fin (Q+1) → ℂ) : Space Q →ₐ[ℂ] Space Q :=
  ExteriorAlgebra.map (orbitalScaling Q d)

theorem projection_scaling (Q : ℕ) (d : Fin (Q+1) → ℂ) (i : Fin (Q+1)) :
    (LinearMap.proj i).comp (orbitalScaling Q d) = d i • LinearMap.proj i := by
  ext v
  rfl

theorem annihilate_scaling (Q : ℕ) (d : Fin (Q+1) → ℂ) (i : Fin (Q+1)) (x : Space Q) :
    annihilate i (exteriorScaling Q d x) = d i • exteriorScaling Q d (annihilate i x) := by
  unfold annihilate exteriorScaling
  rw [contraction_map, projection_scaling, map_smul, LinearMap.smul_apply, map_smul]

theorem exteriorScaling_inverse (Q : ℕ) (d : Fin (Q+1) → ℂ) (hd : ∀ i, d i ≠ 0)
    (x : Space Q) : exteriorScaling Q (fun i => (d i)⁻¹) (exteriorScaling Q d x) = x := by
  have h : (orbitalScaling Q (fun i => (d i)⁻¹)).comp (orbitalScaling Q d) = LinearMap.id := by
    apply LinearMap.ext
    intro v
    funext i
    change (d i)⁻¹*(d i*v i) = v i
    rw [← mul_assoc, inv_mul_cancel₀ (hd i), one_mul]
  change ((ExteriorAlgebra.map (orbitalScaling Q (fun i => (d i)⁻¹))).comp
    (ExteriorAlgebra.map (orbitalScaling Q d))) x = x
  rw [ExteriorAlgebra.map_comp_map, h, ExteriorAlgebra.map_id]
  rfl

theorem modeFactor_pos (Q : ℕ) (hQ : 0 < Q) (i : Fin (Q+1)) : 0 < modeFactor Q i.val := by
  unfold modeFactor
  apply Real.sqrt_pos.mpr
  apply div_pos
  · exact_mod_cast (Nat.descFactorial_pos.mpr (show i.val ≤ Q by omega))
  · exact pow_pos (by exact_mod_cast hQ) _

end Laughlin.Fock

end OAI
