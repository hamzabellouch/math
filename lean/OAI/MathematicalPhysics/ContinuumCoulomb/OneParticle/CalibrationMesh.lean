import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PhysicalNuclearProgram

namespace OAI

/-! Exact compatibility between polynomial hopping amplification and the
equal masses of the unit-nucleus Gauss mesh. -/

namespace ContinuumCoulomb.CalibrationMesh

def base (n : ℕ) : ℕ := n^30
def radius (n k : ℕ) : ℕ := n^k
def mesh (n k : ℕ) : ℕ := n^(10*k)
def width (n k : ℕ) : ℕ := n^(5*k)
def horizontal (n k : ℕ) : ℕ := width n k ^ 10
def prefactor (rho : ℕ) : ℚ := 8/(rho:ℚ)
def amplification (rho n k : ℕ) : ℚ := prefactor rho * (base n:ℚ)^k

theorem prefactor_positive {rho : ℕ} (hrho : 0 < rho) : 0 < prefactor rho := by
  unfold prefactor
  positivity

theorem base_ge_two {n : ℕ} (hn : 2 ≤ n) : 2 ≤ base n := by
  exact (by norm_num : 2 ≤ 2^30).trans (Nat.pow_le_pow_left hn 30)

theorem mesh_positive {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < mesh n k := pow_pos hn _

theorem base_power_eq_mesh_cube (n k : ℕ) : base n ^ k = mesh n k ^ 3 := by
  simp only [base,mesh,← pow_mul]
  congr 1
  omega

theorem amplification_eq_mesh (rho n k : ℕ) :
    amplification rho n k = 8*(mesh n k:ℚ)^3/(rho:ℚ) := by
  have he : (base n:ℚ)^k = (mesh n k:ℚ)^3 := by
    exact_mod_cast base_power_eq_mesh_cube n k
  rw [amplification,he,prefactor]
  ring

theorem physical_factor_eq (rho n k : ℕ) :
    PhysicalNuclearProgram.factor rho (mesh n k) = (amplification rho n k)⁻¹ := by
  rw [amplification_eq_mesh,PhysicalNuclearProgram.factor]
  exact (inv_div _ _).symm

theorem amplification_positive {rho n : ℕ} (hrho : 0 < rho) (hn : 0 < n) (k : ℕ) :
    0 < amplification rho n k := by
  rw [amplification_eq_mesh]
  have hm := mesh_positive hn k
  positivity

theorem mesh_eq_radius (n k : ℕ) : mesh n k = radius n k ^ 10 := by
  simp only [mesh,radius,← pow_mul]
  congr 1
  omega

theorem width_eq_radius (n k : ℕ) : width n k = radius n k ^ 5 := by
  simp only [width,radius,← pow_mul]
  congr 1
  omega

end ContinuumCoulomb.CalibrationMesh

end OAI
