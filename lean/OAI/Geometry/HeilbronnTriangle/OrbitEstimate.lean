import OAI.Geometry.HeilbronnTriangle.OrbitCardinality
import OAI.Geometry.HeilbronnTriangle.StabilizerConjugation
import OAI.Geometry.HeilbronnTriangle.DiagonalDetImage
import OAI.Geometry.HeilbronnTriangle.PrimePowerGL

namespace OAI


namespace Problem355.Section04Orbit

open Matrix

variable {R : Type*} [CommRing R]

def slOrbit (C : Matrix (Fin 3) (Fin 3) R) : Set (Matrix (Fin 3) (Fin 3) R) :=
  Set.range fun g : Matrix.SpecialLinearGroup (Fin 3) R => (g : Matrix _ _ _) * C

theorem slOrbit_eq_kernel_orbit (C : Matrix (Fin 3) (Fin 3) R) :
    slOrbit C = MulAction.orbit
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 3) R →* Rˣ).ker C := by
  ext M
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨⟨Matrix.SpecialLinearGroup.toGL g, ?_⟩, rfl⟩
    exact Matrix.SpecialLinearGroup.coeToGL_det g
  · rintro ⟨g, rfl⟩
    have hd : (g.1 : Matrix (Fin 3) (Fin 3) R).det = 1 := by
      exact congrArg Units.val g.2
    exact ⟨⟨g.1.val, hd⟩, rfl⟩

theorem slOrbit_lower_bound_of_diagonal_form
    {p k b e : ℕ} (hp : p.Prime) (hb : b ≤ k) (he : e ≤ k)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k)))
    (hC : C = (P : Matrix _ _ _) *
      Matrix.diagonal ![1, ((p ^ b : ℕ) : ZMod (p ^ k)), ((p ^ e : ℕ) : ZMod (p ^ k))] *
      (Q : Matrix _ _ _))
    {c : ℝ}
    (hGL : c * ((p ^ k : ℕ) : ℝ) ^ 9 ≤
      (Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k))) : ℝ)) :
    c * ((p ^ k : ℕ) : ℝ) ^ 8 /
      (((p ^ b : ℕ) : ℝ) ^ 3 * ((p ^ e : ℕ) : ℝ) ^ 2) ≤
        (Nat.card (slOrbit C) : ℝ) := by
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hs := Problem355.card_unit_matrix_stabilizer_le_of_diagonalization
    (p ^ k) (p ^ b) (p ^ e) (pow_dvd_pow p hb) (pow_dvd_pow p he) C P Q hC
  have hi := DiagonalDetImage.card_stabilizer_det_image_ratio_of_diagonal_form
    hp he ((p ^ b : ℕ) : ZMod (p ^ k)) P Q C hC
  rw [slOrbit_eq_kernel_orbit]
  apply OrbitCardinality.kernel_orbit_bound Matrix.GeneralLinearGroup.det
      Matrix.GeneralLinearGroup.det_surjective C
      (by exact_mod_cast pow_pos hp.pos k)
      (by exact_mod_cast pow_pos hp.pos b)
      (by exact_mod_cast pow_pos hp.pos e) hGL
  · exact_mod_cast hs
  · exact_mod_cast hi

theorem slOrbit_lower_bound
    {p k b e : ℕ} (hp : p.Prime) (hk : 0 < k) (hb : b ≤ k) (he : e ≤ k)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k)))
    (hC : C = (P : Matrix _ _ _) *
      Matrix.diagonal ![1, ((p ^ b : ℕ) : ZMod (p ^ k)), ((p ^ e : ℕ) : ZMod (p ^ k))] *
      (Q : Matrix _ _ _)) :
    (21 / 64 : ℝ) * ((p ^ k : ℕ) : ℝ) ^ 8 /
      (((p ^ b : ℕ) : ℝ) ^ 3 * ((p ^ e : ℕ) : ℝ) ^ 2) ≤
        (Nat.card (slOrbit C) : ℝ) :=
  slOrbit_lower_bound_of_diagonal_form hp hb he C P Q hC
    (PrimePowerGL.card_GL_three_prime_power_lower p k hp hk)

end Problem355.Section04Orbit

end OAI
