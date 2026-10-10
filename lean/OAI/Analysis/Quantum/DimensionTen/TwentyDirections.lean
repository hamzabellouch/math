import OAI.Analysis.Quantum.DimensionTen.PencilPoints
import OAI.Analysis.Quantum.DimensionTen.QuadraticBounds

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma pencilR_smul {R : Type*} [CommRing R] (c : R) (x : Fin 4 → R) :
    pencilR (c • x) = c • pencilR x := by
  simp only [pencilR, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

lemma minor_smul {R : Type*} [CommRing R] (c : R) (x : Fin 4 → R) :
    minor (c • x) = c ^ 4 • minor x := by
  ext i
  simp [minor, pencilR_smul, Matrix.submatrix_smul, Pi.smul_apply]

lemma points_injective : Function.Injective points :=
  fun _ _ h => embeddingsC.injective (embedding_points_injective h)

lemma rank_points (k : Fin 20) : (pencil (chart (points k))).rank < 4 :=
  rank_embedding (embeddingsC k)

lemma rankloss_point (x : Fin 4 → ℂ) (hx : x ≠ 0) (hr : (pencil x).rank < 4) :
    ∃ k : Fin 20, ∃ c : ℂ, c ≠ 0 ∧ x = c • chart (points k) := by
  have hm : minor x = 0 := minor_zero_of_rank_lt x hr
  have h0 : x 0 ≠ 0 := no_infinity x hx hm
  let t : Fin 3 → ℂ := fun j => (x 0)⁻¹ * x j.succ
  have he : (x 0)⁻¹ • x = Fin.cons 1 t := by
    ext i
    refine Fin.cases (by simpa using inv_mul_cancel₀ h0) (fun j => rfl) i
  have ht : minor (Fin.cons 1 t) = 0 := by
    rw [← he, minor_smul, hm, smul_zero]
  obtain ⟨σ, hσ⟩ := embedding_of_minor_zero t ht
  obtain ⟨k, rfl⟩ := embeddingsC.surjective σ
  have hp : points k = t := funext hσ
  refine ⟨k, x 0, h0, ?_⟩
  rw [hp]
  change x = x 0 • Fin.cons 1 t
  rw [← he, smul_smul, mul_inv_cancel₀ h0, one_smul]

end DimensionTen.Border
namespace DimensionTen

theorem twentyDirections : TwentyDirections :=
  ⟨Border.points, Border.points_injective, Border.rank_points,
    Border.rankloss_point, Border.quadratic_zero_bound⟩

end DimensionTen

end
end

end OAI
