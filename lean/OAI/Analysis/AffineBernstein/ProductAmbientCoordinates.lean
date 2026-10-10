import Mathlib
import OAI.Analysis.AffineBernstein.AmbientStraightening
import OAI.Analysis.AffineBernstein.FixedBasisCoordinates

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ProductAmbientCoordinates
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
lemma targetBasisCoordinates_coord {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ G)
    (z : G) (i : Fin n ⊕ Unit) :
    ambientCoordinates n (targetBasisCoordinates b z) i = b.equivFun z i := by
  have he : (ambientCoordinates n).toLinearMap.comp (targetBasisCoordinates b).toLinearMap =
      b.equivFun.toLinearMap := by
    apply b.ext
    intro j
    simp [targetBasisCoordinates,ambientCoordinates]
  exact congrFun (LinearMap.congr_fun he z) i
end ProductAmbientCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

def productAmbientBasis {n k : ℕ} (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (e : Fin n ≃ Fin k ⊕ κ) : Module.Basis (Fin n ⊕ Unit) ℝ (Space k × E) :=
  ((EuclideanSpace.basisFun (Fin k) ℝ).toBasis.prod bE.toBasis).reindex
    ((Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc (Fin k) κ Unit)).symm

def productBaseIndex {n k : ℕ} (e : Fin n ≃ Fin k ⊕ κ) (i : Fin k) : Fin n ⊕ Unit :=
  ((Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc (Fin k) κ Unit)).symm (Sum.inl i)

omit [DecidableEq κ] in
lemma productAmbientCoordinates_base {n k : ℕ} (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (e : Fin n ≃ Fin k ⊕ κ) (z : Space k × E) (i : Fin k) :
    ambientCoordinates n (targetBasisCoordinates (productAmbientBasis bE e) z)
      (productBaseIndex e i) = z.1 i := by
  rw [targetBasisCoordinates_coord]
  change (productAmbientBasis bE e).repr z (productBaseIndex e i) = z.1 i
  rw [productAmbientBasis,Module.Basis.repr_reindex_apply]
  simp only [productBaseIndex, Equiv.symm_symm, Equiv.apply_symm_apply,
    Module.Basis.prod_repr_inl]
  simp

lemma ambientCoordinate_abs_le_norm {n : ℕ} (z : Space n × ℝ) (i : Fin n ⊕ Unit) :
    |ambientCoordinates n z i| ≤ ‖z‖ := by
  rcases i with i | i
  · rw [ambientCoordinates_inl]
    have hi : |z.1 i| ≤ ‖z.1‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z.1 i
    exact hi.trans (le_max_left _ _)
  · rw [ambientCoordinates_inr]
    exact le_max_right _ _

end AffineBernstein

end

end OAI
