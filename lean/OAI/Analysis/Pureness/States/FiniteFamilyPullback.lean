import OAI.Analysis.Pureness.States.FiniteFamilyBaseCarrier
import OAI.Analysis.Pureness.Quasitrace.QuasitraceNormalization

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped CStarAlgebra NNReal ComplexOrder
variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma matrixMap_inclusion (φ : A →⋆ₙₐ[ℂ] B) {n m : ℕ} (h : n ≤ m) (x : FinMatrix A n) :
    CStarMatrix.mapₙₐ φ (matrixInclusion h x) = matrixInclusion h (CStarMatrix.mapₙₐ φ x) := by
  apply CStarMatrix.ext
  intro i j
  change φ (matrixInclusion h x i j) = matrixInclusion h (CStarMatrix.mapₙₐ φ x) i j
  rw [matrixInclusion_entry,matrixInclusion_entry]
  split_ifs <;> simp

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma matrixMap_scalarMatrix (φ : A →⋆ₙₐ[ℂ] B) (n : ℕ) (x : A) :
    CStarMatrix.mapₙₐ φ (scalarMatrixHom (ι := Fin n) x) = scalarMatrixHom (φ x) := by
  apply CStarMatrix.ext
  intro i j
  change φ (if i=j then x else 0) = if i=j then φ x else 0
  split_ifs <;> simp

namespace CompatibleFiniteQuasitrace

def comap (F : CompatibleFiniteQuasitrace B) (φ : A →⋆ₙₐ[ℂ] B) : CompatibleFiniteQuasitrace A where
  level n := (F.level n).comap (CStarMatrix.mapₙₐ φ)
  inclusion := by
    intro n m h x
    change F.level m (CStarMatrix.mapₙₐ φ (matrixInclusion h x)) = F.level n (CStarMatrix.mapₙₐ φ x)
    rw [matrixMap_inclusion,F.inclusion]

lemma comap_monotone (F : CompatibleFiniteQuasitrace B)
    (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix B n) => (F.level n a.1).re))
    (φ : A →⋆ₙₐ[ℂ] B) (n : ℕ) :
    Monotone (fun a : Positive (FinMatrix A n) => ((F.comap φ).level n a.1).re) := by
  intro a b hab
  exact ((F.positiveLevel hmono n).comap (CStarMatrix.mapₙₐ φ)).monotone hab

lemma comap_base (F : CompatibleFiniteQuasitrace B) (φ : A →⋆ₙₐ[ℂ] B) (x : A) :
    (F.comap φ).toTwoQuasitrace.base x = F.toTwoQuasitrace.base (φ x) := by
  change F.level 1 (CStarMatrix.mapₙₐ φ (scalarMatrixHom x))=F.level 1 (scalarMatrixHom (φ x))
  rw [matrixMap_scalarMatrix]

def scale (F : CompatibleFiniteQuasitrace A) (c : ℝ≥0) : CompatibleFiniteQuasitrace A where
  level n := (F.level n).scale c
  inclusion h x := congrArg ((c : ℂ)*·) (F.inclusion h x)

lemma scale_monotone (F : CompatibleFiniteQuasitrace A)
    (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re))
    (c : ℝ≥0) (n : ℕ) :
    Monotone (fun a : Positive (FinMatrix A n) => ((F.scale c).level n a.1).re) := by
  intro a b hab
  change (((c : ℝ) : ℂ)*F.level n a.1).re ≤ (((c : ℝ) : ℂ)*F.level n b.1).re
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_le_mul_of_nonneg_left (hmono n hab) c.2

lemma scale_unit (F : CompatibleFiniteQuasitrace A) (c : ℝ) (hc : 0 < c)
    (hF : F.level 1 1=(c : ℂ)) :
    (F.scale ⟨c⁻¹,inv_nonneg.mpr hc.le⟩).level 1 1=1 := by
  change ((c⁻¹ : ℝ) : ℂ)*F.level 1 1=1
  rw [hF,← Complex.ofReal_mul,inv_mul_cancel₀ hc.ne',Complex.ofReal_one]

lemma scale_base (F : CompatibleFiniteQuasitrace A) (c : ℝ≥0) (x : A) :
    (F.scale c).toTwoQuasitrace.base x = (c : ℂ)*F.toTwoQuasitrace.base x := rfl

theorem normalized_comap_mem (F : CompatibleFiniteQuasitrace B)
    (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix B n) => (F.level n a.1).re))
    (φ : A →⋆ₙₐ[ℂ] B) (c : ℝ) (hc : 0 < c)
    (hunit : F.toTwoQuasitrace.base (φ 1)=(c : ℂ)) :
    (fun x => ((c⁻¹ : ℝ) : ℂ)*F.toTwoQuasitrace.base (φ x)) ∈
      normalizedFiniteBaseQuasitraceCarrier := by
  let G := (F.comap φ).scale ⟨c⁻¹,inv_nonneg.mpr hc.le⟩
  have hG : G.level 1 1=1 := (F.comap φ).scale_unit c hc (by
    have h := (F.comap_base φ 1).trans hunit
    change (F.comap φ).level 1 (scalarMatrixHom 1)=(c : ℂ) at h
    rwa [map_one] at h)
  apply (mem_normalizedFiniteBaseQuasitraceCarrier _).mpr
  refine ⟨G,(F.comap φ).scale_monotone (F.comap_monotone hmono φ) _ ,hG,?_⟩
  funext x
  exact congrArg (((c⁻¹ : ℝ) : ℂ)*·) (F.comap_base φ x)

end CompatibleFiniteQuasitrace
end CuntzPureness

end

end OAI
