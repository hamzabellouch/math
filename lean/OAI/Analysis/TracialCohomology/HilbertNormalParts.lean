import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts

namespace OAI

/-! Hilbert normal parts for bounded Hochschild cohomology. -/

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def hilbertNormalFunctional (T : M →L[ℂ] H) (a : M) : StrongDual ℂ H :=
  LinearMap.mkContinuous
    { toFun := fun η => star (scalarNormalPart e ((innerSL ℂ η).comp T) a)
      map_add' := by
        intro η ξ
        simp only [map_add,ContinuousLinearMap.add_comp,add_apply,star_add]
      map_smul' := by
        intro c η
        have hη : (innerSL ℂ (c • η)).comp T = star c • (innerSL ℂ η).comp T := by
          ext b
          change ⟪c • η,T b⟫_ℂ=star c*⟪η,T b⟫_ℂ
          simp only [inner_smul_left,starRingEnd_apply]
        change star (scalarNormalPart e ((innerSL ℂ (c • η)).comp T) a) =
          c • star (scalarNormalPart e ((innerSL ℂ η).comp T) a)
        rw [hη,map_smul,smul_apply,star_smul,star_star] }
    (4*‖T‖*‖a‖) (by
      intro η
      have hP := (scalarNormalPart e).le_opNorm ((innerSL ℂ η).comp T)
      have hT := ContinuousLinearMap.opNorm_comp_le (innerSL ℂ η) T
      have h := (scalarNormalPart e ((innerSL ℂ η).comp T)).le_opNorm a
      change ‖star (scalarNormalPart e ((innerSL ℂ η).comp T) a)‖ ≤ _
      rw [norm_star]
      calc
        _ ≤ ‖scalarNormalPart e ((innerSL ℂ η).comp T)‖*‖a‖ := h
        _ ≤ (4*(‖η‖*‖T‖))*‖a‖ := by
          gcongr
          exact hP.trans (mul_le_mul (scalarNormalPart_norm e)
            (by simpa only [innerSL_apply_norm] using hT) (norm_nonneg _) (by norm_num))
        _ = (4*‖T‖*‖a‖)*‖η‖ := by ring)

omit [CompleteSpace H] in
@[simp] lemma hilbertNormalFunctional_apply (T : M →L[ℂ] H) (a : M) (η : H) :
    hilbertNormalFunctional e T a η =
      star (scalarNormalPart e ((innerSL ℂ η).comp T) a) := rfl

def hilbertNormalValue (T : M →L[ℂ] H) (a : M) : H :=
  (InnerProductSpace.toDual ℂ H).symm (hilbertNormalFunctional e T a)

lemma hilbertNormalValue_inner (T : M →L[ℂ] H) (a : M) (η : H) :
    ⟪η,hilbertNormalValue e T a⟫_ℂ =
      scalarNormalPart e ((innerSL ℂ η).comp T) a := by
  have h := (InnerProductSpace.toDual ℂ H).apply_symm_apply (hilbertNormalFunctional e T a)
  have h' := congrArg (fun φ : StrongDual ℂ H => φ η) h
  change ⟪hilbertNormalValue e T a,η⟫_ℂ = _ at h'
  rw [hilbertNormalFunctional_apply] at h'
  apply star_injective
  simpa only [← starRingEnd_apply,inner_conj_symm] using h'

lemma hilbertNormalValue_add (T : M →L[ℂ] H) (a b : M) :
    hilbertNormalValue e T (a+b)=hilbertNormalValue e T a+hilbertNormalValue e T b := by
  apply ext_inner_left ℂ
  intro η
  simp only [inner_add_right,hilbertNormalValue_inner,map_add]

lemma hilbertNormalValue_smul (T : M →L[ℂ] H) (c : ℂ) (a : M) :
    hilbertNormalValue e T (c • a)=c • hilbertNormalValue e T a := by
  apply ext_inner_left ℂ
  intro η
  simp only [inner_smul_right,hilbertNormalValue_inner,map_smul,smul_eq_mul]

lemma hilbertNormalValue_norm (T : M →L[ℂ] H) (a : M) :
    ‖hilbertNormalValue e T a‖≤4*‖T‖*‖a‖ := by
  rw [hilbertNormalValue,LinearIsometryEquiv.norm_map]
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

def hilbertNormalPart (T : M →L[ℂ] H) : M →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := hilbertNormalValue e T
      map_add' := hilbertNormalValue_add e T
      map_smul' := hilbertNormalValue_smul e T }
    (4*‖T‖) (hilbertNormalValue_norm e T)

lemma hilbertNormalPart_inner (T : M →L[ℂ] H) (a : M) (η : H) :
    ⟪η,hilbertNormalPart e T a⟫_ℂ =
      scalarNormalPart e ((innerSL ℂ η).comp T) a := hilbertNormalValue_inner e T a η

lemma hilbertNormalPart_pairing (T : M →L[ℂ] H) (a : M) (φ : StrongDual ℂ H) :
    φ (hilbertNormalPart e T a)=scalarNormalPart e (φ.comp T) a := by
  let η := (InnerProductSpace.toDual ℂ H).symm φ
  have hη : innerSL ℂ η=φ := (InnerProductSpace.toDual ℂ H).apply_symm_apply φ
  rw [← hη]
  change ⟪η,hilbertNormalPart e T a⟫_ℂ = _
  exact hilbertNormalPart_inner e T a η

lemma hilbertNormalPart_norm (T : M →L[ℂ] H) : ‖hilbertNormalPart e T‖≤4*‖T‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

lemma hilbertNormalPart_mem (T : M →L[ℂ] H) (K : Submodule ℂ H)
    (hK : IsClosed (K : Set H)) (hT : ∀ a,T a ∈ K) (a : M) :
    hilbertNormalPart e T a ∈ K := by
  rw [← hK.submodule_topologicalClosure_eq,← K.orthogonal_orthogonal_eq_closure]
  apply (K.orthogonal.mem_orthogonal _).mpr
  intro η hη
  rw [hilbertNormalPart_inner]
  have hz : (innerSL ℂ η).comp T=0 := by
    ext b
    exact (K.mem_orthogonal' η).mp hη (T b) (hT b)
  rw [hz,map_zero,zero_apply]

lemma factored_normal_part_mem (α : H →L[ℂ] StrongDual ℂ M) (β : M →L[ℂ] H)
    (hn : ∀ b,α (β b) ∈ normalDual e) (b : M) :
    α (hilbertNormalPart e β b) ∈ normalDual e := by
  let K : Submodule ℂ H := (normalDual e).comap α.toLinearMap
  have hK : IsClosed (K : Set H) := (normalDual_closed e).preimage α.continuous
  exact hilbertNormalPart_mem e β K hK hn b

lemma factored_normal_part_apply (α : H →L[ℂ] StrongDual ℂ M) (β : M →L[ℂ] H)
    (a b : M) :
    α (hilbertNormalPart e β b) a =
      scalarNormalPart e ((((ContinuousLinearMap.apply ℂ ℂ) a).comp α).comp β) b := by
  exact hilbertNormalPart_pairing e β b (((ContinuousLinearMap.apply ℂ ℂ) a).comp α)

lemma factored_bilinear_normalization (B : M →L[ℂ] StrongDual ℂ M)
    (α : H →L[ℂ] StrongDual ℂ M) (β : M →L[ℂ] H)
    (hfac : ∀ a b,B a b=α (β b) a)
    (hn : ∀ b,B.flip b ∈ normalDual e) (b : M) :
    ((scalarNormalPart e).comp B).flip b ∈ normalDual e := by
  have hB (a : M) : B a=(((ContinuousLinearMap.apply ℂ ℂ) a).comp α).comp β := by
    ext b
    exact hfac a b
  have hN : ((scalarNormalPart e).comp B).flip b=α (hilbertNormalPart e β b) := by
    ext a
    change scalarNormalPart e (B a) b=α (hilbertNormalPart e β b) a
    rw [hB,factored_normal_part_apply]
  rw [hN]
  apply factored_normal_part_mem e α β
  intro c
  have hc : α (β c)=B.flip c := by
    ext a
    exact (hfac a c).symm
  rw [hc]
  exact hn c

end HochschildNormalPart

namespace HochschildNormalPart
open BoundedHochschild
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

omit [CompleteSpace X] in
lemma hasPreadjoint_iff_scalar (T : M →L[ℂ] M) :
    HasPreadjoint e T ↔ ∀ z, (predualEmbedding e z).comp T ∈ normalDual e := by
  constructor
  · intro h z
    exact normalDual_comp e ⟨z,rfl⟩ T h
  · intro h z
    obtain ⟨w,hw⟩ := (mem_normalDual e _).mp (h z)
    exact ⟨w,fun a => star_injective (hw a)⟩

lemma operator_bilinear_normalization
    (B : M →L[ℂ] M →L[ℂ] M)
    (H : X → Type v) [∀ z, NormedAddCommGroup (H z)]
    [∀ z, InnerProductSpace ℂ (H z)] [∀ z, CompleteSpace (H z)]
    (α : ∀ z,H z →L[ℂ] StrongDual ℂ M) (β : ∀ z,M →L[ℂ] H z)
    (hfac : ∀ z a b,predualEmbedding e z (B a b)=α z (β z b) a)
    (hn : ∀ b,HasPreadjoint e (B.flip b)) (b : M) :
    HasPreadjoint e (((operatorNormalPart e).comp B).flip b) := by
  rw [hasPreadjoint_iff_scalar]
  intro z
  let Bz : M →L[ℂ] StrongDual ℂ M :=
    (ContinuousLinearMap.compL ℂ M M ℂ (predualEmbedding e z)).comp B
  have hzfac : ∀ a c,Bz a c=α z (β z c) a := hfac z
  have hzn (c : M) : Bz.flip c ∈ normalDual e := by
    exact (hasPreadjoint_iff_scalar e (B.flip c)).mp (hn c) z
  have h := factored_bilinear_normalization e Bz (α z) (β z) hzfac hzn b
  have heq : (predualEmbedding e z).comp (((operatorNormalPart e).comp B).flip b)=
      ((scalarNormalPart e).comp Bz).flip b := by
    ext a
    exact operatorNormalPart_pairing e (B a) b z
  rw [heq]
  exact h

end HochschildNormalPart

end

end OAI
