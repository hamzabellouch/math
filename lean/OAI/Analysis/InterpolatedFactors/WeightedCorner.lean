import OAI.Analysis.InterpolatedFactors.InverseRecognition

namespace OAI

noncomputable section
namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification GaussianRecognition
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

instance ambientClosed : IsClosed (ambientAlgebra (ι := ℕ) u v : Set (Operator ℕ)) :=
  Set.isClosed_centralizer _

@[instance_reducible] def ambientTopology : TopologicalSpace (ambientAlgebra (ι := ℕ) u v) :=
  subalgebraTopology (HilbertUltraweak.topology (H ℕ)) (ambientAlgebra u v)
@[instance_reducible] def pAmbientTopology : TopologicalSpace (pAmbient (ι := ℕ) u v) :=
  subalgebraTopology (cornerTopology (HilbertUltraweak.topology (H ℕ)) P projection_P) (pAmbient u v)

theorem pAmbientRepresentation_mem (a : PCorner ℕ) :
    pRepresentation a∈representedAmbient u v ↔ a∈pAmbient u v := by
  change (pRepresentation (ι := ℕ)).symm (pRepresentation a)∈pAmbient u v ↔ a∈pAmbient u v
  rw [StarAlgEquiv.symm_apply_apply]

def pAmbientRepresentation : pAmbient (ι := ℕ) u v ≃⋆ₐ[ℂ] representedAmbient u v where
  toFun a := ⟨pRepresentation a,(pAmbientRepresentation_mem u v a).mpr a.property⟩
  invFun b := ⟨(pRepresentation (ι := ℕ)).symm b,b.property⟩
  left_inv _ := Subtype.ext (StarAlgEquiv.symm_apply_apply _ _)
  right_inv _ := Subtype.ext (StarAlgEquiv.apply_symm_apply _ _)
  map_mul' a b := Subtype.ext ((pRepresentation (ι := ℕ)).map_mul (a:PCorner ℕ) (b:PCorner ℕ))
  map_add' a b := Subtype.ext ((pRepresentation (ι := ℕ)).map_add (a:PCorner ℕ) (b:PCorner ℕ))
  map_smul' c a := Subtype.ext ((pRepresentation (ι := ℕ)).map_smul' c (a:PCorner ℕ))
  map_star' a := Subtype.ext ((pRepresentation (ι := ℕ)).map_star' (a:PCorner ℕ))

theorem pAmbientRepresentation_normal :
    @Continuous (pAmbient (ι := ℕ) u v) (representedAmbient u v) (pAmbientTopology u v)
      (subalgebraTopology (HilbertUltraweak.topology (PRange ℕ)) (representedAmbient u v))
        (pAmbientRepresentation u v) := by
  let : TopologicalSpace (PCorner ℕ) := cornerTopology (HilbertUltraweak.topology (H ℕ)) P projection_P
  let : TopologicalSpace (pAmbient (ι := ℕ) u v) := pAmbientTopology u v
  let : TopologicalSpace (PRange ℕ →L[ℂ] PRange ℕ) := HilbertUltraweak.topology (PRange ℕ)
  exact ((projectionRepresentation_normal P projection_P).comp continuous_subtype_val).subtype_mk _

theorem pAmbientRepresentation_symm_normal :
    @Continuous (representedAmbient u v) (pAmbient (ι := ℕ) u v) (subalgebraTopology (HilbertUltraweak.topology (PRange ℕ)) (representedAmbient u v))
      (pAmbientTopology u v) (pAmbientRepresentation u v).symm := by
  let : TopologicalSpace (PCorner ℕ) := cornerTopology (HilbertUltraweak.topology (H ℕ)) P projection_P
  let : TopologicalSpace (representedAmbient u v) :=
    subalgebraTopology (HilbertUltraweak.topology (PRange ℕ)) (representedAmbient u v)
  let : TopologicalSpace (PRange ℕ →L[ℂ] PRange ℕ) := HilbertUltraweak.topology (PRange ℕ)
  exact ((projectionRepresentation_symm_normal P projection_P).comp continuous_subtype_val).subtype_mk _

def representedGeneratedIso : representedAmbient u v ≃⋆ₐ[ℂ]
    (weightedSystem u v hv hvu).generated scalarFlip where
  toFun a := ⟨a.val, by rw [weighted_generated_eq_ambient]; exact a.property⟩
  invFun a := ⟨a.val, by rw [←weighted_generated_eq_ambient u v hv hvu]; exact a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

theorem representedGeneratedIso_normal :
    @Continuous (representedAmbient u v) ((weightedSystem u v hv hvu).generated scalarFlip)
      (subalgebraTopology (HilbertUltraweak.topology (PRange ℕ)) (representedAmbient u v))
      ((weightedSystem u v hv hvu).generatedTopology scalarFlip) (representedGeneratedIso u v hv hvu) := by
  let : TopologicalSpace (PRange ℕ →L[ℂ] PRange ℕ) := HilbertUltraweak.topology (PRange ℕ)
  let : TopologicalSpace (representedAmbient u v) :=
    subalgebraTopology (HilbertUltraweak.topology (PRange ℕ)) (representedAmbient u v)
  exact continuous_subtype_val.subtype_mk _

theorem representedGeneratedIso_symm_normal :
    @Continuous ((weightedSystem u v hv hvu).generated scalarFlip) (representedAmbient u v)
      ((weightedSystem u v hv hvu).generatedTopology scalarFlip)
      (subalgebraTopology (HilbertUltraweak.topology (PRange ℕ)) (representedAmbient u v))
        (representedGeneratedIso u v hv hvu).symm := by
  let : TopologicalSpace (PRange ℕ →L[ℂ] PRange ℕ) := HilbertUltraweak.topology (PRange ℕ)
  let : TopologicalSpace ((weightedSystem u v hv hvu).generated scalarFlip) :=
    (weightedSystem u v hv hvu).generatedTopology scalarFlip
  exact continuous_subtype_val.subtype_mk _

def pAmbientGeneratedIso : pAmbient (ι := ℕ) u v ≃⋆ₐ[ℂ]
    (weightedSystem u v hv hvu).generated scalarFlip :=
  (pAmbientRepresentation u v).trans (representedGeneratedIso u v hv hvu)

def pAmbientGaussianIso : pAmbient (ι := ℕ) u v ≃⋆ₐ[ℂ] scalarSystem.generated scalarFlip :=
  (pAmbientGeneratedIso u v hv hvu).trans (fullGaussianIso u v hv hvu)

theorem pAmbientGaussianIso_normal :
    @Continuous _ _ (pAmbientTopology u v) (scalarSystem.generatedTopology scalarFlip)
      (pAmbientGaussianIso u v hv hvu) := by
  let : TopologicalSpace (pAmbient (ι := ℕ) u v) := pAmbientTopology u v
  let : TopologicalSpace (representedAmbient u v) := subalgebraTopology
    (HilbertUltraweak.topology (PRange ℕ)) (representedAmbient u v)
  let : TopologicalSpace ((weightedSystem u v hv hvu).generated scalarFlip) :=
    (weightedSystem u v hv hvu).generatedTopology scalarFlip
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  have hc := (fullGaussianIso_normal u v hv hvu).comp
    ((representedGeneratedIso_normal u v hv hvu).comp
        (pAmbientRepresentation_normal u v))
  convert hc using 1 ; rfl

theorem pAmbientGaussianIso_symm_normal :
    @Continuous _ _ (scalarSystem.generatedTopology scalarFlip) (pAmbientTopology u v)
      (pAmbientGaussianIso u v hv hvu).symm := by
  let : TopologicalSpace (pAmbient (ι := ℕ) u v) := pAmbientTopology u v
  let : TopologicalSpace (representedAmbient u v) := subalgebraTopology
    (HilbertUltraweak.topology (PRange ℕ)) (representedAmbient u v)
  let : TopologicalSpace ((weightedSystem u v hv hvu).generated scalarFlip) :=
    (weightedSystem u v hv hvu).generatedTopology scalarFlip
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  have hc := (pAmbientRepresentation_symm_normal u v).comp
    ((representedGeneratedIso_symm_normal u v hv hvu).comp (fullGaussianIso_symm_normal u v hv hvu))
  convert hc using 1 ; rfl

theorem pAmbientGaussianIso_trace (x : pAmbient (ι := ℕ) u v) :
    inner ℂ scalarSystem.root ((pAmbientGaussianIso u v hv hvu x : FreeFock.Operator ScalarIndex) scalarSystem.root)=
      pVacuumTrace u v (x.val:Operator ℕ) := by
  rw [pAmbientGaussianIso,StarAlgEquiv.trans_apply,fullGaussianIso_trace]
  exact (pRepresentation_vacuumTrace u v (ne_of_gt (lt_trans hv hvu)) x.val).symm

def ambientP : ambientAlgebra (ι := ℕ) u v := ⟨P,P_mem_ambient u v⟩
theorem ambientP_projection : IsStarProjection (ambientP u v) :=
  ⟨Subtype.ext projection_P.isIdempotentElem.eq,Subtype.ext projection_P.isSelfAdjoint.star_eq⟩

def ambientCornerGaussianIso : Corner (ambientP u v) (ambientP_projection u v) ≃⋆ₐ[ℂ]
    scalarSystem.generated scalarFlip :=
  (cornerSubtypeEquiv _ (ambientP u v) (ambientP_projection u v)).trans (pAmbientGaussianIso u v hv hvu)

theorem ambientCornerGaussianIso_normal :
    @Continuous _ _ (cornerTopology (ambientTopology u v) (ambientP u v) (ambientP_projection u v))
      (scalarSystem.generatedTopology scalarFlip) (ambientCornerGaussianIso u v hv hvu) := by
  let : TopologicalSpace (Corner (ambientP u v) (ambientP_projection u v)) :=
    cornerTopology (ambientTopology u v) (ambientP u v) (ambientP_projection u v)
  let : TopologicalSpace (pAmbient (ι := ℕ) u v) := pAmbientTopology u v
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  have hc := (pAmbientGaussianIso_normal u v hv hvu).comp
    (cornerSubtypeEquiv_normal _ (ambientP u v) (ambientP_projection u v) (HilbertUltraweak.topology (H ℕ)))
  convert hc using 1
  rfl

theorem ambientCornerGaussianIso_symm_normal :
    @Continuous _ _ (scalarSystem.generatedTopology scalarFlip)
      (cornerTopology (ambientTopology u v) (ambientP u v) (ambientP_projection u v)) (ambientCornerGaussianIso u v hv hvu).symm := by
  let : TopologicalSpace (Corner (ambientP u v) (ambientP_projection u v)) :=
    cornerTopology (ambientTopology u v) (ambientP u v) (ambientP_projection u v)
  let : TopologicalSpace (pAmbient (ι := ℕ) u v) := pAmbientTopology u v
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  have hr : @Continuous _ _ (pAmbientTopology u v)
      (cornerTopology (ambientTopology u v) (ambientP u v) (ambientP_projection u v))
      (cornerSubtypeEquiv _ (ambientP u v) (ambientP_projection u v)).symm := by
    convert cornerSubtypeEquiv_symm_normal _ (ambientP u v) (ambientP_projection u v)
      (HilbertUltraweak.topology (H ℕ)) using 1 ; rfl
  exact hr.comp (pAmbientGaussianIso_symm_normal u v hv hvu)

theorem ambientCornerGaussianIso_trace (x : Corner (ambientP u v) (ambientP_projection u v)) :
    inner ℂ scalarSystem.root ((ambientCornerGaussianIso u v hv hvu x : FreeFock.Operator ScalarIndex) scalarSystem.root)=
      pVacuumTrace u v (x.val:Operator ℕ) :=
  pAmbientGaussianIso_trace u v hv hvu _

variable (hu : u≠0) (hv' : v≠0) (hunit : u^2+v^2=1)
def ambientScalarIso : ambientAlgebra (ι := ℕ) u v ≃⋆ₐ[ℂ] scalarSystem.generated scalarFlip :=
  (subalgebraEqualityEquiv _ _ (ambient_generated_eq u v hu hv' hunit).symm).trans
    (ambientGaussianIso u v hu hv' hunit)

theorem ambientScalarIso_normal :
    @Continuous _ _ (ambientTopology u v) (scalarSystem.generatedTopology scalarFlip)
      (ambientScalarIso u v hu hv' hunit) := by
  let : TopologicalSpace (ambientAlgebra (ι := ℕ) u v) := ambientTopology u v
  let : TopologicalSpace ((ambientSystem u v hu hv' hunit).generated scalarFlip) :=
    (ambientSystem u v hu hv' hunit).generatedTopology scalarFlip
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  exact (ambientGaussianIso_normal u v hu hv' hunit).comp
    (subalgebraEqualityEquiv_normal _ _ (ambient_generated_eq u v hu hv' hunit).symm
      (HilbertUltraweak.topology (H ℕ)))

theorem ambientScalarIso_symm_normal :
    @Continuous _ _ (scalarSystem.generatedTopology scalarFlip) (ambientTopology u v)
      (ambientScalarIso u v hu hv' hunit).symm := by
  let : TopologicalSpace (ambientAlgebra (ι := ℕ) u v) := ambientTopology u v
  let : TopologicalSpace ((ambientSystem u v hu hv' hunit).generated scalarFlip) :=
    (ambientSystem u v hu hv' hunit).generatedTopology scalarFlip
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  exact (subalgebraEqualityEquiv_symm_normal _ _ (ambient_generated_eq u v hu hv' hunit).symm
      (HilbertUltraweak.topology (H ℕ))).comp (ambientGaussianIso_symm_normal u v hu hv' hunit)

theorem ambientScalarIso_trace (T : ambientAlgebra (ι := ℕ) u v) :
    inner ℂ scalarSystem.root ((ambientScalarIso u v hu hv' hunit T : FreeFock.Operator ScalarIndex) scalarSystem.root)=
      vacuumTrace u v (T:Operator ℕ) :=
  ambientGaussianIso_trace u v hu hv' hunit _
end FreeGroupFactorMain.WeightedFock

end

end OAI
