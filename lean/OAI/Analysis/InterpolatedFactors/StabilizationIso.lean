import OAI.Analysis.InterpolatedFactors.Spatial

namespace OAI

noncomputable section

universe u_1 u_2 u_3

namespace FreeGroupFactorMain.Amplification

section
variable {G : Type u_1} {H : Type u_2} [Group G] [Group H]

def stabilizationIso (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (he : ∀ T : GroupOperator G, T ∈ groupVonNeumann G ↔ e.conjStarAlgEquiv T ∈ groupVonNeumann H) :
    stabilization G ≃⋆ₐ[ℂ] stabilization H where
  toFun T := ⟨(productSpatial ℕ e).conjStarAlgEquiv T, (productSpatial_stabilization e he T).mp T.property⟩
  invFun T := ⟨(productSpatial ℕ e).conjStarAlgEquiv.symm T,
    (productSpatial_stabilization e he _).mpr (by
      rw [(productSpatial ℕ e).conjStarAlgEquiv.apply_symm_apply]; exact T.property)⟩
  left_inv T := Subtype.ext ((productSpatial ℕ e).conjStarAlgEquiv.symm_apply_apply T)
  right_inv T := Subtype.ext ((productSpatial ℕ e).conjStarAlgEquiv.apply_symm_apply T)
  map_mul' T U := Subtype.ext (map_mul (productSpatial ℕ e).conjStarAlgEquiv
    (T : GroupOperator (ℕ × G)) (U : GroupOperator (ℕ × G)))
  map_add' T U := Subtype.ext (map_add (productSpatial ℕ e).conjStarAlgEquiv
    (T : GroupOperator (ℕ × G)) (U : GroupOperator (ℕ × G)))
  map_star' T := Subtype.ext (map_star (productSpatial ℕ e).conjStarAlgEquiv (T : GroupOperator (ℕ × G)))
  map_smul' c T := Subtype.ext (map_smul (productSpatial ℕ e).conjStarAlgEquiv c (T : GroupOperator (ℕ × G)))

theorem stabilizationIso_normal (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (he : ∀ T : GroupOperator G, T ∈ groupVonNeumann G ↔ e.conjStarAlgEquiv T ∈ groupVonNeumann H) :
    @Continuous _ _ (stabilizationTopology G) (stabilizationTopology H) (stabilizationIso e he) := by
  let : TopologicalSpace (GroupOperator (ℕ × G)) := ultraweakOperatorTopology (ℕ × G)
  let : TopologicalSpace (GroupOperator (ℕ × H)) := ultraweakOperatorTopology (ℕ × H)
  let : TopologicalSpace (stabilization G) := stabilizationTopology G
  let : TopologicalSpace (stabilization H) := stabilizationTopology H
  exact ((spatial_ultraweak_continuous (productSpatial ℕ e)).comp continuous_subtype_val).subtype_mk _

theorem stabilizationDelta_eq_single [DecidableEq (ℕ × G)] (k : ℕ) :
    stabilizationDelta G k = lp.single 2 (k,1) 1 := by
  classical
  ext x
  by_cases hx : x=(k,1) <;> simp [stabilizationDelta,lp.single_apply,hx]

theorem productSpatial_delta (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (hδ : e deltaOne = deltaOne) (k : ℕ) :
    productSpatial ℕ e (stabilizationDelta G k) = stabilizationDelta H k := by
  classical
  have hg : stabilizationDelta G k=productSingle ℕ G k deltaOne := (productSingle_single k (1:G)).symm
  have hh : stabilizationDelta H k=productSingle ℕ H k deltaOne := (productSingle_single k (1:H)).symm
  rw [hg,hh,productSpatial_productSingle,hδ]

theorem stabilizationIso_projectionTrace (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (he : ∀ T : GroupOperator G, T ∈ groupVonNeumann G ↔ e.conjStarAlgEquiv T ∈ groupVonNeumann H)
    (hδ : e deltaOne = deltaOne) (T : stabilization G) :
    stabilizedProjectionTrace (stabilizationIso e he T) = stabilizedProjectionTrace T := by
  classical
  unfold stabilizedProjectionTrace
  apply tsum_congr
  intro k
  rw [← stabilizationDelta_eq_single,← stabilizationDelta_eq_single]
  change ENNReal.ofReal (‖(productSpatial ℕ e) ((T : GroupOperator (ℕ × G))
    ((productSpatial ℕ e).symm (stabilizationDelta H k)))‖^2) = _
  rw [← productSpatial_delta e hδ,(productSpatial ℕ e).symm_apply_apply,(productSpatial ℕ e).norm_map]

theorem stabilizationIso_trace (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (he : ∀ T : GroupOperator G, T ∈ groupVonNeumann G ↔ e.conjStarAlgEquiv T ∈ groupVonNeumann H)
    (hδ : e deltaOne = deltaOne) (T : stabilization G) :
    stabilizedTrace (stabilizationIso e he T) = stabilizedTrace T := by
  classical
  unfold stabilizedTrace
  apply tsum_congr
  intro k
  rw [← stabilizationDelta_eq_single,← stabilizationDelta_eq_single]
  change inner ℂ (stabilizationDelta H k) ((productSpatial ℕ e) ((T : GroupOperator (ℕ × G))
    ((productSpatial ℕ e).symm (stabilizationDelta H k)))) = _
  rw [← productSpatial_delta e hδ,(productSpatial ℕ e).symm_apply_apply,(productSpatial ℕ e).inner_map_map]

theorem amplification_functoriality (h : HasNormalTracialIso G H) :
    ∃ Φ : stabilization G ≃⋆ₐ[ℂ] stabilization H,
      (∀ p, stabilizedProjectionTrace (Φ p) = stabilizedProjectionTrace p) ∧
      (∀ T, stabilizedTrace (Φ T) = stabilizedTrace T) ∧
      @Continuous _ _ (stabilizationTopology G) (stabilizationTopology H) Φ := by
  obtain ⟨Ψ,ht,_⟩ := h
  obtain ⟨e,hδ,he⟩ := spatial_of_trace_iso Ψ ht
  exact ⟨stabilizationIso e he,stabilizationIso_projectionTrace e he hδ,
    stabilizationIso_trace e he hδ,stabilizationIso_normal e he⟩

end

open scoped ENNReal
variable {G : Type u_3}

@[simp] theorem pairedIndex_apply (i j : ℕ) (g : G) : pairedIndex G (i,j,g)=(Nat.pair i j,g) := rfl
variable [Group G]

instance doubleStabilization_isClosed : IsClosed (doubleStabilization G : Set (GroupOperator (ℕ × (ℕ × G)))) := by
  rw [doubleStabilization,StarSubalgebra.coe_centralizer]
  exact Set.isClosed_centralizer _

instance doubleStabilization_CStarAlgebra : CStarAlgebra (doubleStabilization G) := inferInstance

theorem mem_doubleStabilization_iff_matrix (T : GroupOperator (ℕ × (ℕ × G))) :
    T ∈ doubleStabilization G ↔ ∀i j,matrixEntry T i j ∈ stabilization G := by
  rw [mem_doubleStabilization_iff_right]
  constructor
  · intro h i j
    rw [mem_stabilization_iff_right]
    intro g
    have hh := congrArg (fun S => matrixEntry S i j) (h g)
    simpa only [doubleRight,matrixEntry_diagonal_mul,matrixEntry_mul_diagonal] using hh
  · intro h g
    apply matrixEntry_ext
    intro i j
    change matrixEntry (productAmplification ℕ (ℕ × G) (productAmplification ℕ G (rightRegular g))*T) i j=_
    rw [matrixEntry_diagonal_mul]
    change _=matrixEntry (T*productAmplification ℕ (ℕ × G) (productAmplification ℕ G (rightRegular g))) i j
    rw [matrixEntry_mul_diagonal]
    exact (mem_stabilization_iff_right _).mp (h i j) g

end FreeGroupFactorMain.Amplification

end

end OAI
