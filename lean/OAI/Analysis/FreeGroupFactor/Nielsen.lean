import OAI.Analysis.FreeGroupFactor.LaurentApproximation

namespace OAI

noncomputable section

universe uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain
open scoped ENNReal

variable {G : Type uG} [Group G]

@[simp] theorem groupL2_groupUnitary [DecidableEq G] (g : G) :
    groupL2 (groupUnitary g) = lp.single 2 g (1 : ℂ) := by
  classical
  ext x
  simp [groupL2, groupUnitary, deltaOne, leftRegular_apply,
    lp.single_apply, Pi.single_apply, inv_mul_eq_one, eq_comm]

omit [Group G] in
theorem group_single_total [DecidableEq G] (K : Submodule ℂ (GroupHilbert G))
    (hK : IsClosed (K : Set (GroupHilbert G)))
    (hsingle : ∀ g : G, lp.single 2 g (1 : ℂ) ∈ K) : ⊤ ≤ K := by
  classical
  intro ξ _hξ
  have hs := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ
  apply hK.mem_of_tendsto hs
  filter_upwards [] with s
  apply K.sum_mem
  intro g _hg
  have he : lp.single 2 g (ξ g) = (ξ g) • (lp.single 2 g (1 : ℂ) : GroupHilbert G) := by
    ext x
    simp [lp.single_apply, Pi.single_apply]
  rw [he]
  exact K.smul_mem _ (hsingle g)

theorem spatialGroupIso_symm_normal {H : Type uH} [Group H]
    (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (hVN : ∀ T : GroupOperator G,
      T ∈ groupVonNeumann G ↔ e.conjStarAlgEquiv T ∈ groupVonNeumann H) :
    @Continuous _ _ (groupUltraweakTopology H) (groupUltraweakTopology G)
      (spatialGroupIso e hVN).symm := by
  let : TopologicalSpace (GroupOperator G) := ultraweakOperatorTopology G
  let : TopologicalSpace (GroupOperator H) := ultraweakOperatorTopology H
  let : TopologicalSpace (groupVonNeumann G) := groupUltraweakTopology G
  let : TopologicalSpace (groupVonNeumann H) := groupUltraweakTopology H
  apply continuous_induced_rng.mpr
  have hinc : Continuous (fun T : groupVonNeumann H => (T : GroupOperator H)) :=
    continuous_induced_dom
  exact (spatial_ultraweak_continuous e.symm).comp hinc

def gaugedRepresentation (e : G ≃* G) (χ : G →* unitary ℂ) : G →* groupVonNeumann G where
  toFun g := (χ g : ℂ) • groupUnitary (e g)
  map_one' := by
    simp only [map_one, Submonoid.coe_one, one_smul]
    exact Subtype.ext leftRegular_one
  map_mul' g h := by
    simp only [map_mul, Submonoid.coe_mul, smul_mul_smul_comm]
    congr 1
    exact Subtype.ext (leftRegular_mul _ _)

@[simp] theorem gaugedRepresentation_apply (e : G ≃* G) (χ : G →* unitary ℂ) (g : G) :
    gaugedRepresentation e χ g = (χ g : ℂ) • groupUnitary (e g) := rfl

theorem gaugedRepresentation_star (e : G ≃* G) (χ : G →* unitary ℂ) (g : G) :
    star (gaugedRepresentation e χ g) = gaugedRepresentation e χ g⁻¹ := by
  simp only [gaugedRepresentation_apply, star_smul, map_inv]
  have hg : star (groupUnitary (e g)) = groupUnitary ((e g)⁻¹) :=
    Subtype.ext (leftRegular_star _)
  rw [hg]
  congr 1

theorem gaugedRepresentation_trace [DecidableEq G] (e : G ≃* G) (χ : G →* unitary ℂ) (g : G) :
    canonicalTrace (gaugedRepresentation e χ g) = if g = 1 then 1 else 0 := by
  classical
  change canonicalTraceLinear ((χ g : ℂ) • groupUnitary (e g)) = _
  rw [map_smul]
  change (χ g : ℂ) • canonicalTrace (groupUnitary (e g)) = _
  rw [canonicalTrace_groupUnitary]
  simp only [e.map_eq_one_iff]
  split_ifs with hg
  · subst g; simp
  · simp

theorem gaugedRepresentation_total (e : G ≃* G) (χ : G →* unitary ℂ) :
    ⊤ ≤ (Submodule.span ℂ (Set.range
      (fun g => groupL2 (gaugedRepresentation e χ g)))).topologicalClosure := by
  classical
  let K := (Submodule.span ℂ (Set.range
    (fun g => groupL2 (gaugedRepresentation e χ g)))).topologicalClosure
  apply group_single_total K (Submodule.isClosed_topologicalClosure _)
  intro g
  have hg : groupL2 (gaugedRepresentation e χ (e.symm g)) ∈ K :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨e.symm g,rfl⟩)
  have hs := K.smul_mem (star (χ (e.symm g) : ℂ)) hg
  simp only [gaugedRepresentation_apply, map_smul, groupL2_groupUnitary,
    e.apply_symm_apply, smul_smul, (χ (e.symm g)).property.1, one_smul] at hs
  exact hs

theorem gaugedIso (e : G ≃* G) (χ : G →* unitary ℂ) :
    ∃ Φ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann G,
      (∀ T, canonicalTrace (Φ T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology G) (groupUltraweakTopology G) Φ ∧
      @Continuous _ _ (groupUltraweakTopology G) (groupUltraweakTopology G) Φ.symm ∧
      ∀ g, Φ (groupUnitary g) = (χ g : ℂ) • groupUnitary (e g) := by
  classical
  obtain ⟨f,hδ,hρ,hVN⟩ := spatial_of_haar_total (gaugedRepresentation e χ)
    (gaugedRepresentation_star e χ) (gaugedRepresentation_trace e χ)
    (gaugedRepresentation_total e χ)
  refine ⟨spatialGroupIso f hVN, ?_, spatialGroupIso_normal f hVN,
    spatialGroupIso_symm_normal f hVN, ?_⟩
  · intro T
    rw [canonicalTrace_eq_inner, canonicalTrace_eq_inner]
    change inner ℂ deltaOne (f ((T : GroupOperator G) (f.symm deltaOne))) =
      inner ℂ deltaOne ((T : GroupOperator G) deltaOne)
    have hf : f.symm deltaOne = deltaOne := f.injective (by simpa only [f.apply_symm_apply] using hδ.symm)
    rw [hf]
    simpa only [hδ] using f.inner_map_map deltaOne ((T : GroupOperator G) deltaOne)
  · intro g
    apply Subtype.ext
    exact hρ g

variable {ι : Type uι}

def nielsenHom (w : FreeGroup ι) : FreeGroup (Option ι) →* FreeGroup (Option ι) :=
  FreeGroup.lift (fun j => j.elim (FreeGroup.of none * FreeGroup.map Option.some w)
    (fun j => FreeGroup.of (some j)))

@[simp] theorem nielsenHom_of_some (w : FreeGroup ι) (j : ι) :
    nielsenHom w (FreeGroup.of (some j)) = FreeGroup.of (some j) := by
  simp [nielsenHom]

@[simp] theorem nielsenHom_of_none (w : FreeGroup ι) :
    nielsenHom w (FreeGroup.of none) = FreeGroup.of none * FreeGroup.map Option.some w := by
  simp [nielsenHom]

@[simp] theorem nielsenHom_map_some (w v : FreeGroup ι) :
    nielsenHom w (FreeGroup.map Option.some v) = FreeGroup.map Option.some v := by
  have he : (nielsenHom w).comp (FreeGroup.map Option.some) = FreeGroup.map Option.some := by
    apply FreeGroup.ext_hom
    intro j
    simp
  exact DFunLike.congr_fun he v

theorem nielsenHom_inv_comp (w : FreeGroup ι) :
    (nielsenHom w⁻¹).comp (nielsenHom w) = MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro j
  cases j <;> simp [mul_assoc]

def nielsenEquiv (w : FreeGroup ι) : FreeGroup (Option ι) ≃* FreeGroup (Option ι) where
  toFun := nielsenHom w
  invFun := nielsenHom w⁻¹
  left_inv g := DFunLike.congr_fun (nielsenHom_inv_comp w) g
  right_inv g := by simpa using DFunLike.congr_fun (nielsenHom_inv_comp w⁻¹) g
  map_mul' := map_mul (nielsenHom w)

theorem gauged_nielsen_iso (w : FreeGroup ι) (z : unitary ℂ) :
    ∃ γ : groupVonNeumann (FreeGroup (Option ι)) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option ι)),
      (∀ T, canonicalTrace (γ T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option ι)))
        (groupUltraweakTopology (FreeGroup (Option ι))) γ ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option ι)))
        (groupUltraweakTopology (FreeGroup (Option ι))) γ.symm ∧
      (∀ j, γ (groupUnitary (FreeGroup.of (some j))) = groupUnitary (FreeGroup.of (some j))) ∧
      γ (groupUnitary (FreeGroup.of none)) =
        (z : ℂ) • (groupUnitary (FreeGroup.of none) * groupUnitary (FreeGroup.map Option.some w)) := by
  let χ : FreeGroup (Option ι) →* unitary ℂ := FreeGroup.lift (fun j => j.elim z (fun _ => 1))
  obtain ⟨γ,ht,hc,hci,hg⟩ := gaugedIso (nielsenEquiv w) χ
  refine ⟨γ,ht,hc,hci,?_,?_⟩
  · intro j
    rw [hg]
    change ((χ (FreeGroup.of (some j)) : unitary ℂ) : ℂ) •
      groupUnitary (nielsenHom w (FreeGroup.of (some j))) = _
    simp only [χ, FreeGroup.lift_apply_of, Option.elim_some, Submonoid.coe_one,
      nielsenHom_of_some, one_smul]
  · rw [hg]
    change ((χ (FreeGroup.of none) : unitary ℂ) : ℂ) •
      groupUnitary (nielsenHom w (FreeGroup.of none)) = _
    simp only [χ, FreeGroup.lift_apply_of, Option.elim_none, nielsenHom_of_none]
    congr 1
    exact Subtype.ext (leftRegular_mul _ _)

end FreeGroupFactorMain

end

end OAI
