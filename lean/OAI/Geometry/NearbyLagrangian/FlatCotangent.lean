import Mathlib
import OAI.Geometry.NearbyLagrangian.CotangentForms

namespace OAI

/-! Flat and open cotangent coordinates with Riesz identifications. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Bundle Set ContinuousLinearMap Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance flatCotangentChartedSpace :
    ChartedSpace (E × (E →L[ℝ] ℝ)) (Cotangent (E:=E) (M:=E)) :=
  inferInstanceAs (ChartedSpace (ModelProd E (E →L[ℝ] ℝ)) (Cotangent (E:=E) (M:=E)))

def cotangentFlatMap (z : Cotangent (E:=E) (M:=E)) : E × (E →L[ℝ] ℝ) :=
  (z.proj,z.snd)
def cotangentFlatInv (z : E × (E →L[ℝ] ℝ)) : Cotangent (E:=E) (M:=E) :=
  ⟨z.1,z.2⟩

lemma cotangentFlat_inCoordinates (x y : E) (L : E →L[ℝ] ℝ) :
    inCoordinates E (TangentSpace 𝓘(ℝ,E)) ℝ (Bundle.Trivial E ℝ) x y x y L = L := by
  simp only [inCoordinates,TangentBundle.symmL_model_space]
  change ((Bundle.Trivial.trivialization E ℝ).continuousLinearMapAt ℝ y).comp
    (L.comp (ContinuousLinearMap.id ℝ E)) = L
  rw [Bundle.Trivial.continuousLinearMapAt_trivialization,ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_id]

lemma contMDiff_cotangentFlatInv :
    ContMDiff 𝓘(ℝ,E × (E →L[ℝ] ℝ)) (cotangentModel (E:=E)) ∞
      (cotangentFlatInv (E:=E)) := by
  intro z
  rw [contMDiffAt_hom_bundle]
  refine ⟨contDiff_fst.contMDiff.contMDiffAt,?_⟩
  simpa only [cotangentFlatInv,cotangentFlat_inCoordinates] using
    (contDiff_snd.contMDiff.contMDiffAt : ContMDiffAt 𝓘(ℝ,E × (E →L[ℝ] ℝ))
      𝓘(ℝ,E →L[ℝ] ℝ) ∞ Prod.snd z)

lemma extChartAt_flat (z w : Cotangent (E:=E) (M:=E)) :
    extChartAt (cotangentModel (E:=E)) z w = cotangentFlatMap w := by
  change chartAt (E × (E →L[ℝ] ℝ)) z w = _
  rw [hom_chart]
  exact Prod.ext rfl (cotangentFlat_inCoordinates z.proj w.proj w.snd)

lemma contMDiff_cotangentFlatMap :
    ContMDiff (cotangentModel (E:=E)) 𝓘(ℝ,E × (E →L[ℝ] ℝ)) ∞
      (cotangentFlatMap (E:=E)) := by
  intro z
  have he : (extChartAt (cotangentModel (E:=E)) z : _ → _) = cotangentFlatMap :=
    funext (extChartAt_flat z)
  rw [← he]
  exact contMDiffAt_extChartAt

def cotangentFlatDiffeomorph :
    Diffeomorph (cotangentModel (E:=E)) 𝓘(ℝ,E × (E →L[ℝ] ℝ))
      (Cotangent (E:=E) (M:=E)) (E × (E →L[ℝ] ℝ)) ∞ where
  toFun := cotangentFlatMap
  invFun := cotangentFlatInv
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_cotangentFlatMap
  contMDiff_invFun := contMDiff_cotangentFlatInv

end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Set ContinuousLinearMap Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance flatCotangentDifferentialChartedSpace :
    ChartedSpace (E × (E →L[ℝ] ℝ)) (Cotangent (E:=E) (M:=E)) :=
  inferInstanceAs (ChartedSpace (ModelProd E (E →L[ℝ] ℝ)) (Cotangent (E:=E) (M:=E)))

lemma mfderiv_cotangentFlatMap (z : Cotangent (E:=E) (M:=E)) :
    (mfderiv (cotangentModel (E:=E)) 𝓘(ℝ,E × (E →L[ℝ] ℝ)) cotangentFlatMap z :
      (E × (E →L[ℝ] ℝ)) →L[ℝ] (E × (E →L[ℝ] ℝ))) = ContinuousLinearMap.id ℝ _ := by
  have he : (extChartAt (cotangentModel (E:=E)) z : _ → _) = cotangentFlatMap :=
    funext (extChartAt_flat z)
  rw [← he]
  exact mfderiv_extChartAt_self

lemma mfderiv_cotangentFlatInv (z : E × (E →L[ℝ] ℝ)) :
    (mfderiv 𝓘(ℝ,E × (E →L[ℝ] ℝ)) (cotangentModel (E:=E)) cotangentFlatInv z :
      (E × (E →L[ℝ] ℝ)) →L[ℝ] (E × (E →L[ℝ] ℝ))) = ContinuousLinearMap.id ℝ _ := by
  have hc := mfderiv_comp z
    (contMDiff_cotangentFlatMap.mdifferentiableAt (x:=cotangentFlatInv z) (by simp))
    (contMDiff_cotangentFlatInv.mdifferentiableAt (x:=z) (by simp))
  have he : (cotangentFlatMap (E:=E)) ∘ cotangentFlatInv = id := rfl
  rw [he,mfderiv_id,mfderiv_cotangentFlatMap] at hc
  erw [ContinuousLinearMap.id_comp] at hc
  exact hc.symm

theorem cotangentFlatInv_symplectic (z u v : E × (E →L[ℝ] ℝ)) :
    symplecticForm (cotangentFlatInv z)
      (mfderiv 𝓘(ℝ,E × (E →L[ℝ] ℝ)) (cotangentModel (E:=E)) cotangentFlatInv z u)
      (mfderiv 𝓘(ℝ,E × (E →L[ℝ] ℝ)) (cotangentModel (E:=E)) cotangentFlatInv z v) =
      u.2 v.1 - v.2 u.1 := by
  rw [symplecticForm_eq]
  erw [mfderiv_cotangentFlatInv]
  rfl

end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Set Bundle ContinuousLinearMap TopologicalSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma extChartAt_openVal (U : Opens E) (x y : U) :
    extChartAt 𝓘(ℝ,E) x y = (y:E) := rfl

lemma mfderiv_openVal (U : Opens E) (x : U) :
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (Subtype.val : U → E) x : E →L[ℝ] E) =
      ContinuousLinearMap.id ℝ E := by
  have he : (extChartAt 𝓘(ℝ,E) x : U → E) = Subtype.val := rfl
  rw [← he]
  exact mfderiv_extChartAt_self

omit [NormedSpace ℝ E] in
lemma openVal_chart_source (U : Opens E) (x y : U) : y ∈ (chartAt E x).source := by
  show True ∧ (y:E) ∈ (chartAt E (x:E)).source
  exact ⟨trivial,mem_univ _⟩

lemma openTangent_continuousLinearMapAt (U : Opens E) (x y : U) :
    ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) x).continuousLinearMapAt ℝ y :
      E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (openVal_chart_source U x y)]
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (Subtype.val : U → E) y = _
  exact mfderiv_openVal U y

lemma openTangent_symmL (U : Opens E) (x y : U) :
    ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) x).symmL ℝ y :
      E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
  ext v
  have h := (trivializationAt E (TangentSpace 𝓘(ℝ,E)) x).continuousLinearMapAt_symmL (R:=ℝ)
    (by rw [TangentBundle.trivializationAt_baseSet]; exact openVal_chart_source U x y) v
  rw [openTangent_continuousLinearMapAt] at h
  exact h

lemma cotangentOpen_inCoordinates (U : Opens E) (x y : U) (L : E →L[ℝ] ℝ) :
    inCoordinates E (TangentSpace 𝓘(ℝ,E)) ℝ (Bundle.Trivial U ℝ) x y x y L = L := by
  simp only [inCoordinates,openTangent_symmL]
  change ((Bundle.Trivial.trivialization U ℝ).continuousLinearMapAt ℝ y).comp
    (L.comp (ContinuousLinearMap.id ℝ E)) = L
  rw [Bundle.Trivial.continuousLinearMapAt_trivialization,ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_id]

local instance (U : Opens E) :
    ChartedSpace (E × (E →L[ℝ] ℝ)) (Cotangent (E:=E) (M:=U)) :=
  inferInstanceAs (ChartedSpace (ModelProd E (E →L[ℝ] ℝ)) (Cotangent (E:=E) (M:=U)))

def cotangentOpenFlatMap (U : Opens E) (z : Cotangent (E:=E) (M:=U)) :
    U × (E →L[ℝ] ℝ) := (z.proj,z.snd)
def cotangentOpenFlatInv (U : Opens E) (z : U × (E →L[ℝ] ℝ)) :
    Cotangent (E:=E) (M:=U) := ⟨z.1,z.2⟩

lemma extChartAt_openFlat (U : Opens E) (z w : Cotangent (E:=E) (M:=U)) :
    extChartAt (cotangentModel (E:=E)) z w = ((w.proj:E),w.snd) := by
  change chartAt (E × (E →L[ℝ] ℝ)) z w = _
  rw [hom_chart]
  exact Prod.ext rfl (cotangentOpen_inCoordinates U z.proj w.proj w.snd)

lemma contMDiff_cotangentOpenFlatInv (U : Opens E) :
    ContMDiff (cotangentModel (E:=E)) (cotangentModel (E:=E)) ∞
      (cotangentOpenFlatInv U) := by
  intro z
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_fst,?_⟩
  simpa only [cotangentOpenFlatInv,cotangentOpen_inCoordinates] using
    (contMDiffAt_snd : ContMDiffAt (cotangentModel (E:=E)) 𝓘(ℝ,E →L[ℝ] ℝ) ∞
      (Prod.snd : U × (E →L[ℝ] ℝ) → _) z)

lemma contMDiff_cotangentOpenFlatMap (U : Opens E) :
    ContMDiff (cotangentModel (E:=E)) (cotangentModel (E:=E)) ∞
      (cotangentOpenFlatMap U) := by
  intro z
  have hs : ContMDiffAt (cotangentModel (E:=E)) 𝓘(ℝ,E →L[ℝ] ℝ) ∞
      (fun w : Cotangent (E:=E) (M:=U) => (cotangentOpenFlatMap U w).2) z := by
    have h := (contDiff_snd.contMDiff.contMDiffAt).comp z
      (contMDiffAt_extChartAt : ContMDiffAt (cotangentModel (E:=E))
        𝓘(ℝ,E × (E →L[ℝ] ℝ)) ∞ (extChartAt (cotangentModel (E:=E)) z) z)
    have he : (Prod.snd ∘ (extChartAt (cotangentModel (E:=E)) z)) =
        (fun w => (cotangentOpenFlatMap U w).2) := by
      funext w
      change (extChartAt (cotangentModel (E:=E)) z w).2 = _
      rw [extChartAt_openFlat]
      rfl
    rw [he] at h
    exact h
  exact contMDiff_projection.contMDiffAt.prodMk hs

def cotangentOpenFlatDiffeomorph (U : Opens E) :
    Diffeomorph (cotangentModel (E:=E)) (cotangentModel (E:=E))
      (Cotangent (E:=E) (M:=U)) (U × (E →L[ℝ] ℝ)) ∞ where
  toFun := cotangentOpenFlatMap U
  invFun := cotangentOpenFlatInv U
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_cotangentOpenFlatMap U
  contMDiff_invFun := contMDiff_cotangentOpenFlatInv U

end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Set TopologicalSpace InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def openPhase (U : Opens E) : Opens (E × E) :=
  ⟨(U:Set E) ×ˢ univ,U.isOpen.prod isOpen_univ⟩

def openPhaseDiffeomorph (U : Opens E) :
    Diffeomorph (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E × E)
      (U × E) (openPhase U) ∞ where
  toFun z := ⟨((z.1:E),z.2),⟨z.1.property,mem_univ _⟩⟩
  invFun z := (⟨z.val.1,z.property.1⟩,z.val.2)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (openPhase U) _).mp
    have hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (Subtype.val : U → E) :=
      contMDiff_subtype_val
    exact (hv.comp (contMDiff_fst (I:=𝓘(ℝ,E)) (J:=𝓘(ℝ,E)) (M:=U) (N:=E))).prodMk_space
      (contMDiff_snd (I:=𝓘(ℝ,E)) (J:=𝓘(ℝ,E)) (M:=U) (N:=E))
  contMDiff_invFun := by
    have hv : ContMDiff 𝓘(ℝ,E × E) 𝓘(ℝ,E × E) ∞
        (Subtype.val : openPhase U → E × E) := contMDiff_subtype_val
    apply ContMDiff.prodMk
    · apply (ContMDiff.subtypeVal_comp_iff U _).mp
      exact contDiff_fst.contMDiff.comp hv
    · exact contDiff_snd.contMDiff.comp hv

def cotangentOpenRieszDiffeomorph (U : Opens E) :
    Diffeomorph (cotangentModel (E:=E)) 𝓘(ℝ,E × E)
      (Cotangent (E:=E) (M:=U)) (openPhase U) ∞ :=
  let e : Diffeomorph (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] ℝ))
      (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (U × (E →L[ℝ] ℝ)) (U × E) ∞ :=
    { toEquiv := (Equiv.refl U).prodCongr (toDual ℝ E).symm.toEquiv
      contMDiff_toFun := contMDiff_fst.prodMk
        ((toDual ℝ E).symm.contDiff.contMDiff.comp contMDiff_snd)
      contMDiff_invFun := contMDiff_fst.prodMk
        ((toDual ℝ E).contDiff.contMDiff.comp contMDiff_snd) }
  (cotangentOpenFlatDiffeomorph U).trans (e.trans (openPhaseDiffeomorph U))

lemma cotangentOpenRieszDiffeomorph_apply (U : Opens E)
    (z : Cotangent (E:=E) (M:=U)) :
    ((cotangentOpenRieszDiffeomorph U z : openPhase U) : E × E) =
      ((z.proj:E),(toDual ℝ E).symm z.snd) := rfl

end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Set TopologicalSpace ContinuousLinearMap InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local instance (U : Opens E) :
    ChartedSpace (E × (E →L[ℝ] ℝ)) (Cotangent (E:=E) (M:=U)) :=
  inferInstanceAs (ChartedSpace (ModelProd E (E →L[ℝ] ℝ)) (Cotangent (E:=E) (M:=U)))

def phaseRiesz : (E × (E →L[ℝ] ℝ)) ≃L[ℝ] (E × E) :=
  (ContinuousLinearEquiv.refl ℝ E).prodCongr (toDual ℝ E).symm.toContinuousLinearEquiv

lemma mfderiv_cotangentOpenRiesz (U : Opens E) (z : Cotangent (E:=E) (M:=U)) :
    (mfderiv (cotangentModel (E:=E)) 𝓘(ℝ,E × E) (cotangentOpenRieszDiffeomorph U) z :
      (E × (E →L[ℝ] ℝ)) →L[ℝ] (E × E)) = (phaseRiesz (E:=E)).toContinuousLinearMap := by
  have hv := contMDiff_subtype_val (I:=𝓘(ℝ,E × E)) (n:=∞) (U:=openPhase U)
  have hc := mfderiv_comp z (hv.mdifferentiableAt (by simp))
    ((cotangentOpenRieszDiffeomorph U).contMDiffAt.mdifferentiableAt (by simp))
  erw [mfderiv_openVal,ContinuousLinearMap.id_comp] at hc
  have he : (Subtype.val ∘ (cotangentOpenRieszDiffeomorph U)) =
      (phaseRiesz (E:=E)) ∘ extChartAt (cotangentModel (E:=E)) z := by
    funext w
    simp only [Function.comp_apply,extChartAt_openFlat,cotangentOpenRieszDiffeomorph_apply]
    rfl
  rw [he] at hc
  erw [mfderiv_comp (I':=𝓘(ℝ,E × (E →L[ℝ] ℝ)))] at hc
  · erw [ContinuousLinearEquiv.mfderiv_eq,mfderiv_extChartAt_self,ContinuousLinearMap.comp_id] at hc
    exact hc.symm
  · exact ((phaseRiesz (E:=E)).contDiff (n:=∞)).contMDiff.mdifferentiableAt (by simp)
  · exact (contMDiffAt_extChartAt (n:=∞)).mdifferentiableAt (by simp)

lemma cotangentOpenRiesz_symplectic (U : Opens E) (z : Cotangent (E:=E) (M:=U))
    (u v : E × (E →L[ℝ] ℝ)) :
    let du := mfderiv (cotangentModel (E:=E)) 𝓘(ℝ,E × E) (cotangentOpenRieszDiffeomorph U) z u
    let dv := mfderiv (cotangentModel (E:=E)) 𝓘(ℝ,E × E) (cotangentOpenRieszDiffeomorph U) z v
    inner ℝ du.2 dv.1 - inner ℝ dv.2 du.1 = symplecticForm z u v := by
  dsimp only
  erw [mfderiv_cotangentOpenRiesz]
  change inner ℝ ((toDual ℝ E).symm u.2) v.1 -
    inner ℝ ((toDual ℝ E).symm v.2) u.1 = _
  rw [toDual_symm_apply,toDual_symm_apply]
  erw [symplecticForm_eq]

end NearbyLagrangian.CotangentGeometry

end

end OAI
