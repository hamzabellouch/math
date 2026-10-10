import Mathlib
import OAI.Geometry.NearbyLagrangian.CotangentModel

namespace OAI

/-! Cotangent bundle coordinates, Liouville forms and generating maps. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.CotangentGeometry

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

abbrev Cotangent := Bundle.TotalSpace (E →L[ℝ] ℝ)
  (fun q : M => TangentSpace 𝓘(ℝ, E) q →L[ℝ] ℝ)

abbrev cotangentModel := 𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℝ)

local instance : ChartedSpace (E × (E →L[ℝ] ℝ)) (Cotangent (E := E) (M := M)) :=
  inferInstanceAs (ChartedSpace (ModelProd E (E →L[ℝ] ℝ)) (Cotangent (E := E) (M := M)))

def differentialMap (f : N → M → ℝ) (g : N → M) : N → Cotangent (E := E) (M := M) :=
  fun x => ⟨g x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f x) (g x)⟩

lemma contMDiffAt_differentialMap {f : N → M → ℝ} {g : N → M} {x : N}
    (hf : ContMDiffAt (𝓘(ℝ, F).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry f) (x, g x))
    (hg : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ g x) :
    ContMDiffAt 𝓘(ℝ, F) (cotangentModel (E := E)) ∞ (differentialMap (E := E) f g) x := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨hg, ?_⟩
  have hd := hf.mfderiv f g hg (by simp)
  convert! hd using 1
  funext y
  simp only [differentialMap, inTangentCoordinates, inCoordinates,
    TangentBundle.continuousLinearMapAt_model_space]
  change ((Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ (g y)).comp _ = _
  rw [Bundle.Trivial.continuousLinearMapAt_trivialization]
  rfl

def projection (z : Cotangent (E := E) (M := M)) : M := z.proj

def liouville (z : Cotangent (E := E) (M := M)) :
    TangentSpace (cotangentModel (E := E)) z →L[ℝ] ℝ :=
  z.snd.comp (mfderiv (cotangentModel (E := E)) 𝓘(ℝ, E) projection z)

lemma contMDiff_projection :
    ContMDiff (cotangentModel (E := E)) 𝓘(ℝ, E) ∞ (projection (E := E) (M := M)) :=
  Bundle.contMDiff_proj (fun q : M => TangentSpace 𝓘(ℝ, E) q →L[ℝ] ℝ)

omit [IsManifold 𝓘(ℝ, F) ∞ N] in

lemma liouville_apply_mfderiv {i : N → Cotangent (E := E) (M := M)} {x : N}
    (hi : MDifferentiableAt 𝓘(ℝ, F) (cotangentModel (E := E)) i x)
    (v : TangentSpace 𝓘(ℝ, F) x) :
    liouville (i x) (mfderiv 𝓘(ℝ, F) (cotangentModel (E := E)) i x v) =
      (i x).snd (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) (projection ∘ i) x v) := by
  rw [mfderiv_comp_apply x (contMDiff_projection.mdifferentiableAt (by simp)) hi]
  rfl

lemma liouville_apply_differentialMap {f : N → M → ℝ} {g : N → M} {x : N}
    (hf : ContMDiffAt (𝓘(ℝ, F).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry f) (x, g x))
    (hg : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ g x)
    (v : TangentSpace 𝓘(ℝ, F) x) :
    liouville (differentialMap (E := E) f g x)
      (mfderiv 𝓘(ℝ, F) (cotangentModel (E := E)) (differentialMap (E := E) f g) x v) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f x) (g x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) g x v) := by
  exact liouville_apply_mfderiv
    ((contMDiffAt_differentialMap hf hg).mdifferentiableAt (by simp)) v

lemma extChartAt_snd {z₀ z : Cotangent (E := E) (M := M)}
    (hz : z.proj ∈ (chartAt E z₀.proj).source) :
    (extChartAt (cotangentModel (E := E)) z₀ z).2 =
      z.snd.comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (extChartAt 𝓘(ℝ, E) z₀.proj).symm (extChartAt 𝓘(ℝ, E) z₀.proj z.proj)) := by
  change (chartAt (E × (E →L[ℝ] ℝ)) z₀ z).2 = _
  rw [hom_chart]
  simp only [inCoordinates]
  change ((Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ z.proj).comp _ = _
  rw [Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_comp,
    TangentBundle.symmL_trivializationAt hz]
  simp only [modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ]
  rfl

lemma extChartAt_fst (z₀ z : Cotangent (E := E) (M := M)) :
    (extChartAt (cotangentModel (E := E)) z₀ z).1 =
      extChartAt 𝓘(ℝ, E) z₀.proj z.proj := by
  change (chartAt (E × (E →L[ℝ] ℝ)) z₀ z).1 = chartAt E z₀.proj z.proj
  rw [hom_chart]

lemma projection_extChartAt_symm {z : Cotangent (E := E) (M := M)}
    {x : E × (E →L[ℝ] ℝ)}
    (hx : x ∈ (extChartAt (cotangentModel (E := E)) z).target) :
    projection ((extChartAt (cotangentModel (E := E)) z).symm x) =
      (extChartAt 𝓘(ℝ, E) z.proj).symm x.1 := by
  have ht := hx
  rw [FiberBundle.extChartAt_target] at ht
  rw [FiberBundle.extChartAt]
  change ((trivializationAt (E →L[ℝ] ℝ)
    (fun q : M => TangentSpace 𝓘(ℝ, E) q →L[ℝ] ℝ) z.proj).toPartialEquiv.symm
    ((extChartAt 𝓘(ℝ, E) z.proj).symm x.1, x.2)).proj = _
  exact (trivializationAt (E →L[ℝ] ℝ)
    (fun q : M => TangentSpace 𝓘(ℝ, E) q →L[ℝ] ℝ) z.proj).proj_symm_apply' ht.1.2

def liouvilleInChart (z : Cotangent (E := E) (M := M)) (x : E × (E →L[ℝ] ℝ)) :
    (E × (E →L[ℝ] ℝ)) →L[ℝ] ℝ :=
  (liouville ((extChartAt (cotangentModel (E := E)) z).symm x)).comp
    (mfderiv 𝓘(ℝ, E × (E →L[ℝ] ℝ)) (cotangentModel (E := E))
      (extChartAt (cotangentModel (E := E)) z).symm x)

lemma covector_extChartAt_symm {z : Cotangent (E := E) (M := M)}
    {x : E × (E →L[ℝ] ℝ)}
    (hx : x ∈ (extChartAt (cotangentModel (E := E)) z).target) :
    ((extChartAt (cotangentModel (E := E)) z).symm x).snd.comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) z.proj).symm x.1) = x.2 := by
  have ht := hx
  rw [FiberBundle.extChartAt_target] at ht
  have hp := projection_extChartAt_symm hx
  have hmem : ((extChartAt (cotangentModel (E := E)) z).symm x).proj ∈
      (chartAt E z.proj).source := by
    change projection _ ∈ _
    rw [hp]
    simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ, E) z.proj).map_target ht.1.1
  have hs := extChartAt_snd hmem
  rw [(extChartAt (cotangentModel (E := E)) z).right_inv hx] at hs
  change x.2 = _ at hs
  have hfst : extChartAt 𝓘(ℝ, E) z.proj
      ((extChartAt (cotangentModel (E := E)) z).symm x).proj = x.1 := by
    change extChartAt 𝓘(ℝ, E) z.proj (projection _) = x.1
    rw [hp, (extChartAt 𝓘(ℝ, E) z.proj).right_inv ht.1.1]
  rw [hfst] at hs
  exact hs.symm

lemma mdifferentiableAt_extChartAt_symm {z : Cotangent (E := E) (M := M)}
    {x : E × (E →L[ℝ] ℝ)}
    (hx : x ∈ (extChartAt (cotangentModel (E := E)) z).target) :
    MDifferentiableAt 𝓘(ℝ, E × (E →L[ℝ] ℝ)) (cotangentModel (E := E))
      (extChartAt (cotangentModel (E := E)) z).symm x :=
  ((contMDiffOn_extChartAt_symm (n := ∞) z).contMDiffAt
    ((isOpen_extChartAt_target z).mem_nhds hx)).mdifferentiableAt (by simp)

lemma mfderiv_projection_extChartAt_symm {z : Cotangent (E := E) (M := M)}
    {x : E × (E →L[ℝ] ℝ)}
    (hx : x ∈ (extChartAt (cotangentModel (E := E)) z).target) :
    mfderiv 𝓘(ℝ, E × (E →L[ℝ] ℝ)) 𝓘(ℝ, E)
      (projection ∘ (extChartAt (cotangentModel (E := E)) z).symm) x =
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) z.proj).symm x.1).comp
      (ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)) := by
  have ht := hx
  rw [FiberBundle.extChartAt_target] at ht
  have hb : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) z.proj).symm x.1 :=
    ((contMDiffOn_extChartAt_symm (n := ∞) z.proj).contMDiffAt
      ((isOpen_extChartAt_target z.proj).mem_nhds ht.1.1)).mdifferentiableAt (by simp)
  have heq : (projection ∘ (extChartAt (cotangentModel (E := E)) z).symm) =ᶠ[𝓝 x]
      ((extChartAt 𝓘(ℝ, E) z.proj).symm ∘ Prod.fst) := by
    filter_upwards [(isOpen_extChartAt_target z).mem_nhds hx] with y hy
    exact projection_extChartAt_symm hy
  rw [heq.mfderiv_eq]
  change mfderiv 𝓘(ℝ, E × (E →L[ℝ] ℝ)) 𝓘(ℝ, E)
    ((extChartAt 𝓘(ℝ, E) z.proj).symm ∘ Prod.fst) x = _
  have hf : MDifferentiableAt 𝓘(ℝ, E × (E →L[ℝ] ℝ)) 𝓘(ℝ, E) Prod.fst x :=
    differentiableAt_fst.mdifferentiableAt
  rw [mfderiv_comp x hb hf]
  congr 1
  rw [mfderiv_eq_fderiv, fderiv_fst]

theorem liouvilleInChart_eq {z : Cotangent (E := E) (M := M)}
    {x : E × (E →L[ℝ] ℝ)}
    (hx : x ∈ (extChartAt (cotangentModel (E := E)) z).target) :
    liouvilleInChart z x = x.2.comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)) := by
  have hi := mdifferentiableAt_extChartAt_symm hx
  have hp : MDifferentiableAt (cotangentModel (E := E)) 𝓘(ℝ, E)
      projection ((extChartAt (cotangentModel (E := E)) z).symm x) :=
    contMDiff_projection.mdifferentiableAt (by simp)
  unfold liouvilleInChart liouville
  erw [ContinuousLinearMap.comp_assoc, ← mfderiv_comp x hp hi,
    mfderiv_projection_extChartAt_symm hx, ← ContinuousLinearMap.comp_assoc,
    covector_extChartAt_symm hx]
  rfl

def coordinateLiouville : (E × (E →L[ℝ] ℝ)) →L[ℝ] ((E × (E →L[ℝ] ℝ)) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (E × (E →L[ℝ] ℝ)) E ℝ).flip
    (ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ))).comp
      (ContinuousLinearMap.snd ℝ E (E →L[ℝ] ℝ))

def symplecticForm (z : Cotangent (E := E) (M := M))
    (u v : TangentSpace (cotangentModel (E := E)) z) : ℝ :=
  let c := extChartAt (cotangentModel (E := E)) z
  let dc := mfderiv (cotangentModel (E := E)) 𝓘(ℝ, E × (E →L[ℝ] ℝ)) c z
  let dlam := fderiv ℝ (liouvilleInChart z) (c z)
  dlam (dc u) (dc v) - dlam (dc v) (dc u)

theorem symplecticForm_eq (z : Cotangent (E := E) (M := M))
    (u v : TangentSpace (cotangentModel (E := E)) z) :
    symplecticForm z u v = u.2 v.1 - v.2 u.1 := by
  have heq : liouvilleInChart z =ᶠ[𝓝 (extChartAt (cotangentModel (E := E)) z z)]
      coordinateLiouville (E := E) := by
    filter_upwards [extChartAt_target_mem_nhds z] with x hx
    exact liouvilleInChart_eq hx
  dsimp only [symplecticForm]
  erw [mfderiv_extChartAt_self, heq.fderiv_eq, ContinuousLinearMap.fderiv]
  rfl

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

def generatingMap (G : M × W → ℝ) (q : N → M) (w : N → W) :
    N → Cotangent (E := E) (M := M) :=
  differentialMap (E := E) (fun x b => G (b, w x)) q

lemma contMDiffAt_generatingMap {G : M × W → ℝ} {q : N → M} {w : N → W} {x : N}
    (hG : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞ G (q x, w x))
    (hq : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ q x)
    (hw : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, W) ∞ w x) :
    ContMDiffAt 𝓘(ℝ, F) (cotangentModel (E := E)) ∞
      (generatingMap (E := E) G q w) x := by
  apply contMDiffAt_differentialMap _ hq
  exact hG.comp (x, q x) (contMDiffAt_snd.prodMk (hw.comp _ contMDiffAt_fst))

theorem generatingMap_primitive {G : M × W → ℝ} {q : N → M} {w : N → W} {x : N}
    (hG : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞ G (q x, w x))
    (hq : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ q x)
    (hw : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, W) ∞ w x)
    (hcrit : fderiv ℝ (fun a : W => G (q x, a)) (w x) = 0)
    (v : TangentSpace 𝓘(ℝ, F) x) :
    liouville (generatingMap (E := E) G q w x)
      (mfderiv 𝓘(ℝ, F) (cotangentModel (E := E)) (generatingMap (E := E) G q w) x v) =
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (fun y => G (q y, w y)) x v := by
  have hGG : ContMDiffAt (𝓘(ℝ, F).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun xb : N × M => G (xb.2, w xb.1)) (x, q x) :=
    hG.comp (x, q x) (contMDiffAt_snd.prodMk (hw.comp _ contMDiffAt_fst))
  change liouville (differentialMap (E := E) (fun y b => G (b, w y)) q x)
    (mfderiv _ _ (differentialMap (E := E) (fun y b => G (b, w y)) q) x v) = _
  rw [liouville_apply_differentialMap hGG hq]
  have hqd := hq.mdifferentiableAt (by simp)
  have hwd := hw.mdifferentiableAt (by simp)
  have hGd := hG.mdifferentiableAt (by simp)
  have hd : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (fun y => G (q y, w y)) x v =
      mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) G (q x, w x)
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) q x v, mfderiv 𝓘(ℝ, F) 𝓘(ℝ, W) w x v) := by
    exact (mfderiv_comp_apply x hGd (hqd.prodMk hwd) v).trans (by
      rw [mfderiv_prodMk hqd hwd]
      rfl)
  rw [hd]
  erw [mfderiv_prod_eq_add_apply hGd, mfderiv_eq_fderiv, hcrit]
  exact (add_zero _).symm

end NearbyLagrangian.CotangentGeometry

end

end OAI
