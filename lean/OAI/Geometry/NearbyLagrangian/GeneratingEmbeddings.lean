import Mathlib
import OAI.Geometry.NearbyLagrangian.CotangentForms
import OAI.Geometry.NearbyLagrangian.Immersions

namespace OAI

/-! Generating-map immersions and closed exact Lagrangian embeddings. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.CotangentGeometry

open scoped Manifold ContDiff Topology
open Function Set Filter
variable {E F W M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

def vertical (G : M × W → ℝ) (p : M × W) : W →L[ℝ] ℝ :=
  fderiv ℝ (fun w => G (p.1, w)) p.2

def familyInChart (G : M × W → ℝ) (q : M) (p : E × W) : ℝ :=
  G ((extChartAt 𝓘(ℝ, E) q).symm p.1, p.2)

def criticalCoordinates (q : M) (p : M × W) : E × W :=
  (extChartAt 𝓘(ℝ, E) q p.1, p.2)

def criticalCoordinatesInv (q : M) (p : E × W) : M × W :=
  ((extChartAt 𝓘(ℝ, E) q).symm p.1, p.2)

lemma contMDiffAt_criticalCoordinates {q : M} {p : M × W}
    (hp : p.1 ∈ (extChartAt 𝓘(ℝ, E) q).source) :
    ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, E × W) ∞
      (criticalCoordinates (E := E) (W := W) q) p := by
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (extChartAt 𝓘(ℝ, E) q) p.1 :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hp)
  have hfst : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, E) ∞
      (Prod.fst : M × W → M) p := contMDiffAt_fst
  have hsnd : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, W) ∞
      (Prod.snd : M × W → W) p := contMDiffAt_snd
  exact (hc.comp p hfst).prodMk_space hsnd

lemma contMDiffAt_criticalCoordinatesInv {q : M} {p : E × W}
    (hp : p.1 ∈ (extChartAt 𝓘(ℝ, E) q).target) :
    ContMDiffAt 𝓘(ℝ, E × W) (𝓘(ℝ, E).prod 𝓘(ℝ, W)) ∞
      (criticalCoordinatesInv (E := E) (W := W) q) p := by
  have hc := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E)) (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) q).mem_nhds hp)
  have hfst : ContMDiffAt 𝓘(ℝ, E × W) 𝓘(ℝ, E) ∞
      (Prod.fst : E × W → E) p := contDiffAt_fst.contMDiffAt
  have hsnd : ContMDiffAt 𝓘(ℝ, E × W) 𝓘(ℝ, W) ∞
      (Prod.snd : E × W → W) p := contDiffAt_snd.contMDiffAt
  exact (hc.comp p hfst).prodMk hsnd

lemma contDiffAt_familyInChart {G : M × W → ℝ}
    (hG : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞ G)
    {q : M} {p : E × W} (hp : p.1 ∈ (extChartAt 𝓘(ℝ, E) q).target) :
    ContDiffAt ℝ ∞ (familyInChart (E := E) G q) p := by
  exact contMDiffAt_iff_contDiffAt.mp
    ((hG _).comp p (contMDiffAt_criticalCoordinatesInv hp))

lemma vertical_familyInChart {G : M × W → ℝ}
    (hG : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞ G)
    {q : M} {p : E × W} (hp : p.1 ∈ (extChartAt 𝓘(ℝ, E) q).target) :
    Generating.vertical (familyInChart (E := E) G q) p =
      vertical G (criticalCoordinatesInv (E := E) (W := W) q p) := by
  exact Generating.vertical_eq_partial
    ((contDiffAt_familyInChart hG hp).differentiableAt (by simp))

lemma vertical_chart_comp_eventually {G : M × W → ℝ}
    (hG : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞ G)
    (p : M × W) :
    (Generating.vertical (familyInChart (E := E) G p.1) ∘ criticalCoordinates (E := E) (W := W) p.1) =ᶠ[𝓝 p]
      vertical G := by
  filter_upwards [continuous_fst.continuousAt.eventually (extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) p.1)]
    with y hy
  rw [comp_apply, vertical_familyInChart hG ((extChartAt 𝓘(ℝ, E) p.1).map_source hy)]
  simp only [criticalCoordinatesInv, criticalCoordinates,
    (extChartAt 𝓘(ℝ, E) p.1).left_inv hy]

lemma vertical_familyInChart_regular {G : M × W → ℝ}
    (hG : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞ G)
    (p : M × W)
    (hreg : Function.Surjective (mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, W))
      𝓘(ℝ, W →L[ℝ] ℝ) (vertical G) p)) :
    Function.Surjective (fderiv ℝ (Generating.vertical (familyInChart (E := E) G p.1))
      (criticalCoordinates (E := E) (W := W) p.1 p)) := by
  have hp : p.1 ∈ (extChartAt 𝓘(ℝ, E) p.1).source := mem_extChartAt_source p.1
  have hf := contDiffAt_familyInChart hG (p := criticalCoordinates (E := E) p.1 p) ((extChartAt 𝓘(ℝ, E) p.1).map_source hp)
  have hfd := (hf.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
  have hv := (Generating.vertical_hasFDerivAt hfd).differentiableAt
  have hd := mfderiv_comp p hv.mdifferentiableAt
    ((contMDiffAt_criticalCoordinates hp).mdifferentiableAt (by simp))
  rw [(vertical_chart_comp_eventually hG p).mfderiv_eq] at hd
  erw [mfderiv_eq_fderiv] at hd
  intro z
  obtain ⟨a, ha⟩ := hreg z
  refine ⟨mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, E × W)
    (criticalCoordinates (E := E) (W := W) p.1) p a, ?_⟩
  exact (congrArg (fun A => A a) hd).symm.trans ha

omit [TopologicalSpace N] in
lemma generatingMap_in_chart {G : M × W → ℝ}
    (hG : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞ G)
    {q : N → M} {w : N → W} (z₀ : Cotangent (E := E) (M := M)) (y : N)
    (hy : q y ∈ (extChartAt 𝓘(ℝ, E) z₀.proj).source) :
    extChartAt (cotangentModel (E := E)) z₀ (generatingMap (E := E) G q w y) =
      Generating.generatingMap (familyInChart (E := E) G z₀.proj)
        (criticalCoordinates (E := E) (W := W) z₀.proj (q y, w y)) := by
  apply Prod.ext
  · exact extChartAt_fst _ _
  · rw [extChartAt_snd (by change q y ∈ _; simpa only [extChartAt_source] using hy)]
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun b => G (b, w y)) (q y)).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) z₀.proj).symm
        (extChartAt 𝓘(ℝ, E) z₀.proj (q y))) =
      Generating.momentum (familyInChart (E := E) G z₀.proj)
        (criticalCoordinates (E := E) (W := W) z₀.proj (q y, w y))
    have ht := (extChartAt 𝓘(ℝ, E) z₀.proj).map_source hy
    rw [Generating.momentum_eq_partial
      ((contDiffAt_familyInChart hG ht).differentiableAt (by simp))]
    have h₁ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
        (fun b => G (b, w y)) (q y) :=
      ((hG (q y, w y)).comp (q y) (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by simp)
    have h₂ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
        (extChartAt 𝓘(ℝ, E) z₀.proj).symm
        (extChartAt 𝓘(ℝ, E) z₀.proj (q y)) :=
      ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E)) (n := ∞) z₀.proj).contMDiffAt
        ((isOpen_extChartAt_target _).mem_nhds ht)).mdifferentiableAt (by simp)
    have h₁' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun b => G (b, w y))
        ((extChartAt 𝓘(ℝ, E) z₀.proj).symm (extChartAt 𝓘(ℝ, E) z₀.proj (q y))) := by
      rwa [(extChartAt 𝓘(ℝ, E) z₀.proj).left_inv hy]
    have hd := mfderiv_comp _ h₁' h₂
    rw [(extChartAt 𝓘(ℝ, E) z₀.proj).left_inv hy] at hd
    erw [mfderiv_eq_fderiv] at hd
    exact hd.symm

theorem generatingMap_mfderiv_injective {G : M × W → ℝ}
    (hG : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞ G)
    {q : N → M} {w : N → W} {x : N}
    (hq : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ q x)
    (hw : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, W) ∞ w x)
    (hcrit : ∀ᶠ y in 𝓝 x, vertical G (q y, w y) = 0)
    (hreg : Function.Surjective (mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, W))
      𝓘(ℝ, W →L[ℝ] ℝ) (vertical G) (q x, w x)))
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, F) (𝓘(ℝ, E).prod 𝓘(ℝ, W))
      (fun y => (q y, w y)) x)) :
    Function.Injective (mfderiv 𝓘(ℝ, F) (cotangentModel (E := E))
      (generatingMap (E := E) G q w) x) := by
  let p : M × W := (q x, w x)
  let j : N → E × W := fun y => criticalCoordinates (E := E) (W := W) (q x) (q y, w y)
  have hp : q x ∈ (extChartAt 𝓘(ℝ, E) (q x)).source := mem_extChartAt_source _
  have ht := (extChartAt 𝓘(ℝ, E) (q x)).map_source hp
  have hmem : ∀ᶠ y in 𝓝 x, q y ∈ (extChartAt 𝓘(ℝ, E) (q x)).source :=
    hq.continuousAt.eventually (extChartAt_source_mem_nhds (q x))
  have hj : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E × W) ∞ j x :=
    (contMDiffAt_criticalCoordinates hp).comp x (hq.prodMk hw)
  have hjinj : Function.Injective (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E × W) j x) := by
    have he : (criticalCoordinatesInv (E := E) (W := W) (q x) ∘ j) =ᶠ[𝓝 x] (fun y => (q y, w y)) := by
      filter_upwards [hmem] with y hy
      simp only [comp_apply, criticalCoordinatesInv, j, criticalCoordinates,
        (extChartAt 𝓘(ℝ, E) (q x)).left_inv hy]
    have hd := mfderiv_comp x
      ((contMDiffAt_criticalCoordinatesInv ht).mdifferentiableAt (by simp))
      (hj.mdifferentiableAt (by simp))
    rw [he.mfderiv_eq] at hd
    intro a b hab
    apply hinj
    apply (tangentSpaceCast (𝓘(ℝ, E).prod 𝓘(ℝ, W)) (q x, w x)
      ((criticalCoordinatesInv (q x) ∘ j) x)).injective
    exact (DFunLike.congr_fun hd a).trans
      ((congrArg (mfderiv 𝓘(ℝ, E × W) (𝓘(ℝ, E).prod 𝓘(ℝ, W))
        (criticalCoordinatesInv (q x)) (j x)) hab).trans (DFunLike.congr_fun hd b).symm)
  have hjcrit : ∀ᶠ y in 𝓝 x, Generating.vertical (familyInChart (E := E) G (q x)) (j y) = 0 := by
    filter_upwards [hmem, hcrit] with y hy hcy
    rw [vertical_familyInChart hG ((extChartAt 𝓘(ℝ, E) (q x)).map_source hy)]
    simpa only [criticalCoordinatesInv, j, criticalCoordinates,
      (extChartAt 𝓘(ℝ, E) (q x)).left_inv hy] using hcy
  have hlinj := Generating.generatingMap_mfderiv_injective
    (contDiffAt_familyInChart hG ht) hj hjcrit
    (vertical_familyInChart_regular hG p hreg) hjinj
  let i := generatingMap (E := E) G q w
  have hi : ContMDiffAt 𝓘(ℝ, F) (cotangentModel (E := E)) ∞ i x :=
    contMDiffAt_generatingMap (hG _) hq hw
  have he : (extChartAt (cotangentModel (E := E)) (i x) ∘ i) =ᶠ[𝓝 x]
      (Generating.generatingMap (familyInChart (E := E) G (q x)) ∘ j) := by
    filter_upwards [hmem] with y hy
    exact generatingMap_in_chart hG (i x) y hy
  have hd := mfderiv_comp x
    (contMDiffAt_extChartAt (I := cotangentModel (E := E)) (n := ∞)
      |>.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp))
  rw [he.mfderiv_eq] at hd
  intro a b hab
  apply hlinj
  apply (tangentSpaceCast 𝓘(ℝ, E × (E →L[ℝ] ℝ))
    ((Generating.generatingMap (familyInChart G (q x)) ∘ j) x)
    ((extChartAt (cotangentModel (E := E)) (i x) ∘ i) x)).injective
  exact (DFunLike.congr_fun hd a).trans
    ((congrArg (mfderiv (cotangentModel (E := E))
      𝓘(ℝ, E × (E →L[ℝ] ℝ)) (extChartAt (cotangentModel (E := E)) (i x)) (i x)) hab).trans
      (DFunLike.congr_fun hd b).symm)

local instance generatingEmbeddingsChartedSpace :
    ChartedSpace (E × (E →L[ℝ] ℝ)) (Cotangent (E := E) (M := M)) :=
  inferInstanceAs (ChartedSpace (ModelProd E (E →L[ℝ] ℝ)) (Cotangent (E := E) (M := M)))

local instance generatingEmbeddingsIsManifold :
    IsManifold 𝓘(ℝ, E × (E →L[ℝ] ℝ)) ∞ (Cotangent (E := E) (M := M)) := by
  have h : IsManifold (cotangentModel (E := E)) ∞ (Cotangent (E := E) (M := M)) :=
    inferInstanceAs (IsManifold (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (Bundle.TotalSpace (E →L[ℝ] ℝ) (fun q : M => TangentSpace 𝓘(ℝ, E) q →L[ℝ] ℝ)))
  rw [modelWithCornersSelf_prod]
  exact h

theorem generatingMap_isImmersion [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {G : M × W → ℝ} (hG : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞ G)
    {q : N → M} {w : N → W}
    (hq : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ q)
    (hw : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, W) ∞ w)
    (hcrit : ∀ y, vertical G (q y, w y) = 0)
    (hreg : ∀ x, Function.Surjective (mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, W))
      𝓘(ℝ, W →L[ℝ] ℝ) (vertical G) (q x, w x)))
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, F) (𝓘(ℝ, E).prod 𝓘(ℝ, W))
      (fun y => (q y, w y)) x)) :
    Manifold.IsImmersion 𝓘(ℝ, F) (cotangentModel (E := E)) ∞
      (generatingMap (E := E) G q w) := by
  have hi : ContMDiff 𝓘(ℝ, F) (cotangentModel (E := E)) ∞
      (generatingMap (E := E) G q w) :=
    fun x => contMDiffAt_generatingMap (hG _) (hq x) (hw x)
  have hiD := fun x => generatingMap_mfderiv_injective hG (hq x) (hw x)
    (Filter.Eventually.of_forall hcrit) (hreg x) (hinj x)
  unfold cotangentModel at hi hiD ⊢
  rw [← modelWithCornersSelf_prod] at hi hiD ⊢
  exact LocalGeometry.manifold_isImmersion_of_injective_mfderiv hi hiD

end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.CotangentGeometry

open scoped Manifold ContDiff Topology
open Function Set Filter
variable {E F W M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

theorem generatingMap_isotropic {G : M × W → ℝ}
    (hG : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞ G)
    {q : N → M} {w : N → W} {x : N}
    (hq : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ q x)
    (hw : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, W) ∞ w x)
    (hcrit : ∀ᶠ y in 𝓝 x, vertical G (q y, w y) = 0)
    (a b : TangentSpace 𝓘(ℝ, F) x) :
    symplecticForm (generatingMap (E := E) G q w x)
      (mfderiv 𝓘(ℝ, F) (cotangentModel (E := E)) (generatingMap (E := E) G q w) x a)
      (mfderiv 𝓘(ℝ, F) (cotangentModel (E := E)) (generatingMap (E := E) G q w) x b) = 0 := by
  let j : N → E × W := fun y => criticalCoordinates (E := E) (W := W) (q x) (q y, w y)
  have hp : q x ∈ (extChartAt 𝓘(ℝ, E) (q x)).source := mem_extChartAt_source _
  have ht := (extChartAt 𝓘(ℝ, E) (q x)).map_source hp
  have hmem : ∀ᶠ y in 𝓝 x, q y ∈ (extChartAt 𝓘(ℝ, E) (q x)).source :=
    hq.continuousAt.eventually (extChartAt_source_mem_nhds (q x))
  have hj : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E × W) ∞ j x :=
    (contMDiffAt_criticalCoordinates hp).comp x (hq.prodMk hw)
  have hjcrit : ∀ᶠ y in 𝓝 x, Generating.vertical (familyInChart (E := E) G (q x)) (j y) = 0 := by
    filter_upwards [hmem, hcrit] with y hy hcy
    rw [vertical_familyInChart hG ((extChartAt 𝓘(ℝ, E) (q x)).map_source hy)]
    simpa only [criticalCoordinatesInv, j, criticalCoordinates,
      (extChartAt 𝓘(ℝ, E) (q x)).left_inv hy] using hcy
  have hiso := Generating.generatingMap_mfderiv_isotropic
    (contDiffAt_familyInChart hG ht) hj hjcrit a b
  let i := generatingMap (E := E) G q w
  have hi : ContMDiffAt 𝓘(ℝ, F) (cotangentModel (E := E)) ∞ i x :=
    contMDiffAt_generatingMap (hG _) hq hw
  have he : (extChartAt (cotangentModel (E := E)) (i x) ∘ i) =ᶠ[𝓝 x]
      (Generating.generatingMap (familyInChart (E := E) G (q x)) ∘ j) := by
    filter_upwards [hmem] with y hy
    exact generatingMap_in_chart hG (i x) y hy
  have hd := mfderiv_comp x
    (contMDiffAt_extChartAt (I := cotangentModel (E := E)) (n := ∞)
      |>.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp))
  erw [he.mfderiv_eq, mfderiv_extChartAt_self, ContinuousLinearMap.id_comp] at hd
  rw [hd] at hiso
  rw [symplecticForm_eq]
  exact hiso

theorem generatingMap_closed_exact_embedding
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [CompactSpace N] [T2Space M]
    {G : M × W → ℝ} (hG : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞ G)
    {q : N → M} {w : N → W}
    (hq : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ q)
    (hw : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, W) ∞ w)
    (hcrit : ∀ y, vertical G (q y, w y) = 0)
    (hreg : ∀ x, Function.Surjective (mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, W))
      𝓘(ℝ, W →L[ℝ] ℝ) (vertical G) (q x, w x)))
    (hj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, F) (𝓘(ℝ, E).prod 𝓘(ℝ, W))
      (fun y => (q y, w y)) x))
    (hinj : Function.Injective (generatingMap (E := E) G q w)) :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, F) (cotangentModel (E := E)) ∞
      (generatingMap (E := E) G q w) ∧
    IsCompact (Set.range (generatingMap (E := E) G q w)) ∧
    (∀ x (a b : TangentSpace 𝓘(ℝ, F) x),
      symplecticForm (generatingMap (E := E) G q w x)
        (mfderiv 𝓘(ℝ, F) (cotangentModel (E := E)) (generatingMap (E := E) G q w) x a)
        (mfderiv 𝓘(ℝ, F) (cotangentModel (E := E)) (generatingMap (E := E) G q w) x b) = 0) ∧
    ∃ f : N → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f ∧
      ∀ x (a : TangentSpace 𝓘(ℝ, F) x),
        liouville (generatingMap (E := E) G q w x)
          (mfderiv 𝓘(ℝ, F) (cotangentModel (E := E)) (generatingMap (E := E) G q w) x a) =
        mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ) f x a := by
  let : T2Space (Cotangent (E := E) (M := M)) := bundleTotalSpace_t2Space
  have hi : ContMDiff 𝓘(ℝ, F) (cotangentModel (E := E)) ∞
      (generatingMap (E := E) G q w) :=
    fun x => contMDiffAt_generatingMap (hG _) (hq x) (hw x)
  refine ⟨⟨generatingMap_isImmersion hG hq hw hcrit hreg hj,
      (hi.continuous.isClosedEmbedding hinj).isEmbedding⟩,
    isCompact_range hi.continuous, ?_, fun y => G (q y, w y), hG.comp (hq.prodMk hw), ?_⟩
  · intro x a b
    exact generatingMap_isotropic hG (hq x) (hw x) (Eventually.of_forall hcrit) a b
  · intro x a
    exact generatingMap_primitive (hG _) (hq x) (hw x) (hcrit x) a

end NearbyLagrangian.CotangentGeometry

end

end OAI
