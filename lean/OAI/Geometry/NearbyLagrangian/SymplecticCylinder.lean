import Mathlib
import OAI.Geometry.NearbyLagrangian.HamiltonianCharts
import OAI.Geometry.NearbyLagrangian.PolarCharts
import OAI.Geometry.NearbyLagrangian.ProductSymplectic
import OAI.Geometry.NearbyLagrangian.CotangentLifts
import OAI.Geometry.NearbyLagrangian.FlatCotangent

namespace OAI

/-! Symplectic radial cylinder charts and central spatial images. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian
open scoped Manifold ContDiff Topology
open ContinuousLinearMap Function
variable {V W X A B C M N P : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  {I : ModelWithCorners ℝ V A} {J : ModelWithCorners ℝ W B} {K : ModelWithCorners ℝ X C}
  [TopologicalSpace M] [ChartedSpace A M]
  [TopologicalSpace N] [ChartedSpace B N]
  [TopologicalSpace P] [ChartedSpace C P]

theorem diffeomorph_preservesForm_trans
    (e : Diffeomorph I J M N ∞) (f : Diffeomorph J K N P ∞)
    (formM : M → V → V → ℝ) (formN : N → W → W → ℝ) (formP : P → X → X → ℝ)
    (he : ∀ x u v, formN (e x) (mfderiv I J e x u) (mfderiv I J e x v) = formM x u v)
    (hf : ∀ x u v, formP (f x) (mfderiv J K f x u) (mfderiv J K f x v) = formN x u v) :
    ∀ x u v, formP ((e.trans f) x) (mfderiv I K (e.trans f) x u)
      (mfderiv I K (e.trans f) x v) = formM x u v := by
  intro x u v
  have h : (e.trans f : M → P) = f ∘ e := rfl
  rw [h,mfderiv_comp x (f.contMDiffAt.mdifferentiableAt (by simp))
    (e.contMDiffAt.mdifferentiableAt (by simp))]
  change formP (f (e x)) (mfderiv J K f (e x) (mfderiv I J e x u))
    (mfderiv J K f (e x) (mfderiv I J e x v)) = _
  exact (hf (e x) _ _).trans (he x u v)

theorem diffeomorph_preservesForm_symm
    (e : Diffeomorph I J M N ∞)
    (formM : M → V → V → ℝ) (formN : N → W → W → ℝ)
    (he : ∀ x u v, formN (e x) (mfderiv I J e x u) (mfderiv I J e x v) = formM x u v) :
    ∀ x u v, formM (e.symm x) (mfderiv J I e.symm x u) (mfderiv J I e.symm x v) = formN x u v := by
  intro x u v
  have hi := diffeomorph_mfderiv_inverse e.symm x
  have hu := congrArg (fun L : W →L[ℝ] W => L u) hi
  have hv := congrArg (fun L : W →L[ℝ] W => L v) hi
  change mfderiv I J e (e.symm x) (mfderiv J I e.symm x u) = u at hu
  change mfderiv I J e (e.symm x) (mfderiv J I e.symm x v) = v at hv
  have h := he (e.symm x) (mfderiv J I e.symm x u) (mfderiv J I e.symm x v)
  erw [hu,hv] at h
  simpa only [e.apply_symm_apply] using h.symm

theorem diffeomorph_preservesForm_prodRight
    (e : Diffeomorph J K N P ∞)
    (formM : M → V → V → ℝ) (formN : N → W → W → ℝ) (formP : P → X → X → ℝ)
    (he : ∀ x u v, formP (e x) (mfderiv J K e x u) (mfderiv J K e x v) = formN x u v) :
    ∀ x u v,
      let f := generalProductDiffeomorph (Diffeomorph.refl I M ∞) e
      let du := mfderiv (I.prod J) (I.prod K) f x u
      let dv := mfderiv (I.prod J) (I.prod K) f x v
      formM (f x).1 du.1 dv.1 + formP (f x).2 du.2 dv.2 =
        formM x.1 u.1 v.1 + formN x.2 u.2 v.2 := by
  intro x u v
  dsimp only
  have hf : (generalProductDiffeomorph (Diffeomorph.refl I M ∞) e : M × N → M × P) = Prod.map id e := rfl
  rw [hf, mfderiv_prodMap mdifferentiableAt_id (e.contMDiffAt.mdifferentiableAt (by simp)),mfderiv_id]
  change formM x.1 u.1 v.1 + formP (e x.2) (mfderiv J K e x.2 u.2) (mfderiv J K e x.2 v.2) = _
  erw [he]

end NearbyLagrangian

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Set TopologicalSpace InnerProductSpace
variable {E F G M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance symplecticCylinderRadialBaseChartedSpace (U : Opens F) : ChartedSpace (E × F) (M × U) :=
  inferInstanceAs (ChartedSpace (ModelProd E F) (M × U))
local instance symplecticCylinderRadialBaseManifold (U : Opens F) : IsManifold 𝓘(ℝ,E × F) ∞ (M × U) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I:=𝓘(ℝ,E)) (I':=𝓘(ℝ,F)) M U
local instance symplecticCylinderRadialCotangentChartedSpace (A B : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
    [TopologicalSpace B] [ChartedSpace A B] [IsManifold 𝓘(ℝ,A) ∞ B] :
    ChartedSpace (A × (A →L[ℝ] ℝ)) (Cotangent (E:=A) (M:=B)) :=
  inferInstanceAs (ChartedSpace (ModelProd A (A →L[ℝ] ℝ)) (Cotangent (E:=A) (M:=B)))

def radialCotangentDiffeomorph (U : Opens F) :
    Diffeomorph ((cotangentModel (E:=E)).prod 𝓘(ℝ,F × F))
      ((cotangentModel (E:=E)).prod (cotangentModel (E:=F)))
      (Cotangent (E:=E) (M:=M) × openPhase U)
      (Cotangent (E:=E) (M:=M) × Cotangent (E:=F) (M:=U)) ∞ :=
  generalProductDiffeomorph (Diffeomorph.refl (cotangentModel (E:=E)) (Cotangent (E:=E) (M:=M)) ∞)
    (cotangentOpenRieszDiffeomorph U).symm

def cotangentCylinderChart (U : Opens F) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × F) 𝓘(ℝ,G) (M × U) W ∞) :
    Diffeomorph ((cotangentModel (E:=E)).prod 𝓘(ℝ,F × F)) 𝓘(ℝ,G × G)
      (Cotangent (E:=E) (M:=M) × openPhase U) (openPhase W) ∞ :=
  (radialCotangentDiffeomorph U).trans
    ((cotangentProductDiffeomorph (E:=E) (F:=F) (M:=M) (N:=U)).symm.trans
      ((cotangentLift e).trans (cotangentOpenRieszDiffeomorph W)))

lemma radialCotangentDiffeomorph_symplectic (U : Opens F)
    (z : Cotangent (E:=E) (M:=M) × openPhase U)
    (u v : (E × (E →L[ℝ] ℝ)) × (F × F)) :
    let f := radialCotangentDiffeomorph (E:=E) (M:=M) U
    let du := mfderiv ((cotangentModel (E:=E)).prod 𝓘(ℝ,F × F))
      ((cotangentModel (E:=E)).prod (cotangentModel (E:=F))) f z u
    let dv := mfderiv ((cotangentModel (E:=E)).prod 𝓘(ℝ,F × F))
      ((cotangentModel (E:=E)).prod (cotangentModel (E:=F))) f z v
    symplecticForm (f z).1 du.1 dv.1 + symplecticForm (f z).2 du.2 dv.2 =
      symplecticForm z.1 u.1 v.1 + (inner ℝ u.2.2 v.2.1 - inner ℝ v.2.2 u.2.1) := by
  have hi := diffeomorph_preservesForm_symm (cotangentOpenRieszDiffeomorph U)
    (fun x a b => symplecticForm x a b)
    (fun _ a b => inner ℝ a.2 b.1 - inner ℝ b.2 a.1)
    (cotangentOpenRiesz_symplectic U)
  exact diffeomorph_preservesForm_prodRight (cotangentOpenRieszDiffeomorph U).symm
    (fun x a b => symplecticForm x a b)
    (fun _ a b => inner ℝ a.2 b.1 - inner ℝ b.2 a.1)
    (fun x a b => symplecticForm x a b) hi z u v

omit [CompleteSpace F] in
lemma cotangentLift_openRiesz_symplectic (U : Opens F) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × F) 𝓘(ℝ,G) (M × U) W ∞)
    (z : Cotangent (E:=E × F) (M:=M × U))
    (u v : (E × F) × ((E × F) →L[ℝ] ℝ)) :
    let f := (cotangentLift e).trans (cotangentOpenRieszDiffeomorph W)
    let du := mfderiv (cotangentModel (E:=E × F)) 𝓘(ℝ,G × G) f z u
    let dv := mfderiv (cotangentModel (E:=E × F)) 𝓘(ℝ,G × G) f z v
    inner ℝ du.2 dv.1 - inner ℝ dv.2 du.1 = symplecticForm z u v := by
  exact diffeomorph_preservesForm_trans (cotangentLift e) (cotangentOpenRieszDiffeomorph W)
    (fun x a b => symplecticForm x a b) (fun x a b => symplecticForm x a b)
    (fun _ a b => inner ℝ a.2 b.1 - inner ℝ b.2 a.1)
    (cotangentLift_symplectic e) (cotangentOpenRiesz_symplectic W) z u v

theorem cotangentCylinderChart_symplectic (U : Opens F) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × F) 𝓘(ℝ,G) (M × U) W ∞)
    (z : Cotangent (E:=E) (M:=M) × openPhase U)
    (u v : (E × (E →L[ℝ] ℝ)) × (F × F)) :
    let f := cotangentCylinderChart U W e
    let du := mfderiv ((cotangentModel (E:=E)).prod 𝓘(ℝ,F × F)) 𝓘(ℝ,G × G) f z u
    let dv := mfderiv ((cotangentModel (E:=E)).prod 𝓘(ℝ,F × F)) 𝓘(ℝ,G × G) f z v
    inner ℝ du.2 dv.1 - inner ℝ dv.2 du.1 =
      symplecticForm z.1 u.1 v.1 + inner ℝ u.2.2 v.2.1 - inner ℝ v.2.2 u.2.1 := by
  have h₂ := diffeomorph_preservesForm_trans
    (cotangentProductDiffeomorph (E:=E) (F:=F) (M:=M) (N:=U)).symm
    ((cotangentLift e).trans (cotangentOpenRieszDiffeomorph W))
    (fun x a b => symplecticForm x.1 a.1 b.1 + symplecticForm x.2 a.2 b.2)
    (fun x a b => symplecticForm x a b)
    (fun _ a b => inner ℝ a.2 b.1 - inner ℝ b.2 a.1)
    (cotangentMerge_symplectic (M:=M) (N:=U)) (cotangentLift_openRiesz_symplectic U W e)
  have h := diffeomorph_preservesForm_trans (radialCotangentDiffeomorph (E:=E) (M:=M) U)
    ((cotangentProductDiffeomorph (E:=E) (F:=F) (M:=M) (N:=U)).symm.trans
      ((cotangentLift e).trans (cotangentOpenRieszDiffeomorph W)))
    (fun x a b => symplecticForm x.1 a.1 b.1 + (inner ℝ a.2.2 b.2.1 - inner ℝ b.2.2 a.2.1))
    (fun x a b => symplecticForm x.1 a.1 b.1 + symplecticForm x.2 a.2 b.2)
    (fun _ a b => inner ℝ a.2 b.1 - inner ℝ b.2 a.1)
    (radialCotangentDiffeomorph_symplectic U) h₂ z u v
  dsimp only [cotangentCylinderChart]
  convert h using 1; first | rfl | ring

end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Set TopologicalSpace InnerProductSpace ContinuousLinearMap
variable {E F G M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance symplecticCylinderPositionBaseChartedSpace (U : Opens F) : ChartedSpace (E × F) (M × U) :=
  inferInstanceAs (ChartedSpace (ModelProd E F) (M × U))
local instance symplecticCylinderPositionBaseManifold (U : Opens F) : IsManifold 𝓘(ℝ,E × F) ∞ (M × U) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I:=𝓘(ℝ,E)) (I':=𝓘(ℝ,F)) M U
local instance symplecticCylinderPositionCotangentChartedSpace (A B : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
    [TopologicalSpace B] [ChartedSpace A B] [IsManifold 𝓘(ℝ,A) ∞ B] :
    ChartedSpace (A × (A →L[ℝ] ℝ)) (Cotangent (E:=A) (M:=B)) :=
  inferInstanceAs (ChartedSpace (ModelProd A (A →L[ℝ] ℝ)) (Cotangent (E:=A) (M:=B)))

lemma cotangentCylinderChart_position (U : Opens F) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × F) 𝓘(ℝ,G) (M × U) W ∞)
    (z : Cotangent (E:=E) (M:=M) × openPhase U) :
    ((cotangentCylinderChart U W e z : openPhase W) : G × G).1 =
      (e (z.1.proj,⟨(z.2:F × F).1,z.2.property.1⟩) : G) := rfl

lemma cotangentCylinderChart_zero (U : Opens F) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × F) 𝓘(ℝ,G) (M × U) W ∞) (x : M) (a : U) :
    (cotangentCylinderChart U W e
      ((⟨x,0⟩ : Cotangent (E:=E) (M:=M)),⟨((a:F),0),⟨a.property,mem_univ _⟩⟩) : G × G) =
      ((e (x,a) : G),0) := by
  apply Prod.ext
  · rfl
  change (toDual ℝ G).symm
    (((0 : E →L[ℝ] ℝ).comp (fst ℝ E F) +
      ((toDual ℝ F) (0:F)).comp (snd ℝ E F)).comp _) = 0
  simp only [map_zero,zero_comp,zero_add]
  change (toDual ℝ G).symm (0 : G →L[ℝ] ℝ) = 0
  exact map_zero _

end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Set TopologicalSpace InnerProductSpace ContinuousLinearMap
variable {E F G M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance symplecticCylinderCentralBaseChartedSpace (U : Opens F) : ChartedSpace (E × F) (M × U) :=
  inferInstanceAs (ChartedSpace (ModelProd E F) (M × U))
local instance symplecticCylinderCentralBaseManifold (U : Opens F) : IsManifold 𝓘(ℝ,E × F) ∞ (M × U) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I:=𝓘(ℝ,E)) (I':=𝓘(ℝ,F)) M U
local instance symplecticCylinderCentralCotangentChartedSpace (A B : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
    [TopologicalSpace B] [ChartedSpace A B] [IsManifold 𝓘(ℝ,A) ∞ B] :
    ChartedSpace (A × (A →L[ℝ] ℝ)) (Cotangent (E:=A) (M:=B)) :=
  inferInstanceAs (ChartedSpace (ModelProd A (A →L[ℝ] ℝ)) (Cotangent (E:=A) (M:=B)))

def centralSpatial (U : Opens F) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × F) 𝓘(ℝ,G) (M × U) W ∞) (C : Set F) : Set G :=
  (fun z : M × U => (e z:G)) '' {z | (z.2:F) ∈ C}

omit [CompleteSpace F] [CompleteSpace G] [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma centralSpatial_subset (U : Opens F) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × F) 𝓘(ℝ,G) (M × U) W ∞) (C : Set F) :
    centralSpatial U W e C ⊆ (W:Set G) := by
  rintro _ ⟨z,_hz,rfl⟩
  exact (e z).property

omit [CompleteSpace F] [CompleteSpace G] [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma centralSpatial_isOpen (U : Opens F) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × F) 𝓘(ℝ,G) (M × U) W ∞) {C : Set F} (hC : IsOpen C) :
    IsOpen (centralSpatial U W e C) := by
  have hi : IsOpen {z : M × U | (z.2:F) ∈ C} :=
    hC.preimage (continuous_subtype_val.comp continuous_snd)
  change IsOpen ((Subtype.val ∘ e) '' _)
  rw [image_comp]
  exact W.isOpenEmbedding'.isOpenMap _ (e.toHomeomorph.isOpenMap _ hi)

theorem cotangentCylinderChart_centralImage (U : Opens F) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × F) 𝓘(ℝ,G) (M × U) W ∞) (C : Set F) :
    (fun z : Cotangent (E:=E) (M:=M) × openPhase U =>
      (cotangentCylinderChart U W e z:G × G)) '' {z | (z.2:F × F).1 ∈ C} =
      centralSpatial U W e C ×ˢ univ := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    refine ⟨⟨(z.1.proj,⟨(z.2:F × F).1,z.2.property.1⟩),hz,?_⟩,mem_univ _⟩
    exact (cotangentCylinderChart_position U W e z).symm
  · rintro ⟨⟨⟨q,a⟩,ha,hpos⟩,_⟩
    have hy : y.1 ∈ W := hpos ▸ (e (q,a)).property
    let z := (cotangentCylinderChart U W e).symm ⟨y,⟨hy,mem_univ _⟩⟩
    have hz : (cotangentCylinderChart U W e z:G × G) = y :=
      congrArg Subtype.val ((cotangentCylinderChart U W e).apply_symm_apply _)
    have hp : (e (z.1.proj,⟨(z.2:F × F).1,z.2.property.1⟩):G) = (e (q,a):G) := by
      rw [← cotangentCylinderChart_position U W e z,hz]
      exact hpos.symm
    have heq := congrArg Prod.snd (e.injective (Subtype.val_injective hp))
    have hr : (z.2:F × F).1 = (a:F) := congrArg Subtype.val heq
    refine ⟨z,?_,hz⟩
    change (z.2:F × F).1 ∈ C
    rw [hr]
    exact ha

theorem cotangentCylinderChart_zeroImage (U : Opens F) (W : Opens G)
    (e : Diffeomorph 𝓘(ℝ,E × F) 𝓘(ℝ,G) (M × U) W ∞) (C : Set F) :
    (fun z : Cotangent (E:=E) (M:=M) × openPhase U =>
      (cotangentCylinderChart U W e z:G × G)) ''
        {z | z.1 ∈ range (fun q : M => (⟨q,0⟩ : Cotangent (E:=E) (M:=M))) ∧
          (z.2:F × F).1 ∈ C ∧ (z.2:F × F).2 = 0} =
      range (fun x : centralSpatial U W e C => ((x:G),(0:G))) := by
  ext y
  constructor
  · rintro ⟨⟨p,u⟩,⟨⟨q,rfl⟩,ha,hp⟩,rfl⟩
    have hu : u = ⟨((u:F × F).1,0),⟨u.property.1,mem_univ _⟩⟩ := by
      apply Subtype.ext
      exact Prod.ext rfl hp
    let a : U := ⟨(u:F × F).1,u.property.1⟩
    refine ⟨⟨(e (q,a):G),⟨(q,a),ha,rfl⟩⟩,?_⟩
    change ((e (q,a):G),0) = (cotangentCylinderChart U W e (⟨q,0⟩,u):G × G)
    rw [hu]
    exact (cotangentCylinderChart_zero U W e q a).symm
  · rintro ⟨x,rfl⟩
    obtain ⟨⟨q,a⟩,ha,hqa⟩ := x.property
    refine ⟨((⟨q,0⟩ : Cotangent (E:=E) (M:=M)),
      ⟨((a:F),0),⟨a.property,mem_univ _⟩⟩),⟨⟨q,rfl⟩,ha,rfl⟩,?_⟩
    change (cotangentCylinderChart U W e (⟨q,0⟩,⟨((a:F),0),_⟩):G × G) = ((x:G),0)
    exact (cotangentCylinderChart_zero U W e q a).trans (congrArg (fun v:G => (v,(0:G))) hqa)

end NearbyLagrangian.CotangentGeometry

end

end OAI
