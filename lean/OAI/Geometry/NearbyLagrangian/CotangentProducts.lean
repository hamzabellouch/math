import Mathlib
import OAI.Geometry.NearbyLagrangian.CotangentForms

namespace OAI

/-! Smooth cotangent pullbacks, sums and product decompositions. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Bundle Set ContinuousLinearMap
variable {E F G H M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
  [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
local instance cotangentProductsPullbackSourceChartedSpace :
    ChartedSpace (E × (E →L[ℝ] ℝ)) (Cotangent (E:=E) (M:=M)) :=
  inferInstanceAs (ChartedSpace (ModelProd E (E →L[ℝ] ℝ)) (Cotangent (E:=E) (M:=M)))
local instance cotangentProductsPullbackTargetChartedSpace :
    ChartedSpace (F × (F →L[ℝ] ℝ)) (Cotangent (E:=F) (M:=N)) :=
  inferInstanceAs (ChartedSpace (ModelProd F (F →L[ℝ] ℝ)) (Cotangent (E:=F) (M:=N)))

def cotangentPullbackMap (z : P → Cotangent (E:=E) (M:=M))
    (f : P → N → M) (g : P → N) (x : P) : Cotangent (E:=F) (M:=N) :=
  ⟨g x,(z x).snd.comp (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (f x) (g x))⟩

lemma contMDiffAt_cotangentPullbackMap
    {z : P → Cotangent (E:=E) (M:=M)} {f : P → N → M} {g : P → N} {x : P}
    (hz : ContMDiffAt I (cotangentModel (E:=E)) ∞ z x)
    (hf : ContMDiffAt (I.prod 𝓘(ℝ,F)) 𝓘(ℝ,E) ∞ (Function.uncurry f) (x,g x))
    (hg : ContMDiffAt I 𝓘(ℝ,F) ∞ g x)
    (hbase : ∀ y, f y (g y) = (z y).proj) :
    ContMDiffAt I (cotangentModel (E:=F)) ∞ (cotangentPullbackMap (E:=E) (F:=F) z f g) x := by
  have hpc := (contMDiffAt_hom_bundle (IB:=𝓘(ℝ,E)) (IM:=I) (n:=∞) (x₀:=x) z).mp hz
  have hd := hf.mfderiv f g hg (by simp)
  simp +unfoldPartialApp only [inTangentCoordinates, inCoordinates, hbase] at hd
  rw [contMDiffAt_hom_bundle]
  refine ⟨hg,?_⟩
  apply (hpc.2.clm_comp hd).congr_of_eventuallyEq
  have hnear : ∀ᶠ y : P in 𝓝 x,
      (z y).proj ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) (z x).proj).baseSet :=
    hpc.1.continuousAt.eventually
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) (z x).proj).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ,E)) (z x).proj))
  filter_upwards [hnear] with y hy
  simp only [cotangentPullbackMap,inCoordinates]
  change (Bundle.Trivial.trivialization N ℝ).continuousLinearMapAt ℝ (g y) ∘L
    (((z y).snd : E →L[ℝ] ℝ) ∘L (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (f y) (g y) : F →L[ℝ] E)) ∘L
      (trivializationAt F (TangentSpace 𝓘(ℝ,F)) (g x)).symmL ℝ (g y) =
    ((Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ (z y).proj ∘L
      (((z y).snd : E →L[ℝ] ℝ) ∘L
        (trivializationAt E (TangentSpace 𝓘(ℝ,E)) (z x).proj).symmL ℝ (z y).proj)) ∘L
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) (z x).proj).continuousLinearMapAt ℝ (f y (g y)) ∘L
        (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (f y) (g y) : F →L[ℝ] E) ∘L
          (trivializationAt F (TangentSpace 𝓘(ℝ,F)) (g x)).symmL ℝ (g y))
  have hcoord := congrArg (β := E →L[ℝ] E) (fun point : M =>
    ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) (z x).proj).continuousLinearMapAt ℝ point :
      E →L[ℝ] E)) (hbase y)
  rw [hcoord]
  simp only [Bundle.Trivial.continuousLinearMapAt_trivialization,ContinuousLinearMap.id_comp]
  ext v
  simp only [ContinuousLinearMap.comp_apply]
  exact congrArg ((z y).snd : E →L[ℝ] ℝ)
    (Trivialization.symmL_continuousLinearMapAt _ hy _).symm

lemma contMDiff_cotangentPullbackMap
    {z : P → Cotangent (E:=E) (M:=M)} {f : P → N → M} {g : P → N}
    (hz : ContMDiff I (cotangentModel (E:=E)) ∞ z)
    (hf : ContMDiff (I.prod 𝓘(ℝ,F)) 𝓘(ℝ,E) ∞ (Function.uncurry f))
    (hg : ContMDiff I 𝓘(ℝ,F) ∞ g)
    (hbase : ∀ y, f y (g y) = (z y).proj) :
    ContMDiff I (cotangentModel (E:=F)) ∞ (cotangentPullbackMap (E:=E) (F:=F) z f g) :=
  fun x => contMDiffAt_cotangentPullbackMap I (hz x) (hf _) (hg x) hbase

end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Bundle Set ContinuousLinearMap
variable {E G H M P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
  [TopologicalSpace P] [ChartedSpace H P]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance cotangentProductsAddChartedSpace :
    ChartedSpace (E × (E →L[ℝ] ℝ)) (Cotangent (E:=E) (M:=M)) :=
  inferInstanceAs (ChartedSpace (ModelProd E (E →L[ℝ] ℝ)) (Cotangent (E:=E) (M:=M)))

def cotangentAddMap (z w : P → Cotangent (E:=E) (M:=M)) (x : P) :
    Cotangent (E:=E) (M:=M) :=
  ⟨(z x).proj,@HAdd.hAdd (E →L[ℝ] ℝ) (E →L[ℝ] ℝ) (E →L[ℝ] ℝ) _ (z x).snd (w x).snd⟩

lemma contMDiffAt_cotangentAddMap {z w : P → Cotangent (E:=E) (M:=M)} {x : P}
    (hz : ContMDiffAt I (cotangentModel (E:=E)) ∞ z x)
    (hw : ContMDiffAt I (cotangentModel (E:=E)) ∞ w x)
    (hbase : ∀ y, (w y).proj = (z y).proj) :
    ContMDiffAt I (cotangentModel (E:=E)) ∞ (cotangentAddMap z w) x := by
  have hz' := (contMDiffAt_hom_bundle (IB:=𝓘(ℝ,E)) (IM:=I) (n:=∞) (x₀:=x) z).mp hz
  have hw' := (contMDiffAt_hom_bundle (IB:=𝓘(ℝ,E)) (IM:=I) (n:=∞) (x₀:=x) w).mp hw
  have heq : (fun y => inCoordinates E (TangentSpace 𝓘(ℝ,E)) ℝ (fun _ : M => ℝ)
      (w x).proj (w y).proj (w x).proj (w y).proj (w y).snd) =
    (fun y => inCoordinates E (TangentSpace 𝓘(ℝ,E)) ℝ (fun _ : M => ℝ)
      (z x).proj (z y).proj (z x).proj (z y).proj (w y).snd) := by
    funext y
    simp only [inCoordinates]
    change (trivializationAt ℝ (fun _ : M => ℝ) (w x).proj).continuousLinearMapAt ℝ (w y).proj ∘L
        ((w y).snd : E →L[ℝ] ℝ) ∘L
        (trivializationAt E (TangentSpace 𝓘(ℝ,E)) (w x).proj).symmL ℝ (w y).proj = _
    have hh : ∀ a b : M,
        ((trivializationAt ℝ (fun _ : M => ℝ) a).continuousLinearMapAt ℝ b : ℝ →L[ℝ] ℝ) =
          ContinuousLinearMap.id ℝ ℝ := fun _ b => Bundle.Trivial.continuousLinearMapAt_trivialization ℝ M ℝ b
    change ((trivializationAt ℝ (fun _ : M => ℝ) (w x).proj).continuousLinearMapAt ℝ (w y).proj : ℝ →L[ℝ] ℝ) ∘L
      ((w y).snd : E →L[ℝ] ℝ) ∘L
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) (w x).proj).symmL ℝ (w y).proj : E →L[ℝ] E) =
      ((trivializationAt ℝ (fun _ : M => ℝ) (z x).proj).continuousLinearMapAt ℝ (z y).proj : ℝ →L[ℝ] ℝ) ∘L
      ((w y).snd : E →L[ℝ] ℝ) ∘L
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) (z x).proj).symmL ℝ (z y).proj : E →L[ℝ] E)
    rw [hh,hh]
    have hs : ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) (w x).proj).symmL ℝ (w y).proj : E →L[ℝ] E) =
        ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) (z x).proj).symmL ℝ (z y).proj : E →L[ℝ] E) := by
      rw [hbase x,hbase y]
    rw [hs]
  rw [heq] at hw'
  rw [contMDiffAt_hom_bundle]
  refine ⟨hz'.1,?_⟩
  apply (hz'.2.add hw'.2).congr_of_eventuallyEq
  filter_upwards [] with y
  simp only [cotangentAddMap,inCoordinates]
  change _ = (inCoordinates E (TangentSpace 𝓘(ℝ,E)) ℝ (fun _ : M => ℝ)
      (z x).proj (z y).proj (z x).proj (z y).proj (z y).snd +
    inCoordinates E (TangentSpace 𝓘(ℝ,E)) ℝ (fun _ : M => ℝ)
      (z x).proj (z y).proj (z x).proj (z y).proj (w y).snd)
  ext v
  let A : ℝ →L[ℝ] ℝ :=
    (trivializationAt ℝ (fun _ : M => ℝ) (z x).proj).continuousLinearMapAt ℝ (z y).proj
  let B : E →L[ℝ] E :=
    (trivializationAt E (TangentSpace 𝓘(ℝ,E)) (z x).proj).symmL ℝ (z y).proj
  change A (((z y).snd : E →L[ℝ] ℝ) (B v) + ((w y).snd : E →L[ℝ] ℝ) (B v)) =
    A (((z y).snd : E →L[ℝ] ℝ) (B v)) + A (((w y).snd : E →L[ℝ] ℝ) (B v))
  exact map_add A _ _

lemma contMDiff_cotangentAddMap {z w : P → Cotangent (E:=E) (M:=M)}
    (hz : ContMDiff I (cotangentModel (E:=E)) ∞ z)
    (hw : ContMDiff I (cotangentModel (E:=E)) ∞ w)
    (hbase : ∀ y, (w y).proj = (z y).proj) :
    ContMDiff I (cotangentModel (E:=E)) ∞ (cotangentAddMap z w) :=
  fun x => contMDiffAt_cotangentAddMap I (hz x) (hw x) hbase

end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Bundle Set ContinuousLinearMap
variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
local instance cotangentProductsSplitBaseChartedSpace : ChartedSpace (E × F) (M × N) :=
  inferInstanceAs (ChartedSpace (ModelProd E F) (M × N))
local instance cotangentProductsSplitBaseIsManifold : IsManifold 𝓘(ℝ,E × F) ∞ (M × N) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I:=𝓘(ℝ,E)) (I':=𝓘(ℝ,F)) M N
local instance cotangentProductsSplitChartedSpace (A B : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
    [TopologicalSpace B] [ChartedSpace A B] [IsManifold 𝓘(ℝ,A) ∞ B] :
    ChartedSpace (A × (A →L[ℝ] ℝ)) (Cotangent (E:=A) (M:=B)) :=
  inferInstanceAs (ChartedSpace (ModelProd A (A →L[ℝ] ℝ)) (Cotangent (E:=A) (M:=B)))

def cotangentLeft (z : Cotangent (E:=E × F) (M:=M × N)) : Cotangent (E:=E) (M:=M) :=
  ⟨z.proj.1,(z.snd : (E × F) →L[ℝ] ℝ).comp (ContinuousLinearMap.inl ℝ E F)⟩

def cotangentRight (z : Cotangent (E:=E × F) (M:=M × N)) : Cotangent (E:=F) (M:=N) :=
  ⟨z.proj.2,(z.snd : (E × F) →L[ℝ] ℝ).comp (ContinuousLinearMap.inr ℝ E F)⟩

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
lemma cotangentLeft_eq_pullback : cotangentLeft (E:=E) (F:=F) (M:=M) (N:=N) =
    cotangentPullbackMap (E:=E × F) (F:=E) id
      (fun z : Cotangent (E:=E × F) (M:=M × N) => fun m : M => (m,z.proj.2))
      (fun z => z.proj.1) := by
  funext z
  apply Bundle.TotalSpace.ext
  · rfl
  apply heq_of_eq
  change (z.snd : (E × F) →L[ℝ] ℝ).comp (ContinuousLinearMap.inl ℝ E F) =
    (z.snd : (E × F) →L[ℝ] ℝ).comp
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E × F) (fun m : M => (m,z.proj.2)) z.proj.1)
  rw [modelWithCornersSelf_prod,mfderiv_prod_left]
  rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
lemma cotangentRight_eq_pullback : cotangentRight (E:=E) (F:=F) (M:=M) (N:=N) =
    cotangentPullbackMap (E:=E × F) (F:=F) id
      (fun z : Cotangent (E:=E × F) (M:=M × N) => fun n : N => (z.proj.1,n))
      (fun z => z.proj.2) := by
  funext z
  apply Bundle.TotalSpace.ext
  · rfl
  apply heq_of_eq
  change (z.snd : (E × F) →L[ℝ] ℝ).comp (ContinuousLinearMap.inr ℝ E F) =
    (z.snd : (E × F) →L[ℝ] ℝ).comp
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E × F) (fun n : N => (z.proj.1,n)) z.proj.2)
  rw [modelWithCornersSelf_prod,mfderiv_prod_right]
  rfl

lemma contMDiff_cotangentLeft :
    ContMDiff (cotangentModel (E:=E × F)) (cotangentModel (E:=E)) ∞
      (cotangentLeft (E:=E) (F:=F) (M:=M) (N:=N)) := by
  rw [cotangentLeft_eq_pullback]
  have hp := contMDiff_projection (E:=E × F) (M:=M × N)
  have hp' : ContMDiff (cotangentModel (E:=E × F)) (𝓘(ℝ,E).prod 𝓘(ℝ,F)) ∞
      (projection (E:=E × F) (M:=M × N)) := by
    simpa only [← modelWithCornersSelf_prod] using hp
  apply contMDiff_cotangentPullbackMap _ contMDiff_id ?_ hp'.fst
    (fun _ => Prod.eta _)
  have h : ContMDiff ((cotangentModel (E:=E × F)).prod 𝓘(ℝ,E))
      (𝓘(ℝ,E).prod 𝓘(ℝ,F)) ∞
      (fun zm : Cotangent (E:=E × F) (M:=M × N) × M => (zm.2,zm.1.proj.2)) :=
    contMDiff_snd.prodMk (hp'.snd.comp contMDiff_fst)
  have hc : ∀ f : Cotangent (E:=E × F) (M:=M × N) × M → M × N,
      ContMDiff ((cotangentModel (E:=E × F)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E × F) ∞ f ↔
      ContMDiff ((cotangentModel (E:=E × F)).prod 𝓘(ℝ,E))
        (𝓘(ℝ,E).prod 𝓘(ℝ,F)) ∞ f := by
    intro f
    conv_lhs => arg 2; rw [modelWithCornersSelf_prod]
  exact (hc _).mpr h

lemma contMDiff_cotangentRight :
    ContMDiff (cotangentModel (E:=E × F)) (cotangentModel (E:=F)) ∞
      (cotangentRight (E:=E) (F:=F) (M:=M) (N:=N)) := by
  rw [cotangentRight_eq_pullback]
  have hp := contMDiff_projection (E:=E × F) (M:=M × N)
  have hp' : ContMDiff (cotangentModel (E:=E × F)) (𝓘(ℝ,E).prod 𝓘(ℝ,F)) ∞
      (projection (E:=E × F) (M:=M × N)) := by
    simpa only [← modelWithCornersSelf_prod] using hp
  apply contMDiff_cotangentPullbackMap _ contMDiff_id ?_ hp'.snd
    (fun _ => Prod.eta _)
  have h : ContMDiff ((cotangentModel (E:=E × F)).prod 𝓘(ℝ,F))
      (𝓘(ℝ,E).prod 𝓘(ℝ,F)) ∞
      (fun zn : Cotangent (E:=E × F) (M:=M × N) × N => (zn.1.proj.1,zn.2)) :=
    (hp'.fst.comp contMDiff_fst).prodMk contMDiff_snd
  have hc : ∀ f : Cotangent (E:=E × F) (M:=M × N) × N → M × N,
      ContMDiff ((cotangentModel (E:=E × F)).prod 𝓘(ℝ,F)) 𝓘(ℝ,E × F) ∞ f ↔
      ContMDiff ((cotangentModel (E:=E × F)).prod 𝓘(ℝ,F))
        (𝓘(ℝ,E).prod 𝓘(ℝ,F)) ∞ f := by
    intro f
    conv_lhs => arg 2; rw [modelWithCornersSelf_prod]
  exact (hc _).mpr h

end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Bundle Set ContinuousLinearMap
variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
local instance cotangentProductsMergeBaseChartedSpace : ChartedSpace (E × F) (M × N) :=
  inferInstanceAs (ChartedSpace (ModelProd E F) (M × N))
local instance cotangentProductsMergeBaseIsManifold : IsManifold 𝓘(ℝ,E × F) ∞ (M × N) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I:=𝓘(ℝ,E)) (I':=𝓘(ℝ,F)) M N
local instance cotangentProductsMergeChartedSpace (A B : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
    [TopologicalSpace B] [ChartedSpace A B] [IsManifold 𝓘(ℝ,A) ∞ B] :
    ChartedSpace (A × (A →L[ℝ] ℝ)) (Cotangent (E:=A) (M:=B)) :=
  inferInstanceAs (ChartedSpace (ModelProd A (A →L[ℝ] ℝ)) (Cotangent (E:=A) (M:=B)))

def cotangentMerge (z : Cotangent (E:=E) (M:=M) × Cotangent (E:=F) (M:=N)) :
    Cotangent (E:=E × F) (M:=M × N) :=
  ⟨(z.1.proj,z.2.proj), (z.1.snd : E →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ E F) +
    (z.2.snd : F →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ E F)⟩

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
lemma cotangentMerge_eq_addPullback : cotangentMerge (E:=E) (F:=F) (M:=M) (N:=N) =
    cotangentAddMap
      (cotangentPullbackMap (E:=E) (F:=E × F) Prod.fst (fun _ => Prod.fst)
        (fun z => (z.1.proj,z.2.proj)))
      (cotangentPullbackMap (E:=F) (F:=E × F) Prod.snd (fun _ => Prod.snd)
        (fun z => (z.1.proj,z.2.proj))) := by
  funext z
  apply Bundle.TotalSpace.ext
  · rfl
  apply heq_of_eq
  change (z.1.snd : E →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ E F) +
      (z.2.snd : F →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ E F) =
    (z.1.snd : E →L[ℝ] ℝ).comp
      (mfderiv 𝓘(ℝ,E × F) 𝓘(ℝ,E) Prod.fst (z.1.proj,z.2.proj)) +
    (z.2.snd : F →L[ℝ] ℝ).comp
      (mfderiv 𝓘(ℝ,E × F) 𝓘(ℝ,F) Prod.snd (z.1.proj,z.2.proj))
  rw [modelWithCornersSelf_prod,mfderiv_fst,mfderiv_snd]
  rfl

lemma contMDiff_cotangentMerge :
    ContMDiff ((cotangentModel (E:=E)).prod (cotangentModel (E:=F)))
      (cotangentModel (E:=E × F)) ∞ (cotangentMerge (E:=E) (F:=F) (M:=M) (N:=N)) := by
  rw [cotangentMerge_eq_addPullback]
  let I := (cotangentModel (E:=E)).prod (cotangentModel (E:=F))
  have hg : ContMDiff I 𝓘(ℝ,E × F) ∞
      (fun z : Cotangent (E:=E) (M:=M) × Cotangent (E:=F) (M:=N) =>
        (z.1.proj,z.2.proj)) := by
    have h : ContMDiff I 𝓘(ℝ,E) ∞
        (fun z : Cotangent (E:=E) (M:=M) × Cotangent (E:=F) (M:=N) => z.1.proj) :=
      contMDiff_projection.comp contMDiff_fst
    have h' : ContMDiff I 𝓘(ℝ,F) ∞
        (fun z : Cotangent (E:=E) (M:=M) × Cotangent (E:=F) (M:=N) => z.2.proj) :=
      contMDiff_projection.comp contMDiff_snd
    have hh := h.prodMk h'
    simpa only [← modelWithCornersSelf_prod] using hh
  have hfst : ContMDiff (I.prod 𝓘(ℝ,E × F)) 𝓘(ℝ,E) ∞
      (fun z : (Cotangent (E:=E) (M:=M) × Cotangent (E:=F) (M:=N)) × (M × N) =>
        z.2.1) := by
    have h : ContMDiff 𝓘(ℝ,E × F) 𝓘(ℝ,E) ∞ (Prod.fst : M × N → M) := by
      rw [modelWithCornersSelf_prod]
      exact contMDiff_fst
    exact h.comp contMDiff_snd
  have hsnd : ContMDiff (I.prod 𝓘(ℝ,E × F)) 𝓘(ℝ,F) ∞
      (fun z : (Cotangent (E:=E) (M:=M) × Cotangent (E:=F) (M:=N)) × (M × N) =>
        z.2.2) := by
    have h : ContMDiff 𝓘(ℝ,E × F) 𝓘(ℝ,F) ∞ (Prod.snd : M × N → N) := by
      rw [modelWithCornersSelf_prod]
      exact contMDiff_snd
    exact h.comp contMDiff_snd
  exact contMDiff_cotangentAddMap I
    (contMDiff_cotangentPullbackMap I contMDiff_fst hfst hg (fun _ => rfl))
    (contMDiff_cotangentPullbackMap I contMDiff_snd hsnd hg (fun _ => rfl))
    (fun _ => rfl)

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
lemma cotangentMerge_left_right (z : Cotangent (E:=E × F) (M:=M × N)) :
    cotangentMerge (cotangentLeft z,cotangentRight z) = z := by
  cases z with | mk q p =>
    apply Bundle.TotalSpace.ext
    · exact Prod.eta q
    apply heq_of_eq
    change ((p : (E × F) →L[ℝ] ℝ).comp (ContinuousLinearMap.inl ℝ E F)).comp
      (ContinuousLinearMap.fst ℝ E F) +
      ((p : (E × F) →L[ℝ] ℝ).comp (ContinuousLinearMap.inr ℝ E F)).comp
      (ContinuousLinearMap.snd ℝ E F) = p
    apply ContinuousLinearMap.ext
    intro v
    change p (v.1,0) + p (0,v.2) = p v
    have hadd : ∀ p : (E × F) →L[ℝ] ℝ, ∀ v : E × F,
        p (v.1,0) + p (0,v.2) = p v := by
      intro p v
      rw [← map_add]
      congr 1
      exact Prod.ext (add_zero _) (zero_add _)
    exact hadd p v

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
lemma cotangentLeft_merge (z : Cotangent (E:=E) (M:=M) × Cotangent (E:=F) (M:=N)) :
    cotangentLeft (cotangentMerge z) = z.1 := by
  rcases z with ⟨⟨q,p⟩,⟨r,s⟩⟩
  apply Bundle.TotalSpace.ext
  · rfl
  apply heq_of_eq
  change ((p : E →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ E F) +
      (s : F →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ E F)).comp
      (ContinuousLinearMap.inl ℝ E F) = p
  ext v
  change p v + s 0 = p v
  simp only [map_zero,add_zero]

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
lemma cotangentRight_merge (z : Cotangent (E:=E) (M:=M) × Cotangent (E:=F) (M:=N)) :
    cotangentRight (cotangentMerge z) = z.2 := by
  rcases z with ⟨⟨q,p⟩,⟨r,s⟩⟩
  apply Bundle.TotalSpace.ext
  · rfl
  apply heq_of_eq
  change ((p : E →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ E F) +
      (s : F →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ E F)).comp
      (ContinuousLinearMap.inr ℝ E F) = s
  ext v
  change p 0 + s v = s v
  simp only [map_zero,zero_add]

def cotangentProductDiffeomorph :
    Diffeomorph (cotangentModel (E:=E × F))
      ((cotangentModel (E:=E)).prod (cotangentModel (E:=F)))
      (Cotangent (E:=E × F) (M:=M × N))
      (Cotangent (E:=E) (M:=M) × Cotangent (E:=F) (M:=N)) ∞ where
  toFun z := (cotangentLeft z,cotangentRight z)
  invFun := cotangentMerge
  left_inv := cotangentMerge_left_right
  right_inv z := Prod.ext (cotangentLeft_merge z) (cotangentRight_merge z)
  contMDiff_toFun := contMDiff_cotangentLeft.prodMk contMDiff_cotangentRight
  contMDiff_invFun := contMDiff_cotangentMerge

end NearbyLagrangian.CotangentGeometry

end

end OAI
