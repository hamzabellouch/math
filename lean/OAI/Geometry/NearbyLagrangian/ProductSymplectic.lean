import Mathlib
import OAI.Geometry.NearbyLagrangian.LiouvilleDifferentials
import OAI.Geometry.NearbyLagrangian.CotangentProducts

namespace OAI

/-! Preservation of Liouville and symplectic forms by cotangent products. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Bundle Set ContinuousLinearMap
section General
variable {E G H M P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
  [TopologicalSpace P] [ChartedSpace H P]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

lemma liouville_apply_mfderiv_general {i : P → Cotangent (E:=E) (M:=M)} {x : P}
    (hi : MDifferentiableAt I (cotangentModel (E:=E)) i x)
    (v : TangentSpace I x) :
    liouville (i x) (mfderiv I (cotangentModel (E:=E)) i x v) =
      (i x).snd (mfderiv I 𝓘(ℝ,E) (projection ∘ i) x v) := by
  rw [mfderiv_comp_apply x (contMDiff_projection.mdifferentiableAt (by simp)) hi]
  rfl
end General

section Product
variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
local instance productSymplecticLiouvilleBaseChartedSpace : ChartedSpace (E × F) (M × N) :=
  inferInstanceAs (ChartedSpace (ModelProd E F) (M × N))
local instance productSymplecticLiouvilleBaseManifold : IsManifold 𝓘(ℝ,E × F) ∞ (M × N) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I:=𝓘(ℝ,E)) (I':=𝓘(ℝ,F)) M N
local instance productSymplecticLiouvilleCotangentChartedSpace
    (A B : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
    [TopologicalSpace B] [ChartedSpace A B] [IsManifold 𝓘(ℝ,A) ∞ B] :
    ChartedSpace (A × (A →L[ℝ] ℝ)) (Cotangent (E:=A) (M:=B)) :=
  inferInstanceAs (ChartedSpace (ModelProd A (A →L[ℝ] ℝ)) (Cotangent (E:=A) (M:=B)))

theorem cotangentMerge_liouville
    (z : Cotangent (E:=E) (M:=M) × Cotangent (E:=F) (M:=N))
    (v : TangentSpace ((cotangentModel (E:=E)).prod (cotangentModel (E:=F))) z) :
    liouville (cotangentMerge z)
      (mfderiv ((cotangentModel (E:=E)).prod (cotangentModel (E:=F)))
        (cotangentModel (E:=E × F)) (cotangentMerge (M:=M) (N:=N)) z v) =
      liouville z.1 v.1 + liouville z.2 v.2 := by
  let I := (cotangentModel (E:=E)).prod (cotangentModel (E:=F))
  rw [liouville_apply_mfderiv_general I
    (contMDiff_cotangentMerge.mdifferentiableAt (by simp))]
  have heq : (projection (E:=E × F) (M:=M × N) ∘ cotangentMerge) =
      Prod.map (projection (E:=E) (M:=M)) (projection (E:=F) (M:=N)) := rfl
  rw [heq]
  have hd : (mfderiv I 𝓘(ℝ,E × F)
      (Prod.map (projection (E:=E) (M:=M)) (projection (E:=F) (M:=N))) z :
        ((E × (E →L[ℝ] ℝ)) × (F × (F →L[ℝ] ℝ))) →L[ℝ] E × F) =
      (mfderiv (cotangentModel (E:=E)) 𝓘(ℝ,E) projection z.1).prodMap
        (mfderiv (cotangentModel (E:=F)) 𝓘(ℝ,F) projection z.2) := by
    let D : ModelWithCorners ℝ (E × F) (E × F) →
        (((E × (E →L[ℝ] ℝ)) × (F × (F →L[ℝ] ℝ))) →L[ℝ] E × F) := fun J => by
      exact mfderiv I J
        (Prod.map (projection (E:=E) (M:=M)) (projection (E:=F) (M:=N))) z
    have hc := congrArg D (modelWithCornersSelf_prod (𝕜:=ℝ) (E:=E) (F:=F))
    exact hc.trans (mfderiv_prodMap (p:=z)
      (contMDiff_projection (E:=E) (M:=M) |>.mdifferentiableAt (by simp))
      (contMDiff_projection (E:=F) (M:=N) |>.mdifferentiableAt (by simp)))
  change ((z.1.snd : E →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ E F) +
      (z.2.snd : F →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ E F))
      ((mfderiv I 𝓘(ℝ,E × F)
      (Prod.map (projection (E:=E) (M:=M)) (projection (E:=F) (M:=N))) z) v) = _
  rw [hd]
  rfl
end Product
end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian
variable {V W H K M N : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ V H} {J : ModelWithCorners ℝ W K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [TopologicalSpace N] [ChartedSpace K N]

lemma chartInverse_mfderiv (z : M) :
    (mfderiv 𝓘(ℝ,V) I (extChartAt I z).symm (extChartAt I z z) : V →L[ℝ] V) =
      ContinuousLinearMap.id ℝ V := by
  have h := mfderivWithin_range_extChartAt_symm (I:=I) (x:=z)
  rw [I.range_eq_univ,mfderivWithin_univ] at h
  exact h

lemma comp_chartInverse_mfderiv {f : M → N} {z : M}
    (hf : MDifferentiableAt I J f z) (v : V) :
    mfderiv 𝓘(ℝ,V) J (f ∘ (extChartAt I z).symm) (extChartAt I z z) v =
      mfderiv I J f z v := by
  have hx : (extChartAt I z).symm (extChartAt I z z) = z :=
    (extChartAt I z).left_inv (mem_extChartAt_source z)
  have hc : MDifferentiableAt 𝓘(ℝ,V) I (extChartAt I z).symm (extChartAt I z z) :=
    ((contMDiffOn_extChartAt_symm (I:=I) (n:=∞) z).contMDiffAt
      ((isOpen_extChartAt_target z).mem_nhds (mem_extChartAt_target z))).mdifferentiableAt (by simp)
  have h := mfderiv_comp_apply_of_eq (extChartAt I z z) hf hc hx v
  have he := congrArg (fun A : V →L[ℝ] V => A v) (chartInverse_mfderiv (I:=I) z)
  exact h.trans (congrArg (mfderiv I J f z) he)
end NearbyLagrangian

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Bundle Set ContinuousLinearMap Function Filter
variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
local instance productSymplecticBaseChartedSpace : ChartedSpace (E × F) (M × N) :=
  inferInstanceAs (ChartedSpace (ModelProd E F) (M × N))
local instance productSymplecticBaseManifold : IsManifold 𝓘(ℝ,E × F) ∞ (M × N) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I:=𝓘(ℝ,E)) (I':=𝓘(ℝ,F)) M N
local instance productSymplecticCotangentChartedSpace
    (A B : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
    [TopologicalSpace B] [ChartedSpace A B] [IsManifold 𝓘(ℝ,A) ∞ B] :
    ChartedSpace (A × (A →L[ℝ] ℝ)) (Cotangent (E:=A) (M:=B)) :=
  inferInstanceAs (ChartedSpace (ModelProd A (A →L[ℝ] ℝ)) (Cotangent (E:=A) (M:=B)))

lemma cotangentMerge_pullback_liouville {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {i : X → Cotangent (E:=E) (M:=M) × Cotangent (E:=F) (M:=N)} {x : X}
    (hi : MDifferentiableAt 𝓘(ℝ,X) ((cotangentModel (E:=E)).prod (cotangentModel (E:=F))) i x)
    (w : X) :
    liouville ((cotangentMerge ∘ i) x)
      (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=E × F)) (cotangentMerge ∘ i) x w) =
    liouville ((Prod.fst ∘ i) x)
      (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=E)) (Prod.fst ∘ i) x w) +
    liouville ((Prod.snd ∘ i) x)
      (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=F)) (Prod.snd ∘ i) x w) := by
  erw [mfderiv_comp_apply x (contMDiff_cotangentMerge.mdifferentiableAt (by simp)) hi,
    mfderiv_comp_apply x ((contMDiff_fst (n:=∞)).mdifferentiableAt (by simp)) hi,
    mfderiv_comp_apply x ((contMDiff_snd (n:=∞)).mdifferentiableAt (by simp)) hi]
  erw [mfderiv_fst,mfderiv_snd]
  change liouville (cotangentMerge (i x))
    (mfderiv ((cotangentModel (E:=E)).prod (cotangentModel (E:=F)))
      (cotangentModel (E:=E × F)) cotangentMerge (i x)
      (mfderiv 𝓘(ℝ,X) ((cotangentModel (E:=E)).prod (cotangentModel (E:=F))) i x w)) =
    liouville (i x).1 (mfderiv 𝓘(ℝ,X) ((cotangentModel (E:=E)).prod (cotangentModel (E:=F))) i x w).1 +
    liouville (i x).2 (mfderiv 𝓘(ℝ,X) ((cotangentModel (E:=E)).prod (cotangentModel (E:=F))) i x w).2
  exact cotangentMerge_liouville (i x) (mfderiv 𝓘(ℝ,X) ((cotangentModel (E:=E)).prod (cotangentModel (E:=F))) i x w)

theorem cotangentMerge_symplectic
    (z : Cotangent (E:=E) (M:=M) × Cotangent (E:=F) (M:=N))
    (u v : TangentSpace ((cotangentModel (E:=E)).prod (cotangentModel (E:=F))) z) :
    symplecticForm (cotangentMerge z)
      (mfderiv ((cotangentModel (E:=E)).prod (cotangentModel (E:=F)))
        (cotangentModel (E:=E × F)) (cotangentMerge (M:=M) (N:=N)) z u)
      (mfderiv ((cotangentModel (E:=E)).prod (cotangentModel (E:=F)))
        (cotangentModel (E:=E × F)) (cotangentMerge (M:=M) (N:=N)) z v) =
      symplecticForm z.1 u.1 v.1 + symplecticForm z.2 u.2 v.2 := by
  let X := (E × (E →L[ℝ] ℝ)) × (F × (F →L[ℝ] ℝ))
  let : ChartedSpace X X := chartedSpaceSelf X
  let I := (cotangentModel (E:=E)).prod (cotangentModel (E:=F))
  let c := extChartAt I z
  let x := c z
  have hx : x ∈ c.target := mem_extChartAt_target z
  have hcx : c.symm x = z := c.left_inv (mem_extChartAt_source z)
  have hcs : ContMDiffAt 𝓘(ℝ,X) I ∞ c.symm x :=
    (contMDiffOn_extChartAt_symm z).contMDiffAt ((isOpen_extChartAt_target z).mem_nhds hx)
  have hleft : ContMDiffAt 𝓘(ℝ,X) (cotangentModel (E:=E)) ∞ (Prod.fst ∘ c.symm) x :=
    contMDiff_fst.contMDiffAt.comp x hcs
  have hright : ContMDiffAt 𝓘(ℝ,X) (cotangentModel (E:=F)) ∞ (Prod.snd ∘ c.symm) x :=
    contMDiff_snd.contMDiffAt.comp x hcs
  have hmerge : ContMDiffAt 𝓘(ℝ,X) (cotangentModel (E:=E × F)) ∞
      (cotangentMerge ∘ c.symm) x := contMDiff_cotangentMerge.contMDiffAt.comp x hcs
  have hl : ∀ᶠ y in 𝓝 x, ∀ w : X,
      liouville ((cotangentMerge ∘ c.symm) y)
        (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=E × F)) (cotangentMerge ∘ c.symm) y w) =
      liouville ((Prod.fst ∘ c.symm) y)
        (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=E)) (Prod.fst ∘ c.symm) y w) +
      liouville ((Prod.snd ∘ c.symm) y)
        (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=F)) (Prod.snd ∘ c.symm) y w) := by
    filter_upwards [(isOpen_extChartAt_target z).mem_nhds hx] with y hy w
    have hcy : MDifferentiableAt 𝓘(ℝ,X) I c.symm y := ((contMDiffOn_extChartAt_symm (I:=I) (n:=∞) z).contMDiffAt ((isOpen_extChartAt_target z).mem_nhds hy)).mdifferentiableAt (by simp)
    exact cotangentMerge_pullback_liouville hcy w
  have hsum := symplectic_sum_of_liouville hleft hright hmerge hl u v
  let ω₁ : Cotangent (E:=E) (M:=M) → (E × (E →L[ℝ] ℝ)) → (E × (E →L[ℝ] ℝ)) → ℝ :=
    fun p a b => symplecticForm p a b
  let ω₂ : Cotangent (E:=F) (M:=N) → (F × (F →L[ℝ] ℝ)) → (F × (F →L[ℝ] ℝ)) → ℝ :=
    fun p a b => symplecticForm p a b
  let ω₃ : Cotangent (E:=E × F) (M:=M × N) →
      ((E × F) × ((E × F) →L[ℝ] ℝ)) → ((E × F) × ((E × F) →L[ℝ] ℝ)) → ℝ :=
    fun p a b => symplecticForm p a b
  change ω₃ ((cotangentMerge ∘ c.symm) x)
    (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=E × F)) (cotangentMerge ∘ c.symm) x u)
    (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=E × F)) (cotangentMerge ∘ c.symm) x v) =
    ω₁ ((Prod.fst ∘ c.symm) x)
    (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=E)) (Prod.fst ∘ c.symm) x u)
    (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=E)) (Prod.fst ∘ c.symm) x v) +
    ω₂ ((Prod.snd ∘ c.symm) x)
    (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=F)) (Prod.snd ∘ c.symm) x u)
    (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=F)) (Prod.snd ∘ c.symm) x v) at hsum
  have hdm := contMDiff_cotangentMerge (E:=E) (F:=F) (M:=M) (N:=N) |>.mdifferentiableAt (x:=z) (by simp)
  have hdf := contMDiff_fst (I:=cotangentModel (E:=E)) (J:=cotangentModel (E:=F)) (n:=∞) |>.mdifferentiableAt (x:=z) (by simp)
  have hds := contMDiff_snd (I:=cotangentModel (E:=E)) (J:=cotangentModel (E:=F)) (n:=∞) |>.mdifferentiableAt (x:=z) (by simp)
  erw [comp_chartInverse_mfderiv hdm u,comp_chartInverse_mfderiv hdm v,
    comp_chartInverse_mfderiv hdf u,comp_chartInverse_mfderiv hdf v,
    comp_chartInverse_mfderiv hds u,comp_chartInverse_mfderiv hds v] at hsum
  simp only [Function.comp_apply,hcx] at hsum
  erw [mfderiv_fst,mfderiv_snd] at hsum
  exact hsum
end NearbyLagrangian.CotangentGeometry

end

end OAI
