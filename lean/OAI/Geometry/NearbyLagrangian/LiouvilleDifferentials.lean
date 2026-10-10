import Mathlib
import OAI.Geometry.NearbyLagrangian.CotangentForms

namespace OAI

/-! Exterior derivatives and pullback identities for Liouville forms. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.CotangentGeometry
open scoped ContDiff Topology
open Filter ContinuousLinearMap
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem canonical_symplectic_of_liouville_coordinates
    {q : E × (E →L[ℝ] ℝ) → F} {p : E × (E →L[ℝ] ℝ) → F →L[ℝ] ℝ}
    {x : E × (E →L[ℝ] ℝ)} (hq : ContDiffAt ℝ ∞ q x)
    (hp : DifferentiableAt ℝ p x)
    (hl : (fun y => (p y).comp (fderiv ℝ q y)) =ᶠ[𝓝 x] coordinateLiouville (E:=E))
    (u v : E × (E →L[ℝ] ℝ)) :
    fderiv ℝ p x u (fderiv ℝ q x v) - fderiv ℝ p x v (fderiv ℝ q x u) =
      u.2 v.1 - v.2 u.1 := by
  have hqd : DifferentiableAt ℝ (fderiv ℝ q) x :=
    (hq.fderiv_right (m:=1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
  have hd := hl.fderiv_eq (𝕜:=ℝ)
  rw [fderiv_clm_comp hp hqd, ContinuousLinearMap.fderiv] at hd
  have h₁ := congrArg (fun A : (E × (E →L[ℝ] ℝ)) →L[ℝ] ((E × (E →L[ℝ] ℝ)) →L[ℝ] ℝ) => A u v) hd
  have h₂ := congrArg (fun A : (E × (E →L[ℝ] ℝ)) →L[ℝ] ((E × (E →L[ℝ] ℝ)) →L[ℝ] ℝ) => A v u) hd
  change p x (fderiv ℝ (fderiv ℝ q) x u v) +
    fderiv ℝ p x u (fderiv ℝ q x v) = u.2 v.1 at h₁
  change p x (fderiv ℝ (fderiv ℝ q) x v u) +
    fderiv ℝ p x v (fderiv ℝ q x u) = v.2 u.1 at h₂
  have hsym := (hq.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)).eq u v
  rw [hsym] at h₁
  linarith

lemma canonical_symplectic_of_liouville_map
    {J : E × (E →L[ℝ] ℝ) → F × (F →L[ℝ] ℝ)} {x : E × (E →L[ℝ] ℝ)}
    (hJ : ContDiffAt ℝ ∞ J x)
    (hl : (fun y => (coordinateLiouville (J y)).comp (fderiv ℝ J y)) =ᶠ[𝓝 x]
      coordinateLiouville (E:=E)) (u v : E × (E →L[ℝ] ℝ)) :
    (fderiv ℝ J x u).2 (fderiv ℝ J x v).1 -
      (fderiv ℝ J x v).2 (fderiv ℝ J x u).1 = u.2 v.1 - v.2 u.1 := by
  have hd := hJ.differentiableAt (by simp)
  have h1 : ContDiffAt ℝ 1 J x := hJ.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hnear := h1.eventually (by simp)
  have hl' : (fun y => (J y).2.comp (fderiv ℝ (fun w => (J w).1) y)) =ᶠ[𝓝 x]
      coordinateLiouville (E:=E) := by
    filter_upwards [hl,hnear] with y hy hys
    rw [fderiv.fst (hys.differentiableAt one_ne_zero)]
    exact hy
  have h := canonical_symplectic_of_liouville_coordinates hJ.fst hd.snd hl' u v
  rw [fderiv.fst hd, fderiv.snd hd] at h
  exact h
end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Bundle Set Function Filter ContinuousLinearMap
variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
local instance : ChartedSpace (E × (E →L[ℝ] ℝ)) (Cotangent (E:=E) (M:=M)) :=
  inferInstanceAs (ChartedSpace (ModelProd E (E →L[ℝ] ℝ)) (Cotangent (E:=E) (M:=M)))
local instance : ChartedSpace (F × (F →L[ℝ] ℝ)) (Cotangent (E:=F) (M:=N)) :=
  inferInstanceAs (ChartedSpace (ModelProd F (F →L[ℝ] ℝ)) (Cotangent (E:=F) (M:=N)))

lemma coordinateLiouville_extChartAt {z₀ z : Cotangent (E:=E) (M:=M)}
    (hz : z ∈ (extChartAt (cotangentModel (E:=E)) z₀).source)
    (v : TangentSpace (cotangentModel (E:=E)) z) :
    coordinateLiouville (extChartAt (cotangentModel (E:=E)) z₀ z)
      (mfderiv (cotangentModel (E:=E)) 𝓘(ℝ,E × (E →L[ℝ] ℝ))
        (extChartAt (cotangentModel (E:=E)) z₀) z v) = liouville z v := by
  have ht := (extChartAt (cotangentModel (E:=E)) z₀).map_source hz
  have hl := liouvilleInChart_eq ht
  have hd := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hz
  simp only [cotangentModel, ← modelWithCornersSelf_prod, modelWithCornersSelf_coe,
    range_id, mfderivWithin_univ] at hd
  have hla := congrArg (fun A : (E × (E →L[ℝ] ℝ)) →L[ℝ] ℝ =>
    A (mfderiv (cotangentModel (E:=E)) 𝓘(ℝ,E × (E →L[ℝ] ℝ))
        (extChartAt (cotangentModel (E:=E)) z₀) z v)) hl
  change _ = coordinateLiouville _ _ at hla
  apply hla.symm.trans
  unfold liouvilleInChart
  change liouville ((extChartAt (cotangentModel (E:=E)) z₀).symm
      (extChartAt (cotangentModel (E:=E)) z₀ z))
    (((mfderiv 𝓘(ℝ,E × (E →L[ℝ] ℝ)) (cotangentModel (E:=E))
        (extChartAt (cotangentModel (E:=E)) z₀).symm
        (extChartAt (cotangentModel (E:=E)) z₀ z)).comp
      (mfderiv (cotangentModel (E:=E)) 𝓘(ℝ,E × (E →L[ℝ] ℝ))
        (extChartAt (cotangentModel (E:=E)) z₀) z)) v) = _
  have hdv := congrArg (fun A : (E × (E →L[ℝ] ℝ)) →L[ℝ] (E × (E →L[ℝ] ℝ)) => A v) hd
  exact (congrArg (liouville ((extChartAt (cotangentModel (E:=E)) z₀).symm
    (extChartAt (cotangentModel (E:=E)) z₀ z)) : (E × (E →L[ℝ] ℝ)) →L[ℝ] ℝ) hdv).trans
      (congrArg (fun w : Cotangent (E:=E) (M:=M) =>
        (liouville w : (E × (E →L[ℝ] ℝ)) →L[ℝ] ℝ) v)
          ((extChartAt (cotangentModel (E:=E)) z₀).left_inv hz))

theorem symplectic_of_liouville
    {i : Cotangent (E:=E) (M:=M) → Cotangent (E:=F) (M:=N)}
    (hi : ContMDiff (cotangentModel (E:=E)) (cotangentModel (E:=F)) ∞ i)
    (hl : ∀ z (u : TangentSpace (cotangentModel (E:=E)) z),
      liouville (i z) (mfderiv (cotangentModel (E:=E)) (cotangentModel (E:=F)) i z u) =
        liouville z u)
    (z : Cotangent (E:=E) (M:=M)) (u v : TangentSpace (cotangentModel (E:=E)) z) :
    symplecticForm (i z)
      (mfderiv (cotangentModel (E:=E)) (cotangentModel (E:=F)) i z u)
      (mfderiv (cotangentModel (E:=E)) (cotangentModel (E:=F)) i z v) =
      symplecticForm z u v := by
  classical
  let c := extChartAt (cotangentModel (E:=E)) z
  let d := extChartAt (cotangentModel (E:=F)) (i z)
  let x := c z
  let J := d ∘ i ∘ c.symm
  have hx : x ∈ c.target := mem_extChartAt_target z
  have hcx : c.symm x = z := c.left_inv (mem_extChartAt_source z)
  have hJ : ContDiffAt ℝ ∞ J x := by
    have h := (contMDiffAt_iff.mp (hi z)).2
    simpa only [J,x,c,d,cotangentModel, ← modelWithCornersSelf_prod, modelWithCornersSelf_coe,
      range_id, contDiffWithinAt_univ] using h
  have hid := (hi z).mdifferentiableAt (by simp)
  have hmfd : (mfderiv (cotangentModel (E:=E)) (cotangentModel (E:=F)) i z :
      (E × (E →L[ℝ] ℝ)) →L[ℝ] (F × (F →L[ℝ] ℝ))) = fderiv ℝ J x := by
    change (if MDifferentiableAt (cotangentModel (E:=E)) (cotangentModel (E:=F)) i z then
      fderivWithin ℝ J (range (cotangentModel (E:=E))) x else 0) = _
    rw [ite_eq_left hid]
    have hr : range (cotangentModel (E:=E)) = univ := by
      simp only [cotangentModel, ← modelWithCornersSelf_prod, modelWithCornersSelf_coe, range_id]
    rw [hr, fderivWithin_univ]
  have hcs : ContMDiffAt 𝓘(ℝ,E × (E →L[ℝ] ℝ)) (cotangentModel (E:=E)) ∞ c.symm x :=
    (contMDiffOn_extChartAt_symm z).contMDiffAt ((isOpen_extChartAt_target z).mem_nhds hx)
  have hic := (hi (c.symm x)).comp x hcs
  have hsource : i (c.symm x) ∈ d.source := by
    rw [hcx]
    exact mem_extChartAt_source (i z)
  have hnear := hic.continuousAt.eventually ((isOpen_extChartAt_source (i z)).mem_nhds hsource)
  have hlam : (fun y => (coordinateLiouville (J y)).comp (fderiv ℝ J y)) =ᶠ[𝓝 x]
      coordinateLiouville (E:=E) := by
    filter_upwards [(isOpen_extChartAt_target z).mem_nhds hx,hnear] with y hy hy'
    have hcy := mdifferentiableAt_extChartAt_symm hy
    have hiy := (hi (c.symm y)).mdifferentiableAt (by simp)
    have hdy : MDifferentiableAt (cotangentModel (E:=F)) 𝓘(ℝ,F × (F →L[ℝ] ℝ))
        d (i (c.symm y)) :=
      (contMDiffAt_extChartAt' (I:=cotangentModel (E:=F)) (x:=i z) (n:=∞) (by
        rw [← extChartAt_source (cotangentModel (E:=F)) (i z)]
        exact hy')).mdifferentiableAt (by simp)
    have hjd : fderiv ℝ J y =
        (mfderiv (cotangentModel (E:=F)) 𝓘(ℝ,F × (F →L[ℝ] ℝ)) d (i (c.symm y))).comp
          ((mfderiv (cotangentModel (E:=E)) (cotangentModel (E:=F)) i (c.symm y)).comp
            (mfderiv 𝓘(ℝ,E × (E →L[ℝ] ℝ)) (cotangentModel (E:=E)) c.symm y)) := by
      change fderiv ℝ (d ∘ (i ∘ c.symm)) y = _
      rw [← mfderiv_eq_fderiv, mfderiv_comp y hdy (hiy.comp y hcy),
        mfderiv_comp y hiy hcy]
      rfl
    apply ContinuousLinearMap.ext
    intro w
    have he := congrArg (fun A : (E × (E →L[ℝ] ℝ)) →L[ℝ] (F × (F →L[ℝ] ℝ)) => A w) hjd
    have h₁ := coordinateLiouville_extChartAt hy'
      (mfderiv (cotangentModel (E:=E)) (cotangentModel (E:=F)) i (c.symm y)
        (mfderiv 𝓘(ℝ,E × (E →L[ℝ] ℝ)) (cotangentModel (E:=E)) c.symm y w))
    have h₂ := hl (c.symm y)
      (mfderiv 𝓘(ℝ,E × (E →L[ℝ] ℝ)) (cotangentModel (E:=E)) c.symm y w)
    have h₃ := congrArg (fun A : (E × (E →L[ℝ] ℝ)) →L[ℝ] ℝ => A w) (liouvilleInChart_eq hy)
    exact (congrArg (coordinateLiouville (J y)) he).trans (h₁.trans (h₂.trans h₃))
  have h := canonical_symplectic_of_liouville_map hJ hlam u v
  have he := congrArg (fun A : (E × (E →L[ℝ] ℝ)) →L[ℝ] (F × (F →L[ℝ] ℝ)) =>
    (A u).2 (A v).1 - (A v).2 (A u).1) hmfd
  exact (symplecticForm_eq _ _ _).trans (he.trans (h.trans (symplecticForm_eq z u v).symm))

end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.CotangentGeometry
open scoped ContDiff Topology Manifold
open Filter ContinuousLinearMap Set Function
section Coordinates
variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : NormedAddCommGroup ((E × (E →L[ℝ] ℝ)) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

lemma canonical_pullback_exterior {J : X → E × (E →L[ℝ] ℝ)} {x : X}
    (hJ : ContDiffAt ℝ ∞ J x) (u v : X) :
    let α : X → X →L[ℝ] ℝ := fun y => (coordinateLiouville (J y)).comp (fderiv ℝ J y)
    DifferentiableAt ℝ α x ∧
    fderiv ℝ α x u v - fderiv ℝ α x v u =
      (fderiv ℝ J x u).2 (fderiv ℝ J x v).1 -
        (fderiv ℝ J x v).2 (fderiv ℝ J x u).1 := by
  dsimp only
  have hd := hJ.differentiableAt (by simp)
  have hD : DifferentiableAt ℝ (fderiv ℝ J) x := (hJ.fderiv_right (m:=1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
  have hC : DifferentiableAt ℝ (coordinateLiouville (E:=E)) (J x) := by
    exact (coordinateLiouville (E:=E)).differentiableAt
  have hL : DifferentiableAt ℝ (fun y => coordinateLiouville (J y)) x :=
    DifferentiableAt.comp (g:=fun y : E × (E →L[ℝ] ℝ) => coordinateLiouville y) x hC hd
  have hl : DifferentiableAt ℝ
      (fun y => (coordinateLiouville (J y)).comp (fderiv ℝ J y)) x := hL.clm_comp hD
  refine ⟨hl,?_⟩
  rw [fderiv_clm_comp hL hD]
  have hcoords : fderiv ℝ (fun y => coordinateLiouville (J y)) x =
      (coordinateLiouville (E:=E)).comp (fderiv ℝ J x) :=
    by
      change fderiv ℝ ((fun y : E × (E →L[ℝ] ℝ) => coordinateLiouville y) ∘ J) x = _
      rw [fderiv_comp (g:=fun y : E × (E →L[ℝ] ℝ) => coordinateLiouville y) x hC hd, ContinuousLinearMap.fderiv]
  rw [hcoords]
  change (J x).2 ((fderiv ℝ (fderiv ℝ J) x u v).1) +
      (fderiv ℝ J x u).2 (fderiv ℝ J x v).1 -
    ((J x).2 ((fderiv ℝ (fderiv ℝ J) x v u).1) +
      (fderiv ℝ J x v).2 (fderiv ℝ J x u).1) = _
  have hsym := (hJ.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)).eq u v
  rw [hsym]
  ring
end Coordinates

variable {X E M : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : ChartedSpace (E × (E →L[ℝ] ℝ)) (Cotangent (E:=E) (M:=M)) :=
  inferInstanceAs (ChartedSpace (ModelProd E (E →L[ℝ] ℝ)) (Cotangent (E:=E) (M:=M)))

theorem liouville_pullback_exterior {i : X → Cotangent (E:=E) (M:=M)} {x : X}
    (hi : ContMDiffAt 𝓘(ℝ,X) (cotangentModel (E:=E)) ∞ i x) (u v : X) :
    let α : X → X →L[ℝ] ℝ := fun y => (liouville (i y)).comp
      (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=E)) i y)
    DifferentiableAt ℝ α x ∧
    fderiv ℝ α x u v - fderiv ℝ α x v u =
      symplecticForm (i x)
        (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=E)) i x u)
        (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=E)) i x v) := by
  dsimp only
  let d := extChartAt (cotangentModel (E:=E)) (i x)
  let J := d ∘ i
  have hs : i x ∈ d.source := mem_extChartAt_source (i x)
  have hdi : ContMDiffAt (cotangentModel (E:=E)) 𝓘(ℝ,E × (E →L[ℝ] ℝ)) ∞ d (i x) :=
    contMDiffAt_extChartAt' (I:=cotangentModel (E:=E)) (x:=i x) (n:=∞) (by
      rw [← extChartAt_source (cotangentModel (E:=E)) (i x)]
      exact hs)
  have hJ : ContDiffAt ℝ ∞ J x := (hdi.comp x hi).contDiffAt
  have h1 : ContMDiffAt 𝓘(ℝ,X) (cotangentModel (E:=E)) 1 i x :=
    hi.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hnear := hi.continuousAt.eventually ((isOpen_extChartAt_source (i x)).mem_nhds hs)
  have heq : (fun y => ((liouville (i y)).comp
      (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=E)) i y) : X →L[ℝ] ℝ)) =ᶠ[𝓝 x]
      (fun y => (coordinateLiouville (J y)).comp (fderiv ℝ J y)) := by
    filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp h1,hnear] with y hy hys
    have hdy : MDifferentiableAt (cotangentModel (E:=E)) 𝓘(ℝ,E × (E →L[ℝ] ℝ)) d (i y) :=
      (contMDiffAt_extChartAt' (I:=cotangentModel (E:=E)) (x:=i x) (n:=∞) (by
        rw [← extChartAt_source (cotangentModel (E:=E)) (i x)]
        exact hys)).mdifferentiableAt (by simp)
    have hjd : fderiv ℝ J y =
        (mfderiv (cotangentModel (E:=E)) 𝓘(ℝ,E × (E →L[ℝ] ℝ)) d (i y)).comp
          (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=E)) i y) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp y hdy (hy.mdifferentiableAt one_ne_zero)
    apply ContinuousLinearMap.ext
    intro w
    rw [hjd]
    exact (coordinateLiouville_extChartAt hys _).symm
  have h := canonical_pullback_exterior hJ u v
  refine ⟨h.1.congr_of_eventuallyEq heq,?_⟩
  rw [heq.fderiv_eq]
  have hd : fderiv ℝ J x =
      (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=E)) i x : X →L[ℝ] E × (E →L[ℝ] ℝ)) := by
    rw [← mfderiv_eq_fderiv]
    change mfderiv 𝓘(ℝ,X) 𝓘(ℝ,E × (E →L[ℝ] ℝ)) (d ∘ i) x = _
    rw [mfderiv_comp x (hdi.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp))]
    dsimp only [d]
    erw [mfderiv_extChartAt_self]
    rfl
  rw [symplecticForm_eq,← hd]
  exact h.2
end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.CotangentGeometry
open scoped ContDiff Topology Manifold
open Filter ContinuousLinearMap Set Function
variable {X E F G M N P : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℝ,G) ∞ P]
local instance (A B : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
    [TopologicalSpace B] [ChartedSpace A B] [IsManifold 𝓘(ℝ,A) ∞ B] :
    ChartedSpace (A × (A →L[ℝ] ℝ)) (Cotangent (E:=A) (M:=B)) :=
  inferInstanceAs (ChartedSpace (ModelProd A (A →L[ℝ] ℝ)) (Cotangent (E:=A) (M:=B)))

theorem symplectic_sum_of_liouville
    {i : X → Cotangent (E:=E) (M:=M)}
    {j : X → Cotangent (E:=F) (M:=N)}
    {k : X → Cotangent (E:=G) (M:=P)} {x : X}
    (hi : ContMDiffAt 𝓘(ℝ,X) (cotangentModel (E:=E)) ∞ i x)
    (hj : ContMDiffAt 𝓘(ℝ,X) (cotangentModel (E:=F)) ∞ j x)
    (hk : ContMDiffAt 𝓘(ℝ,X) (cotangentModel (E:=G)) ∞ k x)
    (hl : ∀ᶠ y in 𝓝 x, ∀ w : X,
      liouville (k y) (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=G)) k y w) =
      liouville (i y) (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=E)) i y w) +
      liouville (j y) (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=F)) j y w)) (u v : X) :
    symplecticForm (k x)
      (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=G)) k x u)
      (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=G)) k x v) =
    symplecticForm (i x)
      (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=E)) i x u)
      (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=E)) i x v) +
    symplecticForm (j x)
      (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=F)) j x u)
      (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=F)) j x v) := by
  let α : X → X →L[ℝ] ℝ := fun y => (liouville (i y)).comp
    (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=E)) i y)
  let β : X → X →L[ℝ] ℝ := fun y => (liouville (j y)).comp
    (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=F)) j y)
  let γ : X → X →L[ℝ] ℝ := fun y => (liouville (k y)).comp
    (mfderiv 𝓘(ℝ,X) (cotangentModel (E:=G)) k y)
  have he : γ =ᶠ[𝓝 x] (α+β) := by
    filter_upwards [hl] with y hy
    exact ContinuousLinearMap.ext (hy)
  have hα := liouville_pullback_exterior hi u v
  have hβ := liouville_pullback_exterior hj u v
  have hγ := liouville_pullback_exterior hk u v
  change DifferentiableAt ℝ α x ∧ _ at hα
  change DifferentiableAt ℝ β x ∧ _ at hβ
  change DifferentiableAt ℝ γ x ∧ _ at hγ
  rw [← hγ.2, he.fderiv_eq, fderiv_add hα.1 hβ.1, ← hα.2, ← hβ.2]
  simp only [add_apply]
  ring
end NearbyLagrangian.CotangentGeometry

end

end OAI
