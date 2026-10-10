import Mathlib
import OAI.Geometry.BallPacking.Forms.QuadricInfinityPrimitive
import OAI.Geometry.BallPacking.Forms.ManifoldFormTransport

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {F E V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def globalHorizontalCoupling (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    (Γ : V → ManifoldOneForm E M) : ManifoldTwoForm (E × V) (M × V) := fun x =>
  Ω.bilinearComp (ContinuousLinearMap.snd ℝ E V) (ContinuousLinearMap.snd ℝ E V)+
    manifoldExteriorOneForm (productHorizontalLift Γ) x

theorem globalHorizontalCoupling_pullback {Ω : V →L[ℝ] V →L[ℝ] ℝ}
    {Γ : V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {g : F → M} {x : F × V} (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x.1) :
    (globalHorizontalCoupling Ω Γ (flatProductMap g x)).bilinearComp
        ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1).prodMap (ContinuousLinearMap.id ℝ V))
        ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1).prodMap (ContinuousLinearMap.id ℝ V))=
      Ω.bilinearComp (ContinuousLinearMap.snd ℝ F V) (ContinuousLinearMap.snd ℝ F V)+
        euclideanExteriorOneForm
          (fun y => euclideanPullbackOneForm (fun _ => productHorizontalLift Γ) (flatProductMap g) (0,y)) x := by
  rw [productHorizontalLift_exterior_pullback hΓ hg]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rfl

theorem globalHorizontalCoupling_isInvertible_coordinates {Ω : V →L[ℝ] V →L[ℝ] ℝ}
    {Γ : V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {g : F → M} {x : F × V} (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g x.1)
    (c : F ≃L[ℝ] E) (hc : (c : F →L[ℝ] E)=mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1)
    (h : (Ω.bilinearComp (ContinuousLinearMap.snd ℝ F V) (ContinuousLinearMap.snd ℝ F V)+
        euclideanExteriorOneForm
          (fun y => euclideanPullbackOneForm (fun _ => productHorizontalLift Γ) (flatProductMap g) (0,y)) x).IsInvertible) :
    (globalHorizontalCoupling Ω Γ (flatProductMap g x)).IsInvertible := by
  apply (bilinearComp_equiv_isInvertible_iff (c.prodCongr (ContinuousLinearEquiv.refl ℝ V))).mp
  have he : ((c.prodCongr (ContinuousLinearEquiv.refl ℝ V)) : (F × V) →L[ℝ] E × V)=
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g x.1).prodMap (ContinuousLinearMap.id ℝ V) := by
    change (c : F →L[ℝ] E).prodMap (ContinuousLinearMap.id ℝ V)=_
    rw [hc]
    rfl
  rw [he,globalHorizontalCoupling_pullback hΓ hg]
  exact h


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

structure IsPrimitiveFamily (Ω : P → ManifoldTwoForm E M) (α : P → ManifoldOneForm E M) : Prop where
  smooth : SmoothOneFormFamily α
  exterior : ∀ p c y, y ∈ (extChartAt 𝓘(ℝ,E) c).target →
    euclideanExteriorOneForm (chartOneForm (α p) c) y = chartTwoForm (Ω p) c y

namespace IsPrimitiveFamily

theorem zero : IsPrimitiveFamily (0 : P → ManifoldTwoForm E M) 0 := by
  constructor
  · intro c
    simpa only [Pi.zero_apply,chartOneForm_zero] using
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : P × E => (0 : E →L[ℝ] ℝ)) _)
  · intro p c y _
    change euclideanExteriorOneForm (chartOneForm 0 c) y = chartTwoForm 0 c y
    rw [show chartOneForm (0 : ManifoldOneForm E M) c = fun _ => 0 from funext fun z => chartOneForm_zero c z]
    simp only [chartTwoForm_zero,euclideanExteriorOneForm,fderiv_const_apply,ContinuousLinearMap.flip_zero]
    exact sub_self (0 : E →L[ℝ] E →L[ℝ] ℝ)

theorem add {Ω Λ : P → ManifoldTwoForm E M} {α β : P → ManifoldOneForm E M}
    (hα : IsPrimitiveFamily Ω α) (hβ : IsPrimitiveFamily Λ β) :
    IsPrimitiveFamily (Ω+Λ) (α+β) := by
  constructor
  · intro c
    simpa only [Pi.add_apply,chartOneForm_add] using (hα.smooth c).add (hβ.smooth c)
  · intro p c y hy
    simp only [Pi.add_apply,chartTwoForm_add]
    rw [show chartOneForm (α p + β p) c =
      chartOneForm (α p) c + chartOneForm (β p) c from funext fun z => chartOneForm_add _ _ c z]
    rw [euclideanExteriorOneForm_add ((hα.smooth.spatial_smooth p c hy).differentiableAt (by simp))
      ((hβ.smooth.spatial_smooth p c hy).differentiableAt (by simp)),hα.exterior p c y hy,hβ.exterior p c y hy]

theorem smul {Ω : P → ManifoldTwoForm E M} {α : P → ManifoldOneForm E M}
    (hα : IsPrimitiveFamily Ω α) {f : P → ℝ} (hf : ContDiff ℝ ∞ f) :
    IsPrimitiveFamily (fun p => f p • Ω p) (fun p => f p • α p) := by
  constructor
  · intro c
    simpa only [chartOneForm_smul,Function.comp_apply,Pi.smul_def'] using
      (hf.comp contDiff_fst).contDiffOn.smul (hα.smooth c)
  · intro p c y hy
    simp only [chartTwoForm_smul]
    rw [show chartOneForm (f p • α p) c = f p • chartOneForm (α p) c from
      funext fun z => chartOneForm_smul _ _ c z]
    rw [euclideanExteriorOneForm_smul _ ((hα.smooth.spatial_smooth p c hy).differentiableAt (by simp)),
      hα.exterior p c y hy]

theorem sum {I : Type*} (s : Finset I) {Ω : I → P → ManifoldTwoForm E M}
    {α : I → P → ManifoldOneForm E M} (hα : ∀ i ∈ s, IsPrimitiveFamily (Ω i) (α i)) :
    IsPrimitiveFamily (∑ i ∈ s, Ω i) (∑ i ∈ s, α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using zero (P := P) (E := E) (M := M)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (hα i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hα j (Finset.mem_insert_of_mem hj)))

theorem const_slice {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {Ω : Q → ManifoldTwoForm E M} {α : Q → ManifoldOneForm E M}
    (hα : IsPrimitiveFamily Ω α) (q : Q) :
    IsPrimitiveFamily (fun _ : P => Ω q) (fun _ : P => α q) := by
  constructor
  · intro c
    apply (hα.smooth c).comp (f := fun t : P × E => (q,t.2))
      (contDiffOn_const.prodMk contDiffOn_snd)
    exact fun t ht => ⟨mem_univ _,ht.2⟩
  · intro _ c y hy
    exact hα.exterior q c y hy

end IsPrimitiveFamily

end

section
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pathSpatialExterior (Γ : ℝ × E → E →L[ℝ] ℝ) (p : ℝ × E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (fderiv ℝ Γ p).comp (ContinuousLinearMap.inr ℝ ℝ E) -
    ((fderiv ℝ Γ p).comp (ContinuousLinearMap.inr ℝ ℝ E)).flip

def pathTimePrimitive (Γ : ℝ × E → E →L[ℝ] ℝ) (p : ℝ × E) : E →L[ℝ] ℝ :=
  fderiv ℝ Γ p (1,0)

@[simp] theorem pathSpatialExterior_apply (Γ : ℝ × E → E →L[ℝ] ℝ) (p : ℝ × E) (v w : E) :
    pathSpatialExterior Γ p v w = fderiv ℝ Γ p (0,v) w - fderiv ℝ Γ p (0,w) v := rfl

@[fun_prop] theorem pathSpatialExterior_smooth {Γ : ℝ × E → E →L[ℝ] ℝ}
    (hΓ : ContDiff ℝ ∞ Γ) : ContDiff ℝ ∞ (pathSpatialExterior Γ) := by
  have hd : ContDiff ℝ ∞ (fun p => (fderiv ℝ Γ p).comp (ContinuousLinearMap.inr ℝ ℝ E)) :=
    (hΓ.fderiv_right (by simp)).clm_comp contDiff_const
  have hflip : ContDiff ℝ ∞ (fun L : E →L[ℝ] E →L[ℝ] ℝ => L.flip) :=
    LinearIsometryEquiv.contDiff (𝕜 := ℝ) (n := ∞) (E := E →L[ℝ] E →L[ℝ] ℝ)
      (F := E →L[ℝ] E →L[ℝ] ℝ) (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ)
  exact hd.sub (hflip.comp hd)

@[fun_prop] theorem pathTimePrimitive_smooth {Γ : ℝ × E → E →L[ℝ] ℝ}
    (hΓ : ContDiff ℝ ∞ Γ) : ContDiff ℝ ∞ (pathTimePrimitive Γ) :=
  (hΓ.fderiv_right (by simp)).clm_apply contDiff_const

theorem fderiv_evaluation_const {P F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : P → F →L[ℝ] G} {p : P} (hg : DifferentiableAt ℝ g p) (u : P) (v : F) :
    fderiv ℝ (fun q => g q v) p u = fderiv ℝ g p u v := by
  rw [(hg.hasFDerivAt.clm_apply (hasFDerivAt_const v p)).fderiv]
  simp

theorem pathSpatialExterior_fderiv {Γ : ℝ × E → E →L[ℝ] ℝ}
    (hΓ : ContDiff ℝ ∞ Γ) (p u : ℝ × E) (v w : E) :
    fderiv ℝ (pathSpatialExterior Γ) p u v w =
      fderiv ℝ (fderiv ℝ Γ) p u (0,v) w - fderiv ℝ (fderiv ℝ Γ) p u (0,w) v := by
  have hD := (hΓ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p
  have hΩ := (pathSpatialExterior_smooth hΓ).differentiable (by simp) p
  rw [←fderiv_evaluation_const hΩ u v,
    ←fderiv_evaluation_const (hΩ.clm_apply (differentiableAt_const v)) u w]
  simp only [pathSpatialExterior_apply]
  change fderiv ℝ ((fun q => fderiv ℝ Γ q (0,v) w)-(fun q => fderiv ℝ Γ q (0,w) v)) p u = _
  rw [fderiv_sub (hD.clm_apply (differentiableAt_const (0,v)) |>.clm_apply (differentiableAt_const w))
    (hD.clm_apply (differentiableAt_const (0,w)) |>.clm_apply (differentiableAt_const v))]
  simp only [sub_apply,fderiv_evaluation_const (hD.clm_apply (differentiableAt_const (0,v))),
    fderiv_evaluation_const (hD.clm_apply (differentiableAt_const (0,w))),fderiv_evaluation_const hD]

theorem pathTimePrimitive_fderiv {Γ : ℝ × E → E →L[ℝ] ℝ}
    (hΓ : ContDiff ℝ ∞ Γ) (p u : ℝ × E) (v : E) :
    fderiv ℝ (pathTimePrimitive Γ) p u v = fderiv ℝ (fderiv ℝ Γ) p u (1,0) v := by
  have hD := (hΓ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p
  rw [←fderiv_evaluation_const ((pathTimePrimitive_smooth hΓ).differentiable (by simp) p)]
  simp only [pathTimePrimitive,fderiv_evaluation_const (hD.clm_apply (differentiableAt_const (1,0))),
    fderiv_evaluation_const hD]

theorem exact_path_time_equation {Γ : ℝ × E → E →L[ℝ] ℝ}
    (hΓ : ContDiff ℝ ∞ Γ) (p : ℝ × E) (v w : E) :
    fderiv ℝ (pathSpatialExterior Γ) p (1,0) v w =
      fderiv ℝ (pathTimePrimitive Γ) p (0,v) w -
        fderiv ℝ (pathTimePrimitive Γ) p (0,w) v := by
  have hs := (hΓ.contDiffAt (x := p)).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [pathSpatialExterior_fderiv hΓ,pathTimePrimitive_fderiv hΓ]
  rw [hs.eq (1,0) (0,v),hs.eq (1,0) (0,w)]

theorem exact_path_closed {Γ : ℝ × E → E →L[ℝ] ℝ}
    (hΓ : ContDiff ℝ ∞ Γ) (p : ℝ × E) (u v w : E) :
    fderiv ℝ (pathSpatialExterior Γ) p (0,u) v w -
      fderiv ℝ (pathSpatialExterior Γ) p (0,v) u w +
      fderiv ℝ (pathSpatialExterior Γ) p (0,w) u v = 0 := by
  have hs := (hΓ.contDiffAt (x := p)).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [pathSpatialExterior_fderiv hΓ]
  rw [hs.eq (0,u) (0,v),hs.eq (0,u) (0,w),hs.eq (0,v) (0,w)]
  ring



@[fun_prop] theorem pathSpatialExterior_smoothAt {Γ : ℝ × E → E →L[ℝ] ℝ}
    {p : ℝ × E} (hΓ : ContDiffAt ℝ ∞ Γ p) : ContDiffAt ℝ ∞ (pathSpatialExterior Γ) p := by
  have hd : ContDiffAt ℝ ∞ (fun q => (fderiv ℝ Γ q).comp (ContinuousLinearMap.inr ℝ ℝ E)) p :=
    (hΓ.fderiv_right (by simp)).clm_comp contDiffAt_const
  have hflip : ContDiff ℝ ∞ (fun L : E →L[ℝ] E →L[ℝ] ℝ => L.flip) :=
    LinearIsometryEquiv.contDiff (𝕜 := ℝ) (n := ∞) (E := E →L[ℝ] E →L[ℝ] ℝ)
      (F := E →L[ℝ] E →L[ℝ] ℝ) (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ)
  exact hd.sub (hflip.contDiffAt.comp p hd)

@[fun_prop] theorem pathTimePrimitive_smoothAt {Γ : ℝ × E → E →L[ℝ] ℝ}
    {p : ℝ × E} (hΓ : ContDiffAt ℝ ∞ Γ p) : ContDiffAt ℝ ∞ (pathTimePrimitive Γ) p :=
  (hΓ.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem pathSpatialExterior_fderivAt {Γ : ℝ × E → E →L[ℝ] ℝ}
    {p : ℝ × E} (hΓ : ContDiffAt ℝ ∞ Γ p) (u : ℝ × E) (v w : E) :
    fderiv ℝ (pathSpatialExterior Γ) p u v w =
      fderiv ℝ (fderiv ℝ Γ) p u (0,v) w - fderiv ℝ (fderiv ℝ Γ) p u (0,w) v := by
  have hD := (hΓ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hΩ := (pathSpatialExterior_smoothAt hΓ).differentiableAt (by simp)
  rw [←fderiv_evaluation_const hΩ u v,
    ←fderiv_evaluation_const (hΩ.clm_apply (differentiableAt_const v)) u w]
  simp only [pathSpatialExterior_apply]
  change fderiv ℝ ((fun q => fderiv ℝ Γ q (0,v) w)-(fun q => fderiv ℝ Γ q (0,w) v)) p u = _
  rw [fderiv_sub (hD.clm_apply (differentiableAt_const (0,v)) |>.clm_apply (differentiableAt_const w))
    (hD.clm_apply (differentiableAt_const (0,w)) |>.clm_apply (differentiableAt_const v))]
  simp only [sub_apply,fderiv_evaluation_const (hD.clm_apply (differentiableAt_const (0,v))),
    fderiv_evaluation_const (hD.clm_apply (differentiableAt_const (0,w))),fderiv_evaluation_const hD]

theorem pathTimePrimitive_fderivAt {Γ : ℝ × E → E →L[ℝ] ℝ}
    {p : ℝ × E} (hΓ : ContDiffAt ℝ ∞ Γ p) (u : ℝ × E) (v : E) :
    fderiv ℝ (pathTimePrimitive Γ) p u v = fderiv ℝ (fderiv ℝ Γ) p u (1,0) v := by
  have hD := (hΓ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  rw [←fderiv_evaluation_const ((pathTimePrimitive_smoothAt hΓ).differentiableAt (by simp))]
  simp only [pathTimePrimitive,fderiv_evaluation_const (hD.clm_apply (differentiableAt_const (1,0))),
    fderiv_evaluation_const hD]

theorem exact_path_time_equationAt {Γ : ℝ × E → E →L[ℝ] ℝ}
    {p : ℝ × E} (hΓ : ContDiffAt ℝ ∞ Γ p) (v w : E) :
    fderiv ℝ (pathSpatialExterior Γ) p (1,0) v w =
      fderiv ℝ (pathTimePrimitive Γ) p (0,v) w -
        fderiv ℝ (pathTimePrimitive Γ) p (0,w) v := by
  have hs := hΓ.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [pathSpatialExterior_fderivAt hΓ,pathTimePrimitive_fderivAt hΓ]
  rw [hs.eq (1,0) (0,v),hs.eq (1,0) (0,w)]

theorem exact_path_closedAt {Γ : ℝ × E → E →L[ℝ] ℝ}
    {p : ℝ × E} (hΓ : ContDiffAt ℝ ∞ Γ p) (u v w : E) :
    fderiv ℝ (pathSpatialExterior Γ) p (0,u) v w -
      fderiv ℝ (pathSpatialExterior Γ) p (0,v) u w +
      fderiv ℝ (pathSpatialExterior Γ) p (0,w) u v = 0 := by
  have hs := hΓ.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [pathSpatialExterior_fderivAt hΓ]
  rw [hs.eq (0,u) (0,v),hs.eq (0,u) (0,w),hs.eq (0,v) (0,w)]
  ring


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def manifoldTimePrimitive (Γ : ℝ → ManifoldOneForm E M) (t : ℝ) : ManifoldOneForm E M :=
  fun x => deriv (fun s => Γ s x) t

theorem chartOneForm_reconstruct_target {α : ManifoldOneForm E M} {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    (chartOneForm α c y).comp (chartDifferential c ((extChartAt 𝓘(ℝ,E) c).symm y)) =
      α ((extChartAt 𝓘(ℝ,E) c).symm y) := by
  have hC : (chartDifferential (E := E) c ((extChartAt 𝓘(ℝ,E) c).symm y)).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) ((extChartAt 𝓘(ℝ,E) c).map_target hy) using 1
  ext v
  exact congrArg (α ((extChartAt 𝓘(ℝ,E) c).symm y)) (hC.inverse_apply_self v)

theorem manifoldTimePrimitive_chart {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {c : M} {t : ℝ} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    chartOneForm (manifoldTimePrimitive Γ t) c y =
      pathTimePrimitive (fun q : ℝ × E => chartOneForm (Γ q.1) c q.2) (t,y) := by
  let F : ℝ × E → E →L[ℝ] ℝ := fun q => chartOneForm (Γ q.1) c q.2
  let x := (extChartAt 𝓘(ℝ,E) c).symm y
  have hF : ContDiffAt ℝ ∞ F (t,y) := (hΓ c).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds
    (show (t,y) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target from ⟨mem_univ t,hy⟩))
  have hdf : HasFDerivAt F (fderiv ℝ F (t,y)) (t,y) :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  have hinc : HasDerivAt (fun s : ℝ => (s,y)) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  have hd : HasDerivAt (fun s => F (s,y)) (pathTimePrimitive F (t,y)) t := by
    have hh := hdf.comp_hasDerivAt t hinc
    simpa only [Function.comp_def,pathTimePrimitive] using hh
  have he : (fun s => (F (s,y)).comp (chartDifferential c x)) = fun s => Γ s x := by
    funext s
    exact chartOneForm_reconstruct_target hy
  have hdn := hd.clm_comp (hasDerivAt_const t (chartDifferential c x))
  rw [he] at hdn
  have hC : (chartDifferential (E := E) c x).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) ((extChartAt 𝓘(ℝ,E) c).map_target hy) using 1
  have hdne : deriv (fun s => Γ s x) t = (pathTimePrimitive F (t,y)).comp (chartDifferential c x) := by
    simpa only [ContinuousLinearMap.comp_zero,add_zero] using hdn.deriv
  unfold chartOneForm manifoldTimePrimitive
  change (deriv (fun s => Γ s x) t).comp (chartDifferential c x).inverse = _
  rw [hdne]
  apply ContinuousLinearMap.ext
  intro v
  change pathTimePrimitive F (t,y) ((chartDifferential c x) ((chartDifferential c x).inverse v)) =
    pathTimePrimitive F (t,y) v
  exact congrArg (pathTimePrimitive F (t,y)) (hC.self_apply_inverse v)

theorem pathSpatialExterior_eq_slice {Γ : ℝ × E → E →L[ℝ] ℝ} {p : ℝ × E}
    (hΓ : DifferentiableAt ℝ Γ p) :
    pathSpatialExterior Γ p = euclideanExteriorOneForm (fun y => Γ (p.1,y)) p.2 := by
  have hi : HasFDerivAt (fun y : E => (p.1,y))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hh : HasFDerivAt Γ (fderiv ℝ Γ p) (p.1,p.2) := hΓ.hasFDerivAt
  have hd := (hh.comp p.2 hi).fderiv
  change fderiv ℝ (fun y => Γ (p.1,y)) p.2 = _ at hd
  unfold euclideanExteriorOneForm
  rw [hd]
  rfl

theorem manifoldExteriorOneForm_path_chart {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {c : M} {t : ℝ} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    chartTwoForm (manifoldExteriorOneForm (Γ t)) c y =
      pathSpatialExterior (fun q : ℝ × E => chartOneForm (Γ q.1) c q.2) (t,y) := by
  rw [manifoldExteriorOneForm_chart (fun b z hz => (hΓ.spatial_smooth t b hz).contDiffWithinAt) hy]
  exact (pathSpatialExterior_eq_slice ((hΓ c).contDiffAt
    ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds (show (t,y) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target from ⟨mem_univ t,hy⟩))
      |>.differentiableAt (by simp))).symm

theorem manifoldExteriorOneForm_path_smooth {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) : SmoothTwoFormFamily (fun t => manifoldExteriorOneForm (Γ t)) := by
  intro c p hp
  have hn := (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds hp
  apply ((pathSpatialExterior_smoothAt ((hΓ c).contDiffAt hn)).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hn] with q hq
  exact manifoldExteriorOneForm_path_chart hΓ hq.2

theorem manifoldTimePrimitive_smooth {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) : SmoothOneFormFamily (manifoldTimePrimitive Γ) := by
  intro c p hp
  have hn := (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds hp
  apply ((pathTimePrimitive_smoothAt ((hΓ c).contDiffAt hn)).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hn] with q hq
  exact manifoldTimePrimitive_chart hΓ hq.2


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

def manifoldWedge (α β : ManifoldOneForm E M) : ManifoldTwoForm E M :=
  fun z => (α z).smulRight (β z)-(β z).smulRight (α z)

@[simp] theorem manifoldWedge_apply (α β : ManifoldOneForm E M) (z : M) (v w : E) :
    manifoldWedge α β z v w=α z v*β z w-β z v*α z w := rfl

theorem manifoldWedge_skew (α β : ManifoldOneForm E M) (z : M) (v w : E) :
    manifoldWedge α β z v w= -manifoldWedge α β z w v := by
  simp only [manifoldWedge_apply]
  ring

theorem chartTwoForm_wedge (α β : ManifoldOneForm E M) (c : M) (y : E) :
    chartTwoForm (manifoldWedge α β) c y =
      (chartOneForm α c y).smulRight (chartOneForm β c y)-
      (chartOneForm β c y).smulRight (chartOneForm α c y) := by
  ext v w
  rfl

theorem manifoldWedge_smooth {α β : ManifoldOneForm E M}
    (hα : ∀ c,ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    (hβ : ∀ c,ContDiffOn ℝ ∞ (chartOneForm β c) (extChartAt 𝓘(ℝ,E) c).target) :
    SmoothTwoForm (manifoldWedge α β) := by
  intro c
  have he : chartTwoForm (manifoldWedge α β) c = fun y =>
      (chartOneForm α c y).smulRight (chartOneForm β c y)-
      (chartOneForm β c y).smulRight (chartOneForm α c y) :=
    funext (chartTwoForm_wedge α β c)
  rw [he]
  exact ((hα c).smulRight (hβ c)).sub ((hβ c).smulRight (hα c))


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def manifoldScalarDifferential (f : M → ℝ) : ManifoldOneForm E M :=
  mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f

theorem manifoldScalarDifferential_chart {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ f) {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    chartOneForm (manifoldScalarDifferential f) c y=
      fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ,E) c).symm) y := by
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hy)
  have hd := mfderiv_comp y (hf.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  rw [chartOneForm,chartDifferential_inverse hy]
  exact hd.symm

theorem manifoldScalar_chart_smooth {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ f) (c : M) :
    ContDiffOn ℝ ∞ (f ∘ (extChartAt 𝓘(ℝ,E) c).symm)
      (extChartAt 𝓘(ℝ,E) c).target :=
  (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c)).contDiffOn

theorem manifoldScalarDifferential_smooth {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ f) (c : M) :
    ContDiffOn ℝ ∞ (chartOneForm (manifoldScalarDifferential f) c)
      (extChartAt 𝓘(ℝ,E) c).target := by
  intro y hy
  have hs := (manifoldScalar_chart_smooth hf c).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hy)
  have he : chartOneForm (manifoldScalarDifferential f) c =ᶠ[𝓝 y]
      fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ,E) c).symm) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hy] with z hz
    exact manifoldScalarDifferential_chart hf hz
  exact ((hs.fderiv_right (by simp)).congr_of_eventuallyEq he).contDiffWithinAt

theorem manifoldScalarDifferential_closed {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ f) (x : M) :
    manifoldExteriorOneForm (manifoldScalarDifferential (E := E) f) x=0 := by
  have hx : extChartAt 𝓘(ℝ,E) x x∈(extChartAt 𝓘(ℝ,E) x).target :=
    (extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source x)
  have hn := (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds hx
  have hs := (manifoldScalar_chart_smooth hf x).contDiffAt hn
  have he : chartOneForm (manifoldScalarDifferential f) x =ᶠ[𝓝 (extChartAt 𝓘(ℝ,E) x x)]
      fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ,E) x).symm) := by
    filter_upwards [hn] with z hz
    exact manifoldScalarDifferential_chart hf hz
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change fderiv ℝ (chartOneForm (manifoldScalarDifferential f) x)
      (extChartAt 𝓘(ℝ,E) x x) (chartDifferential x x u) (chartDifferential x x v)-
    fderiv ℝ (chartOneForm (manifoldScalarDifferential f) x)
      (extChartAt 𝓘(ℝ,E) x x) (chartDifferential x x v) (chartDifferential x x u)=0
  rw [he.fderiv_eq]
  exact sub_eq_zero.mpr ((hs.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)).eq _ _)

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem manifoldScalarDifferential_support (f : M → ℝ) :
    support (manifoldScalarDifferential (E := E) f) ⊆ tsupport f := by
  intro x hx
  by_contra hn
  have he : f =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hn] with y hy
    exact notMem_support.mp (fun hs => hy (subset_closure hs))
  apply hx
  exact he.mfderiv_eq.trans (by
    rw [mfderiv_const,ContinuousLinearMap.comp_zero]
    rfl)


end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
@[simp] theorem chartOneForm_sub (α β : ManifoldOneForm E M) (c : M) (y : E) :
    chartOneForm (α-β) c y=chartOneForm α c y-chartOneForm β c y := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

def glueManifoldOneForm (U : Set M) (α β : ManifoldOneForm E M) : ManifoldOneForm E M :=
  β + extendManifoldOneForm U (α-β)

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] in
@[simp] theorem glueManifoldOneForm_inside {U : Set M} (α β : ManifoldOneForm E M)
    {x : M} (hx : x ∈ U) : glueManifoldOneForm U α β x=α x := by
  simp [glueManifoldOneForm,extendManifoldOneForm_inside hx]

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] in
@[simp] theorem glueManifoldOneForm_outside {U : Set M} (α β : ManifoldOneForm E M)
    {x : M} (hx : x ∉ U) : glueManifoldOneForm U α β x=β x := by
  simp [glueManifoldOneForm,extendManifoldOneForm_outside hx]

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem glueManifoldOneForm_off_support {U K : Set M} (α β : ManifoldOneForm E M)
    (hmatch : ∀ x ∈ U, x ∉ K → α x=β x) {x : M} (hx : x ∉ K) :
    glueManifoldOneForm U α β x=β x := by
  by_cases hu : x ∈ U
  · rw [glueManifoldOneForm_inside α β hu,hmatch x hu hx]
  · exact glueManifoldOneForm_outside α β hu

theorem glueManifoldOneForm_smooth {U K : Set M} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) {α β : P → ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ ((extChartAt 𝓘(ℝ,E) c).target ∩ (extChartAt 𝓘(ℝ,E) c).symm ⁻¹' U)))
    (hβ : SmoothOneFormFamily β) (hmatch : ∀ p x, x ∈ U → x ∉ K → α p x=β p x) :
    SmoothOneFormFamily (fun p => glueManifoldOneForm U (α p) (β p)) := by
  have hs := extendManifoldOneForm_smooth hU hK hKU
    (α := fun p => α p-β p)
    (fun c => by
      simp only [chartOneForm_sub]
      exact (hα c).sub ((hβ c).mono (fun _ hq => ⟨hq.1,hq.2.1⟩)))
    (fun p x hu hx => sub_eq_zero.mpr (hmatch p x hu hx))
  intro c
  simpa only [glueManifoldOneForm,chartOneForm_add] using (hβ c).add (hs c)

theorem glueManifoldOneForm_exterior {U K : Set M} (hU : IsOpen U) (hK : IsClosed K)
    (α β : ManifoldOneForm E M) (hmatch : ∀ x ∈ U, x ∉ K → α x=β x) :
    (∀ x ∈ U, manifoldExteriorOneForm (glueManifoldOneForm U α β) x=manifoldExteriorOneForm α x) ∧
    (∀ x, x ∉ K → manifoldExteriorOneForm (glueManifoldOneForm U α β) x=manifoldExteriorOneForm β x) := by
  constructor
  · intro x hx
    apply manifoldExteriorOneForm_congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with y hy
    exact glueManifoldOneForm_inside α β hy
  · intro x hx
    apply manifoldExteriorOneForm_congr_of_eventuallyEq
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    exact glueManifoldOneForm_off_support α β hmatch hy

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem glueManifoldOneForm_time {U K : Set M} (α β : ℝ → ManifoldOneForm E M)
    (hmatch : ∀ t x, x ∈ U → x ∉ K → α t x=β t x) (t : ℝ) :
    (∀ x ∈ U, manifoldTimePrimitive (fun s => glueManifoldOneForm U (α s) (β s)) t x=
      manifoldTimePrimitive α t x) ∧
    (∀ x, x ∉ K → manifoldTimePrimitive (fun s => glueManifoldOneForm U (α s) (β s)) t x=
      manifoldTimePrimitive β t x) := by
  constructor
  · intro x hx
    unfold manifoldTimePrimitive
    congr 1
    funext s
    exact glueManifoldOneForm_inside (α s) (β s) hx
  · intro x hx
    unfold manifoldTimePrimitive
    congr 1
    funext s
    exact glueManifoldOneForm_off_support (α s) (β s) (hmatch s) hx

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem glueManifoldOneForm_initial {U : Set M} {α β : ℝ → ManifoldOneForm E M}
    (hzero : ∀ x ∈ U, α 0 x=β 0 x) : glueManifoldOneForm U (α 0) (β 0)=β 0 := by
  funext x
  by_cases hx : x ∈ U
  · rw [glueManifoldOneForm_inside _ _ hx,hzero x hx]
  · exact glueManifoldOneForm_outside _ _ hx



end PackingSufficiencySupport.Hamiltonian
end

end OAI
