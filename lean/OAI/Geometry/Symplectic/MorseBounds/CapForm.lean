import OAI.Geometry.Symplectic.MorseBounds.ProductForm

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.CapSymplectic
open MorseArnold.Geometry MorseArnold.SphereCaps MorseArnold.SphereSymplectic
open MorseArnold.CapProduct MorseArnold.SymplecticProduct
open scoped Manifold ContDiff
open Set
noncomputable section
abbrev SI := (𝓡 2).prod (𝓡 2)
abbrev PI := 𝓘(ℝ,Plane).prod 𝓘(ℝ,Plane)
def planeArea : Plane →L[ℝ] Plane →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ) -
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ)
def fourPlaneForm : SymplecticProduct.TwoForm PP (M := PlaneFour) :=
  prodForm PI PI (prodForm 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (fun _ => planeArea) (fun _ => planeArea))
    (prodForm 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (fun _ => planeArea) (fun _ => planeArea))
def fourSphereForm (ws : Geometry.SymplecticForm (n := 2) (M := S2)) :
    SymplecticProduct.TwoForm SP (M := SphereFour) :=
  prodForm SI SI (prodForm (𝓡 2) (𝓡 2) ws.form ws.form)
    (prodForm (𝓡 2) (𝓡 2) ws.form ws.form)
def allChart {X : Type} [TopologicalSpace X] (l : ℝ) (hl : 0 < l) (nu : Choices) :
    OpenPartialHomeomorph (X × SphereFour) (X × PlaneFour) :=
  (OpenPartialHomeomorph.refl X).prod (fourChart l hl nu)

def CapSymplecticObligation : Prop :=
  (∃ wp : SymplecticProduct.SymplecticForm 𝓘(ℝ,Plane) (M := Plane),
    wp.form = fun _ => planeArea) ∧
  ∀ (l : ℝ) (hl : 25 / 2 < l)
    (ws : Geometry.SymplecticForm (n := 2) (M := S2)),
    (∀ p u v, ws.form p u v = l * standardArea (p : R3)
      (tangentInclusion p u) (tangentInclusion p v)) →
    ∀ (X : Type) [TopologicalSpace X] [ChartedSpace (Model 4) X]
      [IsManifold (𝓡 4) ∞ X] (wX : Geometry.SymplecticForm (n := 4) (M := X))
      (nu : Choices) (p : X × SphereFour),
      p ∈ (allChart (X := X) l (by linarith) nu).source →
      ∀ u v : TangentSpace ((𝓡 4).prod SP) p,
      prodForm (𝓡 4) PP wX.form fourPlaneForm (allChart l (by linarith) nu p)
        (mfderiv ((𝓡 4).prod SP) ((𝓡 4).prod PP) (allChart l (by linarith) nu) p u)
        (mfderiv ((𝓡 4).prod SP) ((𝓡 4).prod PP) (allChart l (by linarith) nu) p v) =
      prodForm (𝓡 4) SP wX.form (fourSphereForm ws) p u v
end
end MorseArnold.CapSymplectic

namespace MorseArnold.CapSymplectic
open MorseArnold.Geometry MorseArnold.SphereCaps MorseArnold.SphereSymplectic
open MorseArnold.CapProduct MorseArnold.SymplecticProduct
open scoped Manifold ContDiff
open Set Filter Topology
noncomputable section
local instance : Fact (Module.finrank ℝ R3 = 2 + 1) := ⟨by simp [R3]⟩

@[simp] lemma planeArea_apply (u v : Plane) :
    planeArea u v = u.1*v.2-u.2*v.1 := rfl

lemma plane_chart (x y : Plane) :
    SymplecticProduct.chartTwoForm 𝓘(ℝ,Plane) (fun _ : Plane => planeArea) x y = planeArea := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change planeArea
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (extChartAt 𝓘(ℝ,Plane) x).symm y u)
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (extChartAt 𝓘(ℝ,Plane) x).symm y v) = _
  have hc : ((extChartAt 𝓘(ℝ,Plane) x).symm : Plane → Plane) = id := rfl
  rw [hc,mfderiv_id]
  rfl

lemma plane_symplectic : ∃ wp : SymplecticProduct.SymplecticForm 𝓘(ℝ,Plane) (M := Plane),
    wp.form = fun _ => planeArea := by
  refine ⟨⟨fun _ => planeArea, ?_, ?_, ?_, ?_⟩, rfl⟩
  · intro p u
    change u.1*u.2-u.2*u.1=0
    ring
  · change ∀ p : Plane, Function.Injective planeArea
    intro p u v h
    have h1 := DFunLike.congr_fun h (1,0)
    have h2 := DFunLike.congr_fun h (0,1)
    simp only [planeArea_apply,mul_zero,mul_one,zero_sub,sub_zero] at h1 h2
    exact Prod.ext h2 (neg_inj.mp h1)
  · intro x
    have he : SymplecticProduct.chartTwoForm 𝓘(ℝ,Plane) (fun _ : Plane => planeArea) x =
      fun _ => planeArea := funext (plane_chart x)
    rw [he]
    exact contDiffOn_const
  · intro x y hy u v w
    have he : SymplecticProduct.chartTwoForm 𝓘(ℝ,Plane) (fun _ : Plane => planeArea) x =
      fun _ => planeArea := funext (plane_chart x)
    rw [he]
    simp

lemma inclusion_inverse_deriv (e : OpenPartialHomeomorph S2 Plane) (z : Plane)
    (he : MDifferentiableAt 𝓘(ℝ,Plane) (𝓡 2) e.symm z) (a : Plane → R3)
    (ha : (fun q : Plane => (e.symm q : R3)) =ᶠ[𝓝 z] a) :
    (tangentInclusion (e.symm z)).comp (mfderiv 𝓘(ℝ,Plane) (𝓡 2) e.symm z) =
      fderiv ℝ a z := by
  have hc : MDifferentiableAt (𝓡 2) 𝓘(ℝ,R3) ((↑) : S2 → R3) (e.symm z) :=
    (contMDiff_coe_sphere (E := R3) (n := 2) (m := (∞ : ℕ∞ω))).mdifferentiableAt (by simp)
  have hh := mfderiv_comp z hc he
  rw [mfderiv_eq_fderiv] at hh
  exact hh.symm.trans ha.fderiv_eq

lemma bigChart_inverse_area (l : ℝ) (hl : 0 < l) (b : Bool)
    (ws : Geometry.SymplecticForm (n := 2) (M := S2))
    (hw : ∀ p u v, ws.form p u v = l * standardArea (p : R3)
      (tangentInclusion p u) (tangentInclusion p v))
    (z : Plane) (hz : z ∈ (bigChart l hl b).target) (u v : Plane) :
    ws.form ((bigChart l hl b).symm z)
      (mfderiv 𝓘(ℝ,Plane) (𝓡 2) (bigChart l hl b).symm z u)
      (mfderiv 𝓘(ℝ,Plane) (𝓡 2) (bigChart l hl b).symm z v) = planeArea u v := by
  have he := ((bigChart_smooth l hl b).2 z hz).contMDiffAt
    ((bigChart l hl b).open_target.mem_nhds hz)
  have hz' : radiusSq z < 4*l := by simpa only [bigChart_target, Set.mem_ofPred_eq] using hz
  rw [hw]
  cases b
  · have heq : (fun q : Plane => ((bigChart l hl false).symm q : R3)) =ᶠ[𝓝 z]
        northInvAmbient l := by
      filter_upwards [(capDomain_open l).mem_nhds hz'] with q hq
      exact northInv_val l hl q hq
    have hd := inclusion_inverse_deriv _ z (he.mdifferentiableAt (by simp)) _ heq
    have hv := heq.self_of_nhds
    dsimp only at hv
    rw [hv]
    change l * standardArea (northInvAmbient l z)
      (((tangentInclusion ((bigChart l hl false).symm z)).comp
        (mfderiv 𝓘(ℝ,Plane) (𝓡 2) (bigChart l hl false).symm z)) u)
      (((tangentInclusion ((bigChart l hl false).symm z)).comp
        (mfderiv 𝓘(ℝ,Plane) (𝓡 2) (bigChart l hl false).symm z)) v) = _
    rw [hd]
    exact (cap_area l hl z hz' u v).1
  · have heq : (fun q : Plane => ((bigChart l hl true).symm q : R3)) =ᶠ[𝓝 z]
        southInvAmbient l := by
      filter_upwards [(capDomain_open l).mem_nhds hz'] with q hq
      change flipL (northInv l hl q : R3) = southInvAmbient l q
      rw [northInv_val l hl q hq,flip_northInv]
    have hd := inclusion_inverse_deriv _ z (he.mdifferentiableAt (by simp)) _ heq
    have hv := heq.self_of_nhds
    dsimp only at hv
    rw [hv]
    change l * standardArea (southInvAmbient l z)
      (((tangentInclusion ((bigChart l hl true).symm z)).comp
        (mfderiv 𝓘(ℝ,Plane) (𝓡 2) (bigChart l hl true).symm z)) u)
      (((tangentInclusion ((bigChart l hl true).symm z)).comp
        (mfderiv 𝓘(ℝ,Plane) (𝓡 2) (bigChart l hl true).symm z)) v) = _
    rw [hd]
    exact (cap_area l hl z hz' u v).2

lemma bigChart_area (l : ℝ) (hl : 0 < l) (b : Bool)
    (ws : Geometry.SymplecticForm (n := 2) (M := S2))
    (hw : ∀ p u v, ws.form p u v = l * standardArea (p : R3)
      (tangentInclusion p u) (tangentInclusion p v))
    (p : S2) (hp : p ∈ (bigChart l hl b).source)
    (u v : TangentSpace (𝓡 2) p) :
    planeArea (mfderiv (𝓡 2) 𝓘(ℝ,Plane) (bigChart l hl b) p u)
      (mfderiv (𝓡 2) 𝓘(ℝ,Plane) (bigChart l hl b) p v) = ws.form p u v := by
  have he : (bigChart l hl b).MDifferentiable (𝓡 2) 𝓘(ℝ,Plane) :=
    ⟨(bigChart_smooth l hl b).1.mdifferentiableOn (by simp),
      (bigChart_smooth l hl b).2.mdifferentiableOn (by simp)⟩
  have hd := he.symm_comp_deriv hp
  have hu := congrArg (fun d => d u) hd
  have hv := congrArg (fun d => d v) hd
  have hh := bigChart_inverse_area l hl b ws hw ((bigChart l hl b) p)
    ((bigChart l hl b).map_source hp)
    (mfderiv (𝓡 2) 𝓘(ℝ,Plane) (bigChart l hl b) p u)
    (mfderiv (𝓡 2) 𝓘(ℝ,Plane) (bigChart l hl b) p v)
  simp only [ContinuousLinearMap.comp_apply] at hu hv
  rw [hu,hv] at hh
  have hleft := (bigChart l hl b).left_inv hp
  rw [hleft] at hh
  exact hh.symm

lemma oneChart_area (l : ℝ) (hl : 0 < l) (b : Bool)
    (ws : Geometry.SymplecticForm (n := 2) (M := S2))
    (hw : ∀ p u v, ws.form p u v = l * standardArea (p : R3)
      (tangentInclusion p u) (tangentInclusion p v))
    (p : S2) (hp : p ∈ (oneChart l hl b).source)
    (u v : TangentSpace (𝓡 2) p) :
    planeArea (mfderiv (𝓡 2) 𝓘(ℝ,Plane) (oneChart l hl b) p u)
      (mfderiv (𝓡 2) 𝓘(ℝ,Plane) (oneChart l hl b) p v) = ws.form p u v :=
  bigChart_area l hl b ws hw p hp.1 u v

section Generic
variable {E₁ E₂ F₁ F₂ H₁ H₂ G₁ G₂ M₁ M₂ N₁ N₂ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [TopologicalSpace H₁] [TopologicalSpace H₂]
  [TopologicalSpace G₁] [TopologicalSpace G₂]
  [TopologicalSpace M₁] [TopologicalSpace M₂]
  [TopologicalSpace N₁] [TopologicalSpace N₂]
  [ChartedSpace H₁ M₁] [ChartedSpace H₂ M₂]
  [ChartedSpace G₁ N₁] [ChartedSpace G₂ N₂]
  {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
  {J₁ : ModelWithCorners ℝ F₁ G₁} {J₂ : ModelWithCorners ℝ F₂ G₂}

lemma prod_area (a₁ : SymplecticProduct.TwoForm I₁ (M := M₁))
    (a₂ : SymplecticProduct.TwoForm I₂ (M := M₂))
    (b₁ : SymplecticProduct.TwoForm J₁ (M := N₁))
    (b₂ : SymplecticProduct.TwoForm J₂ (M := N₂))
    (f : M₁ → N₁) (g : M₂ → N₂) (p : M₁ × M₂)
    (hf : MDifferentiableAt I₁ J₁ f p.1) (hg : MDifferentiableAt I₂ J₂ g p.2)
    (h₁ : ∀ u v, b₁ (f p.1) (mfderiv I₁ J₁ f p.1 u) (mfderiv I₁ J₁ f p.1 v) = a₁ p.1 u v)
    (h₂ : ∀ u v, b₂ (g p.2) (mfderiv I₂ J₂ g p.2 u) (mfderiv I₂ J₂ g p.2 v) = a₂ p.2 u v)
    (u v : TangentSpace (I₁.prod I₂) p) :
    prodForm J₁ J₂ b₁ b₂ (Prod.map f g p)
      (mfderiv (I₁.prod I₂) (J₁.prod J₂) (Prod.map f g) p u)
      (mfderiv (I₁.prod I₂) (J₁.prod J₂) (Prod.map f g) p v) =
    prodForm I₁ I₂ a₁ a₂ p u v := by
  rw [mfderiv_prodMap hf hg]
  change b₁ (f p.1) (mfderiv I₁ J₁ f p.1 u.1) (mfderiv I₁ J₁ f p.1 v.1) +
    b₂ (g p.2) (mfderiv I₂ J₂ g p.2 u.2) (mfderiv I₂ J₂ g p.2 v.2) =
    a₁ p.1 u.1 v.1 + a₂ p.2 u.2 v.2
  exact congrArg₂ (fun a b : ℝ => a + b) (h₁ u.1 v.1) (h₂ u.2 v.2)
end Generic

lemma oneChart_mdiff (l : ℝ) (hl : 0 < l) (b : Bool) (p : S2)
    (hp : p ∈ (oneChart l hl b).source) :
    MDifferentiableAt (𝓡 2) 𝓘(ℝ,Plane) (oneChart l hl b) p :=
  (((oneChart_smooth l hl b).1 p hp).contMDiffAt
    ((oneChart l hl b).open_source.mem_nhds hp)).mdifferentiableAt (by simp)

lemma pairChart_area (l : ℝ) (hl : 0 < l) (b c : Bool)
    (ws : Geometry.SymplecticForm (n := 2) (M := S2))
    (hw : ∀ p u v, ws.form p u v = l * standardArea (p : R3)
      (tangentInclusion p u) (tangentInclusion p v))
    (p : S2 × S2) (hp : p ∈ ((oneChart l hl b).prod (oneChart l hl c)).source)
    (u v : TangentSpace SI p) :
    prodForm 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (fun _ => planeArea) (fun _ => planeArea)
      (((oneChart l hl b).prod (oneChart l hl c)) p)
      (mfderiv SI PI ((oneChart l hl b).prod (oneChart l hl c)) p u)
      (mfderiv SI PI ((oneChart l hl b).prod (oneChart l hl c)) p v) =
    prodForm (𝓡 2) (𝓡 2) ws.form ws.form p u v :=
  prod_area ws.form ws.form (fun _ => planeArea) (fun _ => planeArea)
    (oneChart l hl b) (oneChart l hl c) p
    (oneChart_mdiff l hl b p.1 hp.1) (oneChart_mdiff l hl c p.2 hp.2)
    (oneChart_area l hl b ws hw p.1 hp.1) (oneChart_area l hl c ws hw p.2 hp.2) u v

lemma fourChart_area (l : ℝ) (hl : 0 < l) (nu : Choices)
    (ws : Geometry.SymplecticForm (n := 2) (M := S2))
    (hw : ∀ p u v, ws.form p u v = l * standardArea (p : R3)
      (tangentInclusion p u) (tangentInclusion p v))
    (p : SphereFour) (hp : p ∈ (fourChart l hl nu).source)
    (u v : TangentSpace SP p) :
    fourPlaneForm (fourChart l hl nu p)
      (mfderiv SP PP (fourChart l hl nu) p u) (mfderiv SP PP (fourChart l hl nu) p v) =
    fourSphereForm ws p u v :=
  prod_area (prodForm (𝓡 2) (𝓡 2) ws.form ws.form)
    (prodForm (𝓡 2) (𝓡 2) ws.form ws.form)
    (prodForm 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (fun _ => planeArea) (fun _ => planeArea))
    (prodForm 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (fun _ => planeArea) (fun _ => planeArea))
    ((oneChart l hl nu.1.1).prod (oneChart l hl nu.1.2))
    ((oneChart l hl nu.2.1).prod (oneChart l hl nu.2.2)) p
    ((oneChart_mdiff l hl nu.1.1 p.1.1 hp.1.1).prodMap
      (oneChart_mdiff l hl nu.1.2 p.1.2 hp.1.2))
    ((oneChart_mdiff l hl nu.2.1 p.2.1 hp.2.1).prodMap
      (oneChart_mdiff l hl nu.2.2 p.2.2 hp.2.2))
    (pairChart_area l hl nu.1.1 nu.1.2 ws hw p.1 hp.1)
    (pairChart_area l hl nu.2.1 nu.2.2 ws hw p.2 hp.2) u v

lemma allChart_area {X : Type} [TopologicalSpace X] [ChartedSpace (Model 4) X]
    [IsManifold (𝓡 4) ∞ X] (wX : Geometry.SymplecticForm (n := 4) (M := X))
    (l : ℝ) (hl : 25 / 2 < l) (nu : Choices)
    (ws : Geometry.SymplecticForm (n := 2) (M := S2))
    (hw : ∀ p u v, ws.form p u v = l * standardArea (p : R3)
      (tangentInclusion p u) (tangentInclusion p v))
    (p : X × SphereFour) (hp : p ∈ (allChart l (by linarith) nu).source)
    (u v : TangentSpace ((𝓡 4).prod SP) p) :
    prodForm (𝓡 4) PP wX.form fourPlaneForm (allChart l (by linarith) nu p)
      (mfderiv ((𝓡 4).prod SP) ((𝓡 4).prod PP) (allChart l (by linarith) nu) p u)
      (mfderiv ((𝓡 4).prod SP) ((𝓡 4).prod PP) (allChart l (by linarith) nu) p v) =
      prodForm (𝓡 4) SP wX.form (fourSphereForm ws) p u v := by
  have hf := (((four_chart_smooth l hl nu).1 p.2 hp.2).contMDiffAt
    ((fourChart l (by linarith) nu).open_source.mem_nhds hp.2)).mdifferentiableAt (by simp)
  have hid : ∀ u v, wX.form p.1 (mfderiv (𝓡 4) (𝓡 4) id p.1 u)
      (mfderiv (𝓡 4) (𝓡 4) id p.1 v) = wX.form p.1 u v := by
    intro u v
    rw [mfderiv_id]
    rfl
  exact prod_area wX.form (fourSphereForm ws) wX.form fourPlaneForm
    id (fourChart l (by linarith) nu) p mdifferentiableAt_id hf hid
    (fourChart_area l (by linarith) nu ws hw p.2 hp.2) u v

theorem capSymplecticObligation : CapSymplecticObligation := by
  refine ⟨plane_symplectic, ?_⟩
  intro l hl ws hw X t c m wX nu p hp u v
  exact allChart_area wX l hl nu ws hw p hp u v

end
end MorseArnold.CapSymplectic

end

end OAI
