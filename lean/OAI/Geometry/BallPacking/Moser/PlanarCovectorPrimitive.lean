import Mathlib
import OAI.Geometry.BallPacking.Moser.BackgroundDensity

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff
open MeasureTheory Set

def planarCovector (U V : ℝ) : Plane →L[ℝ] ℝ :=
  U • ContinuousLinearMap.fst ℝ ℝ ℝ + V • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem planarCovector_apply (U V : ℝ) (v : Plane) :
    planarCovector U V v = U*v.1+V*v.2 := rfl

@[simp] theorem planarCovector_zero : planarCovector 0 0=0 := by
  simp [planarCovector]

theorem planarCovector_smooth {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U V : P → ℝ} (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun p => planarCovector (U p) (V p)) := by
  exact (hU.smul contDiff_const).add (hV.smul contDiff_const)

theorem planar_deriv_first {f : Plane → ℝ} {p : Plane} (hf : DifferentiableAt ℝ f p) :
    deriv (fun x => f (x,p.2)) p.1 = fderiv ℝ f p (1,0) := by
  have hd := hf.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  exact hd.deriv

theorem planar_deriv_second {f : Plane → ℝ} {p : Plane} (hf : DifferentiableAt ℝ f p) :
    deriv (fun y => f (p.1,y)) p.2 = fderiv ℝ f p (0,1) := by
  have hd := hf.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  exact hd.deriv

theorem planarCovector_exterior {U V : Plane → ℝ}
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) (p : Plane) :
    euclideanExteriorOneForm (fun x => planarCovector (U x) (V x)) p =
      (deriv (fun x => V (x,p.2)) p.1 - deriv (fun y => U (p.1,y)) p.2) • planarArea := by
  let α : Plane → Plane →L[ℝ] ℝ := fun x => planarCovector (U x) (V x)
  have ha : DifferentiableAt ℝ α p := (planarCovector_smooth hU hV).contDiffAt.differentiableAt (by simp)
  have hV' : fderiv ℝ α p (1,0) (0,1) = fderiv ℝ V p (1,0) := by
    rw [← fderiv_clm_eval ha]
    simp only [α,planarCovector_apply,mul_zero,mul_one,zero_add]
  have hU' : fderiv ℝ α p (0,1) (1,0) = fderiv ℝ U p (0,1) := by
    rw [← fderiv_clm_eval ha]
    simp only [α,planarCovector_apply,mul_zero,mul_one,add_zero]
  rw [planar_deriv_first (hV.contDiffAt.differentiableAt (by simp)),
    planar_deriv_second (hU.contDiffAt.differentiableAt (by simp))]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change fderiv ℝ α p u v - fderiv ℝ α p v u = _
  rw [bilinear_skew_plane,hV',hU']
  rfl

theorem fixed_spatial_covector_primitive {P : Type} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] {A : ℝ} (hA : 0<A)
    {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ p x y, A ≤ |x| ∨ A ≤ |y| → f (p,(x,y))=0)
    (hmass : ∀ p, (∫ x, f (p,x))=0) :
    ∃ α : P × Plane → Plane →L[ℝ] ℝ, ContDiff ℝ ∞ α ∧
      (∀ p x y, A ≤ |x| ∨ A ≤ |y| → α (p,(x,y))=0) ∧
      (∀ p z, euclideanExteriorOneForm (fun x => α (p,x)) z = f (p,z) • planarArea) ∧
      (∀ p, (∀ z, f (p,z)=0) → ∀ z, α (p,z)=0) := by
  obtain ⟨U,V,hU,hV,hz,hd,hall⟩ := fixed_spatial_planar_primitive hA hf hzero hmass
  refine ⟨fun p => planarCovector (U p) (V p),planarCovector_smooth hU hV,?_,?_,?_⟩
  · intro p x y h
    dsimp only
    rw [(hz p x y h).1,(hz p x y h).2,planarCovector_zero]
  · intro p z
    dsimp only
    have hUp : ContDiff ℝ ∞ (fun x => U (p,x)) := hU.comp (contDiff_const.prodMk contDiff_id)
    have hVp : ContDiff ℝ ∞ (fun x => V (p,x)) := hV.comp (contDiff_const.prodMk contDiff_id)
    rw [planarCovector_exterior hUp hVp,hd p z]
  · intro p hp z
    dsimp only
    rw [(hall p hp z).1,(hall p hp z).2,planarCovector_zero]


end

section
open scoped ContDiff Topology
attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def symplecticProjection (Ω : E →L[ℝ] E →L[ℝ] ℝ) (i : F →L[ℝ] E) : E →L[ℝ] F :=
  (Ω.bilinearComp i i).inverse.comp (Ω.bilinearComp (ContinuousLinearMap.id ℝ E) i)

def symplecticNormalJet (Ω : E →L[ℝ] E →L[ℝ] ℝ) (i : F →L[ℝ] E)
    (α : E →L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  α.comp (i.comp (symplecticProjection Ω i)) - α

theorem symplecticProjection_leftInverse {Ω : E →L[ℝ] E →L[ℝ] ℝ} {i : F →L[ℝ] E}
    (hi : (Ω.bilinearComp i i).IsInvertible) (u : F) :
    symplecticProjection Ω i (i u) = u := by
  exact hi.inverse_apply_self u

theorem symplecticProjection_pairing {Ω : E →L[ℝ] E →L[ℝ] ℝ} {i : F →L[ℝ] E}
    (hi : (Ω.bilinearComp i i).IsInvertible) (x : E) (u : F) :
    Ω (i (symplecticProjection Ω i x)) (i u) = Ω x (i u) := by
  exact congrArg (fun A : F →L[ℝ] ℝ => A u)
    (hi.self_apply_inverse ((Ω.bilinearComp (ContinuousLinearMap.id ℝ E) i) x))

theorem symplecticProjection_normal {Ω : E →L[ℝ] E →L[ℝ] ℝ} {i : F →L[ℝ] E}
    (hi : (Ω.bilinearComp i i).IsInvertible) (x : E) (u : F) :
    Ω (x - i (symplecticProjection Ω i x)) (i u) = 0 := by
  simp only [map_sub,sub_apply,symplecticProjection_pairing hi,sub_self]

theorem symplecticNormalJet_tangent {Ω : E →L[ℝ] E →L[ℝ] ℝ} {i : F →L[ℝ] E}
    (hi : (Ω.bilinearComp i i).IsInvertible) (α : E →L[ℝ] ℝ) (u : F) :
    symplecticNormalJet Ω i α (i u) = 0 := by
  simp only [symplecticNormalJet,sub_apply,ContinuousLinearMap.comp_apply,
    symplecticProjection_leftInverse hi,sub_self]

theorem symplecticNormalJet_normal {Ω : E →L[ℝ] E →L[ℝ] ℝ} {i : F →L[ℝ] E}
    {x : E} (hx : symplecticProjection Ω i x = 0) (α : E →L[ℝ] ℝ) :
    symplecticNormalJet Ω i α x = -α x := by
  simp only [symplecticNormalJet,sub_apply,ContinuousLinearMap.comp_apply,
    hx,map_zero,zero_sub]

theorem corrected_moser_vector_tangent
    {Ω : E →L[ℝ] E →L[ℝ] ℝ} {i : F →L[ℝ] E}
    (hΩ : Ω.IsInvertible) (hi : (Ω.bilinearComp i i).IsInvertible)
    (hskew : ∀ u v, Ω u v = -Ω v u) (α : E →L[ℝ] ℝ) :
    -Ω.inverse (α + symplecticNormalJet Ω i α) =
      i (-((Ω.bilinearComp i i).inverse (α.comp i))) := by
  let u := (Ω.bilinearComp i i).inverse (α.comp i)
  have hu (v : F) : Ω (i u) (i v) = α (i v) :=
    congrArg (fun A : F →L[ℝ] ℝ => A v) (hi.self_apply_inverse (α.comp i))
  have hp (x : E) : Ω (i u) x = α (i (symplecticProjection Ω i x)) := by
    calc
      Ω (i u) x = -Ω x (i u) := hskew _ _
      _ = -Ω (i (symplecticProjection Ω i x)) (i u) := by
        rw [symplecticProjection_pairing hi]
      _ = Ω (i u) (i (symplecticProjection Ω i x)) := (hskew _ _).symm
      _ = _ := hu _
  apply hΩ.injective
  rw [map_neg,hΩ.self_apply_inverse,map_neg,map_neg]
  apply ContinuousLinearMap.ext
  intro x
  change -(α x + (α (i (symplecticProjection Ω i x)) - α x)) = -Ω (i u) x
  rw [hp]
  ring

theorem smooth_bilinear_flip {P A B C : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {f : P → A →L[ℝ] B →L[ℝ] C} {p : P} (h : ContDiffAt ℝ ∞ f p) :
    ContDiffAt ℝ ∞ (fun q => (f q).flip) p := by
  have hflip : ContDiff ℝ ∞ (fun L : A →L[ℝ] B →L[ℝ] C => L.flip) :=
    LinearIsometryEquiv.contDiff (𝕜 := ℝ) (n := ∞) (E := A →L[ℝ] B →L[ℝ] C)
      (F := B →L[ℝ] A →L[ℝ] C) (ContinuousLinearMap.flipₗᵢ ℝ A B C)
  exact hflip.contDiffAt.comp p h

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace F]

theorem symplecticProjection_contDiffAt {Ω : P → E →L[ℝ] E →L[ℝ] ℝ}
    {i : P → F →L[ℝ] E} {p : P}
    (hΩ : ContDiffAt ℝ ∞ Ω p) (hi : ContDiffAt ℝ ∞ i p)
    (hinv : ((Ω p).bilinearComp (i p) (i p)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun q => symplecticProjection (Ω q) (i q)) p := by
  have hB : ContDiffAt ℝ ∞ (fun q => (Ω q).bilinearComp (i q) (i q)) p :=
    smooth_bilinear_flip ((smooth_bilinear_flip (hΩ.clm_comp hi)).clm_comp hi)
  exact (hinv.contDiffAt_map_inverse.comp p hB).clm_comp
    (smooth_bilinear_flip ((smooth_bilinear_flip (hΩ.clm_comp (contDiffAt_const (c := ContinuousLinearMap.id ℝ E)))).clm_comp hi))


end

section
open scoped ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def staticPullbackOneForm (α : E → E →L[ℝ] ℝ) (g : F → E) (x : F) : F →L[ℝ] ℝ :=
  (α (g x)).comp (fderiv ℝ g x)

theorem staticPullbackOneForm_smoothAt {α : E → E →L[ℝ] ℝ} {g : F → E} {x : F}
    (ha : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (staticPullbackOneForm α g) x :=
  (ha.comp x hg).clm_comp (hg.fderiv_right (by simp))

theorem staticPullbackOneForm_fderiv {α : E → E →L[ℝ] ℝ} {g : F → E} {x : F}
    (ha : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) (u v : F) :
    fderiv ℝ (staticPullbackOneForm α g) x u v =
      fderiv ℝ α (g x) (fderiv ℝ g x u) (fderiv ℝ g x v) +
        α (g x) (fderiv ℝ (fderiv ℝ g) x u v) := by
  have hd := ((ha.differentiableAt (by simp)).hasFDerivAt.comp x
    (hg.differentiableAt (by simp)).hasFDerivAt).clm_comp
      ((hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  rw [show fderiv ℝ (staticPullbackOneForm α g) x = _ from hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

theorem staticPullbackOneForm_exterior {α : E → E →L[ℝ] ℝ} {g : F → E} {x : F}
    (ha : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) :
    euclideanExteriorOneForm (staticPullbackOneForm α g) x =
      (euclideanExteriorOneForm α (g x)).bilinearComp (fderiv ℝ g x) (fderiv ℝ g x) := by
  ext u v
  simp only [euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.bilinearComp_apply,staticPullbackOneForm_fderiv ha hg]
  have hs := hg.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  rw [hs.eq u v]
  ring


end

section
open scoped ContDiff
open MeasureTheory Set Function

theorem translated_covector_exterior {α : Plane → Plane →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (a z : Plane) :
    euclideanExteriorOneForm (fun x => α (x-a)) z =
      euclideanExteriorOneForm α (z-a) := by
  have hD (x : Plane) : fderiv ℝ (fun y : Plane => y-a) x = ContinuousLinearMap.id ℝ Plane :=
    ((hasFDerivAt_id x).sub_const a).fderiv
  have he : staticPullbackOneForm α (fun x => x-a) = fun x => α (x-a) := by
    funext x
    unfold staticPullbackOneForm
    rw [hD]
    rfl
  have hsm : ContDiffAt ℝ ∞ (fun x : Plane => x-a) z := contDiffAt_id.sub contDiffAt_const
  have hd := staticPullbackOneForm_exterior (α := α) hα.contDiffAt hsm
  rw [he,hD] at hd
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun B : Plane →L[ℝ] Plane →L[ℝ] ℝ => B u v) hd

theorem translated_spatial_covector_primitive {P : Type} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] {A : ℝ} (hA : 0<A) (a : Plane)
    {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ p x y, A ≤ |x-a.1| ∨ A ≤ |y-a.2| → f (p,(x,y))=0)
    (hmass : ∀ p, (∫ x, f (p,x))=0) :
    ∃ α : P × Plane → Plane →L[ℝ] ℝ, ContDiff ℝ ∞ α ∧
      (∀ p x y, A ≤ |x-a.1| ∨ A ≤ |y-a.2| → α (p,(x,y))=0) ∧
      (∀ p z, euclideanExteriorOneForm (fun x => α (p,x)) z = f (p,z) • planarArea) ∧
      (∀ p, (∀ z, f (p,z)=0) → ∀ z, α (p,z)=0) := by
  let g : P × Plane → ℝ := fun q => f (q.1,q.2+a)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))
  have hgzero : ∀ p x y, A ≤ |x| ∨ A ≤ |y| → g (p,(x,y))=0 := by
    intro p x y h
    apply hzero
    simpa only [add_sub_cancel_right] using h
  have hgmass : ∀ p, (∫ x, g (p,x))=0 := by
    intro p
    exact (integral_add_right_eq_self (fun x => f (p,x)) a).trans (hmass p)
  obtain ⟨β,hβ,hβzero,hβd,hβall⟩ := fixed_spatial_covector_primitive hA hg hgzero hgmass
  refine ⟨fun q => β (q.1,q.2-a),
    hβ.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)),?_,?_,?_⟩
  · intro p x y h
    exact hβzero p (x-a.1) (y-a.2) h
  · intro p z
    dsimp only
    have hβp : ContDiff ℝ ∞ (fun x => β (p,x)) := hβ.comp (contDiff_const.prodMk contDiff_id)
    rw [translated_covector_exterior hβp,hβd]
    simp only [g,sub_add_cancel]
  · intro p hp z
    exact hβall p (fun x => hp (x+a)) (z-a)


end

section
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem bilinearComp_isInvertible {A : E →L[ℝ] E →L[ℝ] ℝ} {C : E →L[ℝ] E}
    (hA : A.IsInvertible) (hC : C.IsInvertible) : (A.bilinearComp C C).IsInvertible := by
  obtain ⟨a,rfl⟩ := hA
  obtain ⟨c,rfl⟩ := hC
  refine ⟨(c.trans a).trans (c.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)),?_⟩
  ext u v
  rfl


end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

abbrev ManifoldTwoForm (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] :=
  M → E →L[ℝ] E →L[ℝ] ℝ

def preferredDifferential (f : M → M) (x : M) : E →L[ℝ] E :=
  mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f x

def chartDifferential (c z : M) : E →L[ℝ] E :=
  mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c) z

def chartTwoForm (Ω : ManifoldTwoForm E M) (c : M) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  let z := (extChartAt 𝓘(ℝ,E) c).symm y
  let A := (chartDifferential c z).inverse
  (Ω z).bilinearComp A A

def timeChartField (V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2)
    (c : M) (p : ℝ × E) : E :=
  let z := (extChartAt 𝓘(ℝ,E) c).symm p.2
  chartDifferential c z (V (p.1,z))

theorem chartTwoForm_apply_chart {Ω : ManifoldTwoForm E M} {c z : M}
    (hz : z ∈ (extChartAt 𝓘(ℝ,E) c).source) (v w : TangentSpace 𝓘(ℝ,E) z) :
    chartTwoForm Ω c (extChartAt 𝓘(ℝ,E) c z)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c) z v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c) z w) = Ω z v w := by
  change E at v w
  change chartTwoForm Ω c (extChartAt 𝓘(ℝ,E) c z)
    (chartDifferential c z v) (chartDifferential c z w) = Ω z v w
  simp only [chartTwoForm,(extChartAt 𝓘(ℝ,E) c).left_inv hz,
    ContinuousLinearMap.bilinearComp_apply]
  have hA : (chartDifferential (E := E) c z).IsInvertible := by
    convert! (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hz) using 1
  rw [hA.inverse_apply_eq.mpr rfl,hA.inverse_apply_eq.mpr rfl]

theorem timeChartField_hasDerivAt
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    {γ : ℝ → M} {t : ℝ} {c : M}
    (hγ : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,γ t))))
    (hc : γ t ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    HasDerivAt (fun s => extChartAt 𝓘(ℝ,E) c (γ s))
      (timeChartField V c (t,extChartAt 𝓘(ℝ,E) c (γ t))) t := by
  have hd := (mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := c) (by simpa only [extChartAt_source] using hc)).hasMFDerivAt.comp t hγ
  rw [timeChartField,(extChartAt 𝓘(ℝ,E) c).left_inv hc]
  rw [hasDerivAt_iff_hasFDerivAt]
  apply (hasMFDerivAt_iff_hasFDerivAt.mp hd).congr_fderiv
  ext
  change (chartDifferential (E := E) c (γ t)) ((1 : ℝ) • (V (t,γ t) : E)) =
    (1 : ℝ) • ((chartDifferential (E := E) c (γ t)) (V (t,γ t)))
  simp only [one_smul]

theorem chart_spatial_pullback {f : M → M} {x c : M}
    (hf : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) f x)
    (hc : f x ∈ (extChartAt 𝓘(ℝ,E) c).source) (Ω : ManifoldTwoForm E M)
    (v w : TangentSpace 𝓘(ℝ,E) x) :
    chartTwoForm Ω c (extChartAt 𝓘(ℝ,E) c (f x))
      (fderiv ℝ (fun y => extChartAt 𝓘(ℝ,E) c (f ((extChartAt 𝓘(ℝ,E) x).symm y)))
        (extChartAt 𝓘(ℝ,E) x x) v)
      (fderiv ℝ (fun y => extChartAt 𝓘(ℝ,E) c (f ((extChartAt 𝓘(ℝ,E) x).symm y)))
        (extChartAt 𝓘(ℝ,E) x x) w) =
      Ω (f x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f x v) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f x w) := by
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,E)) x
  have hy := (extChartAt 𝓘(ℝ,E) x).map_source hx
  have hinv : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E)
      (extChartAt 𝓘(ℝ,E) x).symm (extChartAt 𝓘(ℝ,E) x x) := by
    simpa only [mfld_simps,mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm hy
  have hid : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) x).symm
      (extChartAt 𝓘(ℝ,E) x x) = ContinuousLinearMap.id ℝ E := by
    simpa only [mfld_simps] using!
      (mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ,E)) (x := x))
  have hd := ((mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := c) (by simpa only [extChartAt_source] using hc)).hasMFDerivAt.comp x hf.hasMFDerivAt)
  have hd1 : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c ∘ f)
      ((extChartAt 𝓘(ℝ,E) x).symm (extChartAt 𝓘(ℝ,E) x x))
      ((chartDifferential (E := E) c (f x)).comp (preferredDifferential (E := E) f x)) := by
    rw [(extChartAt 𝓘(ℝ,E) x).left_inv hx]
    exact hd
  have hd' := hd1.comp (extChartAt 𝓘(ℝ,E) x x) hinv.hasMFDerivAt
  have he : fderiv ℝ (fun y => extChartAt 𝓘(ℝ,E) c (f ((extChartAt 𝓘(ℝ,E) x).symm y)))
      (extChartAt 𝓘(ℝ,E) x x) =
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c) (f x)).comp
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f x) := by
    let A : E →L[ℝ] E :=
      ((chartDifferential (E := E) c (f x)).comp (preferredDifferential (E := E) f x)).comp
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) x).symm (extChartAt 𝓘(ℝ,E) x x))
    have hh : HasFDerivAt
        (fun y : E => extChartAt 𝓘(ℝ,E) c (f ((extChartAt 𝓘(ℝ,E) x).symm y)))
        A (extChartAt 𝓘(ℝ,E) x x) := hasMFDerivAt_iff_hasFDerivAt.mp hd'
    dsimp only [A] at hh
    have hh1 := hh.fderiv
    rw [hid] at hh1
    change _ = (chartDifferential (E := E) c (f x)).comp
      (preferredDifferential (E := E) f x)
    convert! hh1 using 1
  rw [he]
  exact chartTwoForm_apply_chart hc _ _



theorem timeChartField_contDiffOn
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M))) (c : M) :
    ContDiffOn ℝ ∞ (timeChartField V c) (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) := by
  have h := (contMDiff_iff.mp hV).2 (0,c) (⟨c,V (0,c)⟩ : TangentBundle 𝓘(ℝ,E) M)
  have hh := h.snd
  have hs : ContDiffOn ℝ ∞
      (fun p : ℝ × E => let z := (extChartAt 𝓘(ℝ,E) c).symm p.2
        tangentCoordChange 𝓘(ℝ,E) z c z (V (p.1,z)))
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) := by
    apply hh.mono
    intro p hp
    refine ⟨?_,?_⟩
    · simp only [mfld_simps]
      change p ∈ univ ×ˢ (chartAt E c).target
      simpa only [mfld_simps] using hp
    · simp only [Set.mem_preimage,mfld_simps,TangentBundle.mem_chart_source_iff]
      change (chartAt E c).symm p.2 ∈ (chartAt E c).source
      simpa only [mfld_simps] using (extChartAt 𝓘(ℝ,E) c).map_target hp.2

  apply hs.congr
  intro p hp
  dsimp only [timeChartField,chartDifferential]
  have hz := (extChartAt 𝓘(ℝ,E) c).map_target hp.2
  have hz' : (extChartAt 𝓘(ℝ,E) c).symm p.2 ∈ (chartAt E c).source := by
    simpa only [extChartAt_source] using hz
  rw [show (extChartAt 𝓘(ℝ,E) c : M → E) = chartAt E c from rfl,
    mfderiv_chartAt_eq_tangentCoordChange hz']

theorem manifoldFamily_coordinate_smoothAt
    {Φ : ℝ × M → M}
    (hΦ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ)
    {x c : M} {p : ℝ × E}
    (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) x).target)
    (hc : Φ (p.1,(extChartAt 𝓘(ℝ,E) x).symm p.2) ∈
      (extChartAt 𝓘(ℝ,E) c).source) :
    ContDiffAt ℝ ∞ (fun q : ℝ × E => extChartAt 𝓘(ℝ,E) c
      (Φ (q.1,(extChartAt 𝓘(ℝ,E) x).symm q.2))) p := by
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) x).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds hp)
  have hc' : Φ (p.1,(extChartAt 𝓘(ℝ,E) x).symm p.2) ∈ (chartAt E c).source := by
    simpa only [extChartAt_source] using hc
  have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞) hc'
  have hm : ContMDiffAt 𝓘(ℝ,ℝ × E) 𝓘(ℝ,E) ∞
      (fun q : ℝ × E => extChartAt 𝓘(ℝ,E) c
        (Φ (q.1,(extChartAt 𝓘(ℝ,E) x).symm q.2))) p :=
    ho.comp p (hΦ.contMDiffAt.comp p
      (contDiffAt_fst.contMDiffAt.prodMk (hi.comp p contDiffAt_snd.contMDiffAt)))
  exact hm.contDiffAt



theorem timeField_smooth_of_coordinates
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ∀ p : ℝ × M, ContDiffAt ℝ ∞ (timeChartField V p.2)
      (p.1,extChartAt 𝓘(ℝ,E) p.2 p.2)) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)) := by
  intro p
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_snd,?_⟩
  have hc : ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ × E) ∞
      (fun q : ℝ × M => (q.1,extChartAt 𝓘(ℝ,E) p.2 q.2)) p :=
    contMDiffAt_fst.prodMk_space (contMDiffAt_extChartAt.comp p contMDiffAt_snd)
  have hh := (hV p).contMDiffAt.comp p hc
  apply hh.congr_of_eventuallyEq
  have hn : ∀ᶠ q : ℝ × M in 𝓝 p, q.2 ∈ (extChartAt 𝓘(ℝ,E) p.2).source :=
    continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds p.2)
  filter_upwards [hn] with q hq
  dsimp only [Function.comp_apply,timeChartField]
  rw [(extChartAt 𝓘(ℝ,E) p.2).left_inv hq]
  have hq' : q.2 ∈ (chartAt E p.2).source := by simpa only [extChartAt_source] using hq
  have he := (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p.2).continuousLinearMapAt_apply_of_mem
    (R := ℝ) (show q.2 ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p.2).baseSet by
      simpa only [TangentBundle.trivializationAt_baseSet] using hq') (V q)
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hq'] at he
  exact he.symm



end PackingSufficiencySupport.Hamiltonian
end

end OAI
