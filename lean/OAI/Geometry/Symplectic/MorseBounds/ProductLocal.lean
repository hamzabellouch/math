import OAI.Geometry.Symplectic.MorseBounds.CapForm
import OAI.Geometry.Symplectic.MorseBounds.SphereHamiltonian
import OAI.Geometry.Symplectic.MorseBounds.Cotangent

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.ProductLocal
open MorseArnold.Geometry MorseArnold.SphereCaps MorseArnold.CapProduct
open MorseArnold.CapSymplectic
open scoped Manifold ContDiff
open Set
noncomputable section
abbrev LE := Model 4 × PlaneFour
abbrev LI := 𝓘(ℝ,LE)
def totalSq (z : PlaneFour) : ℝ :=
  radiusSq z.1.1 + radiusSq z.1.2 + radiusSq z.2.1 + radiusSq z.2.2
def quadratic (z : PlaneFour) : ℝ :=
  (-radiusSq z.1.1 - radiusSq z.1.2 + radiusSq z.2.1 + radiusSq z.2.2) / 2
variable {X : Type} [TopologicalSpace X] [ChartedSpace (Model 4) X]
instance productCharts : ChartedSpace LE (X × PlaneFour) :=
  prodChartedSpace (Model 4) X PlaneFour PlaneFour
instance productManifold [IsManifold (𝓡 4) ∞ X] : IsManifold LI ∞ (X × PlaneFour) := by
  rw [show LI = (𝓡 4).prod 𝓘(ℝ,PlaneFour) from modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓡 4) (I' := 𝓘(ℝ,PlaneFour)) (M := X) (M' := PlaneFour)
def exteriorFlow (t : ℝ) (p : X × PlaneFour) : X × PlaneFour := (p.1,quadFlow t p.2)
def ProductLocalObligation : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [ChartedSpace (Model 4) X]
    [IsManifold (𝓡 4) ∞ X] [T2Space X] [SecondCountableTopology X]
    [CompactSpace X] [ConnectedSpace X]
    (wX : Geometry.SymplecticForm (n := 4) (M := X)) (F : X × PlaneFour → ℝ),
    GenericGeometry.IsMorse (E := LE) F →
    (∀ p, 9 ≤ totalSq p.2 → F p = quadratic p.2) →
    ∃ w : GenericGeometry.SymplecticForm (E := LE) (M := X × PlaneFour),
      (∀ p u v, w.form p u v = wX.form p.1 u.1 v.1 +
        planeArea u.2.1.1 v.2.1.1 + planeArea u.2.1.2 v.2.1.2 +
        planeArea u.2.2.1 v.2.2.1 + planeArea u.2.2.2 v.2.2.2) ∧
      ∃ Φ : ℝ × (X × PlaneFour) → X × PlaneFour,
        ContMDiff (𝓘(ℝ).prod LI) LI ∞ Φ ∧
        (∀ x, Φ (0,x) = x) ∧
        (∀ s t x, Φ (s+t,x) = Φ (s,Φ (t,x))) ∧
        (∀ x, IsMIntegralCurve (fun t => Φ (t,x)) (GenericGeometry.hamiltonianField w F)) ∧
        (∀ t x, 9 ≤ totalSq x.2 → Φ (t,x) = exteriorFlow t x) ∧
        (∀ t x, x.2 ∈ box → (Φ (t,x)).2 ∈ box) ∧
        (GenericGeometry.criticalSet (E := LE) F).Finite ∧
        (∀ x ∈ GenericGeometry.criticalSet (E := LE) F, totalSq x.2 < 9) ∧
        ∃ ε : ℝ, 0 < ε ∧ ε < Real.pi ∧
          (∀ x, Φ (ε,x) = x ↔ x ∈ GenericGeometry.criticalSet (E := LE) F) ∧
          (∀ x, Φ (ε,x) = x →
            let c := extChartAt LI x
            IsUnit (fderiv ℝ (c ∘ (fun y => Φ (ε,y)) ∘ c.symm) (c x) -
              ContinuousLinearMap.id ℝ LE))
end
end MorseArnold.ProductLocal

namespace MorseArnold.ProductLocal
open MorseArnold.Geometry MorseArnold.SphereCaps MorseArnold.SphereHamiltonian
open MorseArnold.CapProduct MorseArnold.CapSymplectic MorseArnold.SymplecticProduct
open scoped Manifold ContDiff
open Filter Topology Set
noncomputable section
lemma totalSq_smooth : ContDiff ℝ ∞ totalSq := by unfold totalSq radiusSq; fun_prop
lemma quadratic_smooth : ContDiff ℝ ∞ quadratic := by unfold quadratic radiusSq; fun_prop
lemma totalSq_nonneg (z : PlaneFour) : 0 ≤ totalSq z := by
  unfold totalSq radiusSq; positivity
lemma norm_le_of_totalSq (z : PlaneFour) (h : totalSq z ≤ 9) : ‖z‖ ≤ 3 := by
  have h1 := sq_nonneg z.1.1.1
  have h2 := sq_nonneg z.1.1.2
  have h3 := sq_nonneg z.1.2.1
  have h4 := sq_nonneg z.1.2.2
  have h5 := sq_nonneg z.2.1.1
  have h6 := sq_nonneg z.2.1.2
  have h7 := sq_nonneg z.2.2.1
  have h8 := sq_nonneg z.2.2.2
  simp only [Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le]
  unfold totalSq radiusSq at h
  refine ⟨⟨⟨?_,?_⟩,⟨?_,?_⟩⟩,⟨⟨?_,?_⟩,⟨?_,?_⟩⟩⟩ <;> constructor <;> nlinarith
lemma in_box_of_totalSq (z : PlaneFour) (h : totalSq z ≤ 9) : z ∈ box := by
  have h1 : 0 ≤ radiusSq z.1.1 := by unfold radiusSq; positivity
  have h2 : 0 ≤ radiusSq z.1.2 := by unfold radiusSq; positivity
  have h3 : 0 ≤ radiusSq z.2.1 := by unfold radiusSq; positivity
  have h4 : 0 ≤ radiusSq z.2.2 := by unfold radiusSq; positivity
  change (radiusSq z.1.1 < 16 ∧ radiusSq z.1.2 < 16) ∧
    (radiusSq z.2.1 < 16 ∧ radiusSq z.2.2 < 16)
  unfold totalSq at h
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
lemma core_compact {X : Type} [TopologicalSpace X] [CompactSpace X] :
    IsCompact {p : X × PlaneFour | totalSq p.2 ≤ 9} := by
  have hc : IsClosed {p : X × PlaneFour | totalSq p.2 ≤ 9} :=
    isClosed_le (totalSq_smooth.continuous.comp continuous_snd) continuous_const
  apply (isCompact_univ.prod (isCompact_closedBall (0 : PlaneFour) 3)).of_isClosed_subset hc
  intro p hp
  exact ⟨mem_univ p.1, by simpa [Metric.mem_closedBall,dist_zero_right] using norm_le_of_totalSq p.2 hp⟩
lemma rotatePlane_radius (t : ℝ) (z : Plane) : radiusSq (rotatePlane t z) = radiusSq z := by
  unfold radiusSq rotatePlane
  dsimp
  nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg z.1, sq_nonneg z.2,
    mul_nonneg (sq_nonneg z.1) (sq_nonneg (Real.sin t))]
lemma quadFlow_radius (t : ℝ) (z : PlaneFour) : totalSq (quadFlow t z) = totalSq z := by
  simp only [totalSq,quadFlow,rotatePlane_radius]
lemma quadFlow_box (t : ℝ) (z : PlaneFour) (h : z ∈ box) : quadFlow t z ∈ box := by
  simpa only [box,disk,mem_prod,mem_ofPred_eq,quadFlow,rotatePlane_radius] using h
lemma quadFlow_zero (z : PlaneFour) : quadFlow 0 z = z := by
  simp [quadFlow,rotatePlane]
lemma quadFlow_smooth : ContDiff ℝ ∞ (fun p : ℝ × PlaneFour => quadFlow p.1 p.2) := by
  unfold quadFlow rotatePlane
  fun_prop
lemma rotatePlane_fixed (t : ℝ) (hc : Real.cos t ≠ 1) (z : Plane)
    (h : rotatePlane t z = z) : z = 0 := by
  have hd : 0 < (Real.cos t - 1)^2 + Real.sin t ^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (sub_ne_zero.mpr hc)) (sq_nonneg _)
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  change Real.cos t*z.1-Real.sin t*z.2=z.1 at h0
  change Real.sin t*z.1+Real.cos t*z.2=z.2 at h1
  have ha : ((Real.cos t-1)^2+Real.sin t^2)*z.1=0 := by
    linear_combination (Real.cos t-1)*h0+Real.sin t*h1
  have hb : ((Real.cos t-1)^2+Real.sin t^2)*z.2=0 := by
    linear_combination -Real.sin t*h0+(Real.cos t-1)*h1
  exact Prod.ext ((mul_eq_zero.mp ha).resolve_left (ne_of_gt hd))
    ((mul_eq_zero.mp hb).resolve_left (ne_of_gt hd))
lemma quadFlow_fixed (t : ℝ) (ht : 0 < t) (htp : t < Real.pi) (z : PlaneFour)
    (h : quadFlow t z = z) : z = 0 := by
  have hc : Real.cos t ≠ 1 := by
    intro h
    have hz := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) (by linarith : t < 2*Real.pi)).mp h
    linarith
  have hn : Real.cos (-t) ≠ 1 := by simpa using hc
  have ha := rotatePlane_fixed t hc z.1.1 (congrArg (fun q : PlaneFour => q.1.1) h)
  have hb := rotatePlane_fixed t hc z.1.2 (congrArg (fun q : PlaneFour => q.1.2) h)
  have hd := rotatePlane_fixed (-t) hn z.2.1 (congrArg (fun q : PlaneFour => q.2.1) h)
  have he := rotatePlane_fixed (-t) hn z.2.2 (congrArg (fun q : PlaneFour => q.2.2) h)
  exact Prod.ext (Prod.ext ha hb) (Prod.ext hd he)

def fourArea : PlaneFour →L[ℝ] PlaneFour →L[ℝ] ℝ := fourPlaneForm (0 : PlaneFour)
lemma fourArea_apply (u v : PlaneFour) : fourArea u v =
    (planeArea u.1.1 v.1.1 + planeArea u.1.2 v.1.2) +
    (planeArea u.2.1 v.2.1 + planeArea u.2.2 v.2.2) := rfl
lemma fourArea_nondegenerate : Function.Injective fourArea := by
  obtain ⟨wp,hwp⟩ := plane_symplectic
  let wpp := symplecticProd wp wp
  have h := prod_nondegenerate wpp wpp (0 : PlaneFour)
  dsimp only [wpp,symplecticProd] at h
  rw [hwp] at h
  change Function.Injective fourArea at h
  exact h
lemma fourArea_chart (x y : PlaneFour) :
    SymplecticProduct.chartTwoForm 𝓘(ℝ,PlaneFour) (fun _ : PlaneFour => fourArea) x y = fourArea := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change fourArea
    (mfderiv 𝓘(ℝ,PlaneFour) 𝓘(ℝ,PlaneFour) (extChartAt 𝓘(ℝ,PlaneFour) x).symm y u)
    (mfderiv 𝓘(ℝ,PlaneFour) 𝓘(ℝ,PlaneFour) (extChartAt 𝓘(ℝ,PlaneFour) x).symm y v) = _
  have hc : ((extChartAt 𝓘(ℝ,PlaneFour) x).symm : PlaneFour → PlaneFour) = id := rfl
  rw [hc,mfderiv_id]
  rfl
def four_symplectic : SymplecticProduct.SymplecticForm 𝓘(ℝ,PlaneFour) (M := PlaneFour) where
  form := fun _ => fourArea
  alternating := by
    intro p u
    change PlaneFour at u
    change fourArea u u = 0
    rw [fourArea_apply]
    simp only [planeArea_apply]
    ring
  nondegenerate := fun _ => fourArea_nondegenerate
  smooth := by
    intro x
    rw [show SymplecticProduct.chartTwoForm 𝓘(ℝ,PlaneFour) (fun _ => fourArea) x =
      (fun _ => fourArea) from funext (fourArea_chart x)]
    exact contDiffOn_const
  closed := by
    intro x y hy u v w
    rw [show SymplecticProduct.chartTwoForm 𝓘(ℝ,PlaneFour) (fun _ => fourArea) x =
      (fun _ => fourArea) from funext (fourArea_chart x)]
    have hd : fderiv ℝ (fun _ : PlaneFour => fourArea) y = 0 := congrFun (fderiv_const fourArea) y
    rw [hd]
    simp

def promoteX {X : Type} [TopologicalSpace X] [ChartedSpace (Model 4) X]
    (wX : Geometry.SymplecticForm (n := 4) (M := X)) :
    SymplecticProduct.SymplecticForm (𝓡 4) (M := X) :=
  ⟨wX.form,wX.alternating,wX.nondegenerate,wX.smooth,wX.closed⟩

lemma local_symplectic {X : Type} [TopologicalSpace X] [ChartedSpace (Model 4) X]
    [IsManifold (𝓡 4) ∞ X] (wX : Geometry.SymplecticForm (n := 4) (M := X)) :
    ∃ w : GenericGeometry.SymplecticForm (E := LE) (M := X × PlaneFour),
      ∀ p u v, w.form p u v = wX.form p.1 u.1 v.1 +
        planeArea u.2.1.1 v.2.1.1 + planeArea u.2.1.2 v.2.1.2 +
        planeArea u.2.2.1 v.2.2.1 + planeArea u.2.2.2 v.2.2.2 := by
  let wt := symplecticProd (promoteX wX) four_symplectic
  have hc (p : X × PlaneFour) : GenericGeometry.chartTwoForm (E := LE) wt.form p =
      SymplecticProduct.chartTwoForm ((𝓡 4).prod 𝓘(ℝ,PlaneFour)) wt.form p := by
    have he : LI = ((𝓡 4).prod 𝓘(ℝ,PlaneFour)) := modelWithCornersSelf_prod
    exact congrArg (fun I : ModelWithCorners ℝ LE LE =>
      SymplecticProduct.chartTwoForm I (fun q => wt.form q) p) he

  refine ⟨⟨wt.form,wt.alternating,wt.nondegenerate,?_,?_⟩,?_⟩
  · intro p
    rw [hc]
    have hh : (extChartAt LI p).target =
        (extChartAt ((𝓡 4).prod 𝓘(ℝ,PlaneFour)) p).target :=
      congrArg (fun I : ModelWithCorners ℝ LE LE => (extChartAt I p).target)
        (modelWithCornersSelf_prod : LI = ((𝓡 4).prod 𝓘(ℝ,PlaneFour)))
    rw [hh]
    exact wt.smooth p
  · intro p y hy u v z
    rw [hc]
    apply wt.closed p y _ u v z
    have hh : (extChartAt LI p).target =
        (extChartAt ((𝓡 4).prod 𝓘(ℝ,PlaneFour)) p).target :=
      congrArg (fun I : ModelWithCorners ℝ LE LE => (extChartAt I p).target)
        (modelWithCornersSelf_prod : LI = ((𝓡 4).prod 𝓘(ℝ,PlaneFour)))
    rwa [← hh]
  · intro p u v
    change wX.form p.1 u.1 v.1 + fourArea u.2 v.2 = _
    rw [fourArea_apply]
    ring

def planeVelocity (s : ℝ) (z : Plane) : Plane := (s*z.2,-s*z.1)
def quadVelocity (z : PlaneFour) : PlaneFour :=
  ((planeVelocity (-1) z.1.1,planeVelocity (-1) z.1.2),
    (planeVelocity 1 z.2.1,planeVelocity 1 z.2.2))
def planePotential (s : ℝ) (z : Plane) : ℝ := (s/2)*radiusSq z

def proj11 : PlaneFour →L[ℝ] Plane :=
  (ContinuousLinearMap.fst ℝ Plane Plane).comp (ContinuousLinearMap.fst ℝ (Plane×Plane) (Plane×Plane))
def proj12 : PlaneFour →L[ℝ] Plane :=
  (ContinuousLinearMap.snd ℝ Plane Plane).comp (ContinuousLinearMap.fst ℝ (Plane×Plane) (Plane×Plane))
def proj21 : PlaneFour →L[ℝ] Plane :=
  (ContinuousLinearMap.fst ℝ Plane Plane).comp (ContinuousLinearMap.snd ℝ (Plane×Plane) (Plane×Plane))
def proj22 : PlaneFour →L[ℝ] Plane :=
  (ContinuousLinearMap.snd ℝ Plane Plane).comp (ContinuousLinearMap.snd ℝ (Plane×Plane) (Plane×Plane))
lemma planePotential_deriv (s : ℝ) (z : Plane) :
    HasFDerivAt (planePotential s) (planeArea (planeVelocity s z)) z := by
  have hx : HasFDerivAt (fun z : Plane => z.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) z := hasFDerivAt_fst
  have hy : HasFDerivAt (fun z : Plane => z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) z := hasFDerivAt_snd
  convert ((hx.pow 2).add (hy.pow 2)).const_mul (s/2) using 1 <;> try rfl
  apply ContinuousLinearMap.ext
  intro v
  simp [planeArea,planeVelocity]
  ring
lemma quadratic_deriv (z : PlaneFour) :
    HasFDerivAt quadratic (fourArea (quadVelocity z)) z := by
  have h1 := (planePotential_deriv (-1) z.1.1).comp z proj11.hasFDerivAt
  have h2 := (planePotential_deriv (-1) z.1.2).comp z proj12.hasFDerivAt
  have h3 := (planePotential_deriv 1 z.2.1).comp z proj21.hasFDerivAt
  have h4 := (planePotential_deriv 1 z.2.2).comp z proj22.hasFDerivAt
  convert ((h1.add h2).add h3).add h4 using 1 <;> try rfl
  · ext y
    change quadratic y = planePotential (-1) y.1.1 +
      planePotential (-1) y.1.2 + planePotential 1 y.2.1 + planePotential 1 y.2.2
    unfold quadratic planePotential
    ring
  · apply ContinuousLinearMap.ext
    intro v
    rw [fourArea_apply]
    simp [proj11,proj12,proj21,proj22,quadVelocity,add_assoc]

lemma rotatePlane_deriv (a t : ℝ) (z : Plane) :
    HasDerivAt (fun r => rotatePlane (a*r) z) (planeVelocity (-a) (rotatePlane (a*t) z)) t := by
  have hc := ((hasDerivAt_id t).const_mul a).cos
  have hs := ((hasDerivAt_id t).const_mul a).sin
  convert ((hc.mul_const z.1).sub (hs.mul_const z.2)).prodMk
    ((hs.mul_const z.1).add (hc.mul_const z.2)) using 1 <;> try rfl
  ext <;> simp [planeVelocity,rotatePlane] <;> ring
lemma quadFlow_ode (t : ℝ) (z : PlaneFour) :
    HasDerivAt (fun r => quadFlow r z) (quadVelocity (quadFlow t z)) t := by
  have h1 := rotatePlane_deriv 1 t z.1.1
  have h2 := rotatePlane_deriv 1 t z.1.2
  have h3 := rotatePlane_deriv (-1) t z.2.1
  have h4 := rotatePlane_deriv (-1) t z.2.2
  simpa only [quadFlow,quadVelocity,one_mul,neg_mul,neg_neg] using
    (h1.prodMk h2).prodMk (h3.prodMk h4)

lemma totalSq_smul (a : ℝ) (z : PlaneFour) : totalSq (a • z) = a^2 * totalSq z := by
  simp only [totalSq,radiusSq,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

lemma exterior_dense {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (f g : X × PlaneFour → Y) (hf : Continuous f) (hg : Continuous g)
    (he : ∀ p, 9 < totalSq p.2 → f p = g p) (p : X × PlaneFour) (hp : 9 ≤ totalSq p.2) :
    f p = g p := by
  let a : ℕ → ℝ := fun n => 1 + 1 / (n + 1 : ℝ)
  have ha : Tendsto a atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht : Tendsto (fun n => (p.1,a n • p.2)) atTop (𝓝 p) := by
    simpa using tendsto_const_nhds.prodMk_nhds (ha.smul_const p.2)
  apply (isClosed_eq hf hg).mem_of_tendsto ht
  filter_upwards [] with n
  apply he
  rw [totalSq_smul]
  have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
  have hh : 1 < a n := by dsimp [a]; linarith
  nlinarith [sq_nonneg (a n-1)]

lemma exteriorField {X : Type} [TopologicalSpace X] [ChartedSpace (Model 4) X]
    [IsManifold (𝓡 4) ∞ X]
    (wX : Geometry.SymplecticForm (n := 4) (M := X))
    (w : GenericGeometry.SymplecticForm (E := LE) (M := X × PlaneFour))
    (hw : ∀ p u v, w.form p u v = wX.form p.1 u.1 v.1 +
      planeArea u.2.1.1 v.2.1.1 + planeArea u.2.1.2 v.2.1.2 +
      planeArea u.2.2.1 v.2.2.1 + planeArea u.2.2.2 v.2.2.2)
    (F : X × PlaneFour → ℝ)
    (hFq : ∀ p, 9 ≤ totalSq p.2 → F p = quadratic p.2)
    (p : X × PlaneFour) (hp : 9 < totalSq p.2) :
    GenericGeometry.hamiltonianField w F p = (0,quadVelocity p.2) := by
  have hEq : F =ᶠ[𝓝 p] (fun q => quadratic q.2) := by
    have hn : {q : X × PlaneFour | 9 < totalSq q.2} ∈ 𝓝 p :=
      (isOpen_lt continuous_const (totalSq_smooth.continuous.comp continuous_snd)).mem_nhds hp
    filter_upwards [hn] with q hq
    exact hFq q (le_of_lt hq)
  have he : LI = ((𝓡 4).prod 𝓘(ℝ,PlaneFour)) := modelWithCornersSelf_prod
  have hQ := ((quadratic_deriv p.2).hasMFDerivAt).comp p
    (hasMFDerivAt_snd (I := 𝓡 4) (I' := 𝓘(ℝ,PlaneFour)) p)
  rw [← he] at hQ
  apply w.nondegenerate p
  rw [GenericGeometry.hamiltonianField_equation]
  apply ContinuousLinearMap.ext
  intro v
  change mfderiv LI 𝓘(ℝ) F p v = _
  refine (congrArg (fun L : LE →L[ℝ] ℝ => L v) hEq.mfderiv_eq).trans
    ((congrArg (fun L : LE →L[ℝ] ℝ => L v) hQ.mfderiv).trans ?_)
  change fourArea (quadVelocity p.2) v.2 = w.form p (0,quadVelocity p.2) v
  have hform := (hw p (0,quadVelocity p.2) v).symm
  erw [map_zero,zero_apply,zero_add] at hform
  simpa only [fourArea_apply,add_assoc] using! hform

lemma quadFlow_msmooth :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ,PlaneFour)) 𝓘(ℝ,PlaneFour) ∞
      (fun q : ℝ × PlaneFour => quadFlow q.1 q.2) := by
  rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod]
  exact quadFlow_smooth.contMDiff

lemma smooth_product_flow {E F A B M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace A M] [ChartedSpace B N]
    {I : ModelWithCorners ℝ E A} {J : ModelWithCorners ℝ F B}
    {Phi : ℝ × N → N} (hPhi : ContMDiff (𝓘(ℝ).prod J) J ∞ Phi) :
    ContMDiff (𝓘(ℝ).prod (I.prod J)) (I.prod J) ∞
      (fun q : ℝ × (M × N) => (q.2.1,Phi (q.1,q.2.2))) := by
  have h1 : ContMDiff (𝓘(ℝ).prod (I.prod J)) I ∞ (fun q : ℝ × (M × N) => q.2.1) :=
    contMDiff_snd.fst
  have h2 : ContMDiff (𝓘(ℝ).prod (I.prod J)) (𝓘(ℝ).prod J) ∞
      (fun q : ℝ × (M × N) => (q.1,q.2.2)) :=
    contMDiff_fst.prodMk contMDiff_snd.snd
  exact h1.prodMk (hPhi.comp h2)

lemma exterior_smooth {X : Type} [TopologicalSpace X] [ChartedSpace (Model 4) X]
    [IsManifold (𝓡 4) ∞ X] :
    ContMDiff (𝓘(ℝ).prod LI) LI ∞ (fun q : ℝ × (X × PlaneFour) => exteriorFlow q.1 q.2) := by
  have he : LI = ((𝓡 4).prod 𝓘(ℝ,PlaneFour)) := modelWithCornersSelf_prod
  rw [he]
  exact smooth_product_flow (I := 𝓡 4) (M := X) quadFlow_msmooth

private theorem zero_prod_toSpanSingleton {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (v : F) :
    (0 : ℝ →L[ℝ] E).prod (ContinuousLinearMap.toSpanSingleton ℝ v) =
      (1 : ℝ →L[ℝ] ℝ).smulRight ((0 : E),v) := by
  apply ContinuousLinearMap.ext
  intro r
  simp

lemma exterior_integral {X : Type} [TopologicalSpace X] [ChartedSpace (Model 4) X]
    [IsManifold (𝓡 4) ∞ X]
    (wX : Geometry.SymplecticForm (n := 4) (M := X))
    (w : GenericGeometry.SymplecticForm (E := LE) (M := X × PlaneFour))
    (hw : ∀ p u v, w.form p u v = wX.form p.1 u.1 v.1 +
      planeArea u.2.1.1 v.2.1.1 + planeArea u.2.1.2 v.2.1.2 +
      planeArea u.2.2.1 v.2.2.1 + planeArea u.2.2.2 v.2.2.2)
    (F : X × PlaneFour → ℝ)
    (hFq : ∀ p, 9 ≤ totalSq p.2 → F p = quadratic p.2)
    (p : X × PlaneFour) (hp : 9 < totalSq p.2) :
    IsMIntegralCurve (fun t => exteriorFlow t p) (GenericGeometry.hamiltonianField w F) := by
  intro t
  have ht : 9 < totalSq (exteriorFlow t p).2 := by simpa only [exteriorFlow,quadFlow_radius] using hp
  rw [exteriorField wX w hw F hFq (exteriorFlow t p) ht]
  have he : LI = ((𝓡 4).prod 𝓘(ℝ,PlaneFour)) := modelWithCornersSelf_prod
  have ha := hasMFDerivAt_const (I := 𝓘(ℝ)) (I' := 𝓡 4) p.1 t
  have hb := (quadFlow_ode t p.2).hasFDerivAt.hasMFDerivAt
  have hc := ha.prodMk hb
  rw [← he] at hc
  exact hc.congr_mfderiv
    (zero_prod_toSpanSingleton (E := Model 4) (quadVelocity (quadFlow t p.2)))

lemma exterior_no_fixed {X : Type} [TopologicalSpace X]
    (t : ℝ) (ht : 0 < t) (htp : t < Real.pi) (x : X × PlaneFour)
    (hx : 9 ≤ totalSq x.2) : exteriorFlow t x ≠ x := by
  intro he
  have hz := quadFlow_fixed t ht htp x.2 (congrArg Prod.snd he)
  rw [hz] at hx
  norm_num [totalSq,radiusSq] at hx

theorem productLocalObligation : ProductLocalObligation := by
  intro X _ _ _ _ _ _ _ wX F hF hFq
  obtain ⟨w,hw⟩ := local_symplectic wX
  refine ⟨w,hw,?_⟩
  let U : Set (X × PlaneFour) := {p | 9 < totalSq p.2}
  let Ψ : ℝ × (X × PlaneFour) → X × PlaneFour := fun q => exteriorFlow q.1 q.2
  have hU : IsOpen U := isOpen_lt continuous_const (totalSq_smooth.continuous.comp continuous_snd)
  have hK : IsCompact Uᶜ := by
    convert (core_compact (X := X)) using 1
    ext p
    simp [U]
  have hΨ : ContMDiff (𝓘(ℝ).prod LI) LI ∞ Ψ := exterior_smooth
  have hΨi : ∀ x ∈ U, Ψ (0,x) = x := by
    intro x hx
    exact Prod.ext rfl (quadFlow_zero x.2)
  have hΨd : ∀ x ∈ U, IsMIntegralCurve (fun t => Ψ (t,x))
      (GenericGeometry.hamiltonianField w F) := by
    intro x hx
    exact exterior_integral wX w hw F hFq x hx
  have hΨU : ∀ t x, x ∈ U → Ψ (t,x) ∈ U := by
    intro t x hx
    change 9 < totalSq (quadFlow t x.2)
    rwa [quadFlow_radius]
  have hnf : ∀ t, 0 < t → t < Real.pi → ∀ x ∈ U, Ψ (t,x) ≠ x := by
    intro t ht htp x hx
    exact exterior_no_fixed t ht htp x (le_of_lt hx)
  obtain ⟨Φ,hΦ,hi,hadd,hd,hext,hInv,hfin,ε,he,hep,hfix,hnd⟩ :=
    GenericGeometry.localHamiltonianModelExistence LE (X × PlaneFour) w F hF U hU hK
      Ψ hΨ.contMDiffOn hΨi hΨd hΨU hnf
  have hext' : ∀ t x, 9 ≤ totalSq x.2 → Φ (t,x) = exteriorFlow t x := by
    intro t x hx
    exact exterior_dense (fun p => Φ (t,p)) (fun p => exteriorFlow t p)
      (hΦ.continuous.comp (continuous_const.prodMk continuous_id))
      (hΨ.continuous.comp (continuous_const.prodMk continuous_id))
      (fun p hp => hext t p hp) x hx
  refine ⟨Φ,hΦ,hi,hadd,hd,hext',?_,hfin,?_,ε,he,hep,hfix,hnd⟩
  · intro t x hx
    by_cases hxu : x ∈ U
    · rw [hext' t x (le_of_lt hxu)]
      exact quadFlow_box t x.2 hx
    · have ht := hInv t x hxu
      apply in_box_of_totalSq
      exact le_of_not_gt ht
  · intro x hx
    by_contra h
    exact exterior_no_fixed ε he hep x (le_of_not_gt h)
      ((hext' ε x (le_of_not_gt h)).symm.trans ((hfix x).mpr hx))

end
end MorseArnold.ProductLocal

end

end OAI
