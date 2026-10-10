import OAI.Geometry.Symplectic.MorseBounds.ProductLocal
import OAI.Geometry.Symplectic.MorseBounds.CotangentFlow
import OAI.Geometry.Symplectic.MorseBounds.Composition

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.LocalCorrection
open MorseArnold.Geometry MorseArnold.GenericGeometry MorseArnold.ProductLocal
open MorseArnold.SphereCaps MorseArnold.CapProduct MorseArnold.CapSymplectic
open scoped Manifold ContDiff Topology
open Set Filter
noncomputable section
variable {X : Type} [TopologicalSpace X] [ChartedSpace (Model 4) X]
  [IsManifold (𝓡 4) ∞ X]
def delta (eps : ℝ) (phi : ℝ × (X × PlaneFour) → X × PlaneFour)
    (p : ℝ × (X × PlaneFour)) : X × PlaneFour :=
  phi (eps*p.1,exteriorFlow (-eps*p.1) p.2)
def K (F : X × PlaneFour → ℝ) (eps : ℝ)
    (phi : ℝ × (X × PlaneFour) → X × PlaneFour)
    (p : ℝ × (X × PlaneFour)) : ℝ :=
  eps * (F p.2 - quadratic (phi (-eps*p.1,p.2)).2)
def LocalModel (wX : Geometry.SymplecticForm (n := 4) (M := X))
    (F : X × PlaneFour → ℝ)
    (w : GenericGeometry.SymplecticForm (E := LE) (M := X × PlaneFour))
    (phi : ℝ × (X × PlaneFour) → X × PlaneFour) (eps : ℝ) : Prop :=
  (∀ p u v, w.form p u v = wX.form p.1 u.1 v.1 +
    planeArea u.2.1.1 v.2.1.1 + planeArea u.2.1.2 v.2.1.2 +
    planeArea u.2.2.1 v.2.2.1 + planeArea u.2.2.2 v.2.2.2) ∧
  ContMDiff (𝓘(ℝ).prod LI) LI ∞ phi ∧
  (∀ x, phi (0,x) = x) ∧
  (∀ s t x, phi (s+t,x) = phi (s,phi (t,x))) ∧
  (∀ x, IsMIntegralCurve (fun t => phi (t,x)) (GenericGeometry.hamiltonianField w F)) ∧
  (∀ t x, 9 ≤ totalSq x.2 → phi (t,x) = exteriorFlow t x) ∧
  (∀ t x, x.2 ∈ box → (phi (t,x)).2 ∈ box) ∧
  (GenericGeometry.criticalSet (E := LE) F).Finite ∧
  (∀ x ∈ GenericGeometry.criticalSet (E := LE) F, totalSq x.2 < 9) ∧
  0 < eps ∧ eps < Real.pi ∧
  (∀ x, phi (eps,x) = x ↔ x ∈ GenericGeometry.criticalSet (E := LE) F) ∧
  (∀ x, phi (eps,x) = x →
    let c := extChartAt LI x
    IsUnit (fderiv ℝ (c ∘ (fun y => phi (eps,y)) ∘ c.symm) (c x) -
      ContinuousLinearMap.id ℝ LE))
def CorrectionObligation : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [ChartedSpace (Model 4) X]
    [IsManifold (𝓡 4) ∞ X] [T2Space X] [SecondCountableTopology X]
    [CompactSpace X] [ConnectedSpace X]
    (wX : Geometry.SymplecticForm (n := 4) (M := X)) (F : X × PlaneFour → ℝ),
    GenericGeometry.IsMorse (E := LE) F →
    (∀ p, 9 ≤ totalSq p.2 → F p = quadratic p.2) →
    ∃ (w : GenericGeometry.SymplecticForm (E := LE) (M := X × PlaneFour))
      (phi : ℝ × (X × PlaneFour) → X × PlaneFour) (eps : ℝ),
      LocalModel wX F w phi eps ∧
      ContMDiff (𝓘(ℝ).prod LI) LI ∞ (delta eps phi) ∧
      ContMDiff (𝓘(ℝ).prod LI) 𝓘(ℝ) ∞ (K F eps phi) ∧
      (∀ t x, 9 ≤ totalSq x.2 → delta eps phi (t,x) = x ∧ K F eps phi (t,x) = 0) ∧
      (∀ t x, x.2 ∈ box → (delta eps phi (t,x)).2 ∈ box) ∧
      ∃ V : ℝ → (x : X × PlaneFour) → TangentSpace LI x,
        (∀ t x, w.form x (V t x) = mvfderiv LI (fun y => K F eps phi (t,y)) x) ∧
        (∀ t x, HasMFDerivAt 𝓘(ℝ) LI (fun s => delta eps phi (s,x)) t
          ((ContinuousLinearMap.id ℝ ℝ).smulRight (V t (delta eps phi (t,x)))))
end
end MorseArnold.LocalCorrection

namespace MorseArnold.LocalCorrection
open MorseArnold.Geometry MorseArnold.GenericGeometry MorseArnold.ProductLocal
open MorseArnold.SphereCaps MorseArnold.SphereHamiltonian
open MorseArnold.CapProduct MorseArnold.CapSymplectic
open scoped Manifold ContDiff Topology
open Set Filter
noncomputable section
variable {X : Type} [TopologicalSpace X] [ChartedSpace (Model 4) X]
  [IsManifold (𝓡 4) ∞ X]

lemma rotate_add (s t : ℝ) (z : Plane) :
    rotatePlane (s+t) z = rotatePlane s (rotatePlane t z) := by
  ext <;> simp [rotatePlane,Real.cos_add,Real.sin_add] <;> ring
lemma quad_add (s t : ℝ) (z : PlaneFour) :
    quadFlow (s+t) z = quadFlow s (quadFlow t z) := by
  simp only [quadFlow,neg_add,rotate_add]
omit [TopologicalSpace X] [ChartedSpace (Model 4) X] [IsManifold (𝓡 4) ∞ X] in
lemma exterior_add (s t : ℝ) (p : X × PlaneFour) :
    exteriorFlow (s+t) p = exteriorFlow s (exteriorFlow t p) := by
  exact Prod.ext rfl (quad_add s t p.2)
omit [TopologicalSpace X] [ChartedSpace (Model 4) X] [IsManifold (𝓡 4) ∞ X] in
lemma exterior_inverse (s : ℝ) (p : X × PlaneFour) :
    exteriorFlow s (exteriorFlow (-s) p) = p := by
  rw [← exterior_add,add_neg_cancel]
  exact Prod.ext rfl (quadFlow_zero p.2)
lemma quadratic_invariant (s : ℝ) (z : PlaneFour) :
    quadratic (quadFlow s z) = quadratic z := by
  simp only [quadratic,quadFlow,rotatePlane_radius]

omit [IsManifold (𝓡 4) ∞ X] in
lemma quadratic_msmooth :
    ContMDiff LI 𝓘(ℝ) ∞ (fun p : X × PlaneFour => quadratic p.2) := by
  have he : LI = ((𝓡 4).prod 𝓘(ℝ,PlaneFour)) := modelWithCornersSelf_prod
  rw [he]
  exact quadratic_smooth.contMDiff.comp contMDiff_snd

omit [IsManifold (𝓡 4) ∞ X] in
lemma quadratic_hamiltonian
    (wX : Geometry.SymplecticForm (n := 4) (M := X))
    (w : GenericGeometry.SymplecticForm (E := LE) (M := X × PlaneFour))
    (hw : ∀ p u v, w.form p u v = wX.form p.1 u.1 v.1 +
      planeArea u.2.1.1 v.2.1.1 + planeArea u.2.1.2 v.2.1.2 +
      planeArea u.2.2.1 v.2.2.1 + planeArea u.2.2.2 v.2.2.2)
    (p : X × PlaneFour) :
    w.form p (0,quadVelocity p.2) = mvfderiv LI (fun q => quadratic q.2) p := by
  have he : LI = ((𝓡 4).prod 𝓘(ℝ,PlaneFour)) := modelWithCornersSelf_prod
  have hQ := ((quadratic_deriv p.2).hasMFDerivAt).comp p
    (hasMFDerivAt_snd (I := 𝓡 4) (I' := 𝓘(ℝ,PlaneFour)) p)
  rw [← he] at hQ
  apply ContinuousLinearMap.ext
  intro v
  change w.form p (0,quadVelocity p.2) v = mfderiv LI 𝓘(ℝ) (fun q => quadratic q.2) p v
  calc
    _ = fourArea (quadVelocity p.2) v.2 := by
      have hform := hw p (0,quadVelocity p.2) v
      erw [map_zero,zero_apply,zero_add] at hform
      simpa only [fourArea_apply,add_assoc] using! hform
    _ = _ := (congrArg (fun L : LE →L[ℝ] ℝ => L v) hQ.mfderiv).symm

private theorem zero_prod_toSpanSingleton {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (v : F) :
    (0 : ℝ →L[ℝ] E).prod (ContinuousLinearMap.toSpanSingleton ℝ v) =
      (1 : ℝ →L[ℝ] ℝ).smulRight ((0 : E),v) := by
  apply ContinuousLinearMap.ext
  intro r
  simp

omit [IsManifold (𝓡 4) ∞ X] in
lemma quadratic_integral (p : X × PlaneFour) :
    IsMIntegralCurve (I := LI) (fun t => exteriorFlow t p)
      (fun q : X × PlaneFour => ((0,quadVelocity q.2) : TangentSpace LI q)) := by
  intro t
  have he : LI = ((𝓡 4).prod 𝓘(ℝ,PlaneFour)) := modelWithCornersSelf_prod
  have ha := hasMFDerivAt_const (I := 𝓘(ℝ)) (I' := 𝓡 4) p.1 t
  have hb := (quadFlow_ode t p.2).hasFDerivAt.hasMFDerivAt
  have hc := ha.prodMk hb
  rw [← he] at hc
  exact hc.congr_mfderiv
    (zero_prod_toSpanSingleton (E := Model 4) (quadVelocity (quadFlow t p.2)))

lemma rescale_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (phi : ℝ × M → M) (V : (x : M) → TangentSpace 𝓘(ℝ,E) x)
    (hODE : ∀ x, IsMIntegralCurve (fun t => phi (t,x)) V) (c t : ℝ) (x : M) :
    HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ,E) (fun s => phi (c*s,x)) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (c • V (phi (c*t,x)))) := by
  have h := (hODE x (c*t)).comp t (((hasDerivAt_id t).const_mul c).hasFDerivAt.hasMFDerivAt)
  have he : ((1 : ℝ →L[ℝ] ℝ).smulRight (show E from V (phi (c*t,x)))).comp
      (ContinuousLinearMap.toSpanSingleton ℝ (c*1)) =
      (ContinuousLinearMap.id ℝ ℝ).smulRight (c • (show E from V (phi (c*t,x)))) := by
    apply ContinuousLinearMap.ext
    intro r
    change (r * (c*1)) • V (phi (c*t,x)) = r • (c • V (phi (c*t,x)))
    simp only [smul_smul,mul_one]
  exact h.congr_mfderiv he

lemma rescale_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (phi : ℝ × M → M)
    (hphi : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ phi) (c : ℝ) :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ (fun p : ℝ × M => phi (c*p.1,p.2)) := by
  exact hphi.comp ((contMDiff_const.mul contMDiff_fst).prodMk contMDiff_snd)

lemma hamiltonian_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (w : (x : M) → TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ)
    (F : M → ℝ) (hF : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ) ∞ F)
    (V : (x : M) → TangentSpace 𝓘(ℝ,E) x)
    (hV : ∀ x, w x (V x) = mvfderiv 𝓘(ℝ,E) F x) (c : ℝ) (x : M) :
    w x (c • V x) = mvfderiv 𝓘(ℝ,E) (fun y => c*F y) x := by
  rw [map_smul,hV]
  have h := mvfderiv_fun_mul (mdifferentiableAt_const (c := c)) (hF.mdifferentiable (by simp) x)
  simpa only [mvfderiv_const, smul_zero, add_zero] using h.symm

theorem correctionObligation : CorrectionObligation := by
  intro X _ _ _ _ _ _ _ wX F hF hFq
  obtain ⟨w,hw,phi,hphi,hzero,hadd,hODE,hex,hbox,hfinite,hcrit,eps,heps,hepspi,hfix,hnd⟩ :=
    productLocalObligation X wX F hF hFq
  let a : ℝ × (X × PlaneFour) → X × PlaneFour := fun p => phi (eps*p.1,p.2)
  let ai : ℝ × (X × PlaneFour) → X × PlaneFour := fun p => phi (-eps*p.1,p.2)
  let b : ℝ × (X × PlaneFour) → X × PlaneFour := fun p => exteriorFlow (-eps*p.1) p.2
  let A : ℝ × (X × PlaneFour) → ℝ := fun p => eps*F p.2
  let B : ℝ × (X × PlaneFour) → ℝ := fun p => (-eps)*quadratic p.2.2
  let VA : ℝ → (x : X × PlaneFour) → TangentSpace LI x :=
    fun _ x => eps • GenericGeometry.hamiltonianField w F x
  let VB : ℝ → (x : X × PlaneFour) → TangentSpace LI x :=
    fun _ x => (-eps) • ((0,quadVelocity x.2) : LE)
  have ha : ContMDiff (𝓘(ℝ).prod LI) LI ∞ a := rescale_smooth phi hphi eps
  have hai : ContMDiff (𝓘(ℝ).prod LI) LI ∞ ai := rescale_smooth phi hphi (-eps)
  have hb : ContMDiff (𝓘(ℝ).prod LI) LI ∞ b :=
    rescale_smooth _ exterior_smooth (-eps)
  have hr : ∀ t, Function.RightInverse (fun x => ai (t,x)) (fun x => a (t,x)) := by
    intro t x
    change phi (eps*t,phi (-eps*t,x)) = x
    rw [← hadd,show eps*t + -eps*t = 0 by ring,hzero]
  have hl : ∀ t, Function.LeftInverse (fun x => ai (t,x)) (fun x => a (t,x)) := by
    intro t x
    change phi (-eps*t,phi (eps*t,x)) = x
    rw [← hadd,show -eps*t + eps*t = 0 by ring,hzero]
  have hs : ∀ t, MorseArnold.HamiltonianComposition.PreservesForm w.form (fun x => a (t,x)) := by
    intro t x u v
    exact GenericGeometry.manifold_hamiltonian_flow_preserves_form w F hF.1
      (GenericGeometry.hamiltonianField w F)
      (GenericGeometry.hamiltonianField_smooth w F hF.1)
      (GenericGeometry.hamiltonianField_equation w F) phi hphi hzero hODE (eps*t) x u v
  have hA : ContMDiff (𝓘(ℝ).prod LI) 𝓘(ℝ) ∞ A :=
    contMDiff_const.mul (hF.1.comp contMDiff_snd)
  have hB : ContMDiff (𝓘(ℝ).prod LI) 𝓘(ℝ) ∞ B :=
    contMDiff_const.mul (quadratic_msmooth.comp contMDiff_snd)
  have hVA : ∀ t x, w.form x (VA t x) = mvfderiv LI (fun y => A (t,y)) x := by
    intro t x
    exact hamiltonian_scale w.form F hF.1 (GenericGeometry.hamiltonianField w F)
      (GenericGeometry.hamiltonianField_equation w F) eps x
  have hVB : ∀ t x, w.form x (VB t x) = mvfderiv LI (fun y => B (t,y)) x := by
    intro t x
    exact hamiltonian_scale w.form (fun q => quadratic q.2) quadratic_msmooth
      (fun q => (0,quadVelocity q.2)) (quadratic_hamiltonian wX w hw) (-eps) x
  have hODEa : ∀ t x, HasMFDerivAt 𝓘(ℝ) LI (fun s => a (s,x)) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (VA t (a (t,x)))) := by
    intro t x
    exact rescale_integral phi (GenericGeometry.hamiltonianField w F) hODE eps t x
  have hODEb : ∀ t x, HasMFDerivAt 𝓘(ℝ) LI (fun s => b (s,x)) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (VB t (b (t,x)))) := by
    intro t x
    exact rescale_integral (fun q => exteriorFlow q.1 q.2)
      (fun q => (0,quadVelocity q.2)) quadratic_integral (-eps) t x
  have hc := MorseArnold.HamiltonianComposition.hamiltonian_path_composition
    w.form a ai b ha hai hb hr hl hs A B hA hB VA VB hVA hVB hODEa hODEb
  dsimp only at hc
  let V : ℝ → (x : X × PlaneFour) → TangentSpace LI x := fun t x =>
    (show LE from VA t x) +
      (show LE from mfderiv LI LI (fun y => a (t,y)) (ai (t,x)) (VB t (ai (t,x))))
  have hK : (fun q => A q + B (q.1,ai q)) = K F eps phi := by
    ext q
    dsimp [A,B,ai,K]
    ring
  rw [hK] at hc
  refine ⟨w,phi,eps,?_,hc.2.1,hc.1,?_,?_,V,?_,hc.2.2.2⟩
  · exact ⟨hw,hphi,hzero,hadd,hODE,hex,hbox,hfinite,hcrit,heps,hepspi,hfix,hnd⟩
  · intro t x hx
    constructor
    · change phi (eps*t,exteriorFlow (-eps*t) x) = x
      rw [hex (eps*t) _ (by simpa only [exteriorFlow,quadFlow_radius] using hx)]
      simpa only [neg_mul] using exterior_inverse (eps*t) x
    · change eps * (F x - quadratic (phi (-eps*t,x)).2) = 0
      rw [hFq x hx,hex (-eps*t) x hx]
      simp only [exteriorFlow,quadratic_invariant,sub_self,mul_zero]
  · intro t x hx
    exact hbox (eps*t) (exteriorFlow (-eps*t) x) (quadFlow_box (-eps*t) x.2 hx)
  · intro t x
    have hKt : (fun y => A (t,y) + B (t,ai (t,y))) = (fun y => K F eps phi (t,y)) :=
      funext (fun y => congrFun hK (t,y))
    simpa only [hKt] using hc.2.2.1 t x

end
end MorseArnold.LocalCorrection

end

end OAI
