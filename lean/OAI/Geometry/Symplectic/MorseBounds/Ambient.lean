import OAI.Geometry.Symplectic.MorseBounds.ProductForm
import OAI.Geometry.Symplectic.MorseBounds.SphereHamiltonian

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.AmbientHamiltonian
open MorseArnold.Geometry MorseArnold.SphereCaps MorseArnold.SphereHamiltonian
open MorseArnold.CapProduct MorseArnold.SphereSymplectic
open scoped Manifold ContDiff
open Set
noncomputable section
abbrev SI := (𝓡 2).prod (𝓡 2)
abbrev AI := (𝓡 4).prod SP

def onePotential (l eps s : ℝ) (p : S2) : ℝ :=
  sphereHamiltonian l eps s ((p : R3) 2)
def pairPotential (l eps s : ℝ) (p : S2 × S2) : ℝ :=
  onePotential l eps s p.1 + onePotential l eps s p.2
def fourPotential (l eps : ℝ) (p : SphereFour) : ℝ :=
  pairPotential l eps (-1) p.1 + pairPotential l eps 1 p.2

def pairVelocity (l eps s : ℝ) (p : S2 × S2) : TangentSpace SI p :=
  (velocity l eps s p.1,velocity l eps s p.2)
def fourVelocity (l eps : ℝ) (p : SphereFour) : TangentSpace SP p :=
  (pairVelocity l eps (-1) p.1, pairVelocity l eps 1 p.2)
def areaValue (l : ℝ) (p : S2) (u v : TangentSpace (𝓡 2) p) : ℝ :=
  l * standardArea (p : R3) (tangentInclusion p u) (tangentInclusion p v)

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Model 4) X]
  [IsManifold (𝓡 4) ∞ X]
def ambientPotential (l eps : ℝ) (p : X × SphereFour) : ℝ := fourPotential l eps p.2
def ambientFlow (l eps t : ℝ) (p : X × SphereFour) : X × SphereFour :=
  (p.1,fourFlow l eps t p.2)
def ambientVelocity (l eps : ℝ) (p : X × SphereFour) : TangentSpace AI p :=
  (0,fourVelocity l eps p.2)

def AmbientHamiltonianObligation : Prop :=
  ∀ (wX : Geometry.SymplecticForm (n := 4) (M := X)) (l eps : ℝ),
  ∀ (hl : 25 / 2 < l), 0 < eps → eps < Real.pi →
  ∃ w : SymplecticProduct.SymplecticForm AI (M := X × SphereFour),
    (∀ p u v, w.form p u v = wX.form p.1 u.1 v.1 +
      ((areaValue l p.2.1.1 u.2.1.1 v.2.1.1 + areaValue l p.2.1.2 u.2.1.2 v.2.1.2) +
       (areaValue l p.2.2.1 u.2.2.1 v.2.2.1 + areaValue l p.2.2.2 u.2.2.2 v.2.2.2))) ∧
    ContMDiff AI 𝓘(ℝ) ∞ (ambientPotential (X := X) l eps) ∧
    (∀ p, w.form p (ambientVelocity l eps p) = mvfderiv AI (ambientPotential l eps) p) ∧
    ContMDiff (𝓘(ℝ).prod AI) AI ∞ (fun q : ℝ × (X × SphereFour) => ambientFlow l eps q.1 q.2) ∧
    (∀ p : X × SphereFour, ambientFlow l eps 0 p = p) ∧
    (∀ (t u : ℝ) (p : X × SphereFour), ambientFlow l eps (t+u) p = ambientFlow l eps t (ambientFlow l eps u p)) ∧
    (∀ (t : ℝ) (p : X × SphereFour), HasMFDerivAt 𝓘(ℝ) AI (fun r => ambientFlow l eps r p) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (ambientVelocity l eps (ambientFlow l eps t p)))) ∧
    (∀ p : X × SphereFour, ambientFlow l eps 1 p = p ↔
      p.2.1.1 ∈ poleSet ∧ p.2.1.2 ∈ poleSet ∧ p.2.2.1 ∈ poleSet ∧ p.2.2.2 ∈ poleSet) ∧
    (∀ p : X × SphereFour, (∀ nu : Choices, p.2 ∉ (fourChart l (by linarith) nu).source) →
      ambientFlow l eps 1 p ≠ p) ∧
    (∀ (nu : Choices) (p : X × SphereFour), p.2 ∈ (fourChart l (by linarith) nu).source →
      fourChart l (by linarith) nu (ambientFlow l eps 1 p).2 =
        quadFlow eps (fourChart l (by linarith) nu p.2))
end
end MorseArnold.AmbientHamiltonian

namespace MorseArnold.AmbientHamiltonian
open MorseArnold.Geometry MorseArnold.SphereCaps MorseArnold.SphereHamiltonian
open MorseArnold.CapProduct MorseArnold.SphereSymplectic
open scoped Manifold ContDiff
open Set
noncomputable section

def promote {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Model n) M]
    (w : Geometry.SymplecticForm (n := n) (M := M)) :
    SymplecticProduct.SymplecticForm (𝓡 n) (M := M) where
  form := w.form
  alternating := w.alternating
  nondegenerate := w.nondegenerate
  smooth := w.smooth
  closed := w.closed

section Generic
variable {E F A B M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace A M] [ChartedSpace B N]
  {I : ModelWithCorners ℝ E A} {J : ModelWithCorners ℝ F B}

lemma prod_potential_deriv {f : M → ℝ} {g : N → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hg : ContMDiff J 𝓘(ℝ) ∞ g)
    (p : M × N) (v : TangentSpace (I.prod J) p) :
    mvfderiv (I.prod J) (fun p : M × N => f p.1 + g p.2) p v =
      mvfderiv I f p.1 v.1 + mvfderiv J g p.2 v.2 := by
  have h1 := ((hf.mdifferentiable (by simp) p.1).hasMFDerivAt).comp p (hasMFDerivAt_fst (I := I) (I' := J) p)
  have h2 := ((hg.mdifferentiable (by simp) p.2).hasMFDerivAt).comp p (hasMFDerivAt_snd (I := I) (I' := J) p)
  have hd := (h1.add h2).mfderiv
  exact congrArg (fun L => L v) hd

lemma prod_hamiltonian (wM : SymplecticProduct.TwoForm I (M := M))
    (wN : SymplecticProduct.TwoForm J (M := N))
    (VM : (p : M) → TangentSpace I p) (VN : (p : N) → TangentSpace J p)
    {f : M → ℝ} {g : N → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hg : ContMDiff J 𝓘(ℝ) ∞ g)
    (hM : ∀ p, wM p (VM p) = mvfderiv I f p)
    (hN : ∀ p, wN p (VN p) = mvfderiv J g p) (p : M × N) :
    SymplecticProduct.prodForm I J wM wN p (VM p.1,VN p.2) =
      mvfderiv (I.prod J) (fun p : M × N => f p.1 + g p.2) p := by
  apply ContinuousLinearMap.ext
  intro v
  change wM p.1 (VM p.1) v.1 + wN p.2 (VN p.2) v.2 = _
  rw [hM,hN,prod_potential_deriv hf hg]

lemma prod_curve_ode {a : ℝ → M} {b : ℝ → N} {t : ℝ}
    {v : TangentSpace I (a t)} {w : TangentSpace J (b t)}
    (ha : HasMFDerivAt 𝓘(ℝ) I a t ((ContinuousLinearMap.id ℝ ℝ).smulRight v))
    (hb : HasMFDerivAt 𝓘(ℝ) J b t ((ContinuousLinearMap.id ℝ ℝ).smulRight w)) :
    HasMFDerivAt 𝓘(ℝ) (I.prod J) (fun r => (a r,b r)) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (v,w)) := by
  have he : (((ContinuousLinearMap.id ℝ ℝ).smulRight v).prod
      ((ContinuousLinearMap.id ℝ ℝ).smulRight w)) =
      (ContinuousLinearMap.id ℝ ℝ).smulRight (v,w) := by
    apply ContinuousLinearMap.ext
    intro r
    rfl
  exact (ha.prodMk hb).congr_mfderiv he
lemma smooth_id_flow {Phi : ℝ × N → N}
    (hPhi : ContMDiff (𝓘(ℝ).prod J) J ∞ Phi) :
    ContMDiff (𝓘(ℝ).prod (I.prod J)) (I.prod J) ∞
      (fun q : ℝ × (M × N) => (q.2.1,Phi (q.1,q.2.2))) := by
  have h1 : ContMDiff (𝓘(ℝ).prod (I.prod J)) I ∞ (fun q : ℝ × (M × N) => q.2.1) :=
    contMDiff_snd.fst
  have h2 : ContMDiff (𝓘(ℝ).prod (I.prod J)) (𝓘(ℝ).prod J) ∞
      (fun q : ℝ × (M × N) => (q.1,q.2.2)) :=
    contMDiff_fst.prodMk contMDiff_snd.snd
  exact h1.prodMk (hPhi.comp h2)
end Generic

lemma onePotential_smooth (l eps s : ℝ) : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (onePotential l eps s) :=
  (sphereHamiltonian_smooth l eps s).contMDiff.comp height_smooth
lemma pairPotential_smooth (l eps s : ℝ) : ContMDiff SI 𝓘(ℝ) ∞ (pairPotential l eps s) :=
  ((onePotential_smooth l eps s).comp contMDiff_fst).add
    ((onePotential_smooth l eps s).comp contMDiff_snd)
lemma fourPotential_smooth (l eps : ℝ) : ContMDiff SP 𝓘(ℝ) ∞ (fourPotential l eps) :=
  ((pairPotential_smooth l eps (-1)).comp contMDiff_fst).add
    ((pairPotential_smooth l eps 1).comp contMDiff_snd)

lemma four_flow_ode (l eps t : ℝ) (p : SphereFour) :
    HasMFDerivAt 𝓘(ℝ) SP (fun r => fourFlow l eps r p) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (fourVelocity l eps (fourFlow l eps t p))) :=
  prod_curve_ode
    (prod_curve_ode (sphereFlow_ode l eps (-1) t p.1.1) (sphereFlow_ode l eps (-1) t p.1.2))
    (prod_curve_ode (sphereFlow_ode l eps 1 t p.2.1) (sphereFlow_ode l eps 1 t p.2.2))

lemma one_hamiltonian (ws : Geometry.SymplecticForm (n := 2) (M := S2)) (l : ℝ)
    (hw : ∀ p u v, ws.form p u v = areaValue l p u v) (eps s : ℝ) (p : S2) :
    ws.form p (velocity l eps s p) = mvfderiv (𝓡 2) (onePotential l eps s) p := by
  apply ContinuousLinearMap.ext
  intro v
  rw [hw]
  change l * standardArea (p : R3) (tangentInclusion p (velocity l eps s p))
      (tangentInclusion p v) =
    mvfderiv (𝓡 2) (fun p : S2 => sphereHamiltonian l eps s ((p : R3) 2)) p v
  rw [tangent_velocity, hamiltonian_differential]
  apply sphere_hamiltonian_equation
  exact (inner_formula (p : R3) (tangentInclusion p v)) ▸ tangent_orthogonal p v

variable {X : Type} [TopologicalSpace X] [ChartedSpace (Model 4) X]
  [IsManifold (𝓡 4) ∞ X]

lemma ambient_hamiltonian_eq (wX : Geometry.SymplecticForm (n := 4) (M := X))
    (wf : SymplecticProduct.SymplecticForm SP (M := SphereFour)) (l eps : ℝ)
    (hfour : ∀ p, wf.form p (fourVelocity l eps p) = mvfderiv SP (fourPotential l eps) p)
    (p : X × SphereFour) :
    (SymplecticProduct.symplecticProd (promote wX) wf).form p (ambientVelocity l eps p) =
      mvfderiv AI (ambientPotential l eps) p := by
  have hzero : ∀ x : X, wX.form x 0 = mvfderiv (𝓡 4) (fun _ : X => (0 : ℝ)) x := by
    intro x
    rw [map_zero, mvfderiv_const]
  have h := prod_hamiltonian (I := 𝓡 4) (J := SP) wX.form wf.form
    (fun _ => 0) (fourVelocity l eps) contMDiff_const (fourPotential_smooth l eps) hzero hfour p
  change SymplecticProduct.prodForm (𝓡 4) SP wX.form wf.form p (0,fourVelocity l eps p.2) =
    mvfderiv AI (ambientPotential l eps) p
  change SymplecticProduct.prodForm (𝓡 4) SP wX.form wf.form p (0,fourVelocity l eps p.2) =
    mvfderiv ((𝓡 4).prod SP) (fun q : X × SphereFour => fourPotential l eps q.2) p
  simpa only [zero_add] using! h

omit [IsManifold (𝓡 4) ∞ X] in
lemma ambientFlow_smooth (l eps : ℝ) :
    ContMDiff (𝓘(ℝ).prod AI) AI ∞
      (fun q : ℝ × (X × SphereFour) => ambientFlow l eps q.1 q.2) :=
  smooth_id_flow (I := 𝓡 4) (M := X) (four_flow_smooth l eps)

omit [TopologicalSpace X] [ChartedSpace (Model 4) X] [IsManifold (𝓡 4) ∞ X] in
lemma ambient_flow_laws (l eps : ℝ) :
    (∀ p : X × SphereFour, ambientFlow l eps 0 p = p) ∧
    (∀ (t u : ℝ) (p : X × SphereFour), ambientFlow l eps (t+u) p =
      ambientFlow l eps t (ambientFlow l eps u p)) := by
  constructor
  · intro p
    simp only [ambientFlow,fourFlow,(sphereFlow_laws l eps (-1)).1,
      (sphereFlow_laws l eps 1).1,Prod.eta]
  · intro t u p
    simp only [ambientFlow,fourFlow,(sphereFlow_laws l eps (-1)).2,
      (sphereFlow_laws l eps 1).2]

omit [IsManifold (𝓡 4) ∞ X] in
lemma ambient_flow_ode (l eps t : ℝ) (p : X × SphereFour) :
    HasMFDerivAt 𝓘(ℝ) AI (fun r => ambientFlow l eps r p) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (ambientVelocity l eps (ambientFlow l eps t p))) := by
  have hc : HasMFDerivAt 𝓘(ℝ) (𝓡 4) (fun _ : ℝ => p.1) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (0 : TangentSpace (𝓡 4) p.1)) := by
    simpa using! (hasMFDerivAt_const (I := 𝓘(ℝ)) (I' := 𝓡 4) p.1 t)
  exact prod_curve_ode hc (four_flow_ode l eps t p.2)

omit [TopologicalSpace X] [ChartedSpace (Model 4) X] [IsManifold (𝓡 4) ∞ X] in
lemma ambient_fixed (l eps : ℝ) (heps : 0 < eps) (hepspi : eps < Real.pi)
    (p : X × SphereFour) : ambientFlow l eps 1 p = p ↔
      p.2.1.1 ∈ poleSet ∧ p.2.1.2 ∈ poleSet ∧ p.2.2.1 ∈ poleSet ∧ p.2.2.2 ∈ poleSet := by
  simp only [ambientFlow,fourFlow,Prod.ext_iff, sphereFlow_fixed l eps (-1) heps hepspi,
    sphereFlow_fixed l eps 1 heps hepspi, true_and,and_assoc]

theorem ambientHamiltonianObligation : AmbientHamiltonianObligation (X := X) := by
  intro wX l eps hl heps hepspi
  obtain ⟨ws,hws⟩ := scaled_standardSphere_symplectic l (by linarith)
  let wp := SymplecticProduct.symplecticProd (promote ws) (promote ws)
  let wf := SymplecticProduct.symplecticProd wp wp
  let wa := SymplecticProduct.symplecticProd (promote wX) wf
  have hpair : ∀ s p, wp.form p (pairVelocity l eps s p) =
      mvfderiv SI (pairPotential l eps s) p := by
    intro s p
    exact prod_hamiltonian ws.form ws.form (velocity l eps s) (velocity l eps s)
      (onePotential_smooth l eps s) (onePotential_smooth l eps s)
      (one_hamiltonian ws l hws eps s) (one_hamiltonian ws l hws eps s) p
  have hfour : ∀ p, wf.form p (fourVelocity l eps p) =
      mvfderiv SP (fourPotential l eps) p := by
    intro p
    exact prod_hamiltonian wp.form wp.form (pairVelocity l eps (-1)) (pairVelocity l eps 1)
      (pairPotential_smooth l eps (-1)) (pairPotential_smooth l eps 1)
      (hpair (-1)) (hpair 1) p
  refine ⟨wa,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro p u v
    change wX.form p.1 u.1 v.1 +
      ((ws.form p.2.1.1 u.2.1.1 v.2.1.1 + ws.form p.2.1.2 u.2.1.2 v.2.1.2) +
       (ws.form p.2.2.1 u.2.2.1 v.2.2.1 + ws.form p.2.2.2 u.2.2.2 v.2.2.2)) = _
    simp only [areaValue]
    erw [hws,hws,hws,hws]
    rfl
  · exact (fourPotential_smooth l eps).comp contMDiff_snd
  · exact ambient_hamiltonian_eq wX wf l eps hfour
  · exact ambientFlow_smooth l eps
  · exact (ambient_flow_laws (X := X) l eps).1
  · exact (ambient_flow_laws (X := X) l eps).2
  · exact ambient_flow_ode l eps
  · exact ambient_fixed l eps heps hepspi
  · intro p hp heq
    exact exterior_not_fixed l eps hl heps hepspi p.2 hp (congrArg Prod.snd heq)
  · intro nu p hp
    exact four_endpoint l eps hl nu p.2 hp

end
end MorseArnold.AmbientHamiltonian

end

end OAI
