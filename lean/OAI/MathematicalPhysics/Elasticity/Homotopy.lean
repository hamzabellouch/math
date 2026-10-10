import OAI.MathematicalPhysics.Elasticity.Parameters
import OAI.MathematicalPhysics.Elasticity.ODE

namespace OAI

section
noncomputable section
open Set
namespace ElasticityODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
def frameDbar (b : ℂ → C(Time,R)) (p : ℂ) : C(Time,R) :=
  fderiv ℝ (fun p => fundamental (b p)) p 1+
    Complex.I • fderiv ℝ (fun p => fundamental (b p)) p Complex.I
def coefficientDbar (b : ℂ → C(Time,R)) (p : ℂ) : C(Time,R) :=
  fderiv ℝ b p 1+Complex.I • fderiv ℝ b p Complex.I
lemma frameDbar_hasDerivWithinAt (b : ℂ → C(Time,R))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (p : ℂ) (t : Time) :
    HasDerivWithinAt (extend (frameDbar b p))
      (b p t*frameDbar b p t+coefficientDbar b p t*fundamental (b p) t) Time t := by
  have h1 := fundamental_variation_hasDerivWithinAt b hb p 1 t
  have hi := (fundamental_variation_hasDerivWithinAt b hb p Complex.I t).const_smul Complex.I
  have h := h1.add hi
  have he :
      b p t*fderiv ℝ (fun p => fundamental (b p)) p 1 t+fderiv ℝ b p 1 t*fundamental (b p) t+
        Complex.I • (b p t*fderiv ℝ (fun p => fundamental (b p)) p Complex.I t+
          fderiv ℝ b p Complex.I t*fundamental (b p) t)=
      b p t*frameDbar b p t+coefficientDbar b p t*fundamental (b p) t := by
    simp only [frameDbar,coefficientDbar,ContinuousMap.add_apply,ContinuousMap.smul_apply,
      smul_add,mul_add,add_mul,mul_smul_comm,smul_mul_assoc]
    abel
  rw [he] at h
  exact h.congr_of_mem (fun x hx => by
    change extend (frameDbar b p) (⟨x,hx⟩ : Time)=_
    rw [extend_apply]
    change _=extend (fderiv ℝ (fun p => fundamental (b p)) p 1) (⟨x,hx⟩ : Time)+
      Complex.I • extend (fderiv ℝ (fun p => fundamental (b p)) p Complex.I) (⟨x,hx⟩ : Time)
    rw [extend_apply,extend_apply]
    rfl) t.property
lemma frameDbar_initial (b : ℂ → C(Time,R)) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (p : ℂ) :
    frameDbar b p ⟨0,by simp [Time]⟩=0 := by
  simp only [frameDbar,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    fundamental_variation_initial b hb,smul_zero,add_zero]

/-- The homotopy defect vanishes. This derives the planar frame equation from
an actual coefficient homotopy, instead of assuming an Oka trivialization. -/
theorem fundamental_transport (b : ℂ → C(Time,R))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (p : ℂ) (A : R)
    (he : ∀ t : Time, coefficientDbar b p t=A+(t:ℝ) • (A*b p t-b p t*A)) (t : Time) :
    frameDbar b p t=(t:ℝ) • (A*fundamental (b p) t) := by
  let u : C(Time,R) := frameDbar b p-
    ⟨fun s => (s:ℝ) • (A*fundamental (b p) s),
      continuous_subtype_val.smul (continuous_const.mul (fundamental (b p)).continuous)⟩
  let v : C(Time,R) := 0
  have hu (s : Time) : HasDerivWithinAt (extend u) (b p s*u s) Time s := by
    have hU := (fundamental_deriv (b p) s).const_mul A
    have hs : HasDerivWithinAt (fun x : ℝ => x) 1 Time s := (hasDerivAt_id (s:ℝ)).hasDerivWithinAt
    have hT := hs.smul hU
    have hD := (frameDbar_hasDerivWithinAt b hb p s).sub hT
    have ha : b p s*frameDbar b p s+coefficientDbar b p s*fundamental (b p) s-
        ((s:ℝ) • (A*(b p s*fundamental (b p) s))+(1:ℝ) • (A*extend (fundamental (b p)) s))=
        b p s*u s := by
      rw [he,extend_apply]
      change _=b p s*(frameDbar b p s-(s:ℝ) • (A*fundamental (b p) s))
      simp only [one_smul,add_mul,smul_mul_assoc,sub_mul,smul_sub,mul_sub,mul_smul_comm,mul_assoc]
      abel
    rw [ha] at hD
    exact hD.congr_of_mem (fun x hx => by
      change extend u (⟨x,hx⟩ : Time)=_
      rw [extend_apply]
      change frameDbar b p ⟨x,hx⟩-x • (A*fundamental (b p) ⟨x,hx⟩)=_
      rw [← extend_apply (frameDbar b p) ⟨x,hx⟩,
        ← extend_apply (fundamental (b p)) ⟨x,hx⟩]
      rfl) s.property
  have hv (s : Time) : HasDerivWithinAt (extend v) (b p s*v s) Time s := by
    have hh : HasDerivWithinAt (fun _ : ℝ => (0:R)) 0 Time s := hasDerivWithinAt_const _ _ _
    have hz : b p s*v s=0 := mul_zero _
    rw [hz]
    exact hh.congr_of_mem (fun x hx => by
      change extend v (⟨x,hx⟩ : Time)=0
      rw [extend_apply]; rfl) s.property
  have hzero : u ⟨0,by simp [Time]⟩=v ⟨0,by simp [Time]⟩ := by
    change frameDbar b p ⟨0,by simp [Time]⟩-(0:ℝ) • _=0
    rw [frameDbar_initial b hb,zero_smul,sub_zero]
  have h := congrArg (fun f : C(Time,R) => f t)
    (linear_ode_unique (leftCoeff (b p)) u v hu hv hzero)
  exact sub_eq_zero.mp h
end ElasticityODE

end
end
section
noncomputable section
open Set Complex Module
open scoped SchwartzMap LineDeriv BigOperators
namespace ElasticityPlanar
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
  [FiniteDimensional ℂ R]
variable {n : Type*} [Fintype n] [DecidableEq n]
def coords (q : Basis n ℂ R) : R ≃L[ℂ] (n → ℂ) := q.equivFun.toContinuousLinearEquiv
def coord (q : Basis n ℂ R) (i : n) : R →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp (coords q).toContinuousLinearMap
omit [CompleteSpace R] [DecidableEq n] in
lemma coords_coord (q : Basis n ℂ R) (x : R) (i : n) : coords q x i=coord q i x := rfl
omit [CompleteSpace R] [DecidableEq n] in
lemma coord_linear_apply (q : Basis n ℂ R) (L : R →ₗ[ℂ] R) (x : R) (i : n) :
    coord q i (L x)=∑ j, coord q i (L (q j))*coord q j x := by
  have h : L x=∑ j, (q.equivFun x j) • L (q j) := by
    calc
      L x=L (∑ j, q.equivFun x j • q j) := congrArg L (q.sum_equivFun x).symm
      _=∑ j, q.equivFun x j • L (q j) := by simp only [map_sum,map_smul]
  rw [h,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul,smul_eq_mul,mul_comm]
  rfl

def classicalDbar (f : ℂ → R) (z : ℂ) : R := fderiv ℝ f z 1+I • fderiv ℝ f z I
omit [CompleteSpace R] [DecidableEq n] in
lemma coord_dbar (q : Basis n ℂ R) (f : ℂ → R) (hf : Differentiable ℝ f) (z : ℂ) (i : n) :
    coord q i (classicalDbar f z)=
      fderiv ℝ (fun z => coord q i (f z)) z 1+I*fderiv ℝ (fun z => coord q i (f z)) z I := by
  have h := ((coord q i).restrictScalars ℝ).hasFDerivAt.comp z (hf z).hasFDerivAt
  change HasFDerivAt (fun z => coord q i (f z)) _ z at h
  rw [h.fderiv]
  simp only [classicalDbar,map_add,map_smul,ContinuousLinearMap.comp_apply,
    smul_eq_mul]
  rfl

omit [CompleteSpace R] [DecidableEq n] in
/-- The commutator homotopy equation in a genuine finite-dimensional complex
Banach algebra, with actual joint smooth representatives. -/
theorem exists_algebra_homotopy {S Ω Ω' : Set ℂ} (hS : IsCompact S)
    (hΩS : Ω ⊆ S) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω)
    (q : Basis n ℂ R) (A : ℂ → R) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hAc : HasCompactSupport A) {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ B : ℝ × ℂ → R, ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ s z, z∈Ω' → classicalDbar (fun z => B (s,z)) z=
        A z+s • (A z*B (s,z)-B (s,z)*A z) := by
  let a : n → n → ℂ → ℂ := fun i j z => coord q i (q j*A z-A z*q j)
  have ha (i j : n) : ContDiff ℝ (⊤ : ℕ∞) (a i j) :=
    ((coord q i).restrictScalars ℝ).contDiff.comp
      ((contDiff_const.mul hA).sub (hA.mul contDiff_const))
  have hac (i j : n) : HasCompactSupport (a i j) :=
    ((hAc.mul_left.sub hAc.mul_right).comp_left (g := coord q i) (map_zero _))
  have hf (i : n) : ContDiff ℝ (⊤ : ℕ∞) (fun z => coord q i (A z)) :=
    ((coord q i).restrictScalars ℝ).contDiff.comp hA
  have hfc (i : n) : HasCompactSupport (fun z => coord q i (A z)) :=
    hAc.comp_left (g := coord q i) (map_zero _)
  let f : n → 𝓢(ℂ,ℂ) := fun i => (hfc i).toSchwartzMap (hf i)
  obtain ⟨v,hv,he⟩ := exists_classical_homotopy hS hΩS hΩ' hsub a ha hac f hg hc hs h1
  let B : ℝ × ℂ → R := fun p => (coords q).symm (fun i => v p.1 i p.2)
  have hL : ContDiff ℝ (⊤ : ℕ∞) (coords q).symm := by
    let L : (n → ℂ) →L[ℝ] R := (coords q).symm.toContinuousLinearMap.restrictScalars ℝ
    exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := n → ℂ) (F := R) L
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := hL.comp (contDiff_pi.mpr hv)
  have hev (s : ℝ) (i : n) : (fun z => coord q i (B (s,z)))=fun z => v s i z := by
    funext z
    change (coords q) ((coords q).symm (fun i => v s i z)) i=v s i z
    rw [ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨B,hB,fun s z hz => ?_⟩
  apply (coords q).injective
  ext i
  change coord q i (classicalDbar (fun z => B (s,z)) z)=
    coord q i (A z+s • (A z*B (s,z)-B (s,z)*A z))
  have hBs : Differentiable ℝ (fun z => B (s,z)) :=
    (hB.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hD := coord_dbar q (fun z => B (s,z)) hBs z i
  rw [hev] at hD
  have he' := he s i hz
  simp only [schwartzDbar,add_apply,smul_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv,smul_eq_mul] at he'
  rw [← hD] at he'
  have hcomm : coord q i (B (s,z)*A z-A z*B (s,z))=∑ j, a i j z*v s j z := by
    let L : R →ₗ[ℂ] R := ((ContinuousLinearMap.mul ℂ R).flip (A z)-
      ContinuousLinearMap.mul ℂ R (A z)).toLinearMap
    have hh := coord_linear_apply q L (B (s,z)) i
    change coord q i (B (s,z)*A z-A z*B (s,z))=
      ∑ j, a i j z*coord q j (B (s,z)) at hh
    simpa only [congrFun (hev s _) z] using hh
  have hs' : coord q i (A z+s • (A z*B (s,z)-B (s,z)*A z))=
      coord q i (A z)-(s:ℂ)*(∑ j, a i j z*v s j z) := by
    rw [map_add]
    have hneg : A z*B (s,z)-B (s,z)*A z=-(B (s,z)*A z-A z*B (s,z)) := by abel
    rw [hneg]
    have hl := ((coord q i).restrictScalars ℝ).map_smul s (-(B (s,z)*A z-A z*B (s,z)))
    change coord q i (s • (-(B (s,z)*A z-A z*B (s,z))))=s • coord q i (-(B (s,z)*A z-A z*B (s,z))) at hl
    rw [hl,map_neg,hcomm]
    simp [Complex.real_smul,sub_eq_add_neg]
  rw [hs']
  change _+∑ j, (s:ℂ)*a i j z*v s j z=coord q i (A z) at he'
  rw [Finset.mul_sum]
  simp_rw [mul_assoc] at he' ⊢
  linear_combination he'
end ElasticityPlanar

end
end
section
noncomputable section
open Set Complex Module
open scoped SchwartzMap LineDeriv BigOperators
namespace ElasticityPlanar
open ElasticityRegularity
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
  [FiniteDimensional ℂ R]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
omit [CompleteSpace R] [DecidableEq n] in
/-- The commutator homotopy equation in a genuine finite-dimensional complex
Banach algebra, with actual joint smooth representatives. -/
theorem exists_algebra_variable_homotopy {S Ω Ω' K : Set ℂ} (hS : IsCompact S)
    (hΩS : Ω ⊆ S) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω)
    (hK : IsCompact K) (q : Basis n ℂ R) (A : P × ℂ → R) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hAc : ∀ p z, z∉K → A (p,z)=0) {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ B : (ℝ × P) × ℂ → R, ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ s p z, z∈Ω' → classicalDbar (fun z => B ((s,p),z)) z=
        A (p,z)+s • (A (p,z)*B ((s,p),z)-B ((s,p),z)*A (p,z)) := by
  let A' : (ℝ × P) × ℂ → R := fun q => A (q.1.2,q.2)
  have hA' : ContDiff ℝ (⊤ : ℕ∞) A' :=
    hA.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  let a : n → n → (ℝ × P) × ℂ → ℂ := fun i j w =>
    (w.1.1 : ℂ)*coord q i (q j*A' w-A' w*q j)
  have ha (i j : n) : ContDiff ℝ (⊤ : ℕ∞) (a i j) :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_fst.comp contDiff_fst)).mul
      (((coord q i).restrictScalars ℝ).contDiff.comp
        ((contDiff_const.mul hA').sub (hA'.mul contDiff_const)))
  have hac (i j : n) (w : ℝ × P) (z : ℂ) (hz : z∉K) : a i j (w,z)=0 := by
    simp only [a,A',hAc w.2 z hz,mul_zero,zero_mul,sub_self,map_zero]
  let f : n → (ℝ × P) × ℂ → ℂ := fun i w => coord q i (A' w)
  have hf (i : n) : ContDiff ℝ (⊤ : ℕ∞) (f i) :=
    ((coord q i).restrictScalars ℝ).contDiff.comp hA'
  have hfc (i : n) (w : ℝ × P) (z : ℂ) (hz : z∉K) : f i (w,z)=0 := by
    simp only [f,A',hAc w.2 z hz,map_zero]
  obtain ⟨v,hv,he⟩ := exists_classical_variable hS hΩS hΩ' hsub hK a ha hac f hf hfc hg hc hs h1
  let B : (ℝ × P) × ℂ → R := fun p => (coords q).symm (fun i => v p.1 i p.2)
  have hL : ContDiff ℝ (⊤ : ℕ∞) (coords q).symm := by
    let L : (n → ℂ) →L[ℝ] R := (coords q).symm.toContinuousLinearMap.restrictScalars ℝ
    exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := n → ℂ) (F := R) L
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := hL.comp (contDiff_pi.mpr hv)
  have hev (w : ℝ × P) (i : n) : (fun z => coord q i (B (w,z)))=fun z => v w i z := by
    funext z
    change (coords q) ((coords q).symm (fun i => v w i z)) i=v w i z
    rw [ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨B,hB,fun s p z hz => ?_⟩
  apply (coords q).injective
  ext i
  change coord q i (classicalDbar (fun z => B ((s,p),z)) z)=
    coord q i (A (p,z)+s • (A (p,z)*B ((s,p),z)-B ((s,p),z)*A (p,z)))
  have hBs : Differentiable ℝ (fun z => B ((s,p),z)) :=
    (hB.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hD := coord_dbar q (fun z => B ((s,p),z)) hBs z i
  rw [hev] at hD
  have he' := he (s,p) i hz
  change schwartzDbar (v (s,p) i) z+∑ j, (s:ℂ)*coord q i (q j*A (p,z)-A (p,z)*q j)*v (s,p) j z=coord q i (A (p,z)) at he'
  simp only [schwartzDbar,add_apply,smul_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv,smul_eq_mul] at he'
  rw [← hD] at he'
  have hcomm : coord q i (B ((s,p),z)*A (p,z)-A (p,z)*B ((s,p),z))=∑ j, coord q i (q j*A (p,z)-A (p,z)*q j)*v (s,p) j z := by
    let L : R →ₗ[ℂ] R := ((ContinuousLinearMap.mul ℂ R).flip (A (p,z))-
      ContinuousLinearMap.mul ℂ R (A (p,z))).toLinearMap
    have hh := coord_linear_apply q L (B ((s,p),z)) i
    change coord q i (B ((s,p),z)*A (p,z)-A (p,z)*B ((s,p),z))=
      ∑ j, coord q i (q j*A (p,z)-A (p,z)*q j)*coord q j (B ((s,p),z)) at hh
    simpa only [congrFun (hev (s,p) _) z] using hh
  have hs' : coord q i (A (p,z)+s • (A (p,z)*B ((s,p),z)-B ((s,p),z)*A (p,z)))=
      coord q i (A (p,z))-(s:ℂ)*(∑ j, coord q i (q j*A (p,z)-A (p,z)*q j)*v (s,p) j z) := by
    rw [map_add]
    have hneg : A (p,z)*B ((s,p),z)-B ((s,p),z)*A (p,z)=-(B ((s,p),z)*A (p,z)-A (p,z)*B ((s,p),z)) := by abel
    rw [hneg]
    have hl := ((coord q i).restrictScalars ℝ).map_smul s (-(B ((s,p),z)*A (p,z)-A (p,z)*B ((s,p),z)))
    change coord q i (s • (-(B ((s,p),z)*A (p,z)-A (p,z)*B ((s,p),z))))=s • coord q i (-(B ((s,p),z)*A (p,z)-A (p,z)*B ((s,p),z))) at hl
    rw [hl,map_neg,hcomm]
    simp [Complex.real_smul,sub_eq_add_neg]
  rw [hs']
  change _+∑ j, (s:ℂ)*coord q i (q j*A (p,z)-A (p,z)*q j)*v (s,p) j z=coord q i (A (p,z)) at he'
  rw [Finset.mul_sum]
  simp_rw [mul_assoc] at he' ⊢
  linear_combination he'
end ElasticityPlanar

end
end
section
noncomputable section
open Set Complex Module
namespace ElasticityPlanar
open ElasticityODE ElasticityCompact
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
omit [CompleteSpace R] in
lemma dbar_evaluation (b : ℂ → C(Time,R)) (hb : Differentiable ℝ b) (z : ℂ) (t : Time) :
    classicalDbar (fun z => b z t) z=coefficientDbar b z t := by
  have h := (ContinuousMap.evalCLM ℝ t : C(Time,R) →L[ℝ] R).hasFDerivAt.comp z (hb z).hasFDerivAt
  change HasFDerivAt (fun z => b z t) _ z at h
  rw [classicalDbar,h.fderiv]
  rfl
lemma dbar_fundamental (b : ℂ → C(Time,R)) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (z : ℂ) (t : Time) :
    classicalDbar (fun z => fundamental (b z) t) z=frameDbar b z t :=
  dbar_evaluation (fun z => fundamental (b z))
    ((fundamental_contDiff b hb).differentiable (by simp)) z t
variable [FiniteDimensional ℂ R] {n : Type*} [Fintype n] [DecidableEq n]
omit [DecidableEq n] in
/-- A global smooth invertible planar frame on the prescribed inner domain.
It is built from the proved planar solver and coefficient homotopy flow. -/
theorem exists_planar_frame {S Ω Ω' : Set ℂ} (hS : IsCompact S)
    (hΩS : Ω ⊆ S) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω)
    (q : Basis n ℂ R) (A : ℂ → R) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hAc : HasCompactSupport A) {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ V : ℂ → R, ContDiff ℝ (⊤ : ℕ∞) V ∧ (∀ z, IsUnit (V z)) ∧
      ∀ z∈Ω', classicalDbar V z=A z*V z := by
  obtain ⟨B,hB,he⟩ := exists_algebra_homotopy hS hΩS hΩ' hsub q A hA hAc hg hc hs h1
  let f : ℂ × ℝ → R := fun p => B (p.2,p.1)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hB.comp (contDiff_snd.prodMk contDiff_fst)
  let b : ℂ → C(Time,R) := curryCompact f hf.continuous (fun t : Time => (t:ℝ)) continuous_subtype_val
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := curryCompact_contDiff f hf _ continuous_subtype_val
  let t : Time := ⟨1,by simp [Time]⟩
  let V : ℂ → R := fun z => fundamental (b z) t
  have hV : ContDiff ℝ (⊤ : ℕ∞) V := by
    have hL : ContDiff ℝ (⊤ : ℕ∞) (ContinuousMap.evalCLM ℝ t : C(Time,R) →L[ℝ] R) :=
      ContinuousLinearMap.contDiff (E := C(Time,R)) (F := R) _
    exact hL.comp (fundamental_contDiff b hb)
  refine ⟨V,hV,fun z => fundamental_isUnit (b z) t,fun z hz => ?_⟩
  have hcoeff (s : Time) : coefficientDbar b z s=A z+(s:ℝ) • (A z*b z s-b z s*A z) := by
    rw [← dbar_evaluation b (hb.differentiable (by simp)) z s]
    exact he (s:ℝ) z hz
  have ht := fundamental_transport b hb z (A z) hcoeff t
  rw [← dbar_fundamental b hb] at ht
  simpa only [t,one_smul] using ht
end ElasticityPlanar

end
end
section
noncomputable section
open Set Complex Module
namespace ElasticityPlanar
open ElasticityODE ElasticityCompact
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
  [FiniteDimensional ℂ R] {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
/-- A genuine jointly smooth global planar frame with arbitrary transverse
parameters. Invertibility holds everywhere, not only at a chosen base point. -/
theorem exists_variable_planar_frame {S Ω Ω' K : Set ℂ} (hS : IsCompact S)
    (hΩS : Ω ⊆ S) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω)
    (hK : IsCompact K) (q : Basis n ℂ R) (A : P × ℂ → R) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hAc : ∀ p z, z∉K → A (p,z)=0) {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ V : P × ℂ → R, ContDiff ℝ (⊤ : ℕ∞) V ∧ (∀ w, IsUnit (V w)) ∧
      ∀ p z, z∈Ω' → classicalDbar (fun z => V (p,z)) z=A (p,z)*V (p,z) := by
  obtain ⟨B,hB,he⟩ := exists_algebra_variable_homotopy hS hΩS hΩ' hsub hK q A hA hAc hg hc hs h1
  let f : (P × ℂ) × ℝ → R := fun w => B ((w.2,w.1.1),w.1.2)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hB.comp
    ((contDiff_snd.prodMk (contDiff_fst.comp contDiff_fst)).prodMk (contDiff_snd.comp contDiff_fst))
  let b : P × ℂ → C(Time,R) := curryCompact f hf.continuous (fun t : Time => (t:ℝ)) continuous_subtype_val
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := curryCompact_contDiff f hf _ continuous_subtype_val
  let t : Time := ⟨1,by simp [Time]⟩
  let V : P × ℂ → R := fun w => fundamental (b w) t
  have hV : ContDiff ℝ (⊤ : ℕ∞) V := by
    have hL : ContDiff ℝ (⊤ : ℕ∞) (ContinuousMap.evalCLM ℝ t : C(Time,R) →L[ℝ] R) :=
      ContinuousLinearMap.contDiff (E := C(Time,R)) (F := R) _
    exact hL.comp (fundamental_contDiff b hb)
  refine ⟨V,hV,fun w => fundamental_isUnit (b w) t,fun p z hz => ?_⟩
  let bp : ℂ → C(Time,R) := fun z => b (p,z)
  have hbp : ContDiff ℝ (⊤ : ℕ∞) bp := hb.comp (contDiff_const.prodMk contDiff_id)
  have hcoeff (s : Time) : coefficientDbar bp z s=A (p,z)+(s:ℝ) • (A (p,z)*bp z s-bp z s*A (p,z)) := by
    rw [← dbar_evaluation bp (hbp.differentiable (by simp)) z s]
    exact he (s:ℝ) p z hz
  have ht := fundamental_transport bp hbp z (A (p,z)) hcoeff t
  rw [← dbar_fundamental bp hbp] at ht
  simpa only [t,one_smul] using ht
end ElasticityPlanar

end
end

end OAI
