import Mathlib
import OAI.Analysis.SymmetricDomains.HolQuadraticSmul
import OAI.Analysis.SymmetricDomains.QuadraticDomainConnectedComponent
import OAI.Analysis.SymmetricDomains.ComplexifyRealContinuousEquiv
import OAI.Analysis.SymmetricDomains.AffineProductCoordinates
import OAI.Analysis.SymmetricDomains.FiniteUnion

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical

def residualQuadraticCoefficients {r k l : ℕ}
    (L : (Fin k → ℝ) ≃L[ℝ] (Fin l → ℝ))
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Affine r) (Fin l → ℝ)) :
    Fin k → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ := fun i =>
  let P := ((ContinuousLinearMap.proj i).comp (-L.symm.toContinuousLinearMap)).compContinuousMultilinearMap Q
  (ContinuousLinearMap.coeLM ℝ).comp
    ((continuousMultilinearCurryFin1 ℝ (Affine r) ℝ).toLinearEquiv.toLinearMap.comp
      P.curryLeft.toLinearMap)

lemma residualQuadraticCoefficients_diag {r k l : ℕ}
    (L : (Fin k → ℝ) ≃L[ℝ] (Fin l → ℝ))
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Affine r) (Fin l → ℝ))
    (z : Affine r) :
    (fun i => residualQuadraticCoefficients L Q i z z) = -L.symm (Q (fun _ => z)) := by
  ext i
  let P := ((ContinuousLinearMap.proj i).comp (-L.symm.toContinuousLinearMap)).compContinuousMultilinearMap Q
  change (continuousMultilinearCurryFin1 ℝ (Affine r) ℝ (P.curryLeft z)) z = _
  rw [continuousMultilinearCurryFin1_apply,ContinuousMultilinearMap.curryLeft_apply]
  change (-L.symm (Q (Fin.cons z (Fin.snoc 0 z)))) i = _
  have he : Fin.cons z (Fin.snoc 0 z)=(fun _ : Fin 2 => z) := by
    funext j
    fin_cases j <;> rfl
  rw [he]

lemma residualQuadraticCoefficients_continuous {r k l : ℕ}
    (L : (Fin k → ℝ) ≃L[ℝ] (Fin l → ℝ))
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Affine r) (Fin l → ℝ)) :
    Continuous (fun z => fun i => residualQuadraticCoefficients L Q i z z) := by
  have he : (fun z i => residualQuadraticCoefficients L Q i z z) =
      (fun z => -L.symm (Q (fun _ => z))) :=
    funext (residualQuadraticCoefficients_diag L Q)
  rw [he]
  exact (L.symm.continuous.comp (Q.cont.comp (continuous_pi fun _ => continuous_id))).neg

lemma residualQuadraticCoefficients_zero {r k l : ℕ}
    (L : (Fin k → ℝ) ≃L[ℝ] (Fin l → ℝ))
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Affine r) (Fin l → ℝ)) :
    (fun i => residualQuadraticCoefficients L Q i 0 0) = 0 := by
  ext i
  simp

def Biholomorph.ofEntireHomeomorph {n m : ℕ} (e : Affine n ≃ₜ Affine m)
    (he : ∀ x, AnalyticAt ℂ e x) (hei : ∀ x, AnalyticAt ℂ e.symm x)
    (S : Set (Affine n)) : Biholomorph S (e '' S) :=
  Biholomorph.ofOpenPartialHomeomorph e.toOpenPartialHomeomorph
    (fun x _ => he x) (fun x _ => hei x) S (subset_univ _)

theorem quadraticShear_biholomorph {r k : ℕ}
    (B : Fin k → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ)) :
    Nonempty (Biholomorph
      ((affineProductCoordinates r k) '' quadraticDomain (fun z i => B i z z) C)
      ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C)) := by
  let e := affineProductCoordinates r k
  let σ := Hermitian.quadraticShear B
  let φ := e.symm.toHomeomorph.trans (σ.trans e.toHomeomorph)
  have ha : ∀ x, AnalyticAt ℂ φ x := by
    intro x
    exact (e.toContinuousLinearMap.analyticAt _).comp
      ((Hermitian.quadraticShear_analytic B _).comp (e.symm.toContinuousLinearMap.analyticAt _))
  have hai : ∀ x, AnalyticAt ℂ φ.symm x := by
    intro x
    exact (e.toContinuousLinearMap.analyticAt _).comp
      ((Hermitian.quadraticShear_inverse_analytic B _).comp (e.symm.toContinuousLinearMap.analyticAt _))
  have himage : φ '' (e '' quadraticDomain (fun z i => B i z z) C) =
      e '' quadraticDomain (Hermitian.hermQuadratic B) C := by
    ext y
    constructor
    · rintro ⟨x,⟨z,hz,rfl⟩,rfl⟩
      refine ⟨σ z,?_,?_⟩
      · change (fun i => ((σ z).2 i).im-Hermitian.hermQuadratic B (σ z).1 i) ∈ C
        rw [Hermitian.quadraticShear_residual]
        exact hz
      · change e (σ z)=e (σ (e.symm (e z)))
        rw [e.symm_apply_apply]
    · rintro ⟨z,hz,rfl⟩
      refine ⟨e (σ.symm z),⟨σ.symm z,?_,rfl⟩,?_⟩
      · have hres := Hermitian.quadraticShear_residual B (σ.symm z)
        change (fun i => ((σ.symm z).2 i).im-B i (σ.symm z).1 (σ.symm z).1) ∈ C
        rw [← hres]
        change (fun i => ((σ (σ.symm z)).2 i).im-
          Hermitian.hermQuadratic B (σ (σ.symm z)).1 i) ∈ C
        rw [σ.apply_symm_apply]
        exact hz
      · change e (σ (e.symm (e (σ.symm z))))=e z
        rw [e.symm_apply_apply,σ.apply_symm_apply]
  exact ⟨himage ▸ Biholomorph.ofEntireHomeomorph φ ha hai _⟩

theorem raw_quadratic_model_normalization {r k l : ℕ}
    (L : (Fin k → ℝ) ≃L[ℝ] (Fin l → ℝ))
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Affine r) (Fin l → ℝ))
    (f : (Fin l → ℝ) → ℝ) (hf : Continuous f) (hf0 : f 0=0)
    (hcone : ∀ t : ℝ, 0 < t → ∀ y, f y=0 ↔ f (t • y)=0)
    (a : Fin k → ℝ) (ha : f (L a) ≠ 0) :
    ∃ (B : Fin k → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ)),
      IsOpen C ∧ IsConnected C ∧ (0 : Fin k → ℝ) ∉ C ∧
      (∀ t : ℝ, 0 < t → ∀ y, t • y ∈ C ↔ y ∈ C) ∧
      Nonempty (Biholomorph (connectedComponentIn
        ((affineProductCoordinates r k) ''
          {z : Affine r × Affine k | f (L (Flatten.imaginaryPart k z.2)+Q (fun _ => z.1)) ≠ 0})
        ((affineProductCoordinates r k) (0,fun i => Complex.I*(a i : ℂ))))
        ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C)) := by
  let B := residualQuadraticCoefficients L Q
  let H : Affine r → Fin k → ℝ := fun z i => B i z z
  let C₀ : Set (Fin k → ℝ) := {y | f (L y) ≠ 0}
  let C := connectedComponentIn C₀ a
  let e := affineProductCoordinates r k
  let p : Affine r × Affine k := (0,fun i => Complex.I*(a i : ℂ))
  have hH : Continuous H := residualQuadraticCoefficients_continuous L Q
  have hH0 : H 0=0 := residualQuadraticCoefficients_zero L Q
  have hC₀ : IsOpen C₀ := isOpen_ne_fun (hf.comp L.continuous) continuous_const
  have hcone₀ : ∀ t : ℝ, 0 < t → ∀ y ∈ C₀, t • y ∈ C₀ := by
    intro t ht y hy
    change f (L (t • y)) ≠ 0
    rw [map_smul]
    exact (hcone t ht (L y)).not.mp hy
  obtain ⟨hCo,hCc,hCcone⟩ := open_cone_component hC₀ hcone₀ ha
  have hCzero : (0 : Fin k → ℝ) ∉ C := by
    intro h
    have h' := connectedComponentIn_subset C₀ a h
    exact h' (by simpa only [map_zero] using hf0)
  have hp : p ∈ quadraticDomain H C₀ := quadraticDomain_axis H hH0 ha
  have hpa : (fun i => (p.2 i).im-H p.1 i)=a := by
    simp only [p,hH0,Pi.zero_apply,sub_zero,Complex.I_mul_im,Complex.ofReal_re]
  have hraw : {z : Affine r × Affine k |
      f (L (Flatten.imaginaryPart k z.2)+Q (fun _ => z.1)) ≠ 0} = quadraticDomain H C₀ := by
    ext z
    have he : L (Flatten.imaginaryPart k z.2-H z.1)=
        L (Flatten.imaginaryPart k z.2)+Q (fun _ => z.1) := by
      rw [show H z.1= -L.symm (Q (fun _ => z.1)) from residualQuadraticCoefficients_diag L Q z.1,
        sub_neg_eq_add,map_add,L.apply_symm_apply]
    change f (L (Flatten.imaginaryPart k z.2)+Q (fun _ => z.1)) ≠ 0 ↔
      f (L (Flatten.imaginaryPart k z.2-H z.1)) ≠ 0
    rw [he]
  have hcc : connectedComponentIn (e '' quadraticDomain H C₀) (e p) =
      e '' quadraticDomain H C := by
    change connectedComponentIn (e.toHomeomorph '' quadraticDomain H C₀) (e.toHomeomorph p) = _
    rw [← e.toHomeomorph.image_connectedComponentIn hp,
      quadraticDomain_connectedComponent H hH C₀ p,hpa]
    rfl
  refine ⟨B,C,hCo,hCc,hCzero,hCcone,?_⟩
  rw [hraw,hcc]
  exact quadraticShear_biholomorph B C

end Release061

end

end OAI
