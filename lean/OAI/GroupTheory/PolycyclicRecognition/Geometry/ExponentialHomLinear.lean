import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateHomLinear
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGroupLaws
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DistortedHomomorphisms

namespace OAI

/-! # Linearity of continuous homomorphisms on nilpotent logarithms -/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {L G W : Type*} [LieRing L] [LieAlgebra ℝ L] [Group G] [PseudoMetricSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Finite polynomial exponential coordinates and continuity suffice to
linearize a homomorphism into an additive real vector space. -/
theorem exists_linearMap_of_exponential_hom {n c : ℕ} (b : Basis (Fin n) ℝ L)
    (Exp : L → G) (hinj : Function.Injective Exp) (hzero : Exp 0 = 1)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    (hcont : Continuous (fun x : Fin n → ℝ => Exp (b.equivFun.symm x)))
    (coeff : DynkinCoefficients c 2)
    (hmul : ∀ x y, Exp (finiteDynkinPolynomial coeff ![x, y]) = Exp x * Exp y)
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd) :
    ∃ A : L →ₗ[ℝ] W, ∀ x, A x = (l (Exp x)).toAdd := by
  let m := dynkinProduct coeff (basisBracket b)
  let e : (Fin n → ℝ) → G := fun x => Exp (b.equivFun.symm x)
  have he : Function.Injective e := hinj.comp b.equivFun.symm.injective
  have hemul (x y : Fin n → ℝ) : e (m x y) = e x * e y := by
    have h := basis_dynkinProduct b coeff (b.equivFun.symm x) (b.equivFun.symm y)
    simp only [LinearEquiv.apply_symm_apply] at h
    dsimp only [e, m]
    rw [h, LinearEquiv.symm_apply_apply, hmul]
  have hleft (x : Fin n → ℝ) : m 0 x = x := by
    apply he
    rw [hemul]
    have h : e 0 = 1 := by simp [e, hzero]
    rw [h, one_mul]
  have hright (x : Fin n → ℝ) : m x 0 = x := by
    apply he
    rw [hemul]
    have h : e 0 = 1 := by simp [e, hzero]
    rw [h, mul_one]
  have hdiff : DifferentiableAt ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) => m p.1 p.2) (0, 0) :=
    (contDiff_dynkinProduct (k := 1) coeff (fun _ => basisBracket b) Prod.fst Prod.snd
      contDiff_const contDiff_fst contDiff_snd).contDiffAt.differentiableAt (by norm_num)
  let f : (Fin n → ℝ) → W := fun x => (l (e x)).toAdd
  have hscale (t : ℝ) (x : Fin n → ℝ) : f (t • x) = t • f x := by
    have h := hom_flow_eq_smul (fun s : ℝ => e (s • x))
      (hcont.comp (continuous_id.smul continuous_const))
      (by simp [e, hzero])
      (fun s u => by simpa only [e, map_smul] using hadd (b.equivFun.symm x) s u) l hl t
    simpa only [f, one_smul] using h
  obtain ⟨A, hA⟩ := exists_linearMap_of_coordinate_hom m hdiff hleft hright f (hl.comp hcont)
    (fun x y => by dsimp [f]; rw [hemul, map_mul]; rfl) hscale
  refine ⟨A.toLinearMap.comp b.equivFun.toLinearMap, ?_⟩
  intro x
  change A (b.equivFun x) = _
  simpa only [f, e, LinearEquiv.symm_apply_apply] using hA (b.equivFun x)

end PolycyclicRecognition

end

end OAI
