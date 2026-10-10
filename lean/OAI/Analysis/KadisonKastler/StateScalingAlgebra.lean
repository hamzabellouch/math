import OAI.Analysis.KadisonKastler.StateCentralizerVonNeumann
import OAI.Analysis.KadisonKastler.PointedSiteBalance

namespace OAI

/-! # Algebraic operations on state-scaling operators

The balance identity is the bounded-operator form of a modular eigenvector.
Its products, adjoints and centralizer compressions are proved directly.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

def StateScales (M : VonNeumannAlgebra H) (Ω : H) (r : ℝ)
    (a : H →L[ℂ] H) : Prop :=
  ∀ b ∈ M, productVectorState Ω (b*a) = (r : ℂ)*productVectorState Ω (a*b)

namespace StateScales

variable {r s : ℝ} {a b : H →L[ℂ] H}

theorem add (ha : StateScales M Ω r a) (hb : StateScales M Ω r b) :
    StateScales M Ω r (a+b) := by
  intro x hx
  simpa only [mul_add,add_mul,productVectorState,add_apply,inner_add_right] using
    congrArg₂ (·+·) (ha x hx) (hb x hx)

theorem smul (ha : StateScales M Ω r a) (z : ℂ) : StateScales M Ω r (z • a) := by
  intro x hx
  simpa only [mul_smul_comm,smul_mul_assoc,productVectorState,smul_apply,
    inner_smul_right,smul_eq_mul,mul_left_comm] using congrArg (z*·) (ha x hx)

theorem mul (ha : StateScales M Ω r a) (hb : StateScales M Ω s b)
    (ham : a ∈ M) (hbm : b ∈ M) : StateScales M Ω (r*s) (a*b) := by
  intro x hx
  calc
    _ = productVectorState Ω ((x*a)*b) := by rw [mul_assoc]
    _ = (s : ℂ)*productVectorState Ω (b*(x*a)) := hb _ (M.mul_mem hx ham)
    _ = (s : ℂ)*productVectorState Ω ((b*x)*a) := by rw [mul_assoc]
    _ = (s : ℂ)*((r : ℂ)*productVectorState Ω (a*(b*x))) :=
      congrArg ((s : ℂ)*·) (ha _ (M.mul_mem hbm hx))
    _ = _ := by rw [Complex.ofReal_mul]; simp only [mul_assoc]; ring

private theorem conjugate_state (x : H →L[ℂ] H) :
    star (productVectorState Ω x) = productVectorState Ω (star x) := by
  change (starRingEnd ℂ) (inner ℂ Ω (x Ω)) = inner ℂ Ω ((star x) Ω)
  rw [inner_conj_symm,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

theorem adjoint (ha : StateScales M Ω r a) (hr : r ≠ 0) :
    StateScales M Ω r⁻¹ (star a) := by
  intro x hx
  have hh := congrArg star (ha (star x) (M.toStarSubalgebra.star_mem' hx))
  rw [conjugate_state,star_mul,star_star,star_mul,conjugate_state,star_mul,
    star_star] at hh
  rw [show star (r : ℂ) = (r : ℂ) from Complex.conj_ofReal r] at hh
  rw [Complex.ofReal_inv]
  calc
    _ = (r : ℂ)⁻¹*((r : ℂ)*productVectorState Ω (x*star a)) := by
      rw [← mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hr),one_mul]
    _ = _ := by rw [← show productVectorState Ω (star a*x) =
      (r : ℂ)*productVectorState Ω (x*star a) from by simpa only [mul_comm] using hh]

theorem of_centralizer (a : Algebra (stateCentralizerVonNeumann (M := M) Ω)) :
    StateScales M Ω 1 a.val := by
  intro x hx
  simpa only [Complex.ofReal_one,one_mul] using (a.property.2 x hx).symm

theorem initial_centralizes (ha : StateScales M Ω r a) (ham : a ∈ M) (hr : r ≠ 0) :
    ProductStateCentralizes M Ω (star a*a) := by
  have hh := (ha.adjoint hr).mul ha (M.toStarSubalgebra.star_mem' ham) ham
  rw [inv_mul_cancel₀ hr] at hh
  intro x hx
  simpa only [Complex.ofReal_one,one_mul] using (hh x hx).symm

theorem final_centralizes (ha : StateScales M Ω r a) (ham : a ∈ M) (hr : r ≠ 0) :
    ProductStateCentralizes M Ω (a*star a) := by
  have hh := ha.mul (ha.adjoint hr) ham (M.toStarSubalgebra.star_mem' ham)
  rw [mul_inv_cancel₀ hr] at hh
  intro x hx
  simpa only [Complex.ofReal_one,one_mul] using (hh x hx).symm

theorem initial_state (ha : StateScales M Ω r a) (ham : a ∈ M) :
    productVectorState Ω (star a*a) = (r : ℂ)*productVectorState Ω (a*star a) :=
  ha (star a) (M.toStarSubalgebra.star_mem' ham)

end StateScales

theorem PointedMatrixSites.site_stateScales
    (S : PointedMatrixSites M Ω twoRatioSiteParameter) (i : TwoRatioSite) :
    StateScales M Ω (twoRatioSiteParameter i) ((S.site i).entry 0 1) := by
  intro x hx
  have hh := S.twoRatio_site_balance i 0 1 x hx
  have hw : (twoSiteWeight (twoRatioSiteParameter i) 0 : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    simp only [twoSiteWeight,ite_true,ne_eq,inv_eq_zero]
    linarith [(S.valid i).1]
  have hw₁ : (twoSiteWeight (twoRatioSiteParameter i) 1 : ℂ) =
      (twoRatioSiteParameter i : ℂ)*(twoSiteWeight (twoRatioSiteParameter i) 0 : ℂ) := by
    simp [twoSiteWeight,div_eq_mul_inv]
  rw [hw₁] at hh
  apply mul_left_cancel₀ hw
  calc
    _ = ((twoRatioSiteParameter i : ℂ)*(twoSiteWeight (twoRatioSiteParameter i) 0 : ℂ))*
        productVectorState Ω ((S.site i).entry 0 1*x) := hh.symm
    _ = _ := by ring

end

end KadisonKastler

end OAI
