import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealShadowOperators
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealSplitAnnihilator
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialRangeAgreement

namespace OAI

/-! # Real triangularizability of the modified Lie algebra -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

def realShadowAdjoint (x : L) : Module.End ℝ L :=
  (cartanRealShadowEquiv T H).symm.toLinearMap.comp
    ((ad ℝ (CartanRealShadow T H) (cartanRealShadowEquiv T H x)).comp
      (cartanRealShadowEquiv T H).toLinearMap)

theorem realShadowAdjoint_apply (x y : L) :
    realShadowAdjoint T H x y =
      ⁅x,y⁆ - T.weightImaginaryAction H x y + T.weightImaginaryAction H y x :=
  cartanRealShadow_bracket T H x y

theorem realShadowAdjoint_weight (x y : L) :
    T.weightMap (realShadowAdjoint T H x y) = 0 :=
  cartanRealShadow_bracket_weight T H x y

theorem realShadowAdjoint_eq_on_kernel (x y : L) (hy : T.weightMap y = 0) :
    realShadowAdjoint T H x y = T.weightCorrectedOperator H x y := by
  rw [realShadowAdjoint_apply,T.weightImaginaryAction_kernel H y hy]
  simp only [LieDerivation.zero_apply,add_zero]
  rfl

theorem realShadowAdjoint_mul (x : L) :
    T.weightCorrectedOperator H x * realShadowAdjoint T H x =
      realShadowAdjoint T H x * realShadowAdjoint T H x := by
  ext y
  exact (realShadowAdjoint_eq_on_kernel T H x _ (realShadowAdjoint_weight T H x y)).symm

/-- The extra correction in the actual adjoint action vanishes on its image.
Thus one extra zero root transfers the real annihilator to that adjoint. -/
theorem realShadowAdjoint_split_annihilator (x : L) :
    ∃ S : Finset ℝ,
      Polynomial.aeval (realShadowAdjoint T H x)
        ((∏ a ∈ S, (Polynomial.X - Polynomial.C a)) ^ (n+1)) = 0 := by
  classical
  obtain ⟨S,hS⟩ := real_split_annihilator_of_complex_triangular
    (T.weightCorrectedOperator H x) T.basis
    (by rw [T.weightCorrectedOperator_complexify H]; exact T.complexWeightCorrectedOperator_upper H x)
    (by rw [T.weightCorrectedOperator_complexify H]; exact T.complexWeightCorrectedOperator_diagonal_im H x)
  let Q : Polynomial ℝ := ∏ a ∈ S, (Polynomial.X - Polynomial.C a)
  let P : Polynomial ℝ := ∏ a ∈ insert 0 S, (Polynomial.X - Polynomial.C a)
  have hz : Polynomial.aeval (realShadowAdjoint T H x) (Polynomial.X * Q^n) = 0 :=
    aeval_X_mul_eq_zero_of_mul_eq _ _ (realShadowAdjoint_mul T H x) _ hS
  have hQP : Q ∣ P := Finset.prod_dvd_prod_of_subset S (insert 0 S) _ (Finset.subset_insert _ _)
  have hXP : Polynomial.X ∣ P := by
    have hd := Finset.dvd_prod_of_mem (fun a : ℝ => (Polynomial.X : Polynomial ℝ) - Polynomial.C a)
      (Finset.mem_insert_self 0 S)
    change (Polynomial.X - Polynomial.C (0 : ℝ)) ∣ P at hd
    rw [Polynomial.C_0,sub_zero] at hd
    exact hd
  have hdiv : Polynomial.X * Q^n ∣ P^(n+1) := by
    simpa only [pow_succ'] using mul_dvd_mul hXP (pow_dvd_pow_of_dvd hQP n)
  exact ⟨insert 0 S,Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdiv hz⟩

theorem realShadowAdjoint_conjugate (x : L) :
    (cartanRealShadowEquiv T H).conjAlgEquiv ℝ (realShadowAdjoint T H x) =
      ad ℝ (CartanRealShadow T H) (cartanRealShadowEquiv T H x) := by
  apply LinearMap.ext
  intro p
  obtain ⟨y,rfl⟩ := (cartanRealShadowEquiv T H).surjective p
  simp only [LinearEquiv.conjAlgEquiv_apply,
    LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  exact (cartanRealShadowEquiv T H).apply_symm_apply _

/-- Every actual adjoint operator of the real shadow splits over the reals. -/
theorem cartanRealShadow_isTriangularizable :
    LieModule.IsTriangularizable ℝ (CartanRealShadow T H) (CartanRealShadow T H) where
  maxGenEigenspace_eq_top p := by
    obtain ⟨x,rfl⟩ := (cartanRealShadowEquiv T H).surjective p
    obtain ⟨S,hS⟩ := realShadowAdjoint_split_annihilator T H x
    apply iSup_maxGenEigenspace_eq_top_of_annihilating_product _ S (n+1)
    change Polynomial.aeval (ad ℝ (CartanRealShadow T H) (cartanRealShadowEquiv T H x)) _ = 0
    rw [← realShadowAdjoint_conjugate T H x,Polynomial.aeval_algHom_apply,hS,map_zero]

/-- A genuine simultaneous real upper triangular adjoint basis. -/
theorem nonempty_cartanRealShadow_triangularAdjoint :
    ∃ m : ℕ, Nonempty (TriangularAdjoint (CartanRealShadow T H) m) := by
  let := cartanRealShadow_solvable T H
  let := cartanRealShadow_isTriangularizable T H
  exact nonempty_triangularAdjoint_of_split (CartanRealShadow T H)

end PolycyclicRecognition

end

end OAI
