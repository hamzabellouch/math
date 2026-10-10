import OAI.Geometry.Kahler.PinchingCompact

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Complex
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra

 def normalIndex : Index → Fin 3
  | none => 2
  | some i => i.castSucc

 def verticalScale (r : ℝ) : Index → ℝ
  | none => r
  | some _ => 1

 def normalCurvature (f : Base → ℝ) (lam : ℝ) (w : ℂ) : Tensor Index :=
  pullTensor (verticalScale ((Real.sqrt (barrierQ (normalLogWeight f w (0,w))))⁻¹))
    (fun a b c d => curvature (complexHessian (normalPotential f lam w)) (0,w)
      (normalIndex a) (normalIndex b) (normalIndex c) (normalIndex d))

lemma normalCurvature_symmetries {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) :
    Symmetries (normalCurvature f lam w) := by
  apply pull_symmetries
  have hs := (normalPotential_contDiffAt hf lam w hn).of_le (m := 4) (WithTop.coe_le_coe.mpr le_top)
  exact ⟨fun a b c d => complexHessian_curvature_hol hs _ _ _ _,
    fun a b c d => complexHessian_curvature_anti hs _ _ _ _,
    fun a b c d => complexHessian_curvature_reality hs _ _ _ _⟩

lemma tensor_symmetries_sub {T Q : Tensor Index} (hT : Symmetries T) (hQ : Symmetries Q) :
    Symmetries (T-Q) := by
  constructor
  · intro a b c d; simp only [Pi.sub_apply, hT.hol a b c d, hQ.hol a b c d]
  · intro a b c d; simp only [Pi.sub_apply, hT.anti a b c d, hQ.anti a b c d]
  · intro a b c d; simp only [Pi.sub_apply, star_sub, hT.reality a b c d, hQ.reality a b c d]

lemma tensor_symmetries_add {T Q : Tensor Index} (hT : Symmetries T) (hQ : Symmetries Q) :
    Symmetries (T+Q) := by
  constructor
  · intro a b c d; simp only [Pi.add_apply, hT.hol a b c d, hQ.hol a b c d]
  · intro a b c d; simp only [Pi.add_apply, hT.anti a b c d, hQ.anti a b c d]
  · intro a b c d; simp only [Pi.add_apply, star_add, hT.reality a b c d, hQ.reality a b c d]

lemma tensor_symmetries_smul {T : Tensor Index} (hT : Symmetries T) (r : ℝ) :
    Symmetries (r • T) := by
  constructor
  · intro a b c d; simp only [Pi.smul_apply, hT.hol a b c d]
  · intro a b c d; simp only [Pi.smul_apply, hT.anti a b c d]
  · intro a b c d; simp only [Pi.smul_apply, star_smul, star_trivial, hT.reality a b c d]

lemma tensor_S_symmetries (A : Matrix Index Index ℂ) (hA : A.IsHermitian) : Symmetries (S A) := by
  constructor
  · intro a b c d; simp only [S]; ring
  · intro a b c d; simp only [S]; ring
  · intro a b c d
    simp only [S, star_add, star_mul]
    rw [show star (A a b) = A b a from hA.apply b a,
      show star (A c d) = A d c from hA.apply d c,
      show star (A a d) = A d a from hA.apply d a,
      show star (A c b) = A b c from hA.apply b c]
    ring

lemma block_isHermitian (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) (r : ℝ) :
    (block A r).IsHermitian := by
  ext a b
  cases a <;> cases b <;> simp [Matrix.conjTranspose, block]
  exact hA.apply _ _

lemma principal_symmetries (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) (lam x : ℝ) :
    Symmetries (curvatureModel A lam x 0 0) := by
  simp only [curvatureModel, add_zero]
  apply tensor_symmetries_sub
  · exact tensor_symmetries_sub
      (tensor_symmetries_sub (tensor_symmetries_smul (tensor_S_symmetries _ (block_isHermitian _ Matrix.isHermitian_one _)) _)
        (tensor_symmetries_smul (tensor_S_symmetries _ (block_isHermitian _ hA _)) _))
      (tensor_S_symmetries _ (block_isHermitian _ Matrix.isHermitian_zero _))
  · exact tensor_symmetries_sub
      (tensor_symmetries_sub (tensor_S_symmetries _ (block_isHermitian _ (mixedMatrix_hermitian A hA _ _) _))
        (tensor_S_symmetries _ (block_isHermitian _ (mixedMatrix_hermitian A hA _ _) _)))
      (tensor_S_symmetries _ (block_isHermitian _ Matrix.isHermitian_zero _))

 def horizontalPart (j : ℕ) (T : Tensor Index) : Tensor Index :=
  fun a b c d => if horizontalCount a b c d = j then T a b c d else 0

lemma horizontalPart_supported (j : ℕ) (T : Tensor Index) : Supported (horizontalPart j T) j := by
  intro a b c d h
  simp [horizontalPart, h]

lemma horizontalPart_symmetries (j : ℕ) (T : Tensor Index) (hT : Symmetries T) :
    Symmetries (horizontalPart j T) := by
  have hh (a b c d : Index) : horizontalCount a b c d = horizontalCount c b a d := by
    unfold horizontalCount; omega
  have ha (a b c d : Index) : horizontalCount a b c d = horizontalCount a d c b := by
    unfold horizontalCount; omega
  have hr (a b c d : Index) : horizontalCount a b c d = horizontalCount b a d c := by
    unfold horizontalCount; omega
  constructor
  · intro a b c d; simp only [horizontalPart, hh a b c d, hT.hol a b c d]
  · intro a b c d; simp only [horizontalPart, ha a b c d, hT.anti a b c d]
  · intro a b c d; simp only [horizontalPart, hr a b c d, apply_ite star, star_zero, hT.reality a b c d]

lemma tensor_split_of_low_blocks {T : Tensor Index} (hT : Symmetries T)
    (h0 : T none none none none = 0)
    (h1 : ∀ a, T (some a) none none none = 0)
    (h2 : ∀ a b, T (some a) (some b) none none = 0)
    (h2' : ∀ a c, T (some a) none (some c) none = 0) :
    T = horizontalPart 4 T + horizontalPart 3 T := by
  ext a b c d
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [horizontalPart, horizontalCount]
  all_goals first
    | exact h0
    | exact h1 _
    | exact h2 _ _
    | exact h2' _ _
    | rfl
    | (rw [hT.hol]; exact h1 _)
    | (rw [hT.hol]; exact h2 _ _)
    | (rw [hT.anti]; exact h2 _ _)
    | (rw [hT.hol, hT.anti]; exact h2 _ _)
    | (apply star_injective; rw [hT.reality, star_zero]; exact h1 _)
    | (apply star_injective; rw [hT.reality, star_zero, hT.hol]; exact h1 _)
    | (apply star_injective; rw [hT.reality, star_zero]; exact h2' _ _)

lemma baseHessian_isHermitian {f : Base → ℝ} {z : Base} (hf : ContDiffAt ℝ 2 f z) :
    (baseHessian f z).IsHermitian := by
  ext i j
  change star (baseHessian f z j i) = baseHessian f z i j
  have hc := complexHessian_hermitian (hf.comp (f := fun q : Ambient => q.1) (z,0) contDiffAt_fst) i.castSucc j.castSucc
  change liftedHessian f (z,0) i.castSucc j.castSucc = star (liftedHessian f (z,0) j.castSucc i.castSucc) at hc
  rw [liftedHessian_horizontal hf, liftedHessian_horizontal hf] at hc
  exact hc.symm

lemma complex_horizontalMetric (A : Matrix (Fin 2) (Fin 2) ℂ) (lam x : ℝ) :
    (lam : ℂ) • 1 + (x : ℂ) • A = horizontalMetric A lam x := by
  ext i j
  simp [horizontalMetric, Complex.real_smul]

lemma mixedMatrix_component (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian)
    (lam x : ℝ) (a b : Fin 2) :
    mixedMatrix A lam x a b =
      (1 + 2 * (x : ℂ)) * A a b - ((x * (1+x) : ℝ) : ℂ) *
        (∑ e : Fin 2, ∑ k : Fin 2, (horizontalMetric A lam x)⁻¹ e k * A a e * star (A b k)) := by
  simp only [mixedMatrix, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul,
    Matrix.mul_apply, Fin.sum_univ_two, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [show star (A b 0) = A 0 b from hA.apply 0 b,
    show star (A b 1) = A 1 b from hA.apply 1 b]
  ring

lemma sqrt_normalization (q : ℝ) (hq : 0 < q) :
    (((Real.sqrt q)⁻¹ : ℝ) : ℂ)^2 * (q : ℂ) = 1 ∧
    (((Real.sqrt q)⁻¹ : ℝ) : ℂ) * (q : ℂ) = (Real.sqrt q : ℂ) ∧
    (((Real.sqrt q)⁻¹ : ℝ) : ℂ)^4 * (q : ℂ)^2 = 1 := by
  have hr : (Real.sqrt q : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hq))
  have hs : (Real.sqrt q : ℂ)^2 = (q : ℂ) := by exact_mod_cast Real.sq_sqrt hq.le
  rw [Complex.ofReal_inv, ← hs]
  constructor
  · field_simp
  · constructor <;> field_simp

lemma normalCurvature_HVHV {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))).det ≠ 0)
    (a b : Fin 2) :
    normalCurvature f lam w (some a) (some b) none none =
      -mixedMatrix (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w))) a b := by
  have hG' := hG
  rw [← complex_horizontalMetric] at hG'
  simp only [normalCurvature, pullTensor, verticalScale, normalIndex, Complex.ofReal_one, one_mul, mul_one]
  erw [normalPotential_curvature_HVHV hf lam w hn hG', complex_horizontalMetric,
    mixedMatrix_component _ (baseHessian_isHermitian (hf.of_le (WithTop.coe_le_coe.mpr le_top)))]
  have hs := (sqrt_normalization (barrierQ (normalLogWeight f w (0,w))) (barrierQ_positive hn)).1
  change _ * (barrierQ _ : ℂ) = 1 at hs
  change _ = -((1 + 2 * (barrierX (normalLogWeight f w (0,w)) : ℂ)) * baseHessian f 0 a b - (barrierQ (normalLogWeight f w (0,w)) : ℂ) * _)
  linear_combination -((1 + 2 * (barrierX (normalLogWeight f w (0,w)) : ℂ)) * baseHessian f 0 a b - (barrierQ (normalLogWeight f w (0,w)) : ℂ) *
    (∑ e : Fin 2, ∑ k : Fin 2, (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w))))⁻¹ e k * baseHessian f 0 a e * star (baseHessian f 0 b k))) * hs

lemma normalCurvature_HHVV {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))).det ≠ 0)
    (a c : Fin 2) : normalCurvature f lam w (some a) none (some c) none = 0 := by
  have hG' := hG
  rw [← complex_horizontalMetric] at hG'
  simp only [normalCurvature, pullTensor, verticalScale, normalIndex, Complex.ofReal_one, one_mul, mul_one]
  rw [normalPotential_curvature_HHVV hf lam w hn hG']
  simp

lemma normalCurvature_HVVV {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))).det ≠ 0)
    (a : Fin 2) : normalCurvature f lam w (some a) none none none = 0 := by
  have hG' := hG
  rw [← complex_horizontalMetric] at hG'
  simp only [normalCurvature, pullTensor, verticalScale, normalIndex, Complex.ofReal_one, one_mul]
  rw [normalPotential_curvature_HVVV hf lam w hn hG']
  simp

lemma normalCurvature_VVVV {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))).det ≠ 0)
     : normalCurvature f lam w none none none none = -2 := by
  have hG' := hG
  rw [← complex_horizontalMetric] at hG'
  simp only [normalCurvature, pullTensor, verticalScale, normalIndex]
  rw [normalPotential_curvature_VVVV hf lam w hn hG']
  have hs := (sqrt_normalization (barrierQ (normalLogWeight f w (0,w))) (barrierQ_positive hn)).2.2
  linear_combination -2 * hs

lemma principal_HHHH (A : Matrix (Fin 2) (Fin 2) ℂ) (lam x : ℝ) (a b c d : Fin 2) :
    curvatureModel A lam x 0 0 (some a) (some b) (some c) (some d) = -(lam : ℂ) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) a b * (1 : Matrix (Fin 2) (Fin 2) ℂ) c d + (1 : Matrix (Fin 2) (Fin 2) ℂ) a d * (1 : Matrix (Fin 2) (Fin 2) ℂ) c b) - ((x*(1+x) : ℝ) : ℂ) * (A a b * A c d + A a d * A c b) := by
  simp [curvatureModel, S, block, Complex.real_smul]
  ; ring

lemma principal_HHHV (A : Matrix (Fin 2) (Fin 2) ℂ) (lam x : ℝ) (a b c : Fin 2) :
    curvatureModel A lam x 0 0 (some a) (some b) (some c) none = 0 := by
  simp [curvatureModel, S, block]

lemma principal_HVHV (A : Matrix (Fin 2) (Fin 2) ℂ) (lam x : ℝ) (a b : Fin 2) :
    curvatureModel A lam x 0 0 (some a) (some b) none none = -mixedMatrix A lam x a b := by
  simp [curvatureModel, S, block]

lemma principal_HHVV (A : Matrix (Fin 2) (Fin 2) ℂ) (lam x : ℝ) (a c : Fin 2) :
    curvatureModel A lam x 0 0 (some a) none (some c) none = 0 := by
  simp [curvatureModel, S, block]

lemma principal_HVVV (A : Matrix (Fin 2) (Fin 2) ℂ) (lam x : ℝ) (a : Fin 2) :
    curvatureModel A lam x 0 0 (some a) none none none = 0 := by
  simp [curvatureModel, S, block]

lemma principal_VVVV (A : Matrix (Fin 2) (Fin 2) ℂ) (lam x : ℝ)  :
    curvatureModel A lam x 0 0 none none none none = -2 := by
  norm_num [curvatureModel, S, block, Complex.real_smul]

def normalError (f : Base → ℝ) (lam : ℝ) (w : ℂ) : Tensor Index :=
  normalCurvature f lam w - curvatureModel (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w))) 0 0

lemma normalError_symmetries {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) :
    Symmetries (normalError f lam w) :=
  tensor_symmetries_sub (normalCurvature_symmetries hf lam w hn)
    (principal_symmetries _ (baseHessian_isHermitian (hf.of_le (WithTop.coe_le_coe.mpr le_top))) _ _)

lemma normalCurvature_model {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))).det ≠ 0) :
    normalCurvature f lam w = curvatureModel (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))
      (horizontalPart 4 (normalError f lam w)) (horizontalPart 3 (normalError f lam w)) := by
  have hs := tensor_split_of_low_blocks (normalError_symmetries hf lam w hn)
    (by simp only [normalError, Pi.sub_apply, normalCurvature_VVVV hf lam w hn hG, principal_VVVV, sub_self])
    (fun a => by simp only [normalError, Pi.sub_apply, normalCurvature_HVVV hf lam w hn hG, principal_HVVV, sub_self])
    (fun a b => by simp only [normalError, Pi.sub_apply, normalCurvature_HVHV hf lam w hn hG, principal_HVHV, sub_self])
    (fun a c => by simp only [normalError, Pi.sub_apply, normalCurvature_HHVV hf lam w hn hG, principal_HHVV, sub_self])
  have he (T4 T3 : Tensor Index) : curvatureModel (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w))) T4 T3 =
      curvatureModel (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w))) 0 0 + (T4+T3) := by
    simp only [curvatureModel, add_zero, add_assoc]
  rw [he, ← hs]
  unfold normalError
  abel

end PinchedHartogs

end

end OAI
