import Mathlib

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

namespace TensorLp
variable {A B : Type*}
abbrev H (A : Type*) := lp (fun _ : A => ℂ) 2

theorem hasSum_square (x : H A) : HasSum (fun a => ‖x a‖^2) (‖x‖^2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (lp.hasSum_norm (p := 2) (by norm_num) x)

theorem tensor_mem (x : H A) (y : H B) :
    Memℓp (fun ab : A × B => x ab.1 * y ab.2) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, mul_pow] using
    (hasSum_square x).summable.mul_of_nonneg (hasSum_square y).summable
      (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)

def tensor (x : H A) (y : H B) : H (A × B) := ⟨_, tensor_mem x y⟩
@[simp] theorem tensor_apply (x : H A) (y : H B) (a : A) (b : B) :
    tensor x y (a,b) = x a*y b := rfl

theorem tensor_norm_sq (x : H A) (y : H B) : ‖tensor x y‖^2 = ‖x‖^2*‖y‖^2 := by
  apply (hasSum_square (tensor x y)).unique
  have hd := (hasSum_square x).summable.mul_of_nonneg (hasSum_square y).summable
    (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  change HasSum (fun ab : A × B => ‖x ab.1*y ab.2‖^2) _
  simpa only [norm_mul, mul_pow] using
    (hasSum_square x).mul (hasSum_square y) hd

theorem tensor_norm (x : H A) (y : H B) : ‖tensor x y‖ = ‖x‖*‖y‖ := by
  have h := tensor_norm_sq x y
  have he : ‖tensor x y‖^2 = (‖x‖*‖y‖)^2 := by rw [mul_pow, h]
  nlinarith [norm_nonneg (tensor x y), mul_nonneg (norm_nonneg x) (norm_nonneg y)]

theorem slice_mem (z : H (A × B)) (b : B) : Memℓp (fun a => z (a,b)) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
  have hs : Summable (fun a => ‖z (a,b)‖^2) :=
    (hasSum_square z).summable.comp_injective (fun a c h => congrArg Prod.fst h)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs

def slice (z : H (A × B)) (b : B) : H A := ⟨_, slice_mem z b⟩
@[simp] theorem slice_apply (z : H (A × B)) (b : B) (a : A) : slice z b a = z (a,b) := rfl

theorem hasSum_slice_norm_sq (z : H (A × B)) : HasSum (fun b => ‖slice z b‖^2) (‖z‖^2) := by
  have hs := (hasSum_square z).summable
  have hp (b : B) : (∑' a, ‖z (a,b)‖^2) = ‖slice z b‖^2 := (hasSum_square (slice z b)).tsum_eq
  have ht : (∑' b, ∑' a, ‖z (a,b)‖^2) = ‖z‖^2 := by
    calc
      _ = ∑' a, ∑' b, ‖z (a,b)‖^2 :=
        Summable.tsum_comm (f := fun a b => ‖z (a,b)‖^2) hs
      _ = ∑' ab : A × B, ‖z ab‖^2 := hs.tsum_prod.symm
      _ = ‖z‖^2 := (hasSum_square z).tsum_eq
  have hh := hs.prod_symm.prod.hasSum
  have hh' := ht ▸ hh
  simpa only [Prod.swap_prod_mk, hp] using hh'

theorem slice_norm_le (z : H (A × B)) (b : B) : ‖slice z b‖ ≤ ‖z‖ := by
  have h := (hasSum_slice_norm_sq z).summable.le_tsum b (fun _ _ => sq_nonneg _)
  rw [(hasSum_slice_norm_sq z).tsum_eq] at h
  nlinarith [norm_nonneg z, norm_nonneg (slice z b)]

def sliceCLM (b : B) : H (A × B) →L[ℂ] H A :=
  LinearMap.mkContinuous
    { toFun := fun z => slice z b
      map_add' := fun x y => by apply lp.ext; rfl
      map_smul' := fun c x => by apply lp.ext; rfl }
    1 (fun z => by change ‖slice z b‖ ≤ 1*‖z‖; simpa only [one_mul] using slice_norm_le z b)

@[simp] theorem sliceCLM_apply (b : B) (z : H (A × B)) : sliceCLM b z = slice z b := rfl

end TensorLp

namespace TensorLp
variable {A B : Type*}

def tensorRight (y : H B) : H A →L[ℂ] H (A × B) :=
  LinearMap.mkContinuous
    { toFun := fun x => tensor x y
      map_add' := fun x z => by
        apply lp.ext
        funext ab
        change (x ab.1 + z ab.1)*y ab.2 = x ab.1*y ab.2 + z ab.1*y ab.2
        ring
      map_smul' := fun c x => by apply lp.ext; funext ab; simp [tensor, mul_assoc] }
    ‖y‖ (fun x => by change ‖tensor x y‖ ≤ ‖y‖*‖x‖; rw [tensor_norm, mul_comm])

@[simp] theorem tensorRight_apply (y : H B) (x : H A) : tensorRight y x = tensor x y := rfl

def tensorLeft (x : H A) : H B →L[ℂ] H (A × B) :=
  LinearMap.mkContinuous
    { toFun := fun y => tensor x y
      map_add' := fun y z => by
        apply lp.ext
        funext ab
        change x ab.1*(y ab.2 + z ab.2) = x ab.1*y ab.2 + x ab.1*z ab.2
        ring
      map_smul' := fun c y => by apply lp.ext; funext ab; simp [tensor, mul_left_comm] }
    ‖x‖ (fun y => by change ‖tensor x y‖ ≤ ‖x‖*‖y‖; rw [tensor_norm])

@[simp] theorem tensorLeft_apply (x : H A) (y : H B) : tensorLeft x y = tensor x y := rfl

theorem inner_tensor (x z : H A) (y w : H B) :
    inner ℂ (tensor x y) (tensor z w) = inner ℂ x z * inner ℂ y w := by
  have ha : Summable (fun a => ‖inner ℂ (x a) (z a)‖) := (lp.summable_inner (𝕜 := ℂ) x z).norm
  have hb : Summable (fun b => ‖inner ℂ (y b) (w b)‖) := (lp.summable_inner (𝕜 := ℂ) y w).norm
  apply (lp.hasSum_inner (𝕜 := ℂ) (tensor x y) (tensor z w)).unique
  convert! (lp.hasSum_inner (𝕜 := ℂ) x z).mul (lp.hasSum_inner (𝕜 := ℂ) y w)
    (summable_mul_of_summable_norm
      (f := fun a => inner ℂ (x a) (z a)) (g := fun b => inner ℂ (y b) (w b)) ha hb) using 1
  ext ab
  change inner ℂ (x ab.1*y ab.2) (z ab.1*w ab.2) = _
  simp only [RCLike.inner_apply, map_mul]
  ring

end TensorLp

namespace TensorLp
variable {A B : Type*}



theorem lift_mem (Z : H A →L[ℂ] H A) (z : H (A × B)) :
    Memℓp (fun ab : A × B => Z (slice z ab.2) ab.1) 2 := by
  have hr : Summable (fun b => ‖Z (slice z b)‖^2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _
      ((hasSum_slice_norm_sq z).summable.mul_left (‖Z‖^2))
    intro b
    calc
      _ ≤ (‖Z‖*‖slice z b‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (Z.le_opNorm _) 2
      _ = ‖Z‖^2*‖slice z b‖^2 := mul_pow _ _ _
  have hd : Summable (fun ba : B × A => ‖Z (slice z ba.1) ba.2‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun b => (hasSum_square (Z (slice z b))).summable, ?_⟩
    simpa only [(hasSum_square _).tsum_eq] using hr
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
  simpa only [Prod.swap, ENNReal.toReal_ofNat, Real.rpow_two] using hd.prod_symm

def liftVector (Z : H A →L[ℂ] H A) (z : H (A × B)) : H (A × B) :=
  ⟨_, lift_mem Z z⟩

@[simp] theorem liftVector_apply (Z : H A →L[ℂ] H A) (z : H (A × B)) (a : A) (b : B) :
    liftVector Z z (a,b) = Z (slice z b) a := rfl

@[simp] theorem slice_liftVector (Z : H A →L[ℂ] H A) (z : H (A × B)) (b : B) :
    slice (liftVector Z z) b = Z (slice z b) := by apply lp.ext; rfl

theorem liftVector_norm (Z : H A →L[ℂ] H A) (z : H (A × B)) :
    ‖liftVector Z z‖ ≤ ‖Z‖*‖z‖ := by
  have h₁ : Summable (fun b => ‖Z (slice z b)‖^2) := by
    simpa only [slice_liftVector] using (hasSum_slice_norm_sq (liftVector Z z)).summable
  have h₂ := (hasSum_slice_norm_sq z).summable.mul_left (‖Z‖^2)
  have hb (b : B) : ‖Z (slice z b)‖^2 ≤ ‖Z‖^2*‖slice z b‖^2 := by
    calc
      _ ≤ (‖Z‖*‖slice z b‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (Z.le_opNorm _) 2
      _ = _ := mul_pow _ _ _
  have ht := h₁.tsum_le_tsum hb h₂
  have he : (∑' b, ‖Z (slice z b)‖^2) = ‖liftVector Z z‖^2 := by
    simpa only [slice_liftVector] using (hasSum_slice_norm_sq (liftVector Z z)).tsum_eq
  rw [he, tsum_mul_left, (hasSum_slice_norm_sq z).tsum_eq, ← mul_pow] at ht
  nlinarith [norm_nonneg (liftVector Z z), mul_nonneg (norm_nonneg Z) (norm_nonneg z)]

def liftLeft (Z : H A →L[ℂ] H A) : H (A × B) →L[ℂ] H (A × B) :=
  LinearMap.mkContinuous
    { toFun := liftVector Z
      map_add' := fun x y => by
        apply lp.ext
        funext ab
        change Z (slice (x+y) ab.2) ab.1 = (Z (slice x ab.2) + Z (slice y ab.2)) ab.1
        rw [show slice (x+y) ab.2 = slice x ab.2 + slice y ab.2 from (sliceCLM ab.2).map_add x y,
          map_add]
      map_smul' := fun c x => by
        apply lp.ext
        funext ab
        change Z (slice (c • x) ab.2) ab.1 = (c • Z (slice x ab.2)) ab.1
        rw [show slice (c • x) ab.2 = c • slice x ab.2 from (sliceCLM ab.2).map_smul c x,
          map_smul] }
    ‖Z‖ (liftVector_norm Z)

@[simp] theorem liftLeft_apply (Z : H A →L[ℂ] H A) (z : H (A × B)) (a : A) (b : B) :
    liftLeft Z z (a,b) = Z (slice z b) a := rfl

theorem liftLeft_norm (Z : H A →L[ℂ] H A) : ‖liftLeft (B := B) Z‖ ≤ ‖Z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  exact liftVector_norm Z

@[simp] theorem slice_liftLeft (Z : H A →L[ℂ] H A) (z : H (A × B)) (b : B) :
    slice (liftLeft Z z) b = Z (slice z b) := slice_liftVector Z z b


theorem hasSum_slice_inner (x y : H (A × B)) :
    HasSum (fun b => inner ℂ (slice x b) (slice y b)) (inner ℂ x y) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) x y
  have hr (b : B) : HasSum (fun a => inner ℂ (x (a,b)) (y (a,b)))
      (inner ℂ (slice x b) (slice y b)) := lp.hasSum_inner (𝕜 := ℂ) (slice x b) (slice y b)
  have hc : HasSum (fun ba : B × A => inner ℂ (x (ba.2,ba.1)) (y (ba.2,ba.1)))
      (inner ℂ x y) := (Equiv.prodComm B A).hasSum_iff.mpr h
  exact hc.prod_fiberwise hr

theorem liftLeft_symmetric {Z : H A →L[ℂ] H A} (hZ : Z.IsSymmetric) :
    (liftLeft (B := B) Z).IsSymmetric := by
  intro x y
  apply HasSum.unique (hasSum_slice_inner (liftLeft Z x) y)
  convert! hasSum_slice_inner x (liftLeft Z y) using 1
  ext b
  simp only [slice_liftLeft]
  exact hZ _ _

theorem liftLeft_positive {Z : H A →L[ℂ] H A} (hZ : Z.IsPositive) :
    (liftLeft (B := B) Z).IsPositive := by
  refine ⟨liftLeft_symmetric hZ.isSymmetric, ?_⟩
  intro x
  have h := (hasSum_slice_inner x (liftLeft Z x)).mapL Complex.reCLM
  have hp (b : B) : 0 ≤ (inner ℂ (slice x b) (Z (slice x b))).re := hZ.re_inner_nonneg_right _
  have hh : HasSum (fun b => (inner ℂ (slice x b) (Z (slice x b))).re)
      (inner ℂ x (liftLeft Z x)).re := by simpa only [Complex.reCLM_apply, slice_liftLeft] using h
  change 0 ≤ (inner ℂ (liftLeft Z x) x).re
  have he : (inner ℂ (liftLeft Z x) x).re = (inner ℂ x (liftLeft Z x)).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  rw [he]
  exact hh.nonneg hp

@[simp] theorem liftLeft_one : liftLeft (B := B) (1 : H A →L[ℂ] H A) = 1 := by
  ext z ab
  rfl

@[simp] theorem liftLeft_mul (Z T : H A →L[ℂ] H A) :
    liftLeft (B := B) (Z*T) = liftLeft Z * liftLeft T := by
  ext z ab
  change Z (T (slice z ab.2)) ab.1 = Z (slice (liftLeft T z) ab.2) ab.1
  rw [slice_liftLeft]

end TensorLp

end

end

end OAI
