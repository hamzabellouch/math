import OAI.NumberTheory.DirichletL.Reflection.Shape
import OAI.NumberTheory.DirichletL.Reflection.Denominator

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma PrimeFamily.product_span {ι : Type*} [Fintype ι] (G : PrimeFamily ι) :
    Ideal.span {∏ i, G.generator i} = ∏ i, G.ideal i := by
  have hf (T : Finset ι) : Ideal.span {∏ i ∈ T, G.generator i} = ∏ i ∈ T, G.ideal i := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert i T hi ih =>
      rw [Finset.prod_insert hi,Finset.prod_insert hi,← Ideal.span_singleton_mul_span_singleton,
        G.generator_span,ih]
  exact hf Finset.univ

lemma reflected_conductor_norm {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) (c : Eis) :
    (Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ) =
      (Ideal.absNorm (Ideal.span {c}*(∏ i, F.ideal i)):ℝ)*
        (Ideal.absNorm K:ℝ)*(Ideal.absNorm (∏ i, S.ideal i):ℝ) := by
  rw [← Ideal.span_singleton_mul_span_singleton,PrimeFamily.product_span,F.reflected_product]
  simp only [map_mul,Nat.cast_mul]
  ring

def kernelSlope : Fin 4 → ℝ := ![-2,-2,1,3]
def kernelLogCoordinates (QK QP Qn Qb k p n b : ℝ) : Fin 4 → ℝ :=
  ![Real.log (k/QK),Real.log (p/QP),Real.log (n/Qn),Real.log (b/Qb)]
def kernelCenter (C QK QP Qn Qb : ℝ) : ℝ := C*Qn*Qb^3/(QK^2*QP^2)

lemma kernelLogCoordinates_exp (QK QP Qn Qb k p n b : ℝ)
    (hQK : 0<QK) (hQP : 0<QP) (hQn : 0<Qn) (hQb : 0<Qb)
    (hk : 0<k) (hp : 0<p) (hn : 0<n) (hb : 0<b) :
    Real.exp (∑ i, kernelSlope i * kernelLogCoordinates QK QP Qn Qb k p n b i) =
      (n/Qn)*(b/Qb)^3/((k/QK)^2*(p/QP)^2) := by
  simp only [kernelSlope,kernelLogCoordinates,Fin.sum_univ_succ,Fin.isValue,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero,one_mul]
  rw [show -2*Real.log (k/QK)+(-2*Real.log (p/QP)+(Real.log (n/Qn)+3*Real.log (b/Qb))) =
    -(2*Real.log (k/QK)) + -(2*Real.log (p/QP)) + Real.log (n/Qn) + 3*Real.log (b/Qb) by ring]
  simp only [Real.exp_add,Real.exp_neg]
  rw [show (2:ℝ)=((2:ℕ):ℝ) by norm_num,show (3:ℝ)=((3:ℕ):ℝ) by norm_num,
    Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_nat_mul,
    Real.exp_log (div_pos hk hQK),Real.exp_log (div_pos hp hQP),
    Real.exp_log (div_pos hn hQn),Real.exp_log (div_pos hb hQb)]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem actual_annular_kernel_identity (C QK QP Qn Qb k p n b : ℝ)
    (hQK : 0<QK) (hQP : 0<QP) (hQn : 0<Qn) (hQb : 0<Qb)
    (hk : 0<k) (hp : 0<p) (hn : 0<n) (hb : 0<b) :
    C*n*b^3/(k^2*p^2) = kernelCenter C QK QP Qn Qb *
      Real.exp (∑ i, kernelSlope i * kernelLogCoordinates QK QP Qn Qb k p n b i) := by
  rw [kernelLogCoordinates_exp _ _ _ _ _ _ _ _ hQK hQP hQn hQb hk hp hn hb]
  unfold kernelCenter
  field_simp

def fixedKernelCoefficient (X tau r : ℝ) (C D1 D2 : Ideal Eis) : ℝ :=
  X/(27*tau^2*(Ideal.absNorm C:ℝ)^2)*r^3*
    (Ideal.absNorm D1:ℝ)*(Ideal.absNorm D2:ℝ)^3

lemma source_kernel_argument_factor {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ)
    (c : Eis) (X tau r : ℝ) (D1 D2 n b : Ideal Eis) :
    (X/(27*tau^2*(Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ)^2))*
      r^3*(Ideal.absNorm (D1*n):ℝ)*(Ideal.absNorm (D2*b):ℝ)^3 =
    fixedKernelCoefficient X tau r (Ideal.span {c}*(∏ i, F.ideal i)) D1 D2 *
      (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3 /
      ((Ideal.absNorm K:ℝ)^2*(Ideal.absNorm (∏ i, S.ideal i):ℝ)^2) := by
  rw [reflected_conductor_norm]
  simp only [fixedKernelCoefficient,map_mul,Nat.cast_mul,mul_pow,div_eq_mul_inv,mul_inv_rev]
  ring

theorem source_kernel_argument_annuli {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ)
    (c : Eis) (X tau r : ℝ) (D1 D2 n b : Ideal Eis)
    (hn : n≠0) (hb : b≠0) (QK QP Qn Qb : ℝ)
    (hQK : 0<QK) (hQP : 0<QP) (hQn : 0<Qn) (hQb : 0<Qb) :
    (X/(27*tau^2*(Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ)^2))*
      r^3*(Ideal.absNorm (D1*n):ℝ)*(Ideal.absNorm (D2*b):ℝ)^3 =
    kernelCenter (fixedKernelCoefficient X tau r (Ideal.span {c}*(∏ i, F.ideal i)) D1 D2)
      QK QP Qn Qb * Real.exp (∑ i, kernelSlope i *
        kernelLogCoordinates QK QP Qn Qb (Ideal.absNorm K:ℝ)
          (Ideal.absNorm (∏ i, S.ideal i):ℝ) (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ) i) := by
  rw [source_kernel_argument_factor]
  have hn0 (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  apply actual_annular_kernel_identity _ _ _ _ _ _ _ _ _ hQK hQP hQn hQb
    (hn0 K hK.1) _ (hn0 n hn) (hn0 b hb)
  apply hn0
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (S.ideal i))

end
end SevenEighths.InverseReflectedPhase

end OAI
