import Mathlib
import OAI.Probability.SKGap.Localization.RecipeCoefficientClosure

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary
variable {n M : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ]
namespace OrdinaryData

def normalizedPrimary (D : OrdinaryData n (Fin M) κ σ) (q : Fin M) :
    OrdinaryData n (Fin M) κ Unit where
  J:=D.J
  j:=D.j
  H:=D.H
  predecessor:=D.predecessor
  θ:=D.θ
  seed:=fun _ _=>(Real.sqrt (n:ℝ))⁻¹
  seedFunction:=fun _ _ _ u=>Real.tanh (u (.inl q))
  seedDerivative:=fun _ _ _ u=>(1-(Real.tanh (u (.inl q)))^2) • ContinuousLinearMap.proj (.inl q)
  auxFunction:=fun _ _ _ _=>0
  auxDerivative:=fun _ _ _ _=>0

lemma normalizedPrimary_source (D : OrdinaryData n (Fin M) κ σ) (q : Fin M) :
    (D.normalizedPrimary q).source 0=fun x i=>Real.tanh (D.H q x i)/Real.sqrt (n:ℝ) := by
  rw [source_eq]
  ext x i
  simp [sourceOf,normalizedPrimary,seedCoefficient,coefficient,localArgs,div_eq_mul_inv]

lemma normalizedPrimary_magnetization (D : OrdinaryData n (Fin M) κ σ) (q : Fin M)
    (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (hh : D.H q=fld j J h k) :
    (D.normalizedPrimary q).source 0=fun x i=>mag j J h (k+1) x i/Real.sqrt (n:ℝ) := by
  rw [normalizedPrimary_source,hh]
  rfl

lemma normalizedPrimary_Admissible (D : OrdinaryData n (Fin M) κ σ) (q : Fin M)
    (p : ℕ) (hp : p≤q.val) (N : ℕ) : (D.normalizedPrimary q).Admissible N p := by
  intro a ha l hl
  have hne : l≠q := by intro he; subst l; omega
  constructor
  · intro s; ext x i
    simp [seedPartial,localPartial,normalizedPrimary,partialAt,hne.symm]
  · intro b; ext x i
    simp [auxPartial,localPartial,normalizedPrimary,partialAt]

lemma normalizedPrimary_seed (D : OrdinaryData n (Fin M) κ σ) (q : Fin M) (hn : 0<n) :
    (∑s,vectorNorm ((D.normalizedPrimary q).seed s))=1 := by
  simp only [normalizedPrimary,Finset.univ_unique,Finset.sum_singleton]
  apply (sq_eq_sq₀ (vectorNorm_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
  rw [vectorNorm_sq]
  have hs : Real.sqrt (n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,inv_pow,one_pow]
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))

end OrdinaryData

lemma normalized_pair_cancel (hn : 0<n) (R U : VectorFields n) (a : Spin n→ℝ) (x : Spin n) :
    (Real.sqrt (n:ℝ)*a x)*(∑i,R x i*(U x i/Real.sqrt (n:ℝ)))=
      a x*(∑i,R x i*U x i) := by
  have hs : Real.sqrt (n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  simp only [div_eq_mul_inv,←mul_assoc,←Finset.sum_mul]
  field_simp

lemma scaledMean_size (hn : 0<n) (U : VectorFields n) (x : Spin n) {C : ℝ}
    (hC : 0≤C) (hU : vectorNorm (U x)≤C) :
    |Real.sqrt (n:ℝ)*siteMean U x|≤C := by
  apply (sq_le_sq₀ (abs_nonneg _) hC).mp
  rw [sq_abs,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
  exact (siteMean_square U x hn).trans (pow_le_pow_left₀ (vectorNorm_nonneg _) hU 2)

lemma scaledMean_difference (hn : 0<n) (U : VectorFields n) (x : Spin n) {C : ℝ}
    (hC : 0≤C) (hU : ‖derivativeMatrix U x‖≤C) :
    (∑i,(halfDiff i (fun y=>Real.sqrt (n:ℝ)*siteMean U y) x)^2)≤C^2 := by
  have H := (siteMean_derivative_square U x hn).trans
    ((sq_le_sq₀ (norm_nonneg _) hC).2 ((Primary.opNorm_le_frobenius _).trans hU))
  have he (i : Fin n) : halfDiff i (fun y=>Real.sqrt (n:ℝ)*siteMean U y) x=
      Real.sqrt (n:ℝ)*halfDiff i (siteMean U) x := by unfold halfDiff; ring
  simp only [he,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n),←Finset.mul_sum]
  convert H using 1
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
lemma tanh_segmentRegular (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (q : ι) :
    SegmentRegular H θ (fun _ u=>Real.tanh (u (.inl q)))
      (fun _ u=>(1-(Real.tanh (u (.inl q)))^2) • ContinuousLinearMap.proj (.inl q)) x 2 := by
  let L : Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ:=ContinuousLinearMap.proj (.inl q)
  have hL : ‖L‖≤1 := by
    apply L.opNorm_le_bound (by norm_num)
    intro u
    exact (norm_le_pi_norm u (.inl q)).trans_eq (by rw [one_mul])
  refine ⟨by norm_num,?_,?_,?_⟩
  · intro i k t ht
    exact (tanh_hasDerivAt _).comp_hasFDerivAt _ L.hasFDerivAt
  · intro i k t ht
    rw [norm_smul,Real.norm_eq_abs]
    have hv : |1-(Real.tanh ((localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)) (.inl q)))^2|≤1 :=
      (abs_of_pos (scalarVariance_pos _)).trans_le (scalarVariance_le_one _)
    exact (mul_le_mul hv hL (norm_nonneg _) (by norm_num)).trans (by norm_num)
  · intro i k t ht
    let u:=localArgs H θ x i
    let v:=localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)
    change ‖scalarVariance (v (.inl q)) • L-scalarVariance (u (.inl q)) • L‖≤_
    have he : scalarVariance (v (.inl q)) • L-scalarVariance (u (.inl q)) • L=
        (scalarVariance (v (.inl q))-scalarVariance (u (.inl q))) • L := by module
    rw [he,norm_smul,Real.norm_eq_abs]
    have hv:=scalarVariance_lipschitz (u (.inl q)) (v (.inl q))
    have hu : |v (.inl q)-u (.inl q)|≤‖v-u‖ := norm_le_pi_norm (v-u) (.inl q)
    calc
      _ ≤ 2*|v (.inl q)-u (.inl q)| := (mul_le_mul hv hL (norm_nonneg _) (by positivity)).trans_eq (by ring)
      _ ≤ 2*‖v-u‖ := mul_le_mul_of_nonneg_left hu (by norm_num)
      _ = _ := by dsimp only [u,v]; rw [add_sub_cancel_left]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma tanh_segmentValue (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (q : ι) :
    SegmentValue H θ (fun _ u=>Real.tanh (u (.inl q))) x 2 := by
  intro i k t ht
  exact (Real.abs_tanh_lt_one _).le.trans (by norm_num)

namespace OrdinaryData
variable {M : ℕ} {σ : Type*}
lemma normalizedPrimary_coefficientClass (D : OrdinaryData n (Fin M) κ σ)
    (q : Fin M) (N : ℕ) (x : Spin n) : (D.normalizedPrimary q).CoefficientClass N x 2 := by
  refine ⟨by norm_num,?_,?_,?_,?_⟩
  · intros
    exact tanh_segmentRegular D.H D.θ x q
  · intros
    exact (segmentRegular_const D.H D.θ x 0).mono (by norm_num)
  · intros
    exact tanh_segmentValue D.H D.θ x q
  · intro a ha b i k t ht
    norm_num [normalizedPrimary]
end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
