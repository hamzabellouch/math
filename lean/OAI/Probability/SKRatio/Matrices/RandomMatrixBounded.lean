import Mathlib
import OAI.Probability.SKRatio.Gaussian.GaussianEmpirical
import OAI.Probability.SKRatio.Matrices.RandomMatrixNet

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKRatio.MatrixNet
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

def bilinearCoefficient {n : ℕ} (x y : Fin n → ℝ) (p : Fin n × Fin n) : ℝ :=
  if p.1 < p.2 then x p.1 * y p.2 + x p.2 * y p.1 else 0

lemma bilinearCoefficient_sq_le {n : ℕ} (x y : Fin n → ℝ) :
    ∑ p, bilinearCoefficient x y p ^ 2 ≤
      2 * (∑ i, x i^2) * (∑ i, y i^2) := by
  have hp (i j : Fin n) : bilinearCoefficient x y (i,j)^2 +
      bilinearCoefficient x y (j,i)^2 ≤ 2 * (x i^2*y j^2 + x j^2*y i^2) := by
    rcases lt_trichotomy i j with h | h | h
    · simp only [bilinearCoefficient, h, not_lt_of_ge h.le, ite_true, ite_false, zero_pow (by decide : (2:ℕ) ≠ 0), add_zero]
      nlinarith [sq_nonneg (x i*y j-x j*y i)]
    · subst j; simp only [bilinearCoefficient, lt_self_iff_false, ite_false, zero_pow (by decide : (2:ℕ) ≠ 0), add_zero]
      positivity
    · simp only [bilinearCoefficient, h, not_lt_of_ge h.le, ite_true, ite_false, zero_pow (by decide : (2:ℕ) ≠ 0), zero_add]
      nlinarith [sq_nonneg (x i*y j-x j*y i)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j))
  simp only [mul_add, Finset.sum_add_distrib] at hs
  rw [Finset.sum_comm (f := fun i j => bilinearCoefficient x y (j,i)^2)] at hs
  rw [Fintype.sum_prod_type]
  have he : ∑ i, ∑ j, 2*(x i^2*y j^2) = 2 * (∑ i, x i^2) * (∑ j, y j^2) := by
    calc
      _ = 2 * (∑ i, ∑ j, x i^2*y j^2) := by simp only [Finset.mul_sum]
      _ = 2 * ((∑ i, x i^2) * (∑ j, y j^2)) := by rw [Finset.sum_mul_sum]
      _ = _ := by ring
  have he' : ∑ i, ∑ j, 2*(x j^2*y i^2) = 2 * (∑ i, x i^2) * (∑ j, y j^2) := by
    rw [Finset.sum_comm]; exact he
  rw [he, he'] at hs
  linarith

lemma coupling_bilinear {n : ℕ} (x y : Fin n → ℝ) (g : Disorder n) :
    ∑ i, ∑ j, x i*coupling g i j*y j =
      ∑ e : Edge n, (x e.1.1*y e.1.2+x e.1.2*y e.1.1)*g e := by
  let F : Fin n × Fin n → ℝ := fun p =>
    if h : p.1 < p.2 then x p.1*y p.2*g ⟨p,h⟩ else 0
  let G : Fin n × Fin n → ℝ := fun p =>
    if h : p.1 < p.2 then x p.2*y p.1*g ⟨p,h⟩ else 0
  have hid (i j : Fin n) : x i*coupling g i j*y j = F (i,j)+G (j,i) := by
    dsimp [F,G,coupling]
    split_ifs with h₁ h₂ h₂ <;> try omega
    all_goals ring
  simp_rw [hid]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => G (j,i)), ← Finset.sum_add_distrib]
  simp_rw [←Finset.sum_add_distrib]
  rw [←Fintype.sum_prod_type (f := fun p => F p+G p)]
  apply Finset.sum_congr_set (s := {p : Fin n × Fin n | p.1<p.2})
  · intro p hp
    simp only [F,G,show p.1<p.2 from hp,dite_eq_left]
    ring
  · intro p hp
    simp [F,G,show ¬p.1<p.2 from hp]

lemma edgeCoefficient_sq_le {n : ℕ} (x y : Fin n → ℝ) :
    ∑ e : Edge n, (x e.1.1*y e.1.2+x e.1.2*y e.1.1)^2 ≤
      2*(∑ i, x i^2)*(∑ i, y i^2) := by
  have he : (∑ p, bilinearCoefficient x y p^2) =
      ∑ e : Edge n, (x e.1.1*y e.1.2+x e.1.2*y e.1.1)^2 := by
    apply Finset.sum_congr_set (s := {p : Fin n × Fin n | p.1<p.2})
    · intro p hp
      simp only [bilinearCoefficient,show p.1<p.2 from hp,ite_true]
    · intro p hp
      simp only [bilinearCoefficient,show ¬p.1<p.2 from hp,ite_false,zero_pow (by decide : (2:ℕ) ≠ 0)]
  rw [←he]
  exact bilinearCoefficient_sq_le x y

lemma coupling_inner {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (g : Disorder n) :
    inner (𝕜 := ℝ) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling g) x) y =
      ∑ e : Edge n, (y e.1.1*x e.1.2+y e.1.2*x e.1.1)*g e := by
  erw [real_inner_comm,Matrix.inner_toEuclideanCLM]
  change (∑ i, y i*∑ j, coupling g i j*x j) = _
  simp only [Finset.mul_sum,←mul_assoc]
  exact coupling_bilinear y x g

lemma subgaussian_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {c d : ℝ≥0} (hX : HasSubgaussianMGF X c μ) (hcd : c ≤ d) :
    HasSubgaussianMGF X d μ where
  integrable_exp_mul := hX.integrable_exp_mul
  mgf_le t := (hX.mgf_le t).trans (Real.exp_le_exp.mpr (by
    have h : (c:ℝ) ≤ d := hcd
    gcongr))

lemma bounded_zero_subgaussian {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hXm : AEMeasurable X μ)
    (T : ℝ≥0) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ T) (hmean : ∫ ω, X ω ∂μ = 0) :
    HasSubgaussianMGF X (T^2) μ := by
  have hb : ∀ᵐ ω ∂μ, X ω ∈ Icc (-(T:ℝ)) T := by
    filter_upwards [hbound] with ω hω
    exact abs_le.mp hω
  have hh := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hXm hb hmean
  convert hh using 1
  congr 1
  apply NNReal.coe_injective
  change (T:ℝ) = |(T:ℝ)-(-(T:ℝ))|/2
  rw [abs_of_nonneg (by linarith [T.coe_nonneg])]
  ring

lemma independent_subgaussian_linear {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (X : ι → Ω → ℝ) (hXi : iIndepFun X μ) {c : ℝ≥0}
    (hX : ∀ i, HasSubgaussianMGF (X i) c μ) (a : ι → ℝ) :
    HasSubgaussianMGF (fun ω => ∑ i, a i*X i ω) (∑ i, (NNReal.mk (a i^2) (sq_nonneg (a i)))*c) μ := by
  have hi := hXi.comp (fun i z => a i*z) (fun i => measurable_const.mul measurable_id)
  have hh := HasSubgaussianMGF.sum_of_iIndepFun hi (s := Finset.univ) (fun i _ => (hX i).const_mul (a i))
  exact hh

lemma bounded_matrix_inner_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 0<n)
    (X : Edge n → Ω → ℝ) (hXi : iIndepFun X μ) {T : ℝ≥0} (hT : 0<T)
    (hX : ∀ e, HasSubgaussianMGF (X e) (T^2) μ)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖≤1) (hy : ‖y‖≤1)
    {u : ℝ} (hu : 0≤u) :
    μ {ω | u ≤ |inner (𝕜 := ℝ)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling (fun e => X e ω/n)) x) y|} ≤
      2*ENNReal.ofReal (Real.exp (-u^2*(n:ℝ)^2/(4*(T:ℝ)^2))) := by
  let a : Edge n → ℝ := fun e => (y e.1.1*x e.1.2+y e.1.2*x e.1.1)/(n:ℝ)
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hcoef : ∑ e : Edge n, a e^2 ≤ 2/(n:ℝ)^2 := by
    dsimp only [a]
    simp only [div_pow,←Finset.sum_div]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have hh := edgeCoefficient_sq_le y x
    rw [←EuclideanSpace.real_norm_sq_eq,←EuclideanSpace.real_norm_sq_eq] at hh
    have hx2 : ‖x‖^2≤1 := by nlinarith [norm_nonneg x]
    have hy2 : ‖y‖^2≤1 := by nlinarith [norm_nonneg y]
    nlinarith [mul_le_mul hy2 hx2 (sq_nonneg ‖x‖) (by norm_num : (0:ℝ)≤1)]
  have hv : (∑ e : Edge n, (NNReal.mk (a e^2) (sq_nonneg (a e)))*T^2) ≤ Real.toNNReal (2*(T:ℝ)^2/(n:ℝ)^2) := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_sum,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_mk,←Finset.sum_mul,Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 2*(T:ℝ)^2/(n:ℝ)^2)]
    calc
      _ ≤ (2/(n:ℝ)^2)*(T:ℝ)^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ = _ := by ring
  have hh := subgaussian_abs_tail
    (subgaussian_mono (independent_subgaussian_linear X hXi hX a) hv) u hu
  have hid (ω : Ω) : inner (𝕜 := ℝ)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (coupling (fun e => X e ω/n)) x) y =
      ∑ e : Edge n, a e*X e ω := by
    rw [coupling_inner]
    apply Finset.sum_congr rfl
    intro e _
    dsimp only [a]
    ring
  simp_rw [hid]
  convert hh using 2
  congr 2
  rw [Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 2*(T:ℝ)^2/(n:ℝ)^2)]
  have htR : (T:ℝ) ≠ 0 := ne_of_gt hT
  field_simp
  ring

lemma bounded_matrix_opNorm_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 0<n)
    (X : Edge n → Ω → ℝ) (hXi : iIndepFun X μ) {T : ℝ≥0} (hT : 0<T)
    (hX : ∀ e, HasSubgaussianMGF (X e) (T^2) μ)
    {u : ℝ} (hu : 0≤u) :
    μ {ω | 2*u < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (coupling (fun e => X e ω/n))‖} ≤
      ENNReal.ofReal (2*(81:ℝ)^n*Real.exp (-u^2*(n:ℝ)^2/(4*(T:ℝ)^2))) := by
  have h := opNorm_tail_of_bilinear μ _ hu _
    (fun x y hx hy => bounded_matrix_inner_tail hn X hXi hT hX x y hx hy hu)
  convert h using 1
  rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
  simp only [ENNReal.ofReal_ofNat,ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤81)]
  ring

end SKRatio.MatrixNet

end
end

end OAI
