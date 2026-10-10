import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.ReciprocalIteratedDerivativeBound

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

def coordinateDivergence (e : ι → E) (ρ : E → ℝ) (X : ι → E → ℝ) (x : E) : ℝ :=
  (ρ x)⁻¹ * ∑ i, fderiv ℝ (fun y => ρ y * X i y) x (e i)

theorem coordinateDivergence_mul (e : ι → E) (ρ f : E → ℝ) (X : ι → E → ℝ)
    (x : E) (hρ : DifferentiableAt ℝ ρ x) (hf : DifferentiableAt ℝ f x)
    (hX : ∀ i, DifferentiableAt ℝ (X i) x) (hρx : ρ x ≠ 0) :
    coordinateDivergence e ρ (fun i y => f y * X i y) x =
      f x * coordinateDivergence e ρ X x +
        ∑ i, fderiv ℝ f x (e i) * X i x := by
  have hprod (i : ι) : (fun y => ρ y * (f y * X i y)) =
      (fun y => f y * (ρ y * X i y)) := by funext y; ring
  unfold coordinateDivergence
  simp only [hprod, fderiv_fun_mul (d := fun y => ρ y * X _ y) hf (hρ.mul (hX _)),
    add_apply, smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsum : ∑ i, ρ x * X i x * fderiv ℝ f x (e i) =
      ρ x * ∑ i, fderiv ℝ f x (e i) * X i x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  field_simp

theorem coordinateDivergence_sub (e : ι → E) (ρ : E → ℝ) (X Y : ι → E → ℝ)
    (x : E) (hρ : DifferentiableAt ℝ ρ x)
    (hX : ∀ i, DifferentiableAt ℝ (X i) x)
    (hY : ∀ i, DifferentiableAt ℝ (Y i) x) :
    coordinateDivergence e ρ (fun i y => X i y - Y i y) x =
      coordinateDivergence e ρ X x - coordinateDivergence e ρ Y x := by
  simp only [coordinateDivergence, fderiv_fun_sub (f := fun y => ρ y * X _ y) (g := fun y => ρ y * Y _ y) (hρ.mul (hX _)) (hρ.mul (hY _)),
    sub_apply, Finset.sum_sub_distrib, mul_sub]

theorem coordinate_scalar_correction (e : ι → E) (ρ U f : E → ℝ)
    (X : ι → E → ℝ) (x : E) (n Λ : ℝ)
    (hρ : DifferentiableAt ℝ ρ x) (hU : DifferentiableAt ℝ U x)
    (hf : DifferentiableAt ℝ f x) (hX : ∀ i, DifferentiableAt ℝ (X i) x)
    (hρx : ρ x ≠ 0) (hΛ : Λ ≠ 0)
    (hden : n ^ 2 * U x ^ 2 + ∑ i, fderiv ℝ U x (e i) * X i x ≠ 0)
    (hfvalue : f x = (coordinateDivergence e ρ X x + Λ * U x) /
      (n ^ 2 * U x ^ 2 + ∑ i, fderiv ℝ U x (e i) * X i x)) :
    coordinateDivergence e ρ (fun i y => (1 - f y * U y) * X i y) x +
      Λ * (1 - Λ⁻¹ * (n ^ 2 * f x * U x -
        coordinateDivergence e ρ (fun i y => f y * X i y) x)) * U x = 0 := by
  have heq : (fun i y => (1 - f y * U y) * X i y) =
      (fun i y => X i y - U y * (f y * X i y)) := by
    funext i y; ring
  rw [heq, coordinateDivergence_sub e ρ X (fun i y => U y * (f y * X i y)) x hρ hX
    (fun i => hU.mul (hf.mul (hX i))),
    coordinateDivergence_mul e ρ U (fun i y => f y * X i y) x hρ hU (fun i => hf.mul (hX i)) hρx]
  have hsum : ∑ i, fderiv ℝ U x (e i) * (f x * X i x) =
      f x * ∑ i, fderiv ℝ U x (e i) * X i x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  have hfprod := (eq_div_iff hden).mp hfvalue
  field_simp
  nlinarith [hfprod]

theorem contDiff_coordinateDivergence (e : ι → E) (ρ : E → ℝ) (X : ι → E → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hX : ∀ i, ContDiff ℝ ∞ (X i))
    (hρne : ∀ x, ρ x ≠ 0) : ContDiff ℝ ∞ (coordinateDivergence e ρ X) := by
  apply (hρ.inv hρne).mul
  apply ContDiff.sum
  intro i _
  exact ((hρ.mul (hX i)).fderiv_right (by simp)).clm_apply contDiff_const

def scalarCorrectionDenominator (e : ι → E) (n : ℝ) (U : E → ℝ)
    (X : ι → E → ℝ) (x : E) : ℝ :=
  n ^ 2 * U x ^ 2 + ∑ i, fderiv ℝ U x (e i) * X i x

def scalarCorrectionRatio (e : ι → E) (ρ : E → ℝ) (n Λ : ℝ) (U : E → ℝ)
    (X : ι → E → ℝ) (x : E) : ℝ :=
  (coordinateDivergence e ρ X x + Λ * U x) / scalarCorrectionDenominator e n U X x

def scalarCorrectionB (e : ι → E) (ρ : E → ℝ) (n Λ : ℝ) (U : E → ℝ)
    (X : ι → E → ℝ) (x : E) : ℝ :=
  1 - scalarCorrectionRatio e ρ n Λ U X x * U x

def scalarCorrectionS (e : ι → E) (ρ : E → ℝ) (n Λ : ℝ) (U : E → ℝ)
    (X : ι → E → ℝ) (x : E) : ℝ :=
  1 - Λ⁻¹ * (n ^ 2 * scalarCorrectionRatio e ρ n Λ U X x * U x -
    coordinateDivergence e ρ (fun i y => scalarCorrectionRatio e ρ n Λ U X y * X i y) x)

theorem contDiff_scalarCorrectionDenominator (e : ι → E) (n : ℝ) (U : E → ℝ)
    (X : ι → E → ℝ) (hU : ContDiff ℝ ∞ U) (hX : ∀ i, ContDiff ℝ ∞ (X i)) :
    ContDiff ℝ ∞ (scalarCorrectionDenominator e n U X) := by
  apply (contDiff_const.mul (hU.pow 2)).add
  apply ContDiff.sum
  intro i _
  exact ((hU.fderiv_right (by simp)).clm_apply contDiff_const).mul (hX i)

theorem contDiff_scalarCorrectionRatio (e : ι → E) (ρ : E → ℝ) (n Λ : ℝ)
    (U : E → ℝ) (X : ι → E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hU : ContDiff ℝ ∞ U) (hX : ∀ i, ContDiff ℝ ∞ (X i))
    (hρne : ∀ x, ρ x ≠ 0)
    (hden : ∀ x, scalarCorrectionDenominator e n U X x ≠ 0) :
    ContDiff ℝ ∞ (scalarCorrectionRatio e ρ n Λ U X) := by
  exact ((contDiff_coordinateDivergence e ρ X hρ hX hρne).add
    (contDiff_const.mul hU)).div (contDiff_scalarCorrectionDenominator e n U X hU hX) hden

theorem scalar_correction (e : ι → E) (ρ : E → ℝ) (n Λ : ℝ)
    (U : E → ℝ) (X : ι → E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hU : ContDiff ℝ ∞ U) (hX : ∀ i, ContDiff ℝ ∞ (X i))
    (hρne : ∀ x, ρ x ≠ 0) (hΛ : Λ ≠ 0)
    (hden : ∀ x, scalarCorrectionDenominator e n U X x ≠ 0) :
    ContDiff ℝ ∞ (scalarCorrectionB e ρ n Λ U X) ∧
    ContDiff ℝ ∞ (scalarCorrectionS e ρ n Λ U X) ∧
    ∀ x, coordinateDivergence e ρ
      (fun i y => scalarCorrectionB e ρ n Λ U X y * X i y) x +
      Λ * scalarCorrectionS e ρ n Λ U X x * U x = 0 := by
  have hf := contDiff_scalarCorrectionRatio e ρ n Λ U X hρ hU hX hρne hden
  refine ⟨contDiff_const.sub (hf.mul hU), ?_, ?_⟩
  · exact contDiff_const.sub (contDiff_const.mul
      (((contDiff_const.mul hf).mul hU).sub (contDiff_coordinateDivergence e ρ _ hρ
        (fun i => hf.mul (hX i)) hρne)))
  · intro x
    exact coordinate_scalar_correction e ρ U _ X x n Λ
      (hρ.differentiable (by simp) x) (hU.differentiable (by simp) x)
      (hf.differentiable (by simp) x) (fun i => (hX i).differentiable (by simp) x)
      (hρne x) hΛ (hden x) rfl

def coordinateFlux (e : ι → E) (a : E → Matrix ι ι ℝ) (U : E → ℝ)
    (i : ι) (x : E) : ℝ :=
  ∑ j, a x i j * fderiv ℝ U x (e j)

theorem fderiv_quotient_apply (U v : E → ℝ) (x y : E)
    (hU : DifferentiableAt ℝ U x) (hv : DifferentiableAt ℝ v x) (hne : v x ≠ 0) :
    fderiv ℝ (fun z => U z / v z) x y =
      (v x * fderiv ℝ U x y - U x * fderiv ℝ v x y) / v x ^ 2 := by
  have hinv := (hasDerivAt_inv hne).comp_hasFDerivAt x hv.hasFDerivAt
  have hprod := hU.hasFDerivAt.mul hinv
  have hq : (fun z => U z / v z) = U * ((fun t : ℝ => t⁻¹) ∘ v) := by
    ext z
    simp [div_eq_mul_inv]
  rw [hq, hprod.fderiv]
  simp only [add_apply, smul_apply, Function.comp_apply, smul_eq_mul]
  field_simp
  ring

theorem coordinateFlux_quotient (e : ι → E) (a : E → Matrix ι ι ℝ)
    (U v : E → ℝ) (i : ι) (x : E)
    (hU : DifferentiableAt ℝ U x) (hv : DifferentiableAt ℝ v x) (hne : v x ≠ 0) :
    v x ^ 2 * coordinateFlux e a (fun y => U y / v y) i x =
      v x * coordinateFlux e a U i x - U x * coordinateFlux e a v i x := by
  simp only [coordinateFlux, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_quotient_apply U v x (e j) hU hv hne]
  field_simp

theorem coordinateFlux_pair_comm (e : ι → E) (a : E → Matrix ι ι ℝ)
    (U v : E → ℝ) (x : E) (ha : (a x).IsSymm) :
    (∑ i, fderiv ℝ v x (e i) * coordinateFlux e a U i x) =
      ∑ i, fderiv ℝ U x (e i) * coordinateFlux e a v i x := by
  simp only [coordinateFlux, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show a x j i = a x i j from congrFun (congrFun ha i) j]
  ring

theorem contDiff_coordinateFlux (e : ι → E) (a : E → Matrix ι ι ℝ)
    (U : E → ℝ) (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    (hU : ContDiff ℝ ∞ U) (i : ι) : ContDiff ℝ ∞ (coordinateFlux e a U i) := by
  apply ContDiff.sum
  intro j _
  exact (ha i j).mul ((hU.fderiv_right (by simp)).clm_apply contDiff_const)

theorem coordinate_conjugation_flux (e : ι → E) (ρ : E → ℝ)
    (a : E → Matrix ι ι ℝ) (U v : E → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    (hU : ContDiff ℝ ∞ U) (hv : ContDiff ℝ ∞ v)
    (hρne : ∀ x, ρ x ≠ 0) (hvne : ∀ x, v x ≠ 0) (hsymm : ∀ x, (a x).IsSymm)
    (x : E) :
    coordinateDivergence e ρ
      (fun i y => v y ^ 2 * coordinateFlux e a (fun z => U z / v z) i y) x =
      v x * coordinateDivergence e ρ (coordinateFlux e a U) x -
        U x * coordinateDivergence e ρ (coordinateFlux e a v) x := by
  have hfluxU := contDiff_coordinateFlux e a U ha hU
  have hfluxv := contDiff_coordinateFlux e a v ha hv
  have heq : (fun i y => v y ^ 2 * coordinateFlux e a (fun z => U z / v z) i y) =
      (fun i y => v y * coordinateFlux e a U i y - U y * coordinateFlux e a v i y) := by
    funext i y
    exact coordinateFlux_quotient e a U v i y (hU.differentiable (by simp) y)
      (hv.differentiable (by simp) y) (hvne y)
  rw [heq, coordinateDivergence_sub e ρ
    (fun i y => v y * coordinateFlux e a U i y)
    (fun i y => U y * coordinateFlux e a v i y) x
    (hρ.differentiable (by simp) x)
    (fun i => ((hv.mul (hfluxU i)).differentiable (by simp) x))
    (fun i => ((hU.mul (hfluxv i)).differentiable (by simp) x)),
    coordinateDivergence_mul e ρ v (coordinateFlux e a U) x
      (hρ.differentiable (by simp) x) (hv.differentiable (by simp) x)
      (fun i => ((hfluxU i).differentiable (by simp) x)) (hρne x),
    coordinateDivergence_mul e ρ U (coordinateFlux e a v) x
      (hρ.differentiable (by simp) x) (hU.differentiable (by simp) x)
      (fun i => ((hfluxv i).differentiable (by simp) x)) (hρne x),
    coordinateFlux_pair_comm e a U v x (hsymm x)]
  ring

def conjugatedDensity (e : ι → E) (ρ : E → ℝ) (a : E → Matrix ι ι ℝ)
    (s v : E → ℝ) (Λ : ℝ) (x : E) : ℝ :=
  s x * v x ^ 2 + Λ⁻¹ * v x * coordinateDivergence e ρ (coordinateFlux e a v) x

theorem coordinate_conjugated_equation (e : ι → E) (ρ : E → ℝ)
    (a : E → Matrix ι ι ℝ) (U v s : E → ℝ) (Λ : ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    (hU : ContDiff ℝ ∞ U) (hv : ContDiff ℝ ∞ v)
    (hρne : ∀ x, ρ x ≠ 0) (hvne : ∀ x, v x ≠ 0) (hsymm : ∀ x, (a x).IsSymm)
    (hΛ : Λ ≠ 0)
    (heq : ∀ x, coordinateDivergence e ρ (coordinateFlux e a U) x + Λ * s x * U x = 0)
    (x : E) :
    coordinateDivergence e ρ
      (fun i y => v y ^ 2 * coordinateFlux e a (fun z => U z / v z) i y) x +
      Λ * conjugatedDensity e ρ a s v Λ x * (U x / v x) = 0 := by
  rw [coordinate_conjugation_flux e ρ a U v hρ ha hU hv hρne hvne hsymm x]
  unfold conjugatedDensity
  have heqx : coordinateDivergence e ρ (coordinateFlux e a U) x = -Λ * s x * U x := by
    linarith [heq x]
  rw [heqx]
  field_simp [hΛ, hvne x]
  ring


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma norm_iteratedFDeriv_scalar_direction {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (v : E) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ f y v) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (k+1) f x‖ := by
  have h : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hb := norm_iteratedFDeriv_clm_apply_const (c := v) (x := x) h.contDiffAt
    (show (k : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))
  simpa only [norm_iteratedFDeriv_fderiv] using hb

lemma norm_iteratedFDeriv_scalar_sum (f : ι → E → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (h : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ h (fun y => ∑ i, f i y) x‖ ≤
      ∑ i, ‖iteratedFDeriv ℝ h (f i) x‖ := by
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => (hf i).contDiffAt.of_le
    (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h))))]
  exact norm_sum_le _ _

theorem scalar_denominator_jet_bound (e : ι → E) (U : E → ℝ) (X : ι → E → ℝ)
    (hU : ContDiff ℝ ∞ U) (hX : ∀ i, ContDiff ℝ ∞ (X i))
    (x : E) (h : ℕ) {n W C : ℝ} (hn : 1 ≤ n) (hW : 0 < W) (hC : 0 ≤ C)
    (hUj : ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j U x‖ ≤ C*n^(j+4)*W)
    (hXj : ∀ i, ∀ j ≤ h, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ C*n^(j+5)*W) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (scalarCorrectionDenominator e n U X) x‖ ≤
      (2^h*C*C*(1+∑ i, ‖e i‖))*n^(j+10)*W^2 := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hu : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => U y*U y) x‖ ≤
      (2^h*C*C)*n^(8+j)*W^2 := by
    simpa only [pow_zero,div_one,show 4+4=8 from rfl] using
      frequency_weighted_product_bound hU hU x h 4 4 0 hn hW hC hC
        (fun j hj => by simpa only [pow_zero,div_one,Nat.add_comm] using hUj j (by omega))
        (fun j hj => by simpa only [Nat.add_comm] using hUj j (by omega))
  have hdu (i : ι) : ContDiff ℝ ∞ (fun y => fderiv ℝ U y (e i)) :=
    (hU.fderiv_right (by simp)).clm_apply contDiff_const
  have hdU (i : ι) (j : ℕ) (hj : j ≤ h) :
      ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ U y (e i)) x‖ ≤
        (‖e i‖*C)*n^(5+j)*W := by
    calc
      _ ≤ ‖e i‖*‖iteratedFDeriv ℝ (j+1) U x‖ := norm_iteratedFDeriv_scalar_direction hU _ _ _
      _ ≤ ‖e i‖*(C*n^((j+1)+4)*W) :=
        mul_le_mul_of_nonneg_left (hUj (j+1) (by omega)) (norm_nonneg _)
      _ = _ := by rw [show j+1+4=5+j by omega]; ring
  have hp (i : ι) : ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ U y (e i)*X i y) x‖ ≤
        (2^h*(‖e i‖*C)*C)*n^(10+j)*W^2 := by
    simpa only [pow_zero,div_one,show 5+5=10 from rfl] using
      frequency_weighted_product_bound (hdu i) (hX i) x h 5 5 0 hn hW
        (mul_nonneg (norm_nonneg _) hC) hC
        (fun j hj => by simpa only [pow_zero,div_one] using hdU i j hj)
        (fun j hj => by simpa only [Nat.add_comm] using hXj i j hj)
  intro j hj
  have hcj : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
  have hsc : ContDiff ℝ ∞ (fun y => n^2*(U y*U y)) := contDiff_const.mul (hU.mul hU)
  have hsum : ContDiff ℝ ∞ (fun y => ∑ i, fderiv ℝ U y (e i)*X i y) :=
    ContDiff.sum (fun i _ => (hdu i).mul (hX i))
  have he : scalarCorrectionDenominator e n U X =
      fun y => n^2*(U y*U y)+(∑ i, fderiv ℝ U y (e i)*X i y) := by
    funext y; simp only [scalarCorrectionDenominator,pow_two]
  rw [he]
  calc
    _ = ‖iteratedFDeriv ℝ j (fun y => n^2*(U y*U y)) x +
        iteratedFDeriv ℝ j (fun y => ∑ i, fderiv ℝ U y (e i)*X i y) x‖ := by
      rw [fun_iteratedFDeriv_add_apply ((hsc.of_le hcj).contDiffAt) ((hsum.of_le hcj).contDiffAt)]
    _ ≤ ‖iteratedFDeriv ℝ j (fun y => n^2*(U y*U y)) x‖ +
        ∑ i, ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ U y (e i)*X i y) x‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl
        (norm_iteratedFDeriv_scalar_sum _ (fun i => (hdu i).mul (hX i)) j x))
    _ = n^2*‖iteratedFDeriv ℝ j (fun y => U y*U y) x‖ +
        ∑ i, ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ U y (e i)*X i y) x‖ := by
      rw [show (fun y => n^2*(U y*U y)) = (fun y => n^2 • (U y*U y)) by rfl,
        iteratedFDeriv_const_smul_apply' ((hU.mul hU).contDiffAt.of_le hcj),norm_smul,
        Real.norm_eq_abs,abs_of_nonneg (sq_nonneg n)]
    _ ≤ n^2*((2^h*C*C)*n^(8+j)*W^2)+
        ∑ i, (2^h*(‖e i‖*C)*C)*n^(10+j)*W^2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left (hu j hj) (sq_nonneg _))
        (Finset.sum_le_sum fun i _ => hp i j hj)
    _ = _ := by
      have hs : (∑ i, (2^h*(‖e i‖*C)*C)*n^(10+j)*W^2) =
          (2^h*C*C)*n^(10+j)*W^2*(∑ i, ‖e i‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hs]
      simp only [pow_add]
      ring

lemma constant_product_jet_bound {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) (h : ℕ)
    {F G : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y*g y) x‖ ≤ 2^h*F*G := by
  intro j hj
  have hb := geometric_product_jet_bound hf hg x j (R:=1) (S:=1) hF hG
    zero_le_one zero_le_one
    (fun i hi => by simpa only [one_pow,mul_one] using hfj i (hi.trans hj))
    (fun i hi => by simpa only [one_pow,mul_one] using hgj i (hi.trans hj))
  calc
    _ ≤ F*G*(1+1)^j := hb
    _ ≤ F*G*(1+1)^h := by gcongr; norm_num
    _ = _ := by norm_num; ring

theorem coordinate_divergence_jet_bound (e : ι → E) (ρ : E → ℝ) (Z : ι → E → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hρne : ∀ y, ρ y ≠ 0)
    (hZ : ∀ i, ContDiff ℝ ∞ (Z i)) (x : E) (h : ℕ)
    {C F : ℝ} (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hρj : ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j ρ x‖ ≤ C)
    (hρij : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => (ρ y)⁻¹) x‖ ≤ C)
    (hZj : ∀ i, ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j (Z i) x‖ ≤ F) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (coordinateDivergence e ρ Z) x‖ ≤
      (2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F := by
  have hρZ (i : ι) : ContDiff ℝ ∞ (fun y => ρ y*Z i y) := hρ.mul (hZ i)
  have hp (i : ι) := constant_product_jet_bound hρ (hZ i) x (h+1) hC hF hρj (hZj i)
  have hdf (i : ι) : ContDiff ℝ ∞ (fun y => fderiv ℝ (fun z => ρ z*Z i z) y (e i)) :=
    ((hρZ i).fderiv_right (by simp)).clm_apply contDiff_const
  have hsum : ContDiff ℝ ∞ (fun y => ∑ i, fderiv ℝ (fun z => ρ z*Z i z) y (e i)) :=
    ContDiff.sum (fun i _ => hdf i)
  have hs : ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (fun y => ∑ i, fderiv ℝ (fun z => ρ z*Z i z) y (e i)) x‖ ≤
        (∑ i, ‖e i‖)*(2^(h+1)*C*F) := by
    intro j hj
    calc
      _ ≤ ∑ i, ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ (fun z => ρ z*Z i z) y (e i)) x‖ :=
        norm_iteratedFDeriv_scalar_sum _ hdf j x
      _ ≤ ∑ i, ‖e i‖*(2^(h+1)*C*F) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (norm_iteratedFDeriv_scalar_direction (hρZ i) (e i) j x).trans
          (mul_le_mul_of_nonneg_left (hp i (j+1) (by omega)) (norm_nonneg _))
      _ = _ := by rw [Finset.sum_mul]
  have hb := constant_product_jet_bound (hρ.inv hρne) hsum x h hC
    (show 0 ≤ (∑ i, ‖e i‖)*(2^(h+1)*C*F) by positivity) hρij hs
  intro j hj
  apply (hb j hj).trans_eq
  rw [show 2*h+1=h+(h+1) by omega,pow_add]
  ring

theorem scalar_denominator_lower {n W u q : ℝ} {B : ℕ} (hn : 0 < n)
    (hW : 0 < W) (hq : 0 ≤ q)
    (hjet : W/n^B ≤ |u|+Real.sqrt q/n) :
    n^2*W^2/(2*n^(2*B)) ≤ n^2*u^2+q := by
  have h0 : 0 ≤ n*W/n^B := by positivity
  have hlin : n*W/n^B ≤ n*|u|+Real.sqrt q := by
    calc
      n*W/n^B = n*(W/n^B) := by ring
      _ ≤ n*(|u|+Real.sqrt q/n) := mul_le_mul_of_nonneg_left hjet hn.le
      _ = n*|u|+Real.sqrt q := by field_simp
  have hs := mul_self_le_mul_self h0 hlin
  have hsqrt := Real.sq_sqrt hq
  have hsqabs := sq_abs u
  have hsplit := sq_nonneg (n*|u|-Real.sqrt q)
  have ht : (n*W/n^B)^2 ≤ 2*(n^2*u^2+q) := by
    nlinarith [mul_nonneg (sq_nonneg n) (show 0 ≤ u^2 by positivity)]
  have he : n^2*W^2/(2*n^(2*B)) = (n*W/n^B)^2/2 := by
    rw [pow_mul]; field_simp; ring
  rw [he]
  linarith

theorem scalar_correction_error_from_quotients
    (e : ι → E) (ρ U : E → ℝ) (X : ι → E → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hρne : ∀ y, ρ y ≠ 0)
    (hU : ContDiff ℝ ∞ U) (hX : ∀ i, ContDiff ℝ ∞ (X i))
    {n : ℝ} (hn : 1 ≤ n)
    (hden : ∀ y, scalarCorrectionDenominator e n U X y ≠ 0)
    (x : E) (h : ℕ) {C F : ℝ} (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hρj : ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j ρ x‖ ≤ C)
    (hρij : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => (ρ y)⁻¹) x‖ ≤ C)
    (hqU : ∀ j ≤ h, ‖iteratedFDeriv ℝ j
      (fun y => scalarCorrectionRatio e ρ n (n*(n+2)) U X y*U y) x‖ ≤ F)
    (hqX : ∀ i, ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j
      (fun y => scalarCorrectionRatio e ρ n (n*(n+2)) U X y*X i y) x‖ ≤ F) :
    ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (fun y => scalarCorrectionB e ρ n (n*(n+2)) U X y-1) x‖ +
      ‖iteratedFDeriv ℝ j (fun y => scalarCorrectionS e ρ n (n*(n+2)) U X y-1) x‖ ≤
      (2+2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F := by
  let f := scalarCorrectionRatio e ρ n (n*(n+2)) U X
  have hf : ContDiff ℝ ∞ f := contDiff_scalarCorrectionRatio e ρ n (n*(n+2)) U X
    hρ hU hX hρne hden
  let Z : ι → E → ℝ := fun i y => f y*X i y
  have hZ (i : ι) : ContDiff ℝ ∞ (Z i) := hf.mul (hX i)
  have hd := contDiff_coordinateDivergence e ρ Z hρ hZ hρne
  have hq := hf.mul hU
  have hdiv := coordinate_divergence_jet_bound e ρ Z hρ hρne hZ x h hC hF hρj hρij hqX
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hΛ : 0 < n*(n+2) := by positivity
  have hΛ1 : 1 ≤ n*(n+2) := by nlinarith
  have hnratio : (n*(n+2))⁻¹*n^2 ≤ 1 := by
    rw [← div_eq_inv_mul,div_le_one hΛ]
    nlinarith
  have hΛinv : (n*(n+2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ1
  have hCb : 0 ≤ 2^(2*h+1)*C*C*(∑ i, ‖e i‖) := by positivity
  intro j hj
  have hj' : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
  have heb : (fun y => scalarCorrectionB e ρ n (n*(n+2)) U X y-1) =
      fun y => -(f y*U y) := by funext y; dsimp only [scalarCorrectionB,f]; ring
  have hes : (fun y => scalarCorrectionS e ρ n (n*(n+2)) U X y-1) =
      fun y => -((n*(n+2))⁻¹ • (n^2 • (f y*U y)-coordinateDivergence e ρ Z y)) := by
    funext y; dsimp only [scalarCorrectionS,f,Z,smul_eq_mul]; ring
  have hb : ‖iteratedFDeriv ℝ j (fun y => scalarCorrectionB e ρ n (n*(n+2)) U X y-1) x‖ ≤ F := by
    rw [heb]
    change ‖iteratedFDeriv ℝ j (-(fun y => f y*U y)) x‖ ≤ F
    rw [iteratedFDeriv_neg_apply,norm_neg]
    exact hqU j hj
  have hs : ‖iteratedFDeriv ℝ j (fun y => scalarCorrectionS e ρ n (n*(n+2)) U X y-1) x‖ ≤
      F+(2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F := by
    have hz : ContDiff ℝ ∞ (fun y => n^2 • (f y*U y)-coordinateDivergence e ρ Z y) :=
      (hq.const_smul (n^2)).sub hd
    rw [hes]
    change ‖iteratedFDeriv ℝ j (-(fun y => (n*(n+2))⁻¹ •
      (n^2 • (f y*U y)-coordinateDivergence e ρ Z y))) x‖ ≤ _
    rw [iteratedFDeriv_neg_apply,norm_neg,iteratedFDeriv_const_smul_apply' (hz.contDiffAt.of_le hj'),
      norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hΛ),
      fun_iteratedFDeriv_sub_apply ((hq.const_smul (n^2)).contDiffAt.of_le hj') (hd.contDiffAt.of_le hj')]
    calc
      _ ≤ (n*(n+2))⁻¹*(‖iteratedFDeriv ℝ j (fun y => n^2 • (f y*U y)) x‖+
          ‖iteratedFDeriv ℝ j (coordinateDivergence e ρ Z) x‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hΛ.le)
      _ = (n*(n+2))⁻¹*(n^2*‖iteratedFDeriv ℝ j (fun y => f y*U y) x‖+
          ‖iteratedFDeriv ℝ j (coordinateDivergence e ρ Z) x‖) := by
        rw [iteratedFDeriv_const_smul_apply' (hq.contDiffAt.of_le hj'),norm_smul,
          Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      _ ≤ (n*(n+2))⁻¹*(n^2*F+(2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left (hqU j hj) (sq_nonneg _)) (hdiv j hj))
          (inv_nonneg.mpr hΛ.le)
      _ = ((n*(n+2))⁻¹*n^2)*F + (n*(n+2))⁻¹*((2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F) := by ring
      _ ≤ _ := add_le_add
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hnratio hF)
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hΛinv (mul_nonneg hCb hF))
  calc
    _ ≤ F+(F+(2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F) := add_le_add hb hs
    _ = _ := by ring

theorem quantitative_scalar_correction_jets
    (e : ι → E) (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρne : ∀ y, ρ y ≠ 0)
    (h B : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ K > 0, ∀ (n : ℝ), 1 ≤ n → ∀ (D : ℕ) (U : E → ℝ) (X : ι → E → ℝ),
      ContDiff ℝ ∞ U → (∀ i, ContDiff ℝ ∞ (X i)) →
      (∀ y, scalarCorrectionDenominator e n U X y ≠ 0) →
      ∀ (x : E) (W : ℝ), 0 < W →
      W^2/(2*n^(2*B)) ≤ scalarCorrectionDenominator e n U X x →
      (∀ j ≤ h+2, ‖iteratedFDeriv ℝ j U x‖ ≤ C*n^(j+4)*W) →
      (∀ i, ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ C*n^(j+5)*W) →
      (∀ j ≤ h+1, ‖iteratedFDeriv ℝ j
        (fun y => coordinateDivergence e ρ X y+n*(n+2)*U y) x‖ ≤ C*n^4/(n^D)*W) →
      (∀ j ≤ h+1, ‖iteratedFDeriv ℝ j ρ x‖ ≤ C) →
      (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => (ρ y)⁻¹) x‖ ≤ C) →
      ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j (fun y => scalarCorrectionB e ρ n (n*(n+2)) U X y-1) x‖ +
        ‖iteratedFDeriv ℝ j (fun y => scalarCorrectionS e ρ n (n*(n+2)) U X y-1) x‖ ≤
        K*n^((2*B+21)*(h+2)+10)/(n^D) := by
  let Cd : ℝ := 2^(h+1)*C*C*(1+∑ i, ‖e i‖)
  let A : ℝ := 2^(h+1)*C*C
  let Kq : ℝ := 2*A*((h+1).factorial:ℝ)^2*(1+max 1 (2*Cd))^(h+1)
  let Kv : ℝ := 2+2^(2*h+1)*C*C*(∑ i, ‖e i‖)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hKq : 0 < Kq := by
    have hc : 0 < (1+max 1 (2*Cd)) := by have := le_max_left (1:ℝ) (2*Cd); linarith
    dsimp only [Kq]
    positivity
  have hKv : 0 < Kv := by dsimp only [Kv]; positivity
  refine ⟨Kv*Kq, mul_pos hKv hKq, ?_⟩
  intro n hn D U X hU hX hden x W hW hx hUj hXj hRj hρj hρij j hj
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  let R : E → ℝ := fun y => coordinateDivergence e ρ X y+n*(n+2)*U y
  let d := scalarCorrectionDenominator e n U X
  have hR : ContDiff ℝ ∞ R :=
    (contDiff_coordinateDivergence e ρ X hρ hX hρne).add (contDiff_const.mul hU)
  have hd : ContDiff ℝ ∞ d := contDiff_scalarCorrectionDenominator e n U X hU hX
  have hRj' : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k R x‖ ≤ C*n^(4+k)/(n^D)*W := by
    intro k hk
    apply (hRj k hk).trans
    gcongr
    omega
  have hUj' : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k U x‖ ≤ C*n^(4+k)*W := by
    intro k hk
    simpa only [Nat.add_comm] using hUj k (by omega)
  have hXj' (i : ι) : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k (X i) x‖ ≤ C*n^(5+k)*W := by
    intro k hk
    simpa only [Nat.add_comm] using hXj i k hk
  have hdj : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k d x‖ ≤ Cd*n^(k+10)*W^2 :=
    scalar_denominator_jet_bound e U X hU hX x (h+1) hn hW hC.le
      (fun k hk => hUj k (by omega)) hXj
  have hRU := frequency_weighted_product_bound hR hU x (h+1) 4 4 D hn hW hC.le hC.le hRj' hUj'
  have hRX (i : ι) := frequency_weighted_product_bound hR (hX i) x (h+1) 4 5 D hn hW hC.le hC.le hRj' (hXj' i)
  have hqU := frequency_weighted_quotient_uniform (hR.mul hU) hd hden x (h+1) B 8 D hn hW hA.le hx hRU
    (fun k _ hk => hdj k hk)
  have hqX (i : ι) := frequency_weighted_quotient_uniform (hR.mul (hX i)) hd hden x (h+1) B 9 D hn hW hA.le hx (hRX i)
    (fun k _ hk => hdj k hk)
  let T : ℕ := 9+2*B+(2*B+11)*(h+1)
  let F : ℝ := Kq*n^T/(n^D)
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hqu : ∀ k ≤ h, ‖iteratedFDeriv ℝ k
      (fun y => scalarCorrectionRatio e ρ n (n*(n+2)) U X y*U y) x‖ ≤ F := by
    intro k hk
    have he : (fun y => scalarCorrectionRatio e ρ n (n*(n+2)) U X y*U y) =
        fun y => (R y*U y)/d y := by
      funext y
      dsimp only [scalarCorrectionRatio,R,d]
      ring
    rw [he]
    apply (hqU k (by omega)).trans
    change Kq*n^(8+2*B+(2*B+11)*(h+1))/(n^D) ≤ Kq*n^T/(n^D)
    gcongr
    dsimp only [T]; omega
  have hqx : ∀ i, ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k
      (fun y => scalarCorrectionRatio e ρ n (n*(n+2)) U X y*X i y) x‖ ≤ F := by
    intro i k hk
    have he : (fun y => scalarCorrectionRatio e ρ n (n*(n+2)) U X y*X i y) =
        fun y => (R y*X i y)/d y := by
      funext y
      dsimp only [scalarCorrectionRatio,R,d]
      ring
    rw [he]
    exact hqX i k hk
  have hb := scalar_correction_error_from_quotients e ρ U X hρ hρne hU hX hn hden x h hC.le hF hρj hρij hqu hqx j hj
  apply hb.trans
  change Kv*(Kq*n^T/(n^D)) ≤ Kv*Kq*n^((2*B+21)*(h+2)+10)/(n^D)
  rw [show Kv*(Kq*n^T/(n^D))=Kv*Kq*n^T/(n^D) by ring]
  gcongr
  dsimp only [T]; nlinarith



end YauCounterexamples
end

end OAI
