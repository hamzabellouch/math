import OAI.InformationTheory.Entanglement.EveBlocks
import OAI.InformationTheory.Entanglement.ScalarGap

namespace OAI

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory
namespace SecretKey
instance matrixMeasurableSpace (n m : Type*) : MeasurableSpace (Matrix n m ℂ) := borel _
instance matrixBorelSpace (n m : Type*) : BorelSpace (Matrix n m ℂ) := ⟨rfl⟩
open ChannelCompletion
variable {n : Type} [Fintype n] [DecidableEq n]
lemma traceNorm_neg (A : Mat n) : traceNorm (-A)=traceNorm A := by
  have h := traceNorm_unitary_left A (U := -1) (by simp)
  simpa only [Matrix.neg_mul,Matrix.one_mul] using h
lemma traceNorm_sub_le (A B : Mat n) : traceNorm (A-B)≤traceNorm A+traceNorm B := by
  simpa only [sub_eq_add_neg,traceNorm_neg] using traceNorm_add_le A (-B)
lemma traceNorm_sub_triangle (A B C : Mat n) :
    traceNorm (A-B)≤traceNorm (A-C)+traceNorm (B-C) := by
  have he : A-B=(A-C)-(B-C) := by abel
  rw [he]
  exact traceNorm_sub_le _ _
lemma trace_sub_reverse_le (A B : Mat n) :
    (Matrix.trace B).re-(Matrix.trace A).re≤traceNorm (A-B) := by
  have h := trace_re_le_traceNorm (B-A)
  simp only [Matrix.trace_sub,Complex.sub_re] at h
  rwa [show B-A=-(A-B) by abel,traceNorm_neg] at h

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
lemma integrable_traceNorm_sub {A B : Ω → Mat n}
    (hAm : Measurable A) (hBm : Measurable B)
    (hAp : ∀ x, (A x).PosSemidef) (hBp : ∀ x, (B x).PosSemidef)
    (hAi : Integrable (fun x => (Matrix.trace (A x)).re) μ)
    (hBi : Integrable (fun x => (Matrix.trace (B x)).re) μ) :
    Integrable (fun x => traceNorm (A x-B x)) μ := by
  apply (hAi.add hBi).mono' (continuous_traceNorm.measurable.comp (hAm.sub hBm)).aestronglyMeasurable
  filter_upwards [] with x
  change ‖traceNorm (A x-B x)‖ ≤ (Matrix.trace (A x)).re+(Matrix.trace (B x)).re
  rw [Real.norm_of_nonneg (traceNorm_nonneg _)]
  simpa only [traceNorm_of_psd (hAp x),traceNorm_of_psd (hBp x)] using traceNorm_sub_le (A x) (B x)

def halfDensity (σ : Mat n) : Mat n := (1/2 : ℂ) • σ
omit [Fintype n] [DecidableEq n] in
lemma halfDensity_psd {σ : Mat n} (hσ : σ.PosSemidef) : (halfDensity σ).PosSemidef :=
  hσ.smul (by rw [Complex.nonneg_iff]; norm_num : (0 : ℂ)≤1/2)
omit [DecidableEq n] in
lemma halfDensity_trace (σ : Mat n) : (Matrix.trace (halfDensity σ)).re=(Matrix.trace σ).re/2 := by
  simp only [halfDensity,Matrix.trace_smul,smul_eq_mul,Complex.mul_re]
  norm_num
  ring

def idealDensity (σ : Ω → Mat n) (i j : Fin 2) (x : Ω) : Mat n :=
  if i=j then halfDensity (σ x) else 0
def bitDistance (τ : Fin 2 → Fin 2 → Ω → Mat n) (σ : Ω → Mat n) (μ : Measure Ω) : ℝ :=
  ∑ i, ∑ j, ∫ x, traceNorm (τ i j x-idealDensity σ i j x) ∂μ

theorem matrix_density_gap (τ : Fin 2 → Fin 2 → Ω → Mat n) (σ : Ω → Mat n)
    (hτm : ∀ i j, Measurable (τ i j)) (hσm : Measurable σ)
    (hτp : ∀ i j x, (τ i j x).PosSemidef) (hσp : ∀ x, (σ x).PosSemidef)
    (hτi : ∀ i j, Integrable (fun x => (Matrix.trace (τ i j x)).re) μ)
    (hσi : Integrable (fun x => (Matrix.trace (σ x)).re) μ)
    (hτ1 : (∑ i, ∑ j, ∫ x, (Matrix.trace (τ i j x)).re ∂μ)=1)
    (hσ1 : (∫ x, (Matrix.trace (σ x)).re ∂μ)=1)
    (hc : ∀ x, fidelity (τ 0 0 x) (τ 1 1 x) ≤
      Real.sqrt ((Matrix.trace (τ 0 0 x)).re*(Matrix.trace (τ 0 1 x)).re)+
      Real.sqrt ((Matrix.trace (τ 1 0 x)).re*(Matrix.trace (τ 1 1 x)).re)+
      2*Real.sqrt ((Matrix.trace (τ 0 1 x)).re*(Matrix.trace (τ 1 0 x)).re)) :
    1/5≤bitDistance τ σ μ := by
  let p := fun i j x => (Matrix.trace (τ i j x)).re
  let P := fun i j => ∫ x, p i j x ∂μ
  let a := fun i => ∫ x, traceNorm (τ i i x-halfDensity (σ x)) ∂μ
  let q := ∫ x, traceNorm (τ 0 0 x-τ 1 1 x) ∂μ
  have pn (i j : Fin 2) (x : Ω) : 0≤p i j x :=
    (Complex.nonneg_iff.mp (hτp i j x).trace_nonneg).1
  have Pn (i j : Fin 2) : 0≤P i j := integral_nonneg (pn i j)
  have hnorm : P 0 0+P 0 1+P 1 0+P 1 1=1 := by
    simp only [Fin.sum_univ_two] at hτ1
    dsimp only [P,p]
    linarith
  have hmhalf : Measurable (fun x => halfDensity (σ x)) := by
    exact (measurable_const : Measurable (fun _ : Ω => (1/2 : ℂ))).smul hσm
  have hihalf : Integrable (fun x => (Matrix.trace (halfDensity (σ x))).re) μ := by
    simpa only [halfDensity_trace] using hσi.div_const 2
  have hai (i : Fin 2) := integrable_traceNorm_sub (hτm i i) hmhalf
    (hτp i i) (fun x => halfDensity_psd (hσp x)) (hτi i i) hihalf
  have hqi := integrable_traceNorm_sub (hτm 0 0) (hτm 1 1) (hτp 0 0) (hτp 1 1)
    (hτi 0 0) (hτi 1 1)
  have heq : bitDistance τ σ μ=P 0 1+P 1 0+a 0+a 1 := by
    unfold bitDistance idealDensity
    simp only [Fin.sum_univ_two,ite_true,show (0 : Fin 2)≠1 by decide,
      show (1 : Fin 2)≠0 by decide,ite_false,sub_zero]
    simp only [traceNorm_of_psd (hτp _ _ _)]
    dsimp only [a,P,p]
    ring
  have hq : q≤a 0+a 1 := by
    have h := integral_mono hqi ((hai 0).add (hai 1))
      (fun x => traceNorm_sub_triangle (τ 0 0 x) (τ 1 1 x) (halfDensity (σ x)))
    simp only [Pi.add_apply] at h
    rwa [integral_add (hai 0) (hai 1)] at h
  have hatrace (i : Fin 2) : 1/2-P i i≤a i := by
    have h := integral_mono (hihalf.sub (hτi i i)) (hai i)
      (fun x => trace_sub_reverse_le (τ i i x) (halfDensity (σ x)))
    simp only [Pi.sub_apply] at h
    rw [integral_sub hihalf (hτi i i)] at h
    simp only [halfDensity_trace,integral_div,hσ1] at h
    exact h
  have he : P 0 1+P 1 0≤bitDistance τ σ μ/2 := by
    rw [heq]
    have h0 := hatrace 0
    have h1 := hatrace 1
    linarith
  have hip (i j k l : Fin 2) := sqrt_product_integrable (hτi i j) (hτi k l) (pn i j) (pn k l)
  have hu := integral_mono (((hτi 0 0).add (hτi 1 1)).sub hqi |>.div_const 2)
    (((hip 0 0 0 1).add (hip 1 0 1 1)).add ((hip 0 1 1 0).const_mul 2))
    (fun x => (fidelity_lower (hτp 0 0 x) (hτp 1 1 x)).trans (hc x))
  simp only [Pi.add_apply,Pi.sub_apply] at hu
  have hsum : Integrable (fun x => p 0 0 x+p 1 1 x) μ := (hτi 0 0).add (hτi 1 1)
  have hroots : Integrable (fun x => Real.sqrt (p 0 0 x*p 0 1 x)+Real.sqrt (p 1 0 x*p 1 1 x)) μ :=
    (hip 0 0 0 1).add (hip 1 0 1 1)
  rw [integral_div,integral_sub hsum hqi,
    integral_add (hτi 0 0) (hτi 1 1),
    integral_add hroots ((hip 0 1 1 0).const_mul 2),
    integral_add (hip 0 0 0 1) (hip 1 0 1 1),integral_const_mul] at hu
  have bound (i j k l : Fin 2) := integral_sqrt_product_le (hτi i j) (hτi k l) (pn i j) (pn k l)
  have hf : (P 0 0+P 1 1-q)/2≤
      Real.sqrt (P 0 0*P 0 1)+Real.sqrt (P 1 0*P 1 1)+2*Real.sqrt (P 0 1*P 1 0) := by
    exact hu.trans (add_le_add (add_le_add (bound 0 0 0 1) (bound 1 0 1 1))
      (mul_le_mul_of_nonneg_left (bound 0 1 1 0) (by norm_num)))
  apply scalar_secret_bit_gap (Pn 0 0) (Pn 0 1) (Pn 1 0) (Pn 1 1) hnorm he _ hf
  rw [heq]
  linarith

end SecretKey

end

end OAI
