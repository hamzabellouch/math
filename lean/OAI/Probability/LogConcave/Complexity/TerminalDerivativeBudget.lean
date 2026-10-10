import Mathlib
import OAI.Probability.LogConcave.Sampling.MeanMaterialVector
import OAI.Probability.LogConcave.Numerics.LogMeshLength
import OAI.Probability.LogConcave.Sampling.Jet
import OAI.Probability.LogConcave.Numerics.BasisDerivative

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

def terminalDerivativeBudget (n d : ℕ) (lam : ℝ≥0) (r : ℝ) : ℝ :=
  (r*((lam:ℝ)*r)*Real.exp (Real.pi^2/4))*
    ((TensorSum.terminalQ n).val.momentBudget d 0 2).toReal

lemma terminalDerivativeBudget_nonneg (n d : ℕ) (lam : ℝ≥0) (r : ℝ) :
    0≤terminalDerivativeBudget n d lam r := by
  unfold terminalDerivativeBudget
  have h : 0≤r*((lam:ℝ)*r) := by nlinarith [sq_nonneg r,lam.coe_nonneg]
  positivity

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

include hlam in
lemma terminalActionChain_sq_uniform (hd : 1≤d) (n : ℕ) {a b : ℝ}
    (ha : 0≤a) (hb : b≤T) (t : ℝ) (ht : t∈Icc a b) :
    let μ := (interpolationLaw F x r T).prod (stdGaussian (Point d))
    let B := (terminalDerivativeBudget n d lam r*
      ((Real.sqrt (1-b^2))⁻¹)^(2*n))^2*d
    Integrable (fun p => ‖terminalActionChain hF x hr hl hT0 hT1 (n+1) (t,p)‖^2) μ ∧
      (∫p,‖terminalActionChain hF x hr hl hT0 hT1 (n+1) (t,p)‖^2 ∂μ)≤B := by
  dsimp only
  have hh := terminalActionChain_sq hF x hr hlam hl hT0 hT1 hd n
    ⟨t,ha.trans ht.1,ht.2.trans hb⟩
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply pow_le_pow_left₀ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (terminalDerivativeBudget_nonneg n d lam r)
  exact pow_le_pow_left₀ (by positivity)
    (inverse_sqrt_time_mono (ha.trans ht.1) ht.2 (hb.trans_lt hT1)) _

lemma terminal_cell_budget_cancel (n : ℕ) {a b h : ℝ} (ha : 0≤a)
    (hab : a≤b) (hb : b<1) (hh : 0≤h) (hc : b-a≤h*(1-b)) :
    ((b-a)^(n+1))^2*((terminalDerivativeBudget (n+1) d lam r*
      ((Real.sqrt (1-b^2))⁻¹)^(2*(n+1)))^2*d)≤
        (terminalDerivativeBudget (n+1) d lam r*h^(n+1))^2*d := by
  have he := cell_singularity_cancel ha hab le_rfl hb hh hc n
  have hA := terminalDerivativeBudget_nonneg (n+1) d lam r
  have hs : 0≤((Real.sqrt (1-b^2))⁻¹)^(2*(n+1)) := by positivity
  have he' : (b-a)^(n+1)*((Real.sqrt (1-b^2))⁻¹)^(2*(n+1))≤h^(n+1) := by
    simpa only [Nat.mul_add,Nat.mul_one] using he
  calc
    _ = ((terminalDerivativeBudget (n+1) d lam r)*
        ((b-a)^(n+1)*((Real.sqrt (1-b^2))⁻¹)^(2*(n+1))))^2*d := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg hA (mul_nonneg (pow_nonneg (sub_nonneg.mpr hab) _) hs))
        (mul_le_mul_of_nonneg_left he' hA) 2) (Nat.cast_nonneg _)

include hlam in

theorem terminal_derivative_cell_rms {I : Type*} [Fintype I] [DecidableEq I]
    (u : I → ℝ) (hu : Function.Injective u) (hun : ∀i,u i∈Icc (0:ℝ) 1)
    (n : ℕ) (hn : n+2≤Fintype.card I) (hd : 1≤d)
    {a b h t : ℝ} (ha : 0≤a) (hab : a<b) (hb : b≤T)
    (hh : 0≤h) (hc : b-a≤h*(1-b)) (ht : t∈Icc (0:ℝ) 1) :
    let J := terminalActionChain hF x hr hl hT0 hT1
    let μ := (interpolationLaw F x r T).prod (stdGaussian (Point d))
    let err := fun z => J 1 (a+(b-a)*t,z)-(b-a)⁻¹ •
      derivativeInterpolation u (fun i => J 0 (a+(b-a)*u i,z)) t
    Integrable (fun z => ‖err z‖^2) μ ∧
      (∫z,‖err z‖^2 ∂μ)≤2*(1+(∑i,|basisDerivative u i t|)^2)*
        (terminalDerivativeBudget (n+1) d lam r*h^(n+1))^2*d := by
  dsimp only
  let := interpolationLaw_probability hF x hr.le (by linarith) T
  let J := terminalActionChain hF x hr hl hT0 hT1
  have hm (s : ℝ) (hs : s∈Icc a (a+(b-a))) :=
    terminalActionChain_sq_uniform hF x hr hlam hl hT0 hT1 hd (n+1) ha hb s
      (by simpa only [add_sub_cancel] using hs)
  have hv := derivative_cell_error_rms u hu hun n hn J
    (fun k => (terminalActionChain_smooth hF x hr hl hT0 hT1 k).continuous)
    (terminalActionChain_hasDerivAt hF x hr hl hT0 hT1)
    (sub_pos.mpr hab) ht (by positivity)
    (fun s hs => (hm s hs).1) (fun s hs => (hm s hs).2)
  refine ⟨hv.1,hv.2.trans ?_⟩
  have he := terminal_cell_budget_cancel (d:=d) (lam:=lam) (r:=r) n ha hab.le
    (hb.trans_lt hT1) hh hc
  convert mul_le_mul_of_nonneg_left he (by positivity : 0≤2*(1+(∑i,|basisDerivative u i t|)^2)) using 1 <;> ring

include hlam in

theorem terminal_hermite_cell_rms {I : Type*} [Fintype I] [DecidableEq I]
    (u : I → ℝ) (hu : Function.Injective u) (i₀ : I) (hu0 : u i₀=0)
    (hun : ∀i,u i∈Icc (0:ℝ) 1) (n : ℕ) (hn : n+1≤Fintype.card I) (hd : 1≤d)
    {b h : ℝ} (hb0 : 0<b) (hb : b≤T) (hh : 0≤h) (hc : b≤h*(1-b)) :
    let J := terminalActionChain hF x hr hl hT0 hT1
    let μ := (interpolationLaw F x r T).prod (stdGaussian (Point d))
    let err := fun z => (∫t in (0:ℝ)..1,t⁻¹ • J 1 (b*t,z))-
      ∑i,(zeroHermiteWeight u i₀ i/b) • J 0 (b*u i,z)
    Integrable (fun z => ‖err z‖^2) μ ∧
      (∫z,‖err z‖^2 ∂μ)≤2*(1+(∑i,|zeroHermiteWeight u i₀ i|)^2)*
        (terminalDerivativeBudget (n+1) d lam r*h^(n+1))^2*d := by
  dsimp only
  let := interpolationLaw_probability hF x hr.le (by linarith) T
  let J := terminalActionChain hF x hr hl hT0 hT1
  have hm (s : ℝ) (hs : s∈Icc (0:ℝ) b) :=
    terminalActionChain_sq_uniform hF x hr hlam hl hT0 hT1 hd (n+1) le_rfl hb s hs
  have hv := zeroHermite_derivative_error_rms u hu i₀ hu0 hun n hn J
    (fun k => (terminalActionChain_smooth hF x hr hl hT0 hT1 k).continuous)
    (terminalActionChain_hasDerivAt hF x hr hl hT0 hT1)
    (terminalActionChain_first_zero hF x hr hlam hl hT0 hT1)
    hb0 (by positivity) (fun s hs => (hm s hs).1) (fun s hs => (hm s hs).2)
  refine ⟨hv.1,hv.2.trans ?_⟩
  have he := terminal_cell_budget_cancel (d:=d) (lam:=lam) (r:=r) n
    (a:=0) le_rfl hb0.le (hb.trans_lt hT1) hh (by simpa only [sub_zero] using hc)
  simp only [sub_zero] at he
  convert mul_le_mul_of_nonneg_left he (by positivity : 0≤2*(1+(∑i,|zeroHermiteWeight u i₀ i|)^2)) using 1 <;> ring
end LogConcaveSampling

end

end

end OAI
