import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.CircuitParameters
import OAI.Probability.LogConcave.Numerics.CompileDeclaredRootNormalized

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree MeasureTheory Quadrature
open scoped Classical NNReal

variable {d : ℕ}

def MeanSize (lam q r σ : ℝ) : Prop :=
  0 < r ∧ r ≤ 1 ∧ 0 < σ ∧ lam*r^2 ≤ q ∧ lam*r ≤ q*σ

def SampleSize (lam q r η : ℝ) : Prop :=
  0 < r ∧ r ≤ 1 ∧ 0 < η ∧ η ≤ 1 ∧ lam*r^2 ≤ q*η

lemma MeanSize.nonneg {lam q r σ : ℝ} (hlam : 0 ≤ lam) (h : MeanSize lam q r σ) : 0 ≤ q :=
  (mul_nonneg hlam (sq_nonneg r)).trans h.2.2.2.1
lemma SampleSize.nonneg {lam q r η : ℝ} (hlam : 0 ≤ lam) (h : SampleSize lam q r η) : 0 ≤ q := by
  have hp := (mul_nonneg hlam (sq_nonneg r)).trans h.2.2.2.2
  exact nonneg_of_mul_nonneg_left hp h.2.2.1

lemma internal_meanSize {lam Q r R D A r' n : ℝ}
    (hlam : 0 ≤ lam) (hQ : 0 ≤ Q) (hr : 0 < r) (hr1 : r ≤ 1)
    (hR : 0 < R) (hD : 0 < D) (hA : 0 < A)
    (hl : lam*r^2 ≤ Q) (hlo : r*R ≤ r') (hhi : r' ≤ r)
    (hn : r*R/(2*D) ≤ n) :
    MeanSize lam (Q+4*D*lam*A/R) r' (declaredNoise n A) := by
  have hr' : 0 < r' := (mul_pos hr hR).trans_le hlo
  have hn0 : 0 < n := (div_pos (mul_pos hr hR) (by positivity)).trans_le hn
  have hτ : 0 < declaredNoise n A := by unfold declaredNoise; positivity
  have hloτ : r*R/(4*D*A) ≤ declaredNoise n A := by
    have hh := div_le_div_of_nonneg_right hn (show 0 ≤ 2*A by positivity)
    convert! hh using 1
    field_simp
    ring
  refine ⟨hr',hhi.trans hr1,hτ,?_,?_⟩
  · have he := (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr'.le hhi 2) hlam).trans hl
    exact he.trans (le_add_of_nonneg_right (by positivity))
  · have hh := mul_le_mul_of_nonneg_left hloτ (show 0 ≤ 4*D*lam*A/R by positivity)
    have hid : (4*D*lam*A/R)*(r*R/(4*D*A))=lam*r := by field_simp
    rw [hid] at hh
    have hrh := mul_le_mul_of_nonneg_left hhi hlam
    have hQt := mul_nonneg hQ hτ.le
    nlinarith

namespace CircuitParameters
variable (C : CircuitParameters)
lemma meanCenterBudget_small {lam q r σ : ℝ} (h : MeanSize lam q r σ) (hA : 0 ≤ C.A) :
    lam*C.meanCenterBudget r σ ≤ 2*C.A*q := by
  have hs : lam*r/σ ≤ q := (div_le_iff₀ h.2.2.1).2 h.2.2.2.2
  have hh := mul_le_mul_of_nonneg_left (add_le_add hs h.2.2.2.1) hA
  unfold meanCenterBudget
  convert! hh using 1 <;> ring

lemma sampleCenterBudget_small {lam q r η : ℝ} (hlam : 0 ≤ lam)
    (h : SampleSize lam q r η) (hA : 0 ≤ C.A) :
    lam*C.sampleCenterBudget r ≤ C.A*q := by
  have hq := h.nonneg hlam
  have he := h.2.2.2.2.trans (mul_le_of_le_one_right hq h.2.2.2.1)
  have hh := mul_le_mul_of_nonneg_left he hA
  unfold sampleCenterBudget
  convert! hh using 1
  ring

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeanTree Quadrature FinitePicard
open scoped Classical BigOperators NNReal

def fixedProbabilityBudget (n : ℕ) : ℝ :=
  (probabilityWeight_budget (n+1) (Nat.succ_pos n)).choose

def fixedHarmonicBudget (n : ℕ) : ℝ≥0 :=
  (harmonicWeight_budget (n+1) (Nat.succ_pos n)).choose

def fixedCenteringBudget (n : ℕ) : ℝ :=
  1+(∑i : Fin (n+1),∑j,|centeringWeight n i j|)+
      ∑j,|Quadrature.weight (probabilityNodes n) j 0 1|

lemma fixedProbabilityBudget_spec (n : ℕ) : 0≤fixedProbabilityBudget n ∧
    ∀{T h : ℝ},0<T → T<1 → 0<h →
      ∀i : ProbabilityNode T h (n+1),∑j,|probabilityWeight T h (n+1) i j|≤fixedProbabilityBudget n :=
  (probabilityWeight_budget (n+1) (Nat.succ_pos n)).choose_spec

lemma fixedCenteringBudget_spec (n : ℕ) : 0≤fixedCenteringBudget n ∧
    (∀i,∑j,|centeringWeight n i j|≤fixedCenteringBudget n) ∧
    (∑j,|Quadrature.weight (probabilityNodes n) j 0 1|≤fixedCenteringBudget n) := by
  have h₁ : 0≤∑i : Fin (n+1),∑j,|centeringWeight n i j| := by positivity
  have h₂ : 0≤∑j : Fin (n+1),|Quadrature.weight (probabilityNodes n) j 0 1| := by positivity
  refine ⟨by unfold fixedCenteringBudget; positivity,?_,?_⟩
  · intro i
    have he := Finset.single_le_sum (fun j (_ : j∈Finset.univ) =>
      show 0≤∑k,|centeringWeight n j k| by positivity) (Finset.mem_univ i)
    unfold fixedCenteringBudget
    linarith
  · unfold fixedCenteringBudget
    linarith

namespace CircuitParameters
variable (C : CircuitParameters)

def quadratureBudget : ℝ := ∑j,|terminalQuadratureWeight C.T C.h C.n j|
def derivativeBudget : ℝ := ∑j : Fin (C.m+1),|derivativeWeight (angleNodes C.m) j/C.ψ|
def actualA : ℝ :=
  1+2*fixedCenteringBudget C.nc*(C.quadratureBudget*C.derivativeBudget*
    (2*fixedProbabilityBudget C.n)+2)+4*fixedProbabilityBudget C.n+fixedHarmonicBudget C.n
def actualAf : ℝ := 1+fixedCenteringBudget C.nc+2*fixedProbabilityBudget C.n

lemma actualA_pos : 0<C.actualA := by
  have hP := (fixedProbabilityBudget_spec C.n).1
  have hB := (fixedCenteringBudget_spec C.nc).1
  have hQ : 0≤C.quadratureBudget := by unfold quadratureBudget; positivity
  have hS : 0≤C.derivativeBudget := by unfold derivativeBudget; positivity
  unfold actualA
  positivity
lemma actualAf_pos : 0<C.actualAf := by
  have hP := (fixedProbabilityBudget_spec C.n).1
  have hB := (fixedCenteringBudget_spec C.nc).1
  unfold actualAf
  positivity

lemma angle_mem (hψ : 0≤C.ψ) (j : Fin (C.m+1)) :
    C.ψ*angleNodes C.m j∈Set.Icc (0:ℝ) 1 := by
  have hj : 0≤angleNodes C.m j := by simp [angleNodes]
  have hv : C.v≤1 := by
    have hR : Real.sqrt (1-C.T^2)≤1 := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by norm_num,by nlinarith [sq_nonneg C.T]⟩
    nlinarith [C.angle_small]
  exact ⟨mul_nonneg hψ hj,(le_abs_self _).trans ((C.angle_bound j).trans hv)⟩

lemma meanTree_actual_weights {d : ℕ} {r σ : ℝ} (hr : 0<r) (hσ : 0<σ)
    (hψ : 0≤C.ψ) : weight (C.meanTree (d:=d) r σ)≤C.actualAf ∧
    centersBound (C.actualA*(r/σ+r^2)) (C.meanTree (d:=d) r σ) := by
  have hT0 : 0<C.T := by linarith [C.T_lower]
  have hP := fixedProbabilityBudget_spec C.n
  have hB := fixedCenteringBudget_spec C.nc
  have hP0 := hP.1
  have hB0 := hB.1
  have hQ : 0≤C.quadratureBudget := by unfold quadratureBudget; positivity
  have hS : 0≤C.derivativeBudget := by unfold derivativeBudget; positivity
  have hh := (harmonicWeight_budget (C.n+1) (Nat.succ_pos C.n)).choose_spec
  apply literalMean_weights hr hσ (by rw [abs_of_pos hT0]; exact C.T_upper.le)
    (by positivity : 0≤2*fixedProbabilityBudget C.n) (fixedHarmonicBudget C.n).coe_nonneg
    hQ hS hB.1 C.n C.m C.N C.nc C.Nc C.meanEndpoint
  · intro j
    have ht := probabilityNodeTime_mem hT0 C.T_upper C.h_pos (Nat.succ_pos C.n) j
    rw [abs_of_nonneg ht.1]
    exact ht.2.trans C.T_upper.le
  · intro a i
    exact reanchorWeight_budget _ (hP.2 hT0 C.T_upper C.h_pos) a i
  · intro k i
    exact hh _ (C.angle_mem hψ k).1 (C.angle_mem hψ k).2 i
  · exact le_rfl
  · exact le_rfl
  · exact hB.2.1
  · exact hB.2.2
  · unfold actualA
    have h := (fixedHarmonicBudget C.n).coe_nonneg
    linarith [hP.1]
  · unfold actualA
    have he : 0≤2*fixedCenteringBudget C.nc*
      (C.quadratureBudget*C.derivativeBudget*(2*fixedProbabilityBudget C.n)+2) := by positivity
    linarith
  · unfold actualAf
    linarith [hP.1]

lemma sampleTree_actual_weights {d : ℕ} {r η : ℝ} (hr : 0<r) (hη : 0<η) (hη1 : η≤1) :
    weight (C.sampleTree (d:=d) r η hη hη1)≤C.actualAf*r ∧
    centersBound (C.actualA*r^2) (C.sampleTree (d:=d) r η hη hη1) := by
  have hp := sampleCorrelation_properties hη hη1
  have hp0 : 0<sampleCorrelation η := by linarith [hp.1]
  have hP := fixedProbabilityBudget_spec C.n
  have hB := fixedCenteringBudget_spec C.nc
  have hP0 := hP.1
  have hB0 := hB.1
  have hQ : 0≤C.quadratureBudget := by unfold quadratureBudget; positivity
  have hS : 0≤C.derivativeBudget := by unfold derivativeBudget; positivity
  apply literalSample_weights hr hP.1 hp.1 (C.n+1) C.N (C.sampleEndpoint η hη hη1)
  · intro j
    have ht := probabilityNodeTime_mem hp0 hp.2.1 C.h_pos (Nat.succ_pos C.n) j
    rw [abs_of_nonneg ht.1]
    exact ht.2.trans hp.2.1.le
  · exact hP.2 hp0 hp.2.1 C.h_pos
  · unfold actualA
    have he : 0≤2*fixedCenteringBudget C.nc*
      (C.quadratureBudget*C.derivativeBudget*(2*fixedProbabilityBudget C.n)+2) := by positivity
    have hh := (fixedHarmonicBudget C.n).coe_nonneg
    linarith [hP.1]
  · unfold actualAf
    linarith [hB.1]

end CircuitParameters
end LogConcaveSampling.OracleCompiler

end

end

end OAI
