import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.CircuitD

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

lemma kernel_error_factor {l B D A c p q f u : ℝ}
    (_ : 0≤l) (_ : 0≤B) (_ : 0≤D) (_ : 0≤A) (hc : 0≤c)
    (hp0 : 0≤p) (hq0 : 0≤q) (hf0 : 0≤f) (hu0 : 0≤u)
    (hp : p≤A*B*D) (hq : q≤A*B*D)
    (hf : f≤A*l*(c+1)*B*D) (hu : u≤c*l) :
    2*(2*u)^2*(32*p^2+2*q^2)+2*f^2 ≤
      300*((c+1)*A*l*B*D)^2 := by
  have hpp := pow_le_pow_left₀ hp0 hp 2
  have hqq := pow_le_pow_left₀ hq0 hq 2
  have hff := pow_le_pow_left₀ hf0 hf 2
  have huu := pow_le_pow_left₀ hu0 hu 2
  have hinside : 32*p^2+2*q^2≤34*(A*B*D)^2 := by linarith
  have hmul := mul_le_mul (by nlinarith : 2*(2*u)^2≤8*(c*l)^2)
    hinside (by positivity : 0≤32*p^2+2*q^2) (by positivity : 0≤8*(c*l)^2)
  have hc' : c^2≤(c+1)^2 := by nlinarith
  have hlast := mul_le_mul_of_nonneg_right hc' (show 0≤272*(A*l*B*D)^2 by positivity)
  nlinarith [sq_nonneg ((c+1)*A*l*B*D)]

def probabilityNormalizedTerm (d k n : ℕ) (h : ℝ) : ℝ :=
  (1+Real.log ((d:ℝ)+1))^k*(2*h)^(n+1)

lemma probabilityNormalizedTerm_nonneg (d k n : ℕ) {h : ℝ} (hh : 0≤h) :
    0≤probabilityNormalizedTerm d k n h := by
  unfold probabilityNormalizedTerm
  have hl : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) d])
  positivity

lemma probabilityRmsBudget_normalized {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam A : ℝ≥0) {r h C : ℝ} (hr : 0≤r) (hh : 0≤h) (hC : 0≤C)
    (hL : (lam:ℝ)*r≤1) (k n N : ℕ) :
    probabilityRmsBudget F x lam A r h C k n N ≤
      (4*C*((lam:ℝ)*r^2)*probabilityNormalizedTerm d k n h+
        (A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(2*circuitGrowthConstant*r))*circuitD F x := by
  have hds := sqrt_le_circuitD F x
  have hp := probabilityInitialRms_growth F x lam hr hL
  have h₁ := mul_le_mul_of_nonneg_left hds
    (show 0≤4*C*((lam:ℝ)*r^2)*probabilityNormalizedTerm d k n h by
      positivity [probabilityNormalizedTerm_nonneg d k n hh])
  have h₂ := mul_le_mul_of_nonneg_left hp
    (show 0≤2*(A*probabilityMeanLipschitz lam r:ℝ≥0)^N by positivity)
  dsimp [probabilityRmsBudget, probabilityNormalizedTerm] at *
  nlinarith

def harmonicNormalizedTerm (n : ℕ) (R z : ℝ) : ℝ :=
  4*(|z|^(n+1)/(n.factorial:ℝ))*(R⁻¹)^(2*(n+1))*Real.sqrt (harmonicMeanBudget (n+1))

lemma harmonicNormalizedTerm_nonneg (n : ℕ) {R z : ℝ} (hR : 0≤R) :
    0≤harmonicNormalizedTerm n R z := by unfold harmonicNormalizedTerm; positivity

lemma harmonicRmsBudget_normalized {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (A : ℝ≥0) {r R t z C : ℝ}
    (hr : 0≤r) (hr1 : r≤1) (hR : 0<R) (hz : 0≤z) (hC : 0≤C)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1) (ht0 : 0≤t) (ht1 : t<1) (n N : ℕ) :
    harmonicRmsBudget F x lam A r R t z C n N ≤
      (C*((lam:ℝ)*r^2)*harmonicNormalizedTerm n R z+
        (A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(2*circuitGrowthConstant*r))*circuitD F x := by
  have hD := circuitD_nonneg F x
  have hsqrtD : Real.sqrt d≤circuitD F x := sqrt_le_circuitD F x
  have hm := harmonicStationaryMoment_growth hF x hr hr1 hl hL ht0 ht1
  have hms : Real.sqrt (harmonicStationaryMoment F x r t)≤2*circuitGrowthConstant*circuitD F x := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity [circuitGrowthConstant_pos],?_⟩
    nlinarith
  let E := 2*C*(|z|^(n+1)/(n.factorial:ℝ))*Real.sqrt d*((lam:ℝ)*r)*
    (R⁻¹)^(2*(n+1))*Real.sqrt (harmonicMeanBudget (n+1))
  have hE : 0≤E := by dsimp [E]; positivity
  have heq : 4*C^2*(z^(n+1)/(n.factorial:ℝ))^2*
      ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1))=E^2 := by
    dsimp [E]
    rw [show 4*(n+1)=2*(2*(n+1)) by omega, pow_mul]
    simp only [abs_of_nonneg hz,mul_pow,div_pow,
      Real.sq_sqrt (show 0≤(d:ℝ) by positivity),Real.sq_sqrt (harmonicMeanBudget_nonneg (n+1))]
    ring
  have hs : Real.sqrt (4*C^2*(z^(n+1)/(n.factorial:ℝ))^2*
      ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1)))=E := by
    rw [heq,Real.sqrt_sq hE]
  have h₁ := mul_le_mul_of_nonneg_left hsqrtD
    (show 0≤C*((lam:ℝ)*r^2)*harmonicNormalizedTerm n R z by
      positivity [harmonicNormalizedTerm_nonneg (z:=z) n hR.le])
  have h₂ := mul_le_mul_of_nonneg_left ht1.le hE
  have h₃ := mul_le_mul_of_nonneg_left h₂ (show 0≤2*r by positivity)
  have h₄ := mul_le_mul_of_nonneg_left hms
    (show 0≤(A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(r*t) by positivity)
  have h₅ := mul_le_mul_of_nonneg_left ht1.le
    (show 0≤(A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(2*circuitGrowthConstant*r)*circuitD F x by
      positivity [circuitGrowthConstant_pos])
  rw [harmonicRmsBudget,hs]
  dsimp [E,harmonicNormalizedTerm] at *
  nlinarith
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory Quadrature
open scoped NNReal BigOperators

def numericalContractionCoefficient (Ap Ah Lp : ℝ≥0) : ℝ :=
  1+((Ap:ℝ)+Ah+Lp)*(Real.pi^2/2)
def numericalErrorCoefficient (C J : ℝ) : ℝ :=
  1+4*|C|+|J|+2*circuitGrowthConstant

def kernelNormalizedTerm (d k n N : ℕ) (lam Ap Ah Lp : ℝ≥0)
    (r R h z : ℝ) : ℝ :=
  probabilityNormalizedTerm d k n h+harmonicNormalizedTerm n R z+
    (numericalContractionCoefficient Ap Ah Lp*((lam:ℝ)*r^2))^N

lemma numericalContractionCoefficient_pos (Ap Ah Lp : ℝ≥0) :
    0<numericalContractionCoefficient Ap Ah Lp := by
  unfold numericalContractionCoefficient
  positivity
lemma numericalErrorCoefficient_pos (C J : ℝ) : 0<numericalErrorCoefficient C J := by
  unfold numericalErrorCoefficient
  positivity [circuitGrowthConstant_pos]

lemma numericalContraction_bound (Ap Ah Lp : ℝ≥0) (lam : ℝ≥0) (r : ℝ) :
    (Ap*probabilityMeanLipschitz lam r:ℝ≥0)≤numericalContractionCoefficient Ap Ah Lp*((lam:ℝ)*r^2) ∧
    (Ah*probabilityMeanLipschitz lam r:ℝ≥0)≤numericalContractionCoefficient Ap Ah Lp*((lam:ℝ)*r^2) ∧
    (Lp*probabilityMeanLipschitz lam r:ℝ≥0)≤numericalContractionCoefficient Ap Ah Lp*((lam:ℝ)*r^2) := by
  have h₁ : (Ap:ℝ)*(Real.pi^2/2)≤numericalContractionCoefficient Ap Ah Lp := by
    dsimp [numericalContractionCoefficient]; nlinarith [Ap.coe_nonneg,Ah.coe_nonneg,Lp.coe_nonneg,sq_nonneg Real.pi]
  have h₂ : (Ah:ℝ)*(Real.pi^2/2)≤numericalContractionCoefficient Ap Ah Lp := by
    dsimp [numericalContractionCoefficient]; nlinarith [Ap.coe_nonneg,Ah.coe_nonneg,Lp.coe_nonneg,sq_nonneg Real.pi]
  have h₃ : (Lp:ℝ)*(Real.pi^2/2)≤numericalContractionCoefficient Ap Ah Lp := by
    dsimp [numericalContractionCoefficient]; nlinarith [Ap.coe_nonneg,Ah.coe_nonneg,Lp.coe_nonneg,sq_nonneg Real.pi]
  refine ⟨?_,?_,?_⟩
  · change (Ap:ℝ)*(Real.pi^2/2*(lam:ℝ)*r^2) ≤ _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h₁ (show 0≤(lam:ℝ)*r^2 by positivity)
  · change (Ah:ℝ)*(Real.pi^2/2*(lam:ℝ)*r^2) ≤ _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h₂ (show 0≤(lam:ℝ)*r^2 by positivity)
  · change (Lp:ℝ)*(Real.pi^2/2*(lam:ℝ)*r^2) ≤ _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h₃ (show 0≤(lam:ℝ)*r^2 by positivity)

theorem kernelValueRmsBudget_normalized {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (Ap Ah Lp : ℝ≥0) {r R ρ h z C J : ℝ}
    (hr : 0≤r) (hr1 : r≤1) (hR : 0<R) (hh : 0≤h) (hz : 0≤z) (hC : 0≤C) (hJ : 0≤J)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (k n N : ℕ) :
    kernelValueRmsBudget F x lam Ap Ah Lp r R ρ h z C J k n N ≤
      300*((numericalContractionCoefficient Ap Ah Lp+1)*numericalErrorCoefficient C J*
        ((lam:ℝ)*r^2)*kernelNormalizedTerm d k n N lam Ap Ah Lp r R h z*circuitD F x)^2 := by
  let l := (lam:ℝ)*r^2
  let c := numericalContractionCoefficient Ap Ah Lp
  let A := numericalErrorCoefficient C J
  let D := circuitD F x
  let P := probabilityNormalizedTerm d k n h
  let H := harmonicNormalizedTerm n R z
  let q := (c*l)^N
  let B := P+H+q
  have hl0 : 0≤l := by positivity
  have hl1 : l≤1 := by dsimp [l]; linarith
  have hc : 0<c := numericalContractionCoefficient_pos Ap Ah Lp
  have hA : 0<A := numericalErrorCoefficient_pos C J
  have hD : 0≤D := circuitD_nonneg F x
  have hP : 0≤P := probabilityNormalizedTerm_nonneg d k n hh
  have hH : 0≤H := harmonicNormalizedTerm_nonneg (z:=z) n hR.le
  have hq : 0≤q := by dsimp [q]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have hAP : 4*C≤A := by dsimp [A,numericalErrorCoefficient]; rw [abs_of_nonneg hC]; linarith [abs_nonneg J,circuitGrowthConstant_pos]
  have hAH : J≤A := by dsimp [A,numericalErrorCoefficient]; rw [abs_of_nonneg hJ]; linarith [abs_nonneg C,circuitGrowthConstant_pos]
  have hAI : 2*circuitGrowthConstant≤A := by dsimp [A,numericalErrorCoefficient]; linarith [abs_nonneg C,abs_nonneg J]
  obtain ⟨htp,hth,htl⟩ := numericalContraction_bound Ap Ah Lp lam r
  have htpN := pow_le_pow_left₀ (show (0:ℝ)≤(Ap*probabilityMeanLipschitz lam r:ℝ≥0) by positivity) htp N
  have hthN := pow_le_pow_left₀ (show (0:ℝ)≤(Ah*probabilityMeanLipschitz lam r:ℝ≥0) by positivity) hth N
  change _≤q at htpN hthN
  have hcommon {a v t : ℝ} (ha : 0≤a) (hv : 0≤v) (ht : 0≤t) (hAa : a≤A) (htq : t≤q) :
      a*l*v+t*(2*circuitGrowthConstant*r)≤A*(v+q) := by
    have h₁ := mul_le_mul_of_nonneg_right hl1 (mul_nonneg ha hv)
    have h₂ := mul_le_mul_of_nonneg_right hAa hv
    have h₃ := mul_le_mul_of_nonneg_left hr1 (show 0≤2*circuitGrowthConstant by positivity [circuitGrowthConstant_pos])
    have h₄ := mul_le_mul htq (by simpa using h₃.trans (by simpa using hAI)) (by positivity [circuitGrowthConstant_pos]) hq
    nlinarith
  have hpb := probabilityRmsBudget_normalized F x lam Ap hr hh hC hL k n N
  have hhb := harmonicRmsBudget_normalized hF x Ah hr hr1 hR hz hJ hl hL hρ0 hρ1 n N
  have hp : probabilityRmsBudget F x lam Ap r h C k n N≤A*B*D := by
    apply hpb.trans
    have h₁ := hcommon (a:=4*C) (v:=P) (t:=(Ap*probabilityMeanLipschitz lam r:ℝ≥0)^N)
      (by positivity) hP (by positivity) hAP htpN
    have h₂ := mul_le_mul_of_nonneg_left (show P+q≤B by dsimp [B]; linarith) hA.le
    exact mul_le_mul_of_nonneg_right (h₁.trans h₂) hD
  have hq' : harmonicRmsBudget F x lam Ah r R ρ z J n N≤A*B*D := by
    apply hhb.trans
    have h₁ := hcommon hJ hH (show (0:ℝ)≤(Ah*probabilityMeanLipschitz lam r:ℝ≥0)^N by positivity) hAH hthN
    have h₂ := mul_le_mul_of_nonneg_left (show H+q≤B by dsimp [B]; linarith) hA.le
    exact mul_le_mul_of_nonneg_right (h₁.trans h₂) hD
  have hf : probabilityRmsBudget F x lam Ap r h C k n (N+1)≤A*l*(c+1)*B*D := by
    apply (probabilityRmsBudget_normalized F x lam Ap hr hh hC hL k n (N+1)).trans
    have hnext := mul_le_mul htpN htp (by positivity : (0:ℝ)≤(Ap*probabilityMeanLipschitz lam r:ℝ≥0)) hq
    rw [←pow_succ] at hnext
    have h₁ := mul_le_mul_of_nonneg_right hAP (mul_nonneg hl0 hP)
    have h₂ := mul_le_mul_of_nonneg_left hr1 (show 0≤2*circuitGrowthConstant by positivity [circuitGrowthConstant_pos])
    have h₃ := mul_le_mul hnext (by simpa using h₂.trans (by simpa using hAI)) (by positivity [circuitGrowthConstant_pos]) (by positivity)
    have h₄ := mul_le_mul_of_nonneg_left (show P+c*q≤(c+1)*B by dsimp [B]; nlinarith) (mul_nonneg hA.le hl0)
    apply mul_le_mul_of_nonneg_right _ hD
    change _≤A*l*(c+1)*B
    nlinarith
  have hlog : 0≤1+Real.log ((d:ℝ)+1) := by
    have := Real.log_nonneg (show 1≤(d:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) d]); linarith
  unfold kernelValueRmsBudget
  apply kernel_error_factor hl0 hB hD hA.le hc.le
    (by unfold probabilityRmsBudget; positivity [probabilityInitialRms_nonneg F x lam r])
    (by unfold harmonicRmsBudget; positivity)
    (by unfold probabilityRmsBudget; positivity [probabilityInitialRms_nonneg F x lam r]) (by positivity) hp hq' hf htl
end LogConcaveSampling

end

end

end OAI
