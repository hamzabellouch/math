import Mathlib
import OAI.Probability.SKRatio.Certificates.CertifiedBatches
import OAI.Probability.SKRatio.Certificates.CertifiedFunctionBounds

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J0K7

def expression : Expr := integrandExpr (7/20) (44507/50000) (110763/200000) (20333/250000) (14573/25000) 7
def blocks : ℕ → Box
  | 0 => ⟨-1/1000000,1/1000000⟩
  | 1 => ⟨-1/1000000,1/1000000⟩
  | 2 => ⟨-1/1000000,1/1000000⟩
  | 3 => ⟨-1/1000000,1/1000000⟩
  | 4 => ⟨-1/1000000,1/1000000⟩
  | 5 => ⟨-1/1000000,1/1000000⟩
  | 6 => ⟨-1/1000000,1/1000000⟩
  | 7 => ⟨-1/1000000,1/1000000⟩
  | 8 => ⟨0,1/1000000⟩
  | 9 => ⟨3/1000000,1/200000⟩
  | 10 => ⟨1/25000,43/1000000⟩
  | 11 => ⟨331/1000000,343/1000000⟩
  | 12 => ⟨2103/1000000,539/250000⟩
  | 13 => ⟨159/15625,10349/1000000⟩
  | 14 => ⟨36733/1000000,18551/500000⟩
  | 15 => ⟨95661/1000000,9607/100000⟩
  | 16 => ⟨169931/1000000,85339/500000⟩
  | 17 => ⟨187633/1000000,18879/100000⟩
  | 18 => ⟨103601/1000000,104181/1000000⟩
  | 19 => ⟨2517/200000,13583/1000000⟩
  | 20 => ⟨2251/62500,36649/1000000⟩
  | 21 => ⟨15061/125000,1517/12500⟩
  | 22 => ⟨144411/1000000,29073/200000⟩
  | 23 => ⟨99259/1000000,4989/50000⟩
  | 24 => ⟨45617/1000000,23043/500000⟩
  | 25 => ⟨15183/1000000,7737/500000⟩
  | 26 => ⟨767/200000,247/62500⟩
  | 27 => ⟨377/500000,197/250000⟩
  | 28 => ⟨117/1000000,1/8000⟩
  | 29 => ⟨7/500000,1/62500⟩
  | 30 => ⟨1/1000000,1/500000⟩
  | 31 => ⟨-1/1000000,1/1000000⟩
  | 32 => ⟨-1/1000000,1/1000000⟩
  | 33 => ⟨-1/1000000,1/1000000⟩
  | 34 => ⟨-1/1000000,1/1000000⟩
  | 35 => ⟨-1/1000000,1/1000000⟩
  | 36 => ⟨-1/1000000,1/1000000⟩
  | 37 => ⟨-1/1000000,1/1000000⟩
  | 38 => ⟨-1/1000000,1/1000000⟩
  | 39 => ⟨-1/1000000,1/1000000⟩
  | _ => Box.rat 0

lemma check_0 : expression.check (-10+(0:ℚ)*(5*(1/10))) (1/10) 5 (blocks 0) = true := by decide +kernel
lemma check_1 : expression.check (-10+(1:ℚ)*(5*(1/10))) (1/10) 5 (blocks 1) = true := by decide +kernel
lemma check_2 : expression.check (-10+(2:ℚ)*(5*(1/10))) (1/10) 5 (blocks 2) = true := by decide +kernel
lemma check_3 : expression.check (-10+(3:ℚ)*(5*(1/10))) (1/10) 5 (blocks 3) = true := by decide +kernel
lemma check_4 : expression.check (-10+(4:ℚ)*(5*(1/10))) (1/10) 5 (blocks 4) = true := by decide +kernel
lemma check_5 : expression.check (-10+(5:ℚ)*(5*(1/10))) (1/10) 5 (blocks 5) = true := by decide +kernel
lemma check_6 : expression.check (-10+(6:ℚ)*(5*(1/10))) (1/10) 5 (blocks 6) = true := by decide +kernel
lemma check_7 : expression.check (-10+(7:ℚ)*(5*(1/10))) (1/10) 5 (blocks 7) = true := by decide +kernel
lemma check_8 : expression.check (-10+(8:ℚ)*(5*(1/10))) (1/10) 5 (blocks 8) = true := by decide +kernel
lemma check_9 : expression.check (-10+(9:ℚ)*(5*(1/10))) (1/10) 5 (blocks 9) = true := by decide +kernel
lemma check_10 : expression.check (-10+(10:ℚ)*(5*(1/10))) (1/10) 5 (blocks 10) = true := by decide +kernel
lemma check_11 : expression.check (-10+(11:ℚ)*(5*(1/10))) (1/10) 5 (blocks 11) = true := by decide +kernel
lemma check_12 : expression.check (-10+(12:ℚ)*(5*(1/10))) (1/10) 5 (blocks 12) = true := by decide +kernel
lemma check_13 : expression.check (-10+(13:ℚ)*(5*(1/10))) (1/10) 5 (blocks 13) = true := by decide +kernel
lemma check_14 : expression.check (-10+(14:ℚ)*(5*(1/10))) (1/10) 5 (blocks 14) = true := by decide +kernel
lemma check_15 : expression.check (-10+(15:ℚ)*(5*(1/10))) (1/10) 5 (blocks 15) = true := by decide +kernel
lemma check_16 : expression.check (-10+(16:ℚ)*(5*(1/10))) (1/10) 5 (blocks 16) = true := by decide +kernel
lemma check_17 : expression.check (-10+(17:ℚ)*(5*(1/10))) (1/10) 5 (blocks 17) = true := by decide +kernel
lemma check_18 : expression.check (-10+(18:ℚ)*(5*(1/10))) (1/10) 5 (blocks 18) = true := by decide +kernel
lemma check_19 : expression.check (-10+(19:ℚ)*(5*(1/10))) (1/10) 5 (blocks 19) = true := by decide +kernel
lemma check_20 : expression.check (-10+(20:ℚ)*(5*(1/10))) (1/10) 5 (blocks 20) = true := by decide +kernel
lemma check_21 : expression.check (-10+(21:ℚ)*(5*(1/10))) (1/10) 5 (blocks 21) = true := by decide +kernel
lemma check_22 : expression.check (-10+(22:ℚ)*(5*(1/10))) (1/10) 5 (blocks 22) = true := by decide +kernel
lemma check_23 : expression.check (-10+(23:ℚ)*(5*(1/10))) (1/10) 5 (blocks 23) = true := by decide +kernel
lemma check_24 : expression.check (-10+(24:ℚ)*(5*(1/10))) (1/10) 5 (blocks 24) = true := by decide +kernel
lemma check_25 : expression.check (-10+(25:ℚ)*(5*(1/10))) (1/10) 5 (blocks 25) = true := by decide +kernel
lemma check_26 : expression.check (-10+(26:ℚ)*(5*(1/10))) (1/10) 5 (blocks 26) = true := by decide +kernel
lemma check_27 : expression.check (-10+(27:ℚ)*(5*(1/10))) (1/10) 5 (blocks 27) = true := by decide +kernel
lemma check_28 : expression.check (-10+(28:ℚ)*(5*(1/10))) (1/10) 5 (blocks 28) = true := by decide +kernel
lemma check_29 : expression.check (-10+(29:ℚ)*(5*(1/10))) (1/10) 5 (blocks 29) = true := by decide +kernel
lemma check_30 : expression.check (-10+(30:ℚ)*(5*(1/10))) (1/10) 5 (blocks 30) = true := by decide +kernel
lemma check_31 : expression.check (-10+(31:ℚ)*(5*(1/10))) (1/10) 5 (blocks 31) = true := by decide +kernel
lemma check_32 : expression.check (-10+(32:ℚ)*(5*(1/10))) (1/10) 5 (blocks 32) = true := by decide +kernel
lemma check_33 : expression.check (-10+(33:ℚ)*(5*(1/10))) (1/10) 5 (blocks 33) = true := by decide +kernel
lemma check_34 : expression.check (-10+(34:ℚ)*(5*(1/10))) (1/10) 5 (blocks 34) = true := by decide +kernel
lemma check_35 : expression.check (-10+(35:ℚ)*(5*(1/10))) (1/10) 5 (blocks 35) = true := by decide +kernel
lemma check_36 : expression.check (-10+(36:ℚ)*(5*(1/10))) (1/10) 5 (blocks 36) = true := by decide +kernel
lemma check_37 : expression.check (-10+(37:ℚ)*(5*(1/10))) (1/10) 5 (blocks 37) = true := by decide +kernel
lemma check_38 : expression.check (-10+(38:ℚ)*(5*(1/10))) (1/10) 5 (blocks 38) = true := by decide +kernel
lemma check_39 : expression.check (-10+(39:ℚ)*(5*(1/10))) (1/10) 5 (blocks 39) = true := by decide +kernel

lemma checks (i : ℕ) (hi : i < 40) :
    expression.check (-10+(i:ℚ)*(5*(1/10))) (1/10) 5 (blocks i) = true := by
  interval_cases i
  · exact check_0
  · exact check_1
  · exact check_2
  · exact check_3
  · exact check_4
  · exact check_5
  · exact check_6
  · exact check_7
  · exact check_8
  · exact check_9
  · exact check_10
  · exact check_11
  · exact check_12
  · exact check_13
  · exact check_14
  · exact check_15
  · exact check_16
  · exact check_17
  · exact check_18
  · exact check_19
  · exact check_20
  · exact check_21
  · exact check_22
  · exact check_23
  · exact check_24
  · exact check_25
  · exact check_26
  · exact check_27
  · exact check_28
  · exact check_29
  · exact check_30
  · exact check_31
  · exact check_32
  · exact check_33
  · exact check_34
  · exact check_35
  · exact check_36
  · exact check_37
  · exact check_38
  · exact check_39

theorem integral_bound :
    (∫ h, scalarFunction (7/20) (44507/50000) (110763/200000) (20333/250000) (14573/25000) 7 h ∂Scalar.fieldLaw (7/20)) ∈ (⟨0,436921/1000000⟩ : Box) := by
  apply gaussian_certificate (e := expression) (B := blocks) (h := (1/10)) (k := 5) (by norm_num)
  · simpa only [expression,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Rat.cast_zero] using integrandExpr_val (7/20) (44507/50000) (110763/200000) (20333/250000) (14573/25000) 7
  · exact (continuous_scalarFunction _ _ _ _ _ _).measurable
  · intro x
    apply scalarFunction_bound <;> norm_num
  · exact checks
  · decide +kernel

end SKRatio.Certificate.Data.J0K7

end

end OAI
