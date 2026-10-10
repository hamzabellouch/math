import OAI.InformationTheory.Entanglement.InformationalComplete
import OAI.Analysis.Quantum.PPTSquare.ChannelModel
import OAI.Analysis.Quantum.PPTSquare.TraceCompletion
import OAI.Analysis.Quantum.PPTSquare.Compression
import OAI.Analysis.Quantum.PPTSquare.ChannelCompletion

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace SecretKey
open ChannelCompletion
variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
def testSum (n : Type) [Fintype n] [DecidableEq n] : Mat n :=
  ∑ k : PositiveTestIndex n, positiveTest k
lemma testSum_psd : (testSum n).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun k _ => positiveTest_psd k)
def probeScale (n : Type) [Fintype n] [DecidableEq n] : ℝ :=
  (1+(Matrix.trace (testSum n)).re)⁻¹
lemma probeScale_pos : 0<probeScale n := by
  apply inv_pos.mpr
  have h := (Complex.nonneg_iff.mp (testSum_psd (n := n)).trace_nonneg).1
  linarith
lemma probeScale_mul_trace : probeScale n+(probeScale n)*(Matrix.trace (testSum n)).re=1 := by
  unfold probeScale
  have h := (Complex.nonneg_iff.mp (testSum_psd (n := n)).trace_nonneg).1
  field_simp

def probePOVM : Option (PositiveTestIndex n) → Mat n
  | some k => (probeScale n : ℂ) • positiveTest k
  | none => 1-(probeScale n : ℂ) • testSum n
lemma probePOVM_psd (k : Option (PositiveTestIndex n)) : (probePOVM k).PosSemidef := by
  cases k with
  | some k => exact (positiveTest_psd k).smul (by exact_mod_cast (probeScale_pos (n := n)).le)
  | none =>
    have htrace : ((Matrix.trace (testSum n)).re : ℂ)=Matrix.trace (testSum n) := by
      exact Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp (testSum_psd (n := n)).trace_nonneg).2)
    have he : (1-(probeScale n : ℂ) • testSum n) =
        (probeScale n : ℂ) • (1 : Mat n)+
          (probeScale n : ℂ) • (Matrix.trace (testSum n) • (1 : Mat n)-testSum n) := by
      rw [smul_sub,smul_smul,← add_sub_assoc,← add_smul]
      have hc : (probeScale n : ℂ)+(probeScale n : ℂ)*Matrix.trace (testSum n)=1 := by
        rw [← htrace,← Complex.ofReal_mul,← Complex.ofReal_add,probeScale_mul_trace]
        rfl
      rw [hc,one_smul]
    change (1-(probeScale n : ℂ) • testSum n).PosSemidef
    rw [he]
    exact (Matrix.PosSemidef.one.smul (by exact_mod_cast (probeScale_pos (n := n)).le)).add
      ((psd_trace_bound testSum_psd).smul (by exact_mod_cast (probeScale_pos (n := n)).le))
lemma probePOVM_sum : (∑ k : Option (PositiveTestIndex n), probePOVM k) = 1 := by
  rw [Fintype.sum_option]
  simp only [probePOVM,← Finset.smul_sum,testSum]
  abel
lemma linear_eq_zero_of_probePOVM (L : Mat n →ₗ[ℂ] ℂ)
    (h : ∀ k, L (probePOVM k)=0) : L=0 := by
  apply linear_eq_zero_of_positive_tests L
  intro k
  have hk := h (some k)
  change L ((probeScale n : ℂ) • positiveTest k)=0 at hk
  rw [map_smul,smul_eq_mul] at hk
  exact (mul_eq_zero.mp hk).resolve_left (by exact_mod_cast (probeScale_pos (n := n)).ne')

theorem tensor_product_of_probePOVM (W : Mat (n×m)) (X : Mat n) (Y : Mat m)
    (htest : ∀ e : Option (PositiveTestIndex n), ∀ g : Option (PositiveTestIndex m),
      Matrix.trace ((probePOVM e ⊗ₖ probePOVM g)*W)=
        Matrix.trace (probePOVM e*X)*Matrix.trace (probePOVM g*Y)) :
    W=X ⊗ₖ Y := by
  apply tensor_product_of_positive_tests
  intro e g
  have h := htest (some e) (some g)
  simp only [probePOVM,Matrix.smul_kronecker,Matrix.kronecker_smul,Matrix.smul_mul,
    Matrix.trace_smul,smul_eq_mul] at h
  have hc : (probeScale n : ℂ) ≠ 0 := by exact_mod_cast (probeScale_pos (n := n)).ne'
  have hd : (probeScale m : ℂ) ≠ 0 := by exact_mod_cast (probeScale_pos (n := m)).ne'
  apply mul_left_cancel₀ hc
  apply mul_left_cancel₀ hd
  linear_combination h

end SecretKey

end

end OAI
