import OAI.Probability.ClassicalON.IsingGinibre

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ClassicalON

theorem signValue_product_moment (l : List Unit) :
    0≤∫ t,(l.map (fun _ => signValue t)).prod ∂signLaw := by
  have he (t : Bool) : (l.map (fun _ => signValue t)).prod=signValue t^l.length := by simp
  simp_rw [he]
  simp only [signLaw,integral_smul_measure,ENNReal.toReal_inv,ENNReal.toReal_ofNat,
    smul_eq_mul,integral_count,Fintype.sum_bool,signValue,Bool.false_eq_true,ite_false,ite_true,
    one_pow]
  have hh : -1≤(-1 : ℝ)^l.length := by
    simpa only [abs_pow,abs_neg,abs_one,one_pow] using neg_abs_le ((-1 : ℝ)^l.length)
  norm_num at *
  linarith

variable {V : Type uV} {E : Type uE} [Fintype V]

theorem ising_reference_mean_nonneg (left right : E → V) (e : E) :
    0≤∫ s,isingEnergy left right e s ∂isingReference := by
  classical
  have hh := independent_moments_nonneg (V := V) signLaw (fun (_ : Unit) t => signValue t)
    signValue_product_moment [(left e,()),(right e,())]
  simpa only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,isingEnergy,
    isingReference] using hh

variable [Fintype E]

theorem ising_edge_mean_nonneg (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e) (e : E) :
    0 ≤ isingMean left right b (isingEnergy left right e) := by
  apply edgeMean_nonneg isingReference (isingEnergy left right)
    (fun _ => continuous_of_discreteTopology)
  · exact ising_edge_covariance_nonneg left right
  · exact ising_reference_mean_nonneg left right
  · exact hb

end ClassicalON

end

end OAI
