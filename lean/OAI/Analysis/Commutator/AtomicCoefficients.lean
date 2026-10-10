import Mathlib
import OAI.Analysis.Commutator.AtomicDecomposition

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

namespace Kadison.AtomicFactor.Decomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (D : Decomposition M p)

def support (s : Finset D.I) : H →L[ℂ] H := ∑ i∈s,D.v i*star (D.v i)

lemma support_mem (s : Finset D.I) : D.support s∈M :=
  M.sum_mem (fun i _ => M.mul_mem (D.mem i) (M.star_mem' (D.mem i)))

lemma support_projection (s : Finset D.I) : IsStarProjection (D.support s) := by
  classical
  constructor
  · change D.support s*D.support s=D.support s
    rw [support,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum,Finset.sum_eq_single_of_mem i hi]
    · calc
        _=(D.v i*(star (D.v i)*D.v i))*star (D.v i) := by noncomm_ring
        _=D.v i*star (D.v i) := by rw [D.initial,D.source]
    · intro j hj hne
      calc
        _=(D.v i*(star (D.v i)*D.v j))*star (D.v j) := by noncomm_ring
        _=0 := by rw [D.cross i j hne.symm,mul_zero,zero_mul]
  · change star (D.support s)=D.support s
    rw [support,star_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [star_mul,star_star]

lemma support_norm_le (s : Finset D.I) : ‖D.support s‖≤1 :=
  (D.support_projection s).norm_le _

lemma support_tendsto (x : H) : Tendsto (fun s : Finset D.I => D.support s x) atTop (𝓝 x) :=
  D.strong x

lemma eq_zero_of_coefficients_zero {a : H →L[ℂ] H}
    (ha : ∀ i j,star (D.v i)*a*D.v j=0) : a=0 := by
  have hleft (i : D.I) : star (D.v i)*a=0 := by
    ext x
    have he (s : Finset D.I) : (star (D.v i)*a) (D.support s x)=0 := by
      have ht : (star (D.v i)*a)*D.support s=0 := by
        rw [support,Finset.mul_sum]
        apply Finset.sum_eq_zero
        intro j hj
        rw [←mul_assoc,ha i j,zero_mul]
      exact congrArg (fun T : H →L[ℂ] H => T x) ht
    exact tendsto_nhds_unique
      (((star (D.v i)*a).continuous.tendsto x).comp (D.support_tendsto x))
      (by simpa only [Function.comp_def,he,zero_apply] using (tendsto_const_nhds : Tendsto (fun _ : Finset D.I => (0:H)) atTop (𝓝 0)))
  ext x
  have he (s : Finset D.I) : D.support s (a x)=0 := by
    have ht : D.support s*a=0 := by
      rw [support,Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro i hi
      rw [mul_assoc,hleft i,mul_zero]
    exact congrArg (fun T : H →L[ℂ] H => T x) ht
  exact tendsto_nhds_unique (D.support_tendsto (a x))
    (by simpa only [Function.comp_def,he,zero_apply] using (tendsto_const_nhds : Tendsto (fun _ : Finset D.I => (0:H)) atTop (𝓝 0)))

lemma eq_of_coefficients_eq {a b : H →L[ℂ] H}
    (h : ∀ i j,star (D.v i)*a*D.v j=star (D.v i)*b*D.v j) : a=b := by
  apply sub_eq_zero.mp
  apply D.eq_zero_of_coefficients_zero
  intro i j
  rw [mul_sub,sub_mul,h i j,sub_self]

end Kadison.AtomicFactor.Decomposition

end

end
end

end OAI
