import Mathlib
import OAI.Probability.SKBarriers.Replicas.MatrixMassUnion
import OAI.Probability.SKBarriers.Gaussian.PolynomialTail

namespace OAI

section

noncomputable section
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem eventual_replicaGibbsMass_polynomial_gap {β c a t ε : ℝ} (hβ : 0<β)
    (d p : ℕ) (hd : 0<d) (hc : 0<c) (ha : 0≤a) (ha24 : a<1/24)
    (ht : t<1-2*a) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (C : Type) [Fintype C],Fintype.card C≤(n+1)^p →
      ∀ (code : ReplicaConfig n d → C),
      (∀ s t,code s=code t → replicaGram s=replicaGram t) →
      ∀ (S : Finset (ReplicaConfig n d)),
      (∀ s∈S,matrixConstrainedPressure n d β (replicaGram s)≤
        (d:ℝ)*finiteParisiInf β-c*(n:ℝ)^(-a)) →
      (∫ J,replicaGibbsMass β J S ∂disorderLaw n)≤ε*Real.exp (-(n:ℝ)^t) := by
  obtain ⟨K,hK,H⟩ := eventual_replicaGibbsMass_code_gap hβ d hd
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have htail₁ := eventual_polynomial_stretched_tail (by linarith : t<1-a)
    (by linarith : 0<1-a) (by positivity : 0<c/4) (half_pos hε) 1 (by norm_num) p
  have htail₂ := eventual_polynomial_stretched_tail ht (by linarith : 0<1-2*a)
    (by positivity : 0<c^2/(16*Real.pi^2*β^2*(d:ℝ)^2)) (half_pos hε) 2 (by norm_num) p
  filter_upwards [H,eventually_const_rpow_le (by linarith : -(1:ℝ)/24 < -a) (2*(d:ℝ)*K) hc,
    htail₁,htail₂,eventually_gt_atTop (0:ℕ)] with n hn herr ht₁ ht₂ hn0
  intro C _ hcard code hcode S hgap
  have hp : (0:ℝ)<n := by exact_mod_cast hn0
  have he₁ : -(n:ℝ)*(c*(n:ℝ)^(-a))/4=-(c/4)*(n:ℝ)^(1-a) := by
    rw [Real.rpow_sub hp,Real.rpow_one,Real.rpow_neg hp.le]
    ring
  have he₂ : -(n:ℝ)*(c*(n:ℝ)^(-a))^2/(16*Real.pi^2*β^2*(d:ℝ)^2)=
      -(c^2/(16*Real.pi^2*β^2*(d:ℝ)^2))*(n:ℝ)^(1-2*a) := by
    rw [mul_pow,← Real.rpow_natCast ((n:ℝ)^(-a)) 2,← Real.rpow_mul hp.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (-a)*(2:ℝ)= -(2*a) by ring,Real.rpow_neg hp.le,
      Real.rpow_sub hp,Real.rpow_one]
    ring
  have HM := hn C code hcode S (c*(n:ℝ)^(-a)) (by positivity) herr hgap
  rw [he₁,he₂] at HM
  have hcard' : (Fintype.card C:ℝ)≤((n:ℝ)+1)^p := by exact_mod_cast hcard
  have HH := HM.trans (mul_le_mul_of_nonneg_right hcard' (by positivity))
  simp only [one_mul] at ht₁
  nlinarith only [HH,ht₁,ht₂]

end SK.Analytic

end
end

end OAI
