import OAI.Geometry.Kahler.BaseDensityMeasure

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma densityBandwidth_le_two {Q : ℕ} (hQ : 2 ≤ Q) (j : ℕ) : densityBandwidth Q j ≤ 2*Q^j := by
  cases j with
  | zero => simp [densityBandwidth]
  | succ j =>
    rw [densityBandwidth_succ]
    have h := densityBandwidth_lt hQ j
    omega

lemma density_low_moment_persist {a : ℝ} (pr : RadialProfiles a) {Q M i N n : ℕ}
    (hQ : 2 ≤ Q) (hM : M+2 < Q) (hiN : i ≤ N) (hn : n ≤ M*Q^i)
    (P : ℕ → Finset Sphere) {V : Sphere → ℂ} (hV : Continuous V)
    (hphase : ∀ z ξ, V (phaseAction z ξ)=phaseChar n z*V ξ) :
    (∫ ξ : Sphere, (V ξ).re*density Q pr.R pr.f pr.b P N ξ ∂sigma)=
      ∫ ξ : Sphere, (V ξ).re*density Q pr.R pr.f pr.b P i ξ ∂sigma := by
  induction N,hiN using Nat.le_induction with
  | base => rfl
  | succ N hiN ih =>
    have hp : Q^i ≤ Q^N := Nat.pow_le_pow_right (by omega : 0 < Q) hiN
    have hb := densityBandwidth_le_two hQ N
    have hn' : n ≤ M*Q^N := hn.trans (Nat.mul_le_mul_left _ hp)
    have hpow : 0 < Q^N := pow_pos (by omega) _
    have hgap : n+densityBandwidth Q N < Q^(N+1) := by
      rw [pow_succ]
      nlinarith
    rw [density_low_moment_step pr (by omega) P N hgap hV hphase,ih]

lemma logTruncation_density_persist {a : ℝ} (pr : RadialProfiles a) {Q M i N : ℕ}
    (hQ : 2 ≤ Q) (hM : M+2 < Q) (hiN : i ≤ N) (P : ℕ → Finset Sphere)
    (ε : ℝ) (c : ℂ) :
    (∫ ξ : Sphere, logTruncation ε M (c*peakPolynomial (P (Q^i)) (Q^i) ξ)*
      density Q pr.R pr.f pr.b P N ξ ∂sigma)=
    ∫ ξ : Sphere, logTruncation ε M (c*peakPolynomial (P (Q^i)) (Q^i) ξ)*
      density Q pr.R pr.f pr.b P i ξ ∂sigma := by
  classical
  let V : Sphere → ℂ := fun ξ => c*peakPolynomial (P (Q^i)) (Q^i) ξ
  have hV : Continuous V := continuous_const.mul ((peakPolynomial_analytic _ _).continuous.comp continuous_subtype_val)
  have hW (j : ℕ) : Continuous (fun ξ : Sphere => density Q pr.R pr.f pr.b P j ξ) :=
    (density_smooth (by omega : 0 < Q) pr.cutoff_lt pr.smooth_f pr.smooth_b pr.tail P j).continuous.comp continuous_subtype_val
  have hm : (∫ ξ : Sphere, logMean ε (V ξ)*density Q pr.R pr.f pr.b P N ξ ∂sigma)=
      ∫ ξ : Sphere, logMean ε (V ξ)*density Q pr.R pr.f pr.b P i ξ ∂sigma := by
    exact density_low_moment_persist pr hQ hM hiN (Nat.zero_le _) P
      (Complex.continuous_ofReal.comp ((logMean_continuous ε).comp hV)) (logMean_peak_phase ε c _ _)
  have ht : ∀ n ∈ Finset.range M,
      (∫ ξ : Sphere, logTerm ε n (V ξ)*density Q pr.R pr.f pr.b P N ξ ∂sigma)=
      ∫ ξ : Sphere, logTerm ε n (V ξ)*density Q pr.R pr.f pr.b P i ξ ∂sigma := by
    intro n hn
    have hbound : Q^i*(n+1) ≤ M*Q^i := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (Q^i) (show n+1 ≤ M by have := Finset.mem_range.mp hn; omega)
    have he : (∫ ξ : Sphere, ((logNormalized ε (V ξ))^(n+1)).re*density Q pr.R pr.f pr.b P N ξ ∂sigma)=
        ∫ ξ : Sphere, ((logNormalized ε (V ξ))^(n+1)).re*density Q pr.R pr.f pr.b P i ξ ∂sigma := density_low_moment_persist pr hQ hM hiN hbound P
      (((logNormalized_continuous ε).comp hV).pow (n+1)) (logNormalized_peak_phase ε c _ _ (n+1))
    have hfun : ∀ ξ : Sphere, ∀ j : ℕ, logTerm ε n (V ξ)*density Q pr.R pr.f pr.b P j ξ=
      (-2/(n+1))*(((logNormalized ε (V ξ))^(n+1)).re*density Q pr.R pr.f pr.b P j ξ) := by
      intro ξ j; dsimp [logTerm]; ring
    simp_rw [hfun,integral_const_mul,he]
  have he (j : ℕ) : (∫ ξ : Sphere, logTruncation ε M (V ξ)*density Q pr.R pr.f pr.b P j ξ ∂sigma)=
      (∫ ξ : Sphere, logMean ε (V ξ)*density Q pr.R pr.f pr.b P j ξ ∂sigma)+
      ∑ n ∈ Finset.range M, ∫ ξ : Sphere, logTerm ε n (V ξ)*density Q pr.R pr.f pr.b P j ξ ∂sigma := by
    simp only [logTruncation,add_mul,Finset.sum_mul]
    have him : Integrable (fun ξ : Sphere => logMean ε (V ξ)*density Q pr.R pr.f pr.b P j ξ) sigma :=
      compact_continuous_integrable (((logMean_continuous ε).comp hV).mul (hW j))
    have hit : ∀ n ∈ Finset.range M, Integrable (fun ξ : Sphere => logTerm ε n (V ξ)*density Q pr.R pr.f pr.b P j ξ) sigma :=
      fun n _ => compact_continuous_integrable (((logTerm_continuous ε n).comp hV).mul (hW j))
    rw [integral_add him (integrable_finsetSum _ hit),integral_finsetSum _ hit]
  change (∫ ξ : Sphere, logTruncation ε M (V ξ)*density Q pr.R pr.f pr.b P N ξ ∂sigma)=_
  rw [he N,he i,hm]
  congr 1
  exact Finset.sum_congr rfl ht

end PinchedHartogs.BaseConstruction

end

end OAI
