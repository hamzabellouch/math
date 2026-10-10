import OAI.Analysis.Pureness.Divisibility.HereditaryRank
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.RingTheory.Adjoin.Singleton

namespace OAI
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder NNReal Polynomial
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma trace_cfc_eq_of_moments (τ : TracialState A) (a b : A)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hm : ∀ n : ℕ, τ.functional (a ^ n) = τ.functional (b ^ n))
    (f : ℝ → ℝ) (hf : Continuous f) :
    τ.functional (cfc f a) = τ.functional (cfc f b) := by
  let : Algebra ℝ (A × A) := Algebra.complexToReal
  let : NormedSpace ℝ (A × A) := NormedSpace.complexToReal
  have hp : IsSelfAdjoint (a, b) := by
    show star (a, b) = (a, b)
    simp only [Prod.star_def, ha.star_eq, hb.star_eq]
  have hpoly (p : ℝ[X]) :
      τ.functional ((Polynomial.aeval (a, b) p).1) =
      τ.functional ((Polynomial.aeval (a, b) p).2) := by
    rw [Polynomial.aeval_eq_sum_range]
    simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
      Prod.pow_mk, map_sum, τ.functional.map_smul_of_tower, hm]
  have hclosed : IsClosed {z : A × A | τ.functional z.1 = τ.functional z.2} :=
    isClosed_eq ((map_continuous τ.functional).comp continuous_fst)
      ((map_continuous τ.functional).comp continuous_snd)
  have hsub : (StarAlgebra.elemental ℝ (a, b) : Set (A × A)) ⊆
      {z : A × A | τ.functional z.1 = τ.functional z.2} := by
    apply closure_minimal _ hclosed
    intro z hz
    change z ∈ (StarAlgebra.adjoin ℝ {(a, b)}).toSubalgebra at hz
    rw [StarAlgebra.adjoin_toSubalgebra, Set.star_singleton, hp.star_eq, Set.union_self,
      Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨p, rfl⟩ := hz
    exact hpoly p
  have hc := hsub (cfc_mem_elemental (p := IsSelfAdjoint) f (a, b))
  have hfst : (cfc f (a, b)).1 = cfc f a :=
    (StarAlgHom.fst ℂ A A).map_cfc f (a, b) hf.continuousOn continuous_fst hp ha
  have hsnd : (cfc f (a, b)).2 = cfc f b :=
    (StarAlgHom.snd ℂ A A).map_cfc f (a, b) hf.continuousOn continuous_snd hp hb
  change τ.functional (cfc f (a, b)).1 = τ.functional (cfc f (a, b)).2 at hc
  rwa [hfst, hsnd] at hc

omit [StarOrderedRing A] in
lemma trace_star_mul_self_pow (τ : TracialState A) (x : A) (n : ℕ) :
    τ.functional ((star x * x) ^ n) = τ.functional ((x * star x) ^ n) := by
  cases n with
  | zero => simp
  | succ n =>
    have hid : (star x * x) ^ (n + 1) = star x * (x * star x) ^ n * x := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ (star x * x) (n + 1), ih, pow_succ (x * star x) n]
        simp only [mul_assoc]
    rw [hid, mul_assoc, τ.tracial (star x) ((x * star x) ^ n * x),
      mul_assoc, ← pow_succ]

lemma trace_nnrpow_eq_of_moments (τ : TracialState A) (a b : A)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : ∀ n : ℕ, τ.functional (a ^ n) = τ.functional (b ^ n))
    (r : ℝ≥0) (hr : 0 < r) :
    τ.functional (CFC.nnrpow a r) = τ.functional (CFC.nnrpow b r) := by
  simp only [CFC.nnrpow_eq_pow, CFC.nnrpow_eq_cfcₙ_real a r ha,
    CFC.nnrpow_eq_cfcₙ_real b r hb]
  have hf0 : (0 : ℝ) ^ (r : ℝ) = 0 := Real.zero_rpow (by exact_mod_cast hr.ne')
  rw [cfcₙ_eq_cfc (hf0 := hf0), cfcₙ_eq_cfc (hf0 := hf0)]
  exact trace_cfc_eq_of_moments τ a b ha.isSelfAdjoint hb.isSelfAdjoint hm _
    (Real.continuous_rpow_const (by positivity))

theorem rank_star_mul_self (τ : TracialState A) (x : A) :
    normalizedRootRank τ (star x * x) = normalizedRootRank τ (x * star x) := by
  have hnorm : ‖star x * x‖ = ‖x * star x‖ := by
    calc
      _ = ‖x‖ * ‖x‖ := CStarRing.norm_star_mul_self (x := x)
      _ = ‖star x‖ * ‖star x‖ := by rw [norm_star]
      _ = _ := by simpa only [star_star] using (CStarRing.norm_star_mul_self (x := star x)).symm
  have hm (n : ℕ) :
      τ.functional ((normalizePositive (star x * x)) ^ n) =
      τ.functional ((normalizePositive (x * star x)) ^ n) := by
    simp only [normalizePositive, smul_pow, τ.functional.map_smul_of_tower,
      hnorm, trace_star_mul_self_pow τ x n]
  unfold normalizedRootRank
  congr 1
  funext j
  unfold normalizedRoot
  rw [trace_nnrpow_eq_of_moments τ _ _
    (normalizePositive_nonneg _ (star_mul_self_nonneg x))
    (normalizePositive_nonneg _ (mul_star_self_nonneg x)) hm _ (by positivity)]
end CuntzPureness

end OAI
