import OAI.Analysis.Pureness.Stabilization.Rank
import OAI.Analysis.Pureness.Stabilization.Pullback

namespace OAI
noncomputable section
open scoped NNReal ENNReal Topology CStarAlgebra
open Filter
namespace CuntzTrace
variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
namespace Positive

lemma map_power (f : A →⋆ₙₐ[ℂ] B) (a : Positive A) (r : ℝ≥0) (hr : 0 < r) :
    map f (power r a) = power r (map f a) := by
  apply Subtype.ext
  change f (a.1 ^ r) = (f a.1) ^ r
  rw [CFC.nnrpow_eq_cfcₙ_real _ _ a.2,
    CFC.nnrpow_eq_cfcₙ_real _ _ (map_nonneg f a.2)]
  exact f.map_cfcₙ (fun t : ℝ => t ^ (r : ℝ)) a.1
    (hf₀ := Real.zero_rpow (by exact_mod_cast hr.ne'))
    (hφ := map_continuous f) (ha := IsSelfAdjoint.of_nonneg a.2)
    (hφa := IsSelfAdjoint.of_nonneg (map_nonneg f a.2))

end Positive
namespace ExtendedTrace

@[simp] theorem rank_zero_trace (a : Positive A) : (0 : ExtendedTrace A).rank a = 0 := by
  simp [rank]

theorem rank_add (τ σ : ExtendedTrace A) (a : Positive A) :
    (τ + σ).rank a = τ.rank a + σ.rank a := by
  exact tendsto_nhds_unique ((τ + σ).tendsto_roots_rank_all a)
    ((τ.tendsto_roots_rank_all a).add (σ.tendsto_roots_rank_all a))

theorem rank_pullback (τ : ExtendedTrace B) (f : A →⋆ₙₐ[ℂ] B) (a : Positive A) :
    (τ.pullback f).rank a = τ.rank (Positive.map f a) := by
  unfold rank
  congr 1
  funext n
  rw [pullback_apply, Positive.map_power f a _ (Positive.rootExponent_pos n)]

theorem rank_le_liminf_of_canonicalConverges {J : Type*} (L : Filter J) [L.NeBot]
    (u : J → ExtendedTrace A) (τ : ExtendedTrace A) (h : CanonicalConverges L u τ)
    (a : Positive A) : τ.rank a ≤ liminf (fun i => (u i).rank a) L := by
  rw [← τ.rank_normalize a, τ.rank_eq_iSup _ (Positive.normalize_norm_le_one a)]
  apply iSup_le
  intro k
  have hb : ∀ᶠ i in L,
      (u i) (Positive.power (Positive.rootExponent k) (Positive.normalize a)) ≤ (u i).rank a := by
    apply Eventually.of_forall
    intro i
    rw [← (u i).rank_normalize a, (u i).rank_eq_iSup _ (Positive.normalize_norm_le_one a)]
    exact le_iSup (fun n : ℕ => (u i) (Positive.power (Positive.rootExponent n) (Positive.normalize a))) k
  exact ((h (Positive.power (Positive.rootExponent k) (Positive.normalize a)) 1 (by norm_num)).2).trans
    (liminf_le_liminf hb)

end ExtendedTrace
end CuntzTrace

end

end OAI
