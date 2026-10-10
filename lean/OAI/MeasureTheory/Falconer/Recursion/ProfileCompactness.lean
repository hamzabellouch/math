import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sequences
import Mathlib.Tactic

namespace OAI

/-! # Compactness of normalized Lipschitz scale profiles -/

namespace Falconer
open Set Metric Filter BoundedContinuousFunction
open scoped Topology NNReal

abbrev ProfileDomain := Icc (0:ℝ) 1
abbrev BoundedProfile := ProfileDomain →ᵇ ℝ

def normalizedLipschitzProfiles (K : ℝ≥0) : Set BoundedProfile :=
  {f | f ⟨0,by constructor <;> norm_num⟩ = 0 ∧ LipschitzWith K f}

theorem normalizedLipschitzProfiles_closed (K : ℝ≥0) :
    IsClosed (normalizedLipschitzProfiles K) := by
  have hzero : IsClosed {f : BoundedProfile | f ⟨0,by constructor <;> norm_num⟩ = 0} :=
    isClosed_eq (continuous_eval_const _) continuous_const
  have hlip : IsClosed {f : BoundedProfile | LipschitzWith K f} := by
    have he : {f : BoundedProfile | LipschitzWith K f} =
        ⋂ x : ProfileDomain, ⋂ y : ProfileDomain,
          {f : BoundedProfile | dist (f x) (f y) ≤ (K:ℝ)*dist x y} := by
      ext f
      simp only [mem_ofPred_eq,mem_iInter]
      exact ⟨fun h x y => h.dist_le_mul x y,fun h => LipschitzWith.of_dist_le_mul h⟩
    rw [he]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le ((continuous_eval_const x).dist (continuous_eval_const y)) continuous_const
  exact hzero.inter hlip

theorem normalizedLipschitzProfiles_compact (K : ℝ≥0) :
    IsCompact (normalizedLipschitzProfiles K) := by
  apply arzela_ascoli₂ (Icc (-(K:ℝ)) K) isCompact_Icc _
    (normalizedLipschitzProfiles_closed K)
  · intro f x hf
    have hh := hf.2.dist_le_mul x ⟨0,by constructor <;> norm_num⟩
    rw [hf.1,Real.dist_eq,sub_zero] at hh
    have hx : dist x (⟨0,by constructor <;> norm_num⟩ : ProfileDomain) ≤ 1 := by
      change dist (x:ℝ) 0 ≤ 1
      simpa only [Real.dist_eq,sub_zero,abs_of_nonneg x.property.1] using x.property.2
    have hb : |f x| ≤ (K:ℝ) := hh.trans (by simpa using mul_le_mul_of_nonneg_left hx K.coe_nonneg)
    exact abs_le.mp hb
  · apply Metric.equicontinuous_of_continuity_modulus (fun r => (K:ℝ)*r)
      (by simpa only [mul_zero] using
        (tendsto_const_nhds.mul tendsto_id : Tendsto (fun r : ℝ => (K:ℝ)*r) (𝓝 0) (𝓝 ((K:ℝ)*0))))
    intro x y f
    exact f.property.2.dist_le_mul x y

theorem normalized_profile_subsequence {K : ℝ≥0} (f : ℕ → BoundedProfile)
    (hf : ∀ n, f n ∈ normalizedLipschitzProfiles K) :
    ∃ m ∈ normalizedLipschitzProfiles K, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ u : ProfileDomain, |f (φ n) u-m u| < ε := by
  obtain ⟨m,hm,φ,hφ,hlim⟩ := (normalizedLipschitzProfiles_compact K).tendsto_subseq hf
  refine ⟨m,hm,φ,hφ,fun ε hε => ?_⟩
  have he : ∀ᶠ n in atTop, dist (f (φ n)) m < ε :=
    (tendsto_iff_dist_tendsto_zero.mp hlim).eventually (eventually_lt_nhds hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,fun n hn u => ?_⟩
  exact (show |f (φ n) u-m u| ≤ dist (f (φ n)) m from by simpa only [Real.dist_eq] using
      (dist_coe_le_dist (f := f (φ n)) (g := m) u)).trans_lt (hN n hn)

end Falconer

end OAI
