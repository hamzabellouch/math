import Mathlib
import OAI.Analysis.FreeWords.UltraDiagonal
import OAI.Analysis.FreeWords.UnitaryLift

namespace OAI

noncomputable section

namespace KKUltraTrace

open scoped ComplexOrder BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

attribute [local instance] KKUltraTrace.seqOrder

attribute [local instance] KKUltraTrace.seqSOR

open scoped InnerProductSpace

end

end KKUltraTrace

namespace KKFactorSupport

open KKUltraTrace

open scoped ComplexOrder InnerProductSpace BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local instance ultraBallFullSeqOrder : PartialOrder (ℕ →ᵇ A) :=
  CStarAlgebra.spectralOrder _

local instance ultraBallFullSeqStarOrderedRing : StarOrderedRing (ℕ →ᵇ A) :=
  CStarAlgebra.spectralOrderedRing _

end

end KKFactorSupport

namespace KKUltraTrace

open Filter Topology

noncomputable section

end

end KKUltraTrace

namespace KKUltraTrace

open scoped BoundedContinuousFunction ComplexOrder

open Filter Topology KKFactorSupport

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local instance ultraBallFullSeqOrder : PartialOrder (ℕ →ᵇ A) :=
  CStarAlgebra.spectralOrder _

local instance ultraBallFullSeqStarOrderedRing : StarOrderedRing (ℕ →ᵇ A) :=
  CStarAlgebra.spectralOrderedRing _

theorem tendsto_ultraVector_norm (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (x : ℕ →ᵇ A) :
    Tendsto (fun j => ‖gnsVector τ (x j)‖) (ω : Filter ℕ)
      (𝓝 ‖gnsVector (ultraTrace τ ω) x‖) := by
  rw [gnsVector_norm_eq_sqrt]
  exact tendsto_gnsVector_norm τ ω x

theorem ultraVectorBall_isClosed (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ atTop) (R : ℝ) :
    IsClosed (gnsVector (ultraTrace τ ω) '' Metric.closedBall (0 : ℕ →ᵇ A) R) := by
  apply isClosed_of_closure_subset
  intro y hy
  let e (n : ℕ) : ℝ := ((n : ℝ)+1)⁻¹
  have he (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have hchoose (n : ℕ) : ∃ s : ℕ →ᵇ A, ‖s‖ ≤ R ∧
      ‖gnsVector (ultraTrace τ ω) s - y‖ < e n := by
    obtain ⟨z, ⟨s, hs, rfl⟩, hz⟩ := Metric.mem_closure_iff.mp hy (e n) (he n)
    exact ⟨s, by simpa using hs, by simpa only [dist_eq_norm, norm_sub_rev] using hz⟩
  choose s hs hsclose using hchoose
  have hR : 0 ≤ R := (norm_nonneg (s 0)).trans (hs 0)
  have hemono {m n : ℕ} (hmn : m ≤ n) : e n ≤ e m := by
    dsimp [e]
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hpair {m n : ℕ} (hmn : m ≤ n) :
      ‖gnsVector (ultraTrace τ ω) (s n - s m)‖ < 2 * e m := by
    rw [map_sub]
    calc
      ‖gnsVector (ultraTrace τ ω) (s n) - gnsVector (ultraTrace τ ω) (s m)‖
        ≤ ‖gnsVector (ultraTrace τ ω) (s n) - y‖ +
          ‖gnsVector (ultraTrace τ ω) (s m) - y‖ := by simpa only [norm_sub_rev] using norm_sub_le_norm_sub_add_norm_sub (gnsVector (ultraTrace τ ω) (s n)) y (gnsVector (ultraTrace τ ω) (s m))
      _ < e n + e m := add_lt_add (hsclose n) (hsclose m)
      _ ≤ 2 * e m := by linarith [hemono hmn]
  let S (n : ℕ) : Set ℕ := {j | ∀ m ≤ n, ‖gnsVector τ ((s n - s m) j)‖ < 3 * e m}
  have hS (n : ℕ) : S n ∈ (ω : Filter ℕ) := by
    have ht (m : ℕ) (hm : m ∈ Finset.range (n+1)) :
        ∀ᶠ j in (ω : Filter ℕ), ‖gnsVector τ ((s n - s m) j)‖ < 3*e m := by
      have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hb : ‖gnsVector (ultraTrace τ ω) (s n - s m)‖ < 3*e m := by
        linarith [hpair hmn, he m]
      exact (tendsto_order.mp (tendsto_ultraVector_norm τ ω (s n - s m))).2 _ hb
    have hh := (Filter.eventually_all_finset (Finset.range (n+1))).mpr ht
    filter_upwards [hh] with j hj
    intro m hm
    exact hj m (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hm))
  obtain ⟨k, hk, hkS⟩ := ultrafilter_diagonal_indices ω hω S hS
  let x : ℕ →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun j => s (k j) j) continuous_of_discreteTopology R
    (fun j => (s (k j)).norm_coe_le_norm j |>.trans (hs (k j)))
  have hx : ‖x‖ ≤ R := (BoundedContinuousFunction.norm_le hR).mpr
    (fun j => (s (k j)).norm_coe_le_norm j |>.trans (hs (k j)))
  have hdist (m : ℕ) : ‖gnsVector (ultraTrace τ ω) x - gnsVector (ultraTrace τ ω) (s m)‖ ≤ 3*e m := by
    rw [← map_sub]
    apply le_of_tendsto (tendsto_ultraVector_norm τ ω (x - s m))
    filter_upwards [hkS, (tendsto_atTop.mp hk) m] with j hj hm
    exact (hj m hm).le
  have htotal (m : ℕ) : ‖gnsVector (ultraTrace τ ω) x - y‖ ≤ 4*e m := by
    calc
      ‖gnsVector (ultraTrace τ ω) x - y‖ ≤
        ‖gnsVector (ultraTrace τ ω) x - gnsVector (ultraTrace τ ω) (s m)‖ +
          ‖gnsVector (ultraTrace τ ω) (s m)-y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 3*e m + e m := add_le_add (hdist m) (hsclose m).le
      _ = 4*e m := by ring
  have hlim : Tendsto (fun m => 4*e m) atTop (𝓝 0) := by
    have ht : Tendsto (fun m : ℕ => ((m : ℝ)+1)⁻¹) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa [e] using ht.const_mul 4
  have hz : ‖gnsVector (ultraTrace τ ω) x-y‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Filter.Eventually.of_forall htotal)
  exact ⟨x, by simpa using hx, sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))⟩

end

end KKUltraTrace
end

end OAI
