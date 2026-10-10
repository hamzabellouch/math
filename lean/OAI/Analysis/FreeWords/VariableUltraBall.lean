import Mathlib
import OAI.Analysis.FreeWords.UltraDiagonal
import OAI.Analysis.FreeWords.VariableUltraAlgebra

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKUltraTrace

open scoped BoundedContinuousFunction ComplexOrder

open Filter Topology

noncomputable section

theorem ultrafilter_diagonal_indices (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ atTop) (S : ℕ → Set ℕ) (hS : ∀ n, S n ∈ (ω : Filter ℕ)) :
    ∃ k : ℕ → ℕ, Tendsto k (ω : Filter ℕ) atTop ∧
      ∀ᶠ j in (ω : Filter ℕ), j ∈ S (k j) := by
  classical
  let P (j n : ℕ) := ∀ m ≤ n, j ∈ S m
  let k (j : ℕ) := Nat.findGreatest (P j) j
  have hP (n : ℕ) : ∀ᶠ j in (ω : Filter ℕ), P j n := by
    induction n with
    | zero => simpa [P] using hS 0
    | succ n ih =>
      filter_upwards [ih, hS (n+1)] with j hj hn
      intro m hm
      rcases Nat.le_or_eq_of_le_add_one hm with h | rfl
      · exact hj m h
      · exact hn
  refine ⟨k, tendsto_atTop.2 ?_, ?_⟩
  · intro n
    filter_upwards [hP n, hω (eventually_ge_atTop n)] with j hj hjn
    exact Nat.le_findGreatest hjn hj
  · filter_upwards [hP 0] with j hj
    have hg : P j (k j) := Nat.findGreatest_spec (Nat.zero_le j) hj
    exact hg (k j) le_rfl

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (R : ℕ → StarSubalgebra ℂ A) [∀ j, IsClosed (R j : Set A)]

local instance : PartialOrder (coordinateAlgebra R) := CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (coordinateAlgebra R) := CStarAlgebra.spectralOrderedRing _

theorem coordinateVectorBall_isClosed (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ atTop) (b : ℝ) :
    IsClosed (gnsVector (coordinateTrace R τ ω) '' Metric.closedBall (0 : coordinateAlgebra R) b) := by
  apply isClosed_of_closure_subset
  intro y hy
  let e (n : ℕ) : ℝ := ((n : ℝ)+1)⁻¹
  have he (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have hchoose (n : ℕ) : ∃ s : coordinateAlgebra R, ‖s‖ ≤ b ∧
      ‖gnsVector (coordinateTrace R τ ω) s - y‖ < e n := by
    obtain ⟨z, ⟨s, hs, rfl⟩, hz⟩ := Metric.mem_closure_iff.mp hy (e n) (he n)
    exact ⟨s, by simpa using hs, by simpa only [dist_eq_norm, norm_sub_rev] using hz⟩
  choose s hs hsclose using hchoose
  have hR : 0 ≤ b := (norm_nonneg (s 0)).trans (hs 0)
  have hemono {m n : ℕ} (hmn : m ≤ n) : e n ≤ e m := by
    dsimp [e]
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hpair {m n : ℕ} (hmn : m ≤ n) :
      ‖gnsVector (coordinateTrace R τ ω) (s n - s m)‖ < 2 * e m := by
    rw [map_sub]
    calc
      ‖gnsVector (coordinateTrace R τ ω) (s n) - gnsVector (coordinateTrace R τ ω) (s m)‖
        ≤ ‖gnsVector (coordinateTrace R τ ω) (s n) - y‖ +
          ‖gnsVector (coordinateTrace R τ ω) (s m) - y‖ := by simpa only [norm_sub_rev] using norm_sub_le_norm_sub_add_norm_sub (gnsVector (coordinateTrace R τ ω) (s n)) y (gnsVector (coordinateTrace R τ ω) (s m))
      _ < e n + e m := add_lt_add (hsclose n) (hsclose m)
      _ ≤ 2 * e m := by linarith [hemono hmn]
  let S (n : ℕ) : Set ℕ := {j | ∀ m ≤ n, ‖gnsVector τ ((s n - s m).val j)‖ < 3 * e m}
  have hS (n : ℕ) : S n ∈ (ω : Filter ℕ) := by
    have ht (m : ℕ) (hm : m ∈ Finset.range (n+1)) :
        ∀ᶠ j in (ω : Filter ℕ), ‖gnsVector τ ((s n - s m).val j)‖ < 3*e m := by
      have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hb : ‖gnsVector (coordinateTrace R τ ω) (s n - s m)‖ < 3*e m := by
        linarith [hpair hmn, he m]
      exact (tendsto_order.mp (coordinate_norm_tendsto R τ ω (s n - s m))).2 _ hb
    have hh := (Filter.eventually_all_finset (Finset.range (n+1))).mpr ht
    filter_upwards [hh] with j hj
    intro m hm
    exact hj m (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hm))
  obtain ⟨k, hk, hkS⟩ := ultrafilter_diagonal_indices ω hω S hS
  let x₀ : ℕ →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun j => (s (k j)).val j) continuous_of_discreteTopology b
    (fun j => (s (k j)).val.norm_coe_le_norm j |>.trans (hs (k j)))
  let x : coordinateAlgebra R := ⟨x₀,fun j => (s (k j)).property j⟩
  have hx : ‖x‖ ≤ b := (BoundedContinuousFunction.norm_le hR).mpr
    (fun j => (s (k j)).val.norm_coe_le_norm j |>.trans (hs (k j)))
  have hdist (m : ℕ) : ‖gnsVector (coordinateTrace R τ ω) x - gnsVector (coordinateTrace R τ ω) (s m)‖ ≤ 3*e m := by
    rw [← map_sub]
    apply le_of_tendsto (coordinate_norm_tendsto R τ ω (x - s m))
    filter_upwards [hkS, (tendsto_atTop.mp hk) m] with j hj hm
    exact (hj m hm).le
  have htotal (m : ℕ) : ‖gnsVector (coordinateTrace R τ ω) x - y‖ ≤ 4*e m := by
    calc
      ‖gnsVector (coordinateTrace R τ ω) x - y‖ ≤
        ‖gnsVector (coordinateTrace R τ ω) x - gnsVector (coordinateTrace R τ ω) (s m)‖ +
          ‖gnsVector (coordinateTrace R τ ω) (s m)-y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 3*e m + e m := add_le_add (hdist m) (hsclose m).le
      _ = 4*e m := by ring
  have hlim : Tendsto (fun m => 4*e m) atTop (𝓝 0) := by
    have ht : Tendsto (fun m : ℕ => ((m : ℝ)+1)⁻¹) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa [e] using ht.const_mul 4
  have hz : ‖gnsVector (coordinateTrace R τ ω) x-y‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Filter.Eventually.of_forall htotal)
  exact ⟨x, by simpa using hx, sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))⟩

end

end KKVariableUltra
end

end OAI
