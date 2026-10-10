import OAI.MeasureTheory.Falconer.Fourier.JointStationaryGeometry

namespace OAI

/-! # The exact derivative cost of the local stationary coefficients

The actual coefficient of order `j` costs `2*j` derivatives. The fixed
patch mask extends it smoothly to the whole ambient space without changing
that scale exponent.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

theorem actualStationaryCoefficient_uniform_budget (m j r : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ B : Space (m+3) → ℂ,
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ l ≤ r+2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ l B w‖ ≤ C*D^l) →
      ∀ k ≤ r, ∀ e : Space (m+3),
        ‖e-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/4 →
        ‖iteratedFDeriv ℝ k (actualStationaryCoefficient m j B) e‖ ≤ A*C*D^(r+2*j) := by
  obtain ⟨H,hH,hHb⟩ := joint_stationary_amplitude_budget m (r+2*j)
  let a := ‖sphereStationaryConstant (m+2) /
    ((2*Complex.I)^j * (j.factorial : ℂ))‖ * ((m+2 : ℕ) : ℝ)^j
  have ha : 0 ≤ a := mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _)
  refine ⟨a*H,mul_nonneg ha hH,?_⟩
  intro B hB C D hC hD hder k hk e he
  have heK : (e,(0 : Space (m+2))) ∈ jointStationaryCompact m := by
    constructor
    · simpa only [mem_closedBall,dist_eq_norm] using he
    · simp
  have hb := quadraticJetCoefficient_derivative_bound_on
    (jointStationaryRegion_isOpen m)
    (fun z hz => (unmaskedStationaryAmplitude_contDiffAt_region m hB hz).contDiffWithinAt)
    j k (jointStationaryCompact_subset m heK)
  change ‖iteratedFDeriv ℝ k (actualStationaryCoefficient m j B) e‖ ≤ _ at hb
  have hh := hHb B hB C D hC hD hder (k+2*j) (by omega) (e,0) heK
  apply (hb.trans (mul_le_mul_of_nonneg_left hh ha)).trans_eq
  dsimp [a]
  ring

theorem stationaryPatchMask_uniform_budget (m r : ℕ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ k ≤ r, ∀ x : Space (m+3),
      ‖iteratedFDeriv ℝ k (fun x => (stationaryPatchMask m x : ℂ)) x‖ ≤ Q := by
  choose P hP hPb using fun j => capBump_ambient_derivatives (m+3) j
  let Q := ∑ j ∈ Finset.range (r+1), P j*(4 : ℝ)^j
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun j _ =>
    mul_nonneg (hP j) (pow_nonneg (by norm_num) j))
  refine ⟨Q,hQ,?_⟩
  intro k hk x
  have hn := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
    ((stationaryPatchMask_contDiff m).contDiffAt (x := x))
    (show (k : ℕ∞ω) ≤ ∞ by simp)
  change ‖iteratedFDeriv ℝ k (Complex.ofRealLI ∘ stationaryPatchMask m) x‖ ≤ _
  rw [hn]
  apply (hPb k (1/4) (by norm_num) (gnomonicChart (0 : Space (m+2))) x).trans
  simp only [one_div,inv_inv]
  exact Finset.single_le_sum (fun j _ => mul_nonneg (hP j) (pow_nonneg (by norm_num) j))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

/-- This global bound is suitable for iterating the inverse recurrence.
Only the original symbol's derivatives at sphere points are needed. -/
theorem maskedStationaryCoefficient_uniform_budget (m j r : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ B : Space (m+3) → ℂ,
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ l ≤ r+2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ l B w‖ ≤ C*D^l) →
      ∀ k ≤ r, ∀ x : Space (m+3),
        ‖iteratedFDeriv ℝ k (maskedStationaryCoefficient m j B) x‖ ≤ A*C*D^(r+2*j) := by
  obtain ⟨H,hH,hHb⟩ := actualStationaryCoefficient_uniform_budget m j r
  obtain ⟨Q,hQ,hQb⟩ := stationaryPatchMask_uniform_budget m r
  refine ⟨2^r*Q*H,by positivity,?_⟩
  intro B hB C D hC hD hder k hk x
  by_cases hx : x ∈ tsupport (stationaryPatchMask m)
  · have he : ‖x-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/4 := by
      simpa only [stationaryPatchMask_support,mem_closedBall,dist_eq_norm] using hx
    have hE : 0 ≤ H*C*D^(r+2*j) := by positivity
    have hh := mixed_product_uniform_bound_at
      ((Complex.ofRealCLM.contDiff.comp (stationaryPatchMask_contDiff m)).contDiffAt)
      (actualStationaryCoefficient_contDiffAt m j hB (stationary_patch_ne_antipode m he))
      hQ hE k (fun l hl => hQb l (hl.trans hk) x)
      (fun l hl => hHb B hB C D hC hD hder l (hl.trans hk) x he)
    change ‖iteratedFDeriv ℝ k (fun y => (stationaryPatchMask m y : ℂ)*
      actualStationaryCoefficient m j B y) x‖ ≤ _
    apply hh.trans
    calc
      _ ≤ 2^r*Q*(H*C*D^(r+2*j)) := by gcongr; norm_num
      _ = _ := by ring
  · have he : maskedStationaryCoefficient m j B =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      change stationaryPatchMask m y = (0 : ℝ) at hy
      simp only [maskedStationaryCoefficient,hy,Complex.ofReal_zero,zero_mul]
    have hz : iteratedFDeriv ℝ k (maskedStationaryCoefficient m j B) x = 0 := by
      simpa using (he.iteratedFDeriv ℝ k).self_of_nhds
    rw [hz,norm_zero]
    positivity

/-- A common constant retains each derivative's own scale power. This is
the form used by the triangular inverse recursion. -/
theorem maskedStationaryCoefficient_scaled_budget (m j r : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ B : Space (m+3) → ℂ,
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ l ≤ r+2*j, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ l B w‖ ≤ C*D^l) →
      ∀ k ≤ r, ∀ x : Space (m+3),
        ‖iteratedFDeriv ℝ k (maskedStationaryCoefficient m j B) x‖ ≤ A*C*D^(k+2*j) := by
  choose A hA hAb using fun k => maskedStationaryCoefficient_uniform_budget m j k
  let H := ∑ k ∈ Finset.range (r+1), A k
  have hH : 0 ≤ H := Finset.sum_nonneg (fun k _ => hA k)
  refine ⟨H,hH,?_⟩
  intro B hB C D hC hD hder k hk x
  have hh := hAb k B hB C D hC hD
    (fun l hl => hder l (by omega)) k le_rfl x
  have hAH : A k ≤ H := Finset.single_le_sum (fun k _ => hA k)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hAH hC) (pow_nonneg (zero_le_one.trans hD) _))

end Falconer

end OAI
