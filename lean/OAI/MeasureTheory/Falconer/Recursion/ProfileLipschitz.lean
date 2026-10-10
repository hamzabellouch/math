import OAI.MeasureTheory.Falconer.Recursion.ProfileInterpolation
import OAI.MeasureTheory.Falconer.Estimates.QuantitativeDifferentiation

namespace OAI

/-! The actual regularized branching profile has the global Lipschitz bound
required by quantitative differentiation, including its constant tails. -/
namespace Falconer.Regularization

theorem finiteRampProfile_increment_all (d c : ℕ → ℝ) (K : ℕ) {C u v : ℝ}
    (hd : Antitone d) (hC : 0 ≤ C) (hc : ∀ i < K, 0 ≤ c i ∧ c i ≤ C)
    (huv : u ≤ v) :
    0 ≤ finiteRampProfile d c K v-finiteRampProfile d c K u ∧
      finiteRampProfile d c K v-finiteRampProfile d c K u ≤ C*(v-u) := by
  have he : finiteRampProfile d c K v-finiteRampProfile d c K u =
      ∑ i ∈ Finset.range K, c i*(intervalRamp (d (i+1)) (d i) v-
        intervalRamp (d (i+1)) (d i) u) := by
    simp only [finiteRampProfile,← Finset.sum_sub_distrib,mul_sub]
  have hr (i : ℕ) := intervalRamp_increment (hd (Nat.le_succ i)) huv
  rw [he]
  constructor
  · exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (hc i (Finset.mem_range.mp hi)).1 (hr i).1
  · calc
      _ ≤ ∑ i ∈ Finset.range K, C*(intervalRamp (d (i+1)) (d i) v-
          intervalRamp (d (i+1)) (d i) u) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
          (hc i (Finset.mem_range.mp hi)).2 (hr i).1
      _ = C*(intervalRamp (d K) (d 0) v-intervalRamp (d K) (d 0) u) := by
        rw [← Finset.mul_sum,Finset.sum_sub_distrib,intervalRamp_sum,intervalRamp_sum]
        unfold intervalRamp
        ring
      _ ≤ C*(v-u) := mul_le_mul_of_nonneg_left
        (intervalRamp_increment (hd (Nat.zero_le K)) huv).2 hC

theorem planarProfile_lipschitz {N : ℕ} (hN : 0 < N) {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (F : CellPath 2 → List ℕ) (B K : ℕ) (p : CellPath 2) :
    LipschitzWith 2 (fun x : ℝ => regularizedProfile L F N B K p ((N : ℝ)*x)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hi {u v : ℝ} (huv : u ≤ v) :
      0 ≤ regularizedProfile L F N B K p ((N : ℝ)*v)-
        regularizedProfile L F N B K p ((N : ℝ)*u) ∧
      regularizedProfile L F N B K p ((N : ℝ)*v)-
        regularizedProfile L F N B K p ((N : ℝ)*u) ≤ 2*(v-u) := by
    have hstep := finiteRampProfile_increment_all
      (fun i => (blockDepth N B i : ℝ)) (fun i => blockSlope L F N B i p) K
      (show Antitone (fun i => (blockDepth N B i : ℝ)) from fun _ _ h =>
        Nat.cast_le.mpr (blockDepth_antitone N B h))
      (show 0 ≤ (2 : ℝ)/(N : ℝ) by positivity)
      (fun i _ => blockSlope_bounds hN hL F B i p)
      (mul_le_mul_of_nonneg_left huv hNR.le)
    refine ⟨hstep.1,hstep.2.trans_eq ?_⟩
    field_simp
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [Real.dist_eq,NNReal.coe_ofNat]
  by_cases hxy : x ≤ y
  · have hb := hi hxy
    rw [abs_of_nonpos (by linarith [hb.1]),abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith [hb.2]
  · have hb := hi (le_of_not_ge hxy)
    rw [abs_of_nonneg hb.1,abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hxy))]
    exact hb.2

theorem planarProfile_linear_decomposition {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (N : ℕ), 0 < N → ∀ (L : Finset (CellPath 2)),
      L ⊆ cubePaths 2 N → ∀ (F : CellPath 2 → List ℕ) (B K : ℕ) (p : CellPath 2),
      ∃ S : List (ℝ × ℝ), S.Pairwise (fun c d => c.1+c.2 ≤ d.1) ∧
        1-ε ≤ (S.map Prod.snd).sum ∧
        ∀ c ∈ S, 0 ≤ c.1 ∧ c.1+c.2 ≤ 1 ∧ τ ≤ c.2 ∧
          ∀ x ∈ Set.Icc c.1 (c.1+c.2),
            |intervalSecantError (fun u => regularizedProfile L F N B K p ((N : ℝ)*u))
              c.1 c.2 x| ≤ ε*c.2 := by
  obtain ⟨τ,hτ,ht⟩ := quantitative_linear_decomposition hε
  refine ⟨τ,hτ,?_⟩
  intro N hN L hL F B K p
  have hd := ht (fun u => regularizedProfile L F N B K p ((N : ℝ)*u))
    (planarProfile_lipschitz hN hL F B K p) 0 1 (by norm_num)
  simpa only [zero_add,one_mul,mul_one] using hd

end Falconer.Regularization

end OAI
