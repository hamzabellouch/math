import OAI.MeasureTheory.Falconer.Recursion.ProfileInterpolation

namespace OAI

/-!
# The constructed d-Lipschitz profiles on the unit interval

This is the paper's normalization of the finite-tree profile. Its slope
bound is the ambient dimension d, and its values lie between zero and d.
-/

namespace Falconer.Regularization
open Set
variable {d : ℕ}

noncomputable def unitProfile (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B : ℕ) (p : CellPath d) (u : ℝ) : ℝ :=
  regularizedProfile L F N B (N/B+1) p ((N : ℝ)*u)

theorem unitProfile_continuous (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B : ℕ) (p : CellPath d) : Continuous (unitProfile L F N B p) :=
  (regularizedProfile_continuous L F N B (N/B+1) p).comp (continuous_const.mul continuous_id)

theorem unitProfile_zero (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B : ℕ) (p : CellPath d) : unitProfile L F N B p 0 = 0 := by
  simp only [unitProfile,mul_zero,regularizedProfile_zero]

theorem unitProfile_increment {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) (p : CellPath d) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    0 ≤ unitProfile L F N B p v-unitProfile L F N B p u ∧
      unitProfile L F N B p v-unitProfile L F N B p u ≤ (d : ℝ)*(v-u) := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hm := regularizedProfile_increment hN hL F hB p
    (mul_nonneg hN0.le hu) (mul_le_mul_of_nonneg_left huv hN0.le)
    (by nlinarith : (N : ℝ)*v ≤ N)
  refine ⟨hm.1,hm.2.trans_eq ?_⟩
  field_simp

theorem unitProfile_monotoneOn {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) (p : CellPath d) :
    MonotoneOn (unitProfile L F N B p) (Icc 0 1) := by
  intro u hu v hv huv
  exact sub_nonneg.mp (unitProfile_increment hN hB hL F p hu.1 huv hv.2).1

theorem unitProfile_lipschitzOn {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) (p : CellPath d) :
    LipschitzOnWith (d : NNReal) (unitProfile L F N B p) (Icc 0 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  rcases le_total v u with hvu | huv
  · have hi := unitProfile_increment hN hB hL F p hv.1 hvu hu.2
    simpa only [Real.dist_eq,abs_of_nonneg hi.1,abs_of_nonneg (sub_nonneg.mpr hvu),
      NNReal.coe_natCast] using hi.2
  · have hi := unitProfile_increment hN hB hL F p hu.1 huv hv.2
    rw [dist_comm,Real.dist_eq,abs_of_nonneg hi.1,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr huv)]
    simpa only [NNReal.coe_natCast,neg_sub] using hi.2

theorem unitProfile_range {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) (p : CellPath d) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    unitProfile L F N B p u ∈ Icc (0 : ℝ) (d : ℝ) := by
  have h := unitProfile_increment hN hB hL F p (u := 0) (v := u) (by rfl) hu.1 hu.2
  rw [unitProfile_zero,sub_zero,sub_zero] at h
  exact ⟨h.1,h.2.trans (mul_le_of_le_one_right (Nat.cast_nonneg d) hu.2)⟩

end Falconer.Regularization

end OAI
