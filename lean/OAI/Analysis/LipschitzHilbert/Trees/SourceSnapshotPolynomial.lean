import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictableDecay
import OAI.Analysis.LipschitzHilbert.Trees.SourceSnapshotSize

namespace OAI

/-! The actual source snapshot envelope is a fixed polynomial in L.
This supplies the unnormalized size input for the normalized-motion theorem. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem source_snapshot_envelope_polynomial {L C A q a Z S : ℝ} {K : ℕ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (_hA : 0 ≤ A) (hAq : A ≤ L^q)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hZ0 : 0 ≤ Z) (hZ : Z ≤ 2*L^2)
    (hK : (K:ℝ) ≤ L^2) (hS : Real.log (max 1 S) ≤ 3*L) :
    (C^8*A*(1+(a+Z*K)*(Real.log (max 1 S)+1)))*C^3 ≤
      (13*C^11)*L^(q+5) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hL4 : 1 ≤ L^4 := one_le_pow₀ hL
  have hL5 : 1 ≤ L^5 := one_le_pow₀ hL
  have hZK : Z*K ≤ 2*L^4 := by
    have hb := mul_le_mul hZ hK (Nat.cast_nonneg K) (by positivity : 0 ≤ 2*L^2)
    nlinarith
  have hlog : 0 ≤ Real.log (max 1 S) := Real.log_nonneg (le_max_left _ _)
  have hfirst : a+Z*K ≤ 3*L^4 := by linarith
  have hsecond : Real.log (max 1 S)+1 ≤ 4*L := by linarith
  have hcore : 1+(a+Z*K)*(Real.log (max 1 S)+1) ≤ 13*L^5 := by
    have hb := mul_le_mul hfirst hsecond (by positivity : 0 ≤ Real.log (max 1 S)+1)
      (by positivity : 0 ≤ 3*L^4)
    nlinarith
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_left hAq (by positivity : 0 ≤ C^8)) hcore
      (by positivity : 0 ≤ 1+(a+Z*K)*(Real.log (max 1 S)+1))
      (by positivity : 0 ≤ C^8*L^q)) (by positivity : 0 ≤ C^3)
  calc
    _ ≤ (C^8*L^q*(13*L^5))*C^3 := hbound
    _ = (13*C^11)*(L^q*L^(5:ℕ)) := by ring
    _ = _ := by
      rw [← Real.rpow_natCast L 5,← Real.rpow_add hL0]
      norm_num only [Nat.cast_ofNat]

theorem eventually_source_snapshot_envelope (C q : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (A a Z S : ℝ) (K : ℕ),
      0 ≤ A → A ≤ L^q → 0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 →
      (K:ℝ) ≤ L^2 → Real.log (max 1 S) ≤ 3*L →
      (C^8*A*(1+(a+Z*K)*(Real.log (max 1 S)+1)))*C^3 ≤ L^(q+6) := by
  filter_upwards [eventually_ge_atTop (1:ℝ), eventually_ge_atTop (13*C^11)] with L hL hconst
  intro A a Z S K hA hAq ha0 ha1 hZ0 hZ hK hS
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  calc
    _ ≤ (13*C^11)*L^(q+5) :=
      source_snapshot_envelope_polynomial hL hC hA hAq ha0 ha1 hZ0 hZ hK hS
    _ ≤ L*L^(q+5) := mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hL0.le _)
    _ = L^(1:ℝ)*L^(q+5) := by rw [Real.rpow_one]
    _ = L^((1:ℝ)+(q+5)) := (Real.rpow_add hL0 _ _).symm
    _ = L^(q+6) := by congr 1; ring

end LipschitzHilbert

end

end OAI
