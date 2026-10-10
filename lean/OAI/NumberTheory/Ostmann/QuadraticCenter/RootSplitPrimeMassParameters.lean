import OAI.NumberTheory.Ostmann.QuadraticCenter.RootSplitPrimeMassBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.QuadraticCenter

theorem rootSplitPrimeMass_modulus_bounds {X eta : ℝ} (hX : 4≤X)
    (heta : eta≤1/1000) {n : ℤ} (hn : n≠0) {m : ℕ} (hm : 0 < m)
    (hmX : (m:ℝ)≤X^eta) (hnX : |(n:ℝ)|≤X^(2*eta)) :
    0 < 4*n.natAbs ∧ 1≤4*m*n.natAbs ∧ 4*n.natAbs∣4*m*n.natAbs ∧
      Real.log (4*n.natAbs:ℕ)≤Real.log 4+2*eta*Real.log X ∧
      Real.log (4*m*n.natAbs:ℕ)≤4*Real.log X := by
  have hXpos : 0 < X := by linarith
  have hXone : 1≤X := by linarith
  have hN : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  have hNr : (0:ℝ)<n.natAbs := by exact_mod_cast hN
  have hmr : (0:ℝ)< m := by exact_mod_cast hm
  have habs : (n.natAbs:ℝ)=|(n:ℝ)| := by
    rw [←Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  have hnX' : (n.natAbs:ℝ)≤X^(2*eta) := by simpa only [habs] using hnX
  have hln := Real.log_le_log hNr hnX'
  have hlm := Real.log_le_log hmr hmX
  rw [Real.log_rpow hXpos] at hln hlm
  have hq : 0 < 4*n.natAbs := by omega
  have hM : 1≤4*m*n.natAbs := by
    have : 0 < 4*m*n.natAbs := by positivity
    omega
  have hd : 4*n.natAbs∣4*m*n.natAbs := ⟨m,by ring⟩
  have hqlog : Real.log (4*n.natAbs:ℕ)=Real.log 4+Real.log n.natAbs := by
    rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num) hNr.ne']
  have hMlog : Real.log (4*m*n.natAbs:ℕ)=Real.log 4+Real.log m+Real.log n.natAbs := by
    rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_ofNat,
      Real.log_mul (mul_pos (by norm_num) hmr).ne' hNr.ne',
      Real.log_mul (by norm_num) hmr.ne']
  refine ⟨hq,hM,hd,?_,?_⟩
  · rw [hqlog]
    nlinarith
  · rw [hMlog]
    have hlogX : 0≤Real.log X := Real.log_nonneg hXone
    have hlogfour : Real.log 4≤Real.log X := Real.log_le_log (by norm_num) hX
    have he := mul_le_mul_of_nonneg_right heta hlogX
    nlinarith

end Ostmann.QuadraticCenter

end

end OAI
