import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PrefactorCalibration
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibrationMesh

namespace OAI

/-! A nominal test at unit weight bounds the shared rational spacing even
when the particular source has no edges. No approximation certificate for
logarithm evaluation needs to be added to the construction interface. -/

noncomputable section
namespace ContinuumCoulomb.PrefactorCalibration

theorem spacing_bounds (rho : ℕ) (a : ℚ) (C : ℕ) {ε c : ℚ}
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1/1000) (hc : 0 < c)
    (k A B N P : ℕ) (hN : 2 ≤ N)
    (hlen :
      (1-(ε:ℝ))*((k:ℝ)*Real.log (CalibrationMesh.base N)) ≤
        value rho a C ε c k A B (CalibrationMesh.base N,(P,1)) ∧
      (value rho a C ε c k A B (CalibrationMesh.base N,(P,1)):ℝ) ≤
        (1+(ε:ℝ))*((k:ℝ)*Real.log (CalibrationMesh.base N))) :
    (59/2:ℝ)*(k:ℝ)*Real.log N ≤ AutomaticCalibration.spacing c k (CalibrationMesh.base N) ∧
      (AutomaticCalibration.spacing c k (CalibrationMesh.base N):ℝ) ≤ 31*(k:ℝ)*Real.log N := by
  let Q := AutomaticCalibration.spacing c k (CalibrationMesh.base N)
  let x : AutomaticCalibration.Input := (CalibrationMesh.base N,(P,1))
  let t := (normalizedValue rho a C ε c k A B x:ℝ)
  let r := (value rho a C ε c k A B x:ℝ)
  have hbase : 0 < CalibrationMesh.base N := lt_of_lt_of_le (by decide : 0 < 2)
    (CalibrationMesh.base_ge_two hN)
  have hQ : (0:ℝ) < Q := by exact_mod_cast AutomaticCalibration.spacing_positive hc k _ hbase
  have he : (Q:ℝ)*t=r := by
    dsimp only [t,r,normalizedValue,x,Q]
    push_cast
    field_simp [show (AutomaticCalibration.spacing c k (CalibrationMesh.base N):ℝ) ≠ 0 from hQ.ne']
  obtain ⟨htl,htu⟩ := normalizedValue_mem rho a C hε hc k A B x hbase
  have hεR : (0:ℝ) ≤ ε := by exact_mod_cast hε
  have hεRsmall : (ε:ℝ) ≤ 1/1000 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hεsmall
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hh
  have htlR : (1:ℝ)-(ε:ℝ)/2 ≤ t := by
    have hh := (Rat.cast_le (K := ℝ)).mpr htl
    simpa only [Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat,t] using hh
  have htuR : t ≤ (1:ℝ)+(ε:ℝ)/2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr htu
    simpa only [Rat.cast_add,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat,t] using hh
  have ht0 : (999/1000:ℝ) ≤ t := by linarith
  have ht1 : t ≤ (1001/1000:ℝ) := by linarith
  have hmul0 := mul_le_mul_of_nonneg_left ht0 hQ.le
  have hmul1 := mul_le_mul_of_nonneg_left ht1 hQ.le
  rw [he] at hmul0 hmul1
  have hlog : Real.log (CalibrationMesh.base N:ℝ)=30*Real.log N := by
    simp only [CalibrationMesh.base,Nat.cast_pow,Real.log_pow]
    norm_num
  have hx : 0 ≤ (k:ℝ)*Real.log N := mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
  change (1-(ε:ℝ))*((k:ℝ)*Real.log (CalibrationMesh.base N)) ≤ r ∧
    r ≤ (1+(ε:ℝ))*((k:ℝ)*Real.log (CalibrationMesh.base N)) at hlen
  rw [hlog] at hlen
  have hl := mul_le_mul_of_nonneg_right hεRsmall hx
  constructor <;> nlinarith [hlen.1,hlen.2]

end ContinuumCoulomb.PrefactorCalibration

end

end OAI
