import OAI.Analysis.LipschitzHilbert.Packets.TopRawPacketData

namespace OAI

/-! The explicit top concentration amplitude is at most quadratic in
the raw packet constant, uniformly before all finite packet families. -/

noncomputable section
namespace LipschitzHilbert

theorem topPairConstant_linear (C : ℝ) (q : ℕ) :
    topPairConstant C q = topPairConstant 1 q*C := by
  unfold topPairConstant
  ring

namespace PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem normalized_coefficient_budget (P : PlanarPacketFamily N κ ι) (A : ℝ) :
    A*P.constant^2*P.coefficientScale⁻¹^2 = A/Real.pi^4 := by
  unfold coefficientScale
  field_simp [P.constant_pos.ne', Real.pi_ne_zero]

end PlanarPacketFamily

theorem uniform_topPacketAmplitude_bound (Ab Am : ℝ) (D : ℕ)
    (hAb : 0 < Ab) (hAm : 0 < Am) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι),
      P.topPacketAmplitude Ab Am D ≤ A*(P.constant+1)^2 := by
  let c := topPairConstant 1 (8*D+1)
  let b := Am*c^2*(Ab/Real.pi^4)+1
  let k := lineMomentBase c b 2
  let A := Real.pi^2*256^(8*D+1)*24*k
  have hc : 0 < c := topPairConstant_pos _ _ (by norm_num)
  have hb : 0 < b := by dsimp [b]; positivity
  have hk : 0 < k := lineMomentBase_pos c b 2 hc.le (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A,hA,?_⟩
  intro N κ ι _ _ P
  have hconstant := P.constant_pos
  let t := P.constant+1
  have ht : 1 ≤ t := by dsimp [t]; linarith [P.constant_pos]
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hpc : P.constant ≤ t := by dsimp [t]; linarith
  have hbudget := P.normalized_coefficient_budget Ab
  let C := topPairConstant P.constant (8*D+1)
  let S := Am*C^2*(Ab*P.constant^2*P.coefficientScale⁻¹^2)+1
  have hC : C = c*P.constant := topPairConstant_linear _ _
  have hCbound : C ≤ c*t := by rw [hC]; exact mul_le_mul_of_nonneg_left hpc hc.le
  have hS : S ≤ b*t^2 := by
    have ha : 0 ≤ Am*c^2*(Ab/Real.pi^4) := by positivity
    have hsq : P.constant^2 ≤ t^2 := pow_le_pow_left₀ P.constant_pos.le hpc 2
    have hone : (1:ℝ) ≤ t^2 := one_le_pow₀ ht
    calc
      S = (Am*c^2*(Ab/Real.pi^4))*P.constant^2+1 := by
        dsimp only [S]
        rw [hC,hbudget]
        ring
      _ ≤ (Am*c^2*(Ab/Real.pi^4))*t^2+t^2 :=
        add_le_add (mul_le_mul_of_nonneg_left hsq ha) hone
      _ = b*t^2 := by dsimp [b]; ring
  have hsqrt : Real.sqrt S ≤ Real.sqrt b*t := by
    apply (Real.sqrt_le_sqrt hS).trans_eq
    rw [Real.sqrt_mul hb.le, Real.sqrt_sq ht0.le]
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  have hline : lineMomentBase C S 2 ≤ k*t := by
    calc
      lineMomentBase C S 2 ≤
          16*((4*(2*(Real.sqrt b*t)+4*((c*t)*(4*Real.pi)^2)))/Real.log (3/2)+
            Real.sqrt b*t+t) := by
        unfold lineMomentBase
        norm_num only
        gcongr
      _ = k*t := by dsimp [k,lineMomentBase]; ring
  calc
    P.topPacketAmplitude Ab Am D =
        P.constant*Real.pi^2*256^(8*D+1)*(24*lineMomentBase C S 2) := by
      rfl
    _ ≤ P.constant*Real.pi^2*256^(8*D+1)*(24*(k*t)) := by gcongr
    _ ≤ t*Real.pi^2*256^(8*D+1)*(24*(k*t)) := by gcongr
    _ = A*(P.constant+1)^2 := by dsimp [A,t]; ring

end LipschitzHilbert

end

end OAI
