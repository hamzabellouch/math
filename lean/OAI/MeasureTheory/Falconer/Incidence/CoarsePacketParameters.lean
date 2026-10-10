import OAI.MeasureTheory.Falconer.Estimates.FiberRegularityBudget
import OAI.MeasureTheory.Falconer.Estimates.PacketSamplingBudget
import OAI.MeasureTheory.Falconer.Estimates.PacketPolynomialLoss
import OAI.MeasureTheory.Falconer.Estimates.PacketCardinalityScales

namespace OAI

/-! A single weak exponent pays for the complete coarse-packet application. -/
namespace Falconer

theorem coarse_packet_parameters {κ θ : ℝ} (hκ : 0 < κ) (hθ : 0 < θ) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let δ := 1/(2:ℝ)^(n+3)
      let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      let D := Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2)
      1 ≤ E ∧ 100 ≤ D ∧ ∀ s t K KP KF m M mF MF L J B : ℝ,
      0 ≤ s → s ≤ 1 → t ≤ 2 → κ ≤ t-s → 1 ≤ K → K ≤ E → 0 ≤ KP → KP ≤ E →
      1 ≤ KF → KF ≤ E → 0 < m → 0 ≤ M → M ≤ E/δ^s → 1/(E*δ^s) ≤ m →
      0 ≤ L → L ≤ E/(δ^s)^2 → 0 < J → J ≤ E → 0 < B → B ≤ E/Δ^s →
      1/(E*(Δ^s)^2) ≤ mF → 0 < MF → MF ≤ E/(Δ^s)^2 →
      (∀ C : Finset (Space 2), C.Nonempty →
        4*pencilEnergyCutoff (n+3) s t (50*K) M (m/50) C*
          (4*L/((m/50)*(C.card:ℝ)))^2*(2:ℝ)^(t-s) ≤ D/100) ∧
      Real.exp ((s-θ)*((n+2:ℕ):ℝ)*Real.log 2) ≤ mF/(4*J*B) ∧
      KF*Δ^s*MF ≤ Real.exp ((s+θ)*((n+2:ℕ):ℝ)*Real.log 2) ∧
      KF*(4*J*B*MF/mF) ≤ D/Δ^s ∧
      projectedSubsetSampleConstant n s t (25*K*(4:ℝ)^s) KP
        (mF/(4*J*B*(KF*Δ^s*MF))) ≤ D := by
  let H := projectionGapConstant κ
  let CF := 2*100*1127219200*(1+H)*(50:ℝ)^12
  let CS := (100:ℝ)^8*(512*(64*Real.exp 1*(1+32*H)+100)^2)
  let A := CF+CS
  have hH : 0 < H := projectionGapConstant_pos hκ
  have hCF : 0 ≤ CF := by dsimp [CF]; positivity
  have hCS : 0 ≤ CS := by dsimp [CS]; positivity
  obtain ⟨ε,N0,hε,hN0,hcost⟩ := packet_polynomial_loss hθ (show 0 ≤ A by dsimp [A]; positivity)
  refine ⟨ε,N0,hε,hN0,?_⟩
  intro n hn
  dsimp only
  let E := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let D := Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2)
  obtain ⟨hE,hD,h16,hall⟩ := hcost (n+2) hn
  refine ⟨hE,hD,?_⟩
  intro s t K KP KF m M mF MF L J B hs hs1 ht hgap hK hKE hKP hKPE hKF hKFE hm hM hME hmE
    hL hLE hJ hJE hB hBE hmFE hMF hMFE
  have hst : s < t := by linarith only [hκ,hgap]
  have hE0 : 0 < E := Real.exp_pos _
  have hN : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hE12 : E^12 ≤ E^48 := pow_le_pow_right₀ hE (by norm_num)
  have hE40 : E^40 ≤ E^48 := pow_le_pow_right₀ hE (by norm_num)
  have hdepth : (n:ℝ)+4 ≤ 2*((n:ℝ)+3)^2 := by nlinarith only [hN]
  have hall' : A*((n:ℝ)+3)^2*E^48 ≤ D := by
    have heq : (n:ℝ)+3 = ((n+2:ℕ):ℝ)+1 := by push_cast; ring
    rw [heq]
    exact hall
  have hCFall : CF*((n:ℝ)+3)^2*E^48 ≤ D := by
    apply le_trans _ hall'
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (show CF ≤ A by dsimp [A]; linarith only [hCS]) (sq_nonneg _)) (pow_nonneg hE0.le _)
  have hCSall : CS*((n:ℝ)+3)^2*E^48 ≤ D := by
    apply le_trans _ hall'
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (show CS ≤ A by dsimp [A]; linarith only [hCF]) (sq_nonneg _)) (pow_nonneg hE0.le _)
  obtain ⟨hlo,hup,hreg⟩ := packet_cardinality_scales n hs hs1 hE hKF hKFE hJ hJE hB hBE hmFE hMF hMFE h16
  refine ⟨?_,hlo,hup,hreg,?_⟩
  · intro C hC
    have hδs : 0 < (1/(2:ℝ)^(n+3))^s := by positivity
    have hE50 : 1 ≤ 50*E := by linarith only [hE]
    have hM50 : M ≤ (50*E)/(1/(2:ℝ)^(n+3))^s := hME.trans
      (div_le_div_of_nonneg_right (by linarith only [hE]) hδs.le)
    have hm50 : 1/((50*E)*(1/(2:ℝ)^(n+3))^s) ≤ m/50 := by
      have hh := div_le_div_of_nonneg_right hmE (by norm_num : (0:ℝ) ≤ 50)
      convert hh using 1
      ring
    have hL50 : L ≤ (50*E)/((1/(2:ℝ)^(n+3))^s)^2 := hLE.trans
      (div_le_div_of_nonneg_right (by linarith only [hE]) (sq_nonneg _))
    have hf := regular_fiber_constant_upper (n+3) hκ hs hs1 ht hgap
      (show 0 ≤ 50*K by linarith only [hK]) hM (show 0 < m/50 by positivity) hL hE50
      (show 50*K ≤ 50*E by linarith only [hKE]) hM50 hm50 hL50 C hC
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 100)).2
    calc
      _ ≤ (1127219200*(1+H))*(((n+3:ℕ):ℝ)+1)*(50*E)^12*100 :=
        mul_le_mul_of_nonneg_right hf (by norm_num)
      _ = (100*1127219200*(1+H)*(50:ℝ)^12)*((n:ℝ)+4)*E^12 := by push_cast; ring
      _ ≤ (100*1127219200*(1+H)*(50:ℝ)^12)*(2*((n:ℝ)+3)^2)*E^48 := by gcongr
      _ = CF*((n:ℝ)+3)^2*E^48 := by dsimp [CF]; ring
      _ ≤ D := hCFall
  · have hb := packet_sampling_budget n hκ hs1 hgap hE (zero_le_one.trans hK) hKE hKP hKPE
      hKF hKFE hJ hJE hB hBE hmFE hMF hMFE
    apply hb.trans
    change CS*((n:ℝ)+1)^2*E^40 ≤ D
    calc
      _ ≤ CS*((n:ℝ)+3)^2*E^48 := by gcongr; linarith only [hN]
      _ ≤ D := hCSall

end Falconer

end OAI
