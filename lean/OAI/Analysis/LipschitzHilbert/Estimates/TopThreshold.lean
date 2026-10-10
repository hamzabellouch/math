import OAI.Analysis.LipschitzHilbert.Estimates.TopAmplitudeBound
import OAI.Analysis.LipschitzHilbert.Estimates.SlopeTopNeighborhood

namespace OAI

/-! A fixed polynomial threshold pays for both the raw packet constant
and the moment order, before choosing any finite family or later mask. -/

noncomputable section
namespace LipschitzHilbert

theorem topAreaPrefactor_one_le : 1 ≤ topAreaPrefactor 1 := by
  unfold topAreaPrefactor
  nlinarith [Real.pi_pos, Real.two_le_pi]

theorem topAreaPrefactor_scale (K : ℝ) :
    topAreaPrefactor K = topAreaPrefactor 1*K^2 := by
  unfold topAreaPrefactor
  ring

theorem topExceptionMoment_power_le (J a L : ℝ) (hJ : 0 ≤ J)
    (ha : 0 ≤ a) (hL : 1 ≤ L) :
    (topExceptionMoment (topAreaPrefactor (L^a)) J L:ℝ) ≤
      ((J+Real.log (topAreaPrefactor 1)+2*a)/Real.log 4+2)*L := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hK : 1 ≤ L^a := Real.one_le_rpow hL ha
  have hC := topAreaPrefactor_one_le
  have hM : 1 ≤ topAreaPrefactor (L^a) := by
    rw [topAreaPrefactor_scale]
    have hs : (1:ℝ) ≤ (L^a)^2 := one_le_pow₀ hK
    nlinarith
  have hlogbound : Real.log (topAreaPrefactor (L^a)) ≤
      (Real.log (topAreaPrefactor 1)+2*a)*L := by
    rw [topAreaPrefactor_scale (L^a), Real.log_mul (by positivity : topAreaPrefactor 1 ≠ 0)
      (by positivity : (L^a)^2 ≠ 0), Real.log_pow, Real.log_rpow hL0]
    have hlog : Real.log L ≤ L := Real.log_le_self hL0.le
    have hlogC := Real.log_nonneg hC
    norm_num only [Nat.cast_ofNat]
    calc
      _ = Real.log (topAreaPrefactor 1)+(2*a)*Real.log L := by ring
      _ ≤ Real.log (topAreaPrefactor 1)*L+(2*a)*L :=
        add_le_add (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hL hlogC)
          (mul_le_mul_of_nonneg_left hlog (by positivity))
      _ = _ := by ring
  simpa only [add_assoc] using topExceptionMoment_le (topAreaPrefactor (L^a)) J L
    (Real.log (topAreaPrefactor 1)+2*a) hJ hL hM hlogbound

theorem exists_top_threshold (Ab Am J a p : ℝ) (D : ℕ)
    (hAb : 0 < Ab) (hAm : 0 < Am) (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type) [Fintype κ] [∀ j, Fintype (ι j)]
        (P : PlanarPacketFamily N κ ι), P.constant ≤ L^p →
      P.topPacketAmplitude Ab Am D*
          (topExceptionMoment (topAreaPrefactor (L^a)) J L:ℝ)*5^(8*D) ≤ L^(2*p+2) := by
  obtain ⟨A,hA,hamp⟩ := uniform_topPacketAmplitude_bound Ab Am D hAb hAm
  let B := (J+Real.log (topAreaPrefactor 1)+2*a)/Real.log 4+2
  let C := 4*A*B*5^(8*D)
  have hlogC := Real.log_nonneg topAreaPrefactor_one_le
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro L hL N κ ι _ _ P hP
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hCL : C ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hpow : 1 ≤ L^p := Real.one_le_rpow hL1 hp
  have hraw : P.constant+1 ≤ 2*L^p := by linarith
  have hconst := P.constant_pos
  have hamplitude : P.topPacketAmplitude Ab Am D ≤ 4*A*L^(2*p) := by
    calc
      _ ≤ A*(P.constant+1)^2 := hamp N κ ι P
      _ ≤ A*(2*L^p)^2 := by gcongr
      _ = 4*A*L^(2*p) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hL0.le]
        ring_nf
  have hn := topExceptionMoment_power_le J a L hJ ha hL1
  change (topExceptionMoment (topAreaPrefactor (L^a)) J L:ℝ) ≤ B*L at hn
  calc
    _ ≤ (4*A*L^(2*p))*(B*L)*5^(8*D) := by
      gcongr
    _ = C*L^(2*p+1) := by
      rw [Real.rpow_add hL0, Real.rpow_one]
      dsimp [C]
      ring
    _ ≤ L*L^(2*p+1) := mul_le_mul_of_nonneg_right hCL (Real.rpow_nonneg hL0.le _)
    _ = L^(2*p+2) := by
      conv_lhs => lhs; rw [← Real.rpow_one L]
      rw [← Real.rpow_add hL0]
      congr 1
      ring

end LipschitzHilbert

end

end OAI
