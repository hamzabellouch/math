import Mathlib.Tactic.IntervalCases
import OAI.MathematicalPhysics.Transonic.Certificates.FixedHighJet
import OAI.MathematicalPhysics.Transonic.Certificates.FixedHighPlusBarrier
import OAI.MathematicalPhysics.Transonic.Certificates.FixedHighPlusPositive

namespace OAI

section

namespace SepticProfile.HighPlusBarrierTransfer
open FixedInterval
def S : ℤ := 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def deltaBox : Box := ⟨1*(FixedHighPlusBarrier.Q/1000),0⟩
theorem scale_eq : FixedHighJet.Q=FixedHighPlusBarrier.Q*S := by decide +kernel
theorem S_pos : 0<S := by decide +kernel
theorem u_zero : FixedHighPlusBarrier.u 0=⟨FixedHighPlusBarrier.Q,0⟩ := by decide +kernel
theorem data_u_1 (n : ℕ) (hl : 1≤n) (hu : n≤20) : FixedHighPlusBarrier.u n=add (scale 1 S (FixedHighJet.w n)) (if n=140 then deltaBox else zero) := by
  interval_cases n <;> decide +kernel
theorem data_u_21 (n : ℕ) (hl : 21≤n) (hu : n≤40) : FixedHighPlusBarrier.u n=add (scale 1 S (FixedHighJet.w n)) (if n=140 then deltaBox else zero) := by
  interval_cases n <;> decide +kernel
theorem data_u_41 (n : ℕ) (hl : 41≤n) (hu : n≤60) : FixedHighPlusBarrier.u n=add (scale 1 S (FixedHighJet.w n)) (if n=140 then deltaBox else zero) := by
  interval_cases n <;> decide +kernel
theorem data_u_61 (n : ℕ) (hl : 61≤n) (hu : n≤80) : FixedHighPlusBarrier.u n=add (scale 1 S (FixedHighJet.w n)) (if n=140 then deltaBox else zero) := by
  interval_cases n <;> decide +kernel
theorem data_u_81 (n : ℕ) (hl : 81≤n) (hu : n≤100) : FixedHighPlusBarrier.u n=add (scale 1 S (FixedHighJet.w n)) (if n=140 then deltaBox else zero) := by
  interval_cases n <;> decide +kernel
theorem data_u_101 (n : ℕ) (hl : 101≤n) (hu : n≤120) : FixedHighPlusBarrier.u n=add (scale 1 S (FixedHighJet.w n)) (if n=140 then deltaBox else zero) := by
  interval_cases n <;> decide +kernel
theorem data_u_121 (n : ℕ) (hl : 121≤n) (hu : n≤140) : FixedHighPlusBarrier.u n=add (scale 1 S (FixedHighJet.w n)) (if n=140 then deltaBox else zero) := by
  interval_cases n <;> decide +kernel
theorem data_u_141 (n : ℕ) (hl : 141≤n) (hu : n≤160) : FixedHighPlusBarrier.u n=add (scale 1 S (FixedHighJet.w n)) (if n=140 then deltaBox else zero) := by
  interval_cases n <;> decide +kernel
theorem data_u_161 (n : ℕ) (hl : 161≤n) (hu : n≤180) : FixedHighPlusBarrier.u n=add (scale 1 S (FixedHighJet.w n)) (if n=140 then deltaBox else zero) := by
  interval_cases n <;> decide +kernel
theorem data_u_181 (n : ℕ) (hl : 181≤n) (hu : n≤200) : FixedHighPlusBarrier.u n=add (scale 1 S (FixedHighJet.w n)) (if n=140 then deltaBox else zero) := by
  interval_cases n <;> decide +kernel
theorem data_u_201 (n : ℕ) (hl : 201≤n) (hu : n≤220) : FixedHighPlusBarrier.u n=add (scale 1 S (FixedHighJet.w n)) (if n=140 then deltaBox else zero) := by
  interval_cases n <;> decide +kernel
theorem data_u (n : ℕ) (hl : 1≤n) (hu : n≤220) : FixedHighPlusBarrier.u n=add (scale 1 S (FixedHighJet.w n)) (if n=140 then deltaBox else zero) := by
  by_cases h1 : n≤20
  · exact data_u_1 n (by omega) h1
  by_cases h21 : n≤40
  · exact data_u_21 n (by omega) h21
  by_cases h41 : n≤60
  · exact data_u_41 n (by omega) h41
  by_cases h61 : n≤80
  · exact data_u_61 n (by omega) h61
  by_cases h81 : n≤100
  · exact data_u_81 n (by omega) h81
  by_cases h101 : n≤120
  · exact data_u_101 n (by omega) h101
  by_cases h121 : n≤140
  · exact data_u_121 n (by omega) h121
  by_cases h141 : n≤160
  · exact data_u_141 n (by omega) h141
  by_cases h161 : n≤180
  · exact data_u_161 n (by omega) h161
  by_cases h181 : n≤200
  · exact data_u_181 n (by omega) h181
  exact data_u_201 n (by omega) (by omega)
theorem data_r_0 (n : ℕ) (hl : 0≤n) (hu : n≤23) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_24 (n : ℕ) (hl : 24≤n) (hu : n≤47) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_48 (n : ℕ) (hl : 48≤n) (hu : n≤71) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_72 (n : ℕ) (hl : 72≤n) (hu : n≤95) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_96 (n : ℕ) (hl : 96≤n) (hu : n≤119) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_120 (n : ℕ) (hl : 120≤n) (hu : n≤143) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_144 (n : ℕ) (hl : 144≤n) (hu : n≤167) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_168 (n : ℕ) (hl : 168≤n) (hu : n≤191) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_192 (n : ℕ) (hl : 192≤n) (hu : n≤215) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_216 (n : ℕ) (hl : 216≤n) (hu : n≤239) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_240 (n : ℕ) (hl : 240≤n) (hu : n≤263) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_264 (n : ℕ) (hl : 264≤n) (hu : n≤287) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_288 (n : ℕ) (hl : 288≤n) (hu : n≤311) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_312 (n : ℕ) (hl : 312≤n) (hu : n≤335) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_336 (n : ℕ) (hl : 336≤n) (hu : n≤359) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_360 (n : ℕ) (hl : 360≤n) (hu : n≤383) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_384 (n : ℕ) (hl : 384≤n) (hu : n≤407) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_408 (n : ℕ) (hl : 408≤n) (hu : n≤431) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_432 (n : ℕ) (hl : 432≤n) (hu : n≤455) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_456 (n : ℕ) (hl : 456≤n) (hu : n≤479) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_480 (n : ℕ) (hl : 480≤n) (hu : n≤503) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_504 (n : ℕ) (hl : 504≤n) (hu : n≤527) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_528 (n : ℕ) (hl : 528≤n) (hu : n≤551) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_552 (n : ℕ) (hl : 552≤n) (hu : n≤575) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_576 (n : ℕ) (hl : 576≤n) (hu : n≤599) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_600 (n : ℕ) (hl : 600≤n) (hu : n≤623) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_624 (n : ℕ) (hl : 624≤n) (hu : n≤647) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_648 (n : ℕ) (hl : 648≤n) (hu : n≤671) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_672 (n : ℕ) (hl : 672≤n) (hu : n≤695) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_696 (n : ℕ) (hl : 696≤n) (hu : n≤719) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r_720 (n : ℕ) (hl : 720≤n) (hu : n≤741) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  interval_cases n <;> decide +kernel
theorem data_r (n : ℕ) (hn : n<742) : FixedHighPlusPositive.r n=FixedHighPlusBarrier.r (n+140) := by
  by_cases h0 : n≤23
  · exact data_r_0 n (by omega) h0
  by_cases h24 : n≤47
  · exact data_r_24 n (by omega) h24
  by_cases h48 : n≤71
  · exact data_r_48 n (by omega) h48
  by_cases h72 : n≤95
  · exact data_r_72 n (by omega) h72
  by_cases h96 : n≤119
  · exact data_r_96 n (by omega) h96
  by_cases h120 : n≤143
  · exact data_r_120 n (by omega) h120
  by_cases h144 : n≤167
  · exact data_r_144 n (by omega) h144
  by_cases h168 : n≤191
  · exact data_r_168 n (by omega) h168
  by_cases h192 : n≤215
  · exact data_r_192 n (by omega) h192
  by_cases h216 : n≤239
  · exact data_r_216 n (by omega) h216
  by_cases h240 : n≤263
  · exact data_r_240 n (by omega) h240
  by_cases h264 : n≤287
  · exact data_r_264 n (by omega) h264
  by_cases h288 : n≤311
  · exact data_r_288 n (by omega) h288
  by_cases h312 : n≤335
  · exact data_r_312 n (by omega) h312
  by_cases h336 : n≤359
  · exact data_r_336 n (by omega) h336
  by_cases h360 : n≤383
  · exact data_r_360 n (by omega) h360
  by_cases h384 : n≤407
  · exact data_r_384 n (by omega) h384
  by_cases h408 : n≤431
  · exact data_r_408 n (by omega) h408
  by_cases h432 : n≤455
  · exact data_r_432 n (by omega) h432
  by_cases h456 : n≤479
  · exact data_r_456 n (by omega) h456
  by_cases h480 : n≤503
  · exact data_r_480 n (by omega) h480
  by_cases h504 : n≤527
  · exact data_r_504 n (by omega) h504
  by_cases h528 : n≤551
  · exact data_r_528 n (by omega) h528
  by_cases h552 : n≤575
  · exact data_r_552 n (by omega) h552
  by_cases h576 : n≤599
  · exact data_r_576 n (by omega) h576
  by_cases h600 : n≤623
  · exact data_r_600 n (by omega) h600
  by_cases h624 : n≤647
  · exact data_r_624 n (by omega) h624
  by_cases h648 : n≤671
  · exact data_r_648 n (by omega) h648
  by_cases h672 : n≤695
  · exact data_r_672 n (by omega) h672
  by_cases h696 : n≤719
  · exact data_r_696 n (by omega) h696
  exact data_r_720 n (by omega) (by omega)
lemma holds_delta : Holds FixedHighPlusBarrier.Q deltaBox (1/1000 : ℝ) := by
  norm_num [Holds,deltaBox,FixedHighPlusBarrier.Q]


theorem barrier_coefficients_enclosed (f : EulerFormal.Series)
    (hf0 : PowerSeries.coeff 0 f=1)
    (hf : ∀ n≤220, Holds FixedHighJet.Q (FixedHighJet.w n) (PowerSeries.coeff n (f-1))) :
    ∀ n, Holds FixedHighPlusBarrier.Q (FixedHighPlusBarrier.u n)
      ((EulerPolynomial.barrier f (1/1000 : ℝ)).coeff n) := by
  intro n
  rw [EulerPolynomial.coeff_barrier]
  by_cases hn0 : n=0
  · subst n
    rw [u_zero]
    simp only [show 0<221 by omega,show (0:ℕ)≠140 by omega,ite_true,ite_false,hf0,add_zero]
    simpa only [mul_one,Int.cast_one] using holds_exact FixedHighPlusBarrier.Q 1
  by_cases hn : n≤220
  · have hfj := hf n hn
    rw [scale_eq] at hfj
    have hs := holds_change_scale S_pos hfj
    have hcoeff : PowerSeries.coeff n (f-1)=PowerSeries.coeff n f := by
      rw [map_sub,PowerSeries.coeff_one,ite_eq_right hn0,sub_zero]
    rw [hcoeff] at hs
    rw [data_u n (by omega) hn]
    simp only [ite_eq_left (show n<221 by omega)]
    by_cases he : n=140
    · simp only [ite_eq_left he]
      exact holds_add hs holds_delta
    · simp only [ite_eq_right he]
      exact holds_add hs (holds_zero FixedHighPlusBarrier.Q)
  · rw [ite_eq_right (by omega),ite_eq_right (by omega),zero_add]
    rw [FixedHighPlusBarrier.u,ite_eq_right (by omega)]
    exact holds_zero FixedHighPlusBarrier.Q
end SepticProfile.HighPlusBarrierTransfer
namespace SepticProfile.HighPlusRange
open FixedInterval Polynomial
def b (n : ℕ) : Box := FixedHighPlusBarrier.u (n+1)
theorem Q_pos : 0<FixedHighPlusBarrier.Q := by decide +kernel
theorem middle (n : ℕ) (hn : 1≤n) (hn' : n<63) : (b n).center+(b n).radius≤0 := by
  interval_cases n <;> decide +kernel
theorem all_bound : 50*absTail 8 0 220 b≤FixedHighPlusBarrier.Q*6^219 := by decide +kernel
theorem tail_bound : 100000*absTail 8 63 220 b≤FixedHighPlusBarrier.Q*6^219 := by decide +kernel
theorem head_bound : 100000*((b 0).center+(b 0).radius)≤ -201*FixedHighPlusBarrier.Q := by decide +kernel

theorem velocity_range (p : ℝ[X]) (hp : p.natDegree≤220) (h0 : p.coeff 0=1)
    (ha : ∀ n, Holds FixedHighPlusBarrier.Q (FixedHighPlusBarrier.u n) (p.coeff n))
    {x : ℝ} (hx : 0≤x) (hx' : x≤5/6) : 1-x/50≤p.eval x ∧ p.eval x≤1-x/500 := by
  apply EulerPolynomial.polynomial_velocity_range Q_pos b p hp h0
    (fun i _ => ha (i+1)) ?_ middle all_bound tail_bound hx hx'
  have hq : 0<(FixedHighPlusBarrier.Q : ℝ) := by exact_mod_cast Q_pos
  have hbd := (bounds (ha 1)).2
  have hbound : 100000*(((b 0).center : ℝ)+(b 0).radius)≤ -201*FixedHighPlusBarrier.Q := by
    exact_mod_cast head_bound
  change (FixedHighPlusBarrier.Q : ℝ)*p.coeff 1≤((b 0).center : ℝ)+(b 0).radius at hbd
  nlinarith
end SepticProfile.HighPlusRange


end

end OAI
