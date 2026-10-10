import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicComparison
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.BurstBlock
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodizationSupportSpatialD

namespace OAI

noncomputable section
namespace VelocityDetection.BurstBlock
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open ChartRouting BurstSchedule BurstCalculus Periodization SpatialCalculus
variable (A : RoutingData) (ν : ℝ) (tr : RoutingArray.Trace A)

theorem rawReference_laplacian (k : ℕ) (t : ℝ) (X : Coord 2) :
    laplacian (rawReference A ν tr k) t X = weight A ν k t*
      laplacian (fun _ Y => SmoothBump.packet (radius A (k+1)) Y) t (X-center A ν tr k t) := by
  change laplacian (fun s Y => weight A ν k s * rawPacket A ν tr k s Y) t X = _
  rw [laplacian_time_mul]
  exact congrArg (fun z => weight A ν k t*z)
    (laplacian_translate (fun _ Y => SmoothBump.packet (radius A (k+1)) Y) (center A ν tr k) t X)

theorem rawReference_laplacian_bound (k : ℕ) (t : ℝ) (X : Coord 2) :
    |laplacian (rawReference A ν tr k) t X| ≤ lapBound A k := by
  rw [rawReference_laplacian,abs_mul,abs_of_nonneg (show 0 ≤ weight A ν k t from (amplitude_bounds _).1)]
  exact (mul_le_mul (amplitude_bounds _).2
    (SmoothBump.laplacian_bound (radius_pos A (k+1)) t _) (abs_nonneg _)
    (by norm_num)).trans_eq (one_mul _)

theorem reference_laplacian_bound (k : ℕ) (h : ∀ n < k+1, tr.stopped n = false)
    (t : ℝ) (X : Coord 2) : |laplacian (reference A ν tr k) t X| ≤ lapBound A k := by
  change |laplacian (Periodization.extend (rawReference A ν tr k)) t X| ≤ _
  rw [laplacian_extend (contDiff_rawReference A ν tr k) (rawReference_boundedSupport A ν tr k h)]
  exact abs_extend_le (fun t X hX => chartSet_interior (support_laplacian isClosed_Icc
    (contDiff_rawReference A ν tr k) (rawReference_support A ν tr k h) t X hX))
    (rawReference_laplacian_bound A ν tr k) t X

theorem reference_laplacian_zero (k : ℕ) (h : ∀ n < k+1, tr.stopped n = false)
    {t : ℝ} (ht : localTime A ν k t ≤ 0 ∨ 1 ≤ localTime A ν k t) (X : Coord 2) :
    laplacian (reference A ν tr k) t X = 0 := by
  have hw : weight A ν k t = 0 := by
    rcases ht with h | h
    · exact amplitude_before h
    · exact amplitude_after h
  change laplacian (Periodization.extend (rawReference A ν tr k)) t X = _
  rw [laplacian_extend (contDiff_rawReference A ν tr k) (rawReference_boundedSupport A ν tr k h)]
  simp only [Periodization.extend,rawReference_laplacian,hw,zero_mul,tsum_zero]

theorem reference_laplacian_barrier (hν : 0 ≤ ν) (k : ℕ) (h : ∀ n < k+1, tr.stopped n = false)
    (t : ℝ) (X : Coord 2) :
    ν*|laplacian (reference A ν tr k) t X| ≤ deriv (barrier A ν k) t := by
  by_cases ht : localTime A ν k t ∈ Icc (0:ℝ) 1
  · exact (mul_le_mul_of_nonneg_left (reference_laplacian_bound A ν tr k h t X) hν).trans
      (barrier_deriv_large A ν hν k ht)
  · have hh : localTime A ν k t ≤ 0 ∨ 1 ≤ localTime A ν k t := by
      rcases lt_or_ge (localTime A ν k t) 0 with h | h
      · exact Or.inl h.le
      · exact Or.inr (le_of_lt (lt_of_not_ge (fun h' => ht ⟨h,h'⟩)))
    rw [reference_laplacian_zero A ν tr k h hh X,abs_zero,mul_zero]
    exact barrier_deriv_nonneg A ν hν k t

theorem reference_zero (k : ℕ) {t : ℝ}
    (ht : localTime A ν k t ≤ 0 ∨ 1 ≤ localTime A ν k t) : reference A ν tr k t = 0 := by
  have hw : weight A ν k t = 0 := by
    rcases ht with h | h
    · exact amplitude_before h
    · exact amplitude_after h
  funext X
  change (∑' j : Fin 2 → ℤ, weight A ν k t*rawPacket A ν tr k t (X-Periodization.lattice j)) = 0
  simp only [hw,zero_mul,tsum_zero]

theorem reference_bounds (k : ℕ) (h : ∀ n < k+1, tr.stopped n = false)
    (t : ℝ) {X : Coord 2} (hX : ∀ i, X i ∈ Icc (0:ℝ) 1) :
    reference A ν tr k t X ∈ Icc (0:ℝ) 1 := by
  unfold reference
  rw [extend_eq_chart (rawReference_interior A ν tr k h) t hX]
  exact ⟨mul_nonneg (amplitude_bounds _).1 (SmoothBump.packet_bounds _ _).1,
    (mul_le_mul (amplitude_bounds _).2 (SmoothBump.packet_bounds _ _).2
      (SmoothBump.packet_bounds _ _).1 (by norm_num)).trans_eq (by ring)⟩

theorem reference_center (k : ℕ) (h : ∀ n < k+1, tr.stopped n = false) (t : ℝ) :
    reference A ν tr k t (center A ν tr k t) = weight A ν k t := by
  have hbounds := ChartTrace.route_bounds A tr (k+1) (by omega) h (clock A ν k t)
  change center A ν tr k t 0 ∈ Icc (1/4:ℝ) (1/4+1/1024) ∧
    center A ν tr k t 1 ∈ Icc (1/16:ℝ) (1/2) at hbounds
  have hX : ∀ i, center A ν tr k t i ∈ Icc (0:ℝ) 1 := by
    intro i
    fin_cases i
    · exact ⟨(by norm_num : (0:ℝ) ≤ 1/4).trans hbounds.1.1, hbounds.1.2.trans (by norm_num)⟩
    · exact ⟨(by norm_num : (0:ℝ) ≤ 1/16).trans hbounds.2.1, hbounds.2.2.trans (by norm_num)⟩
  unfold reference
  rw [extend_eq_chart (rawReference_interior A ν tr k h) t hX]
  simp [rawReference,rawPacket]

theorem reference_zero_detector (k : ℕ) (h : ∀ n ≤ k+1, tr.stopped n = false)
    (t : ℝ) {X : Coord 2} (hX : ∀ i, X i ∈ Icc (0:ℝ) 1) (hY : X 1 < 1/8) :
    reference A ν tr k t X = 0 := by
  unfold reference
  rw [extend_eq_chart (rawReference_interior A ν tr k (fun n hn => h n hn.le)) t hX]
  change weight A ν k t * SmoothBump.packet _ (X-ChartTrace.route A tr (k+1) _) = 0
  rw [ChartTrace.packet_zero_detector A tr (k+1) (by omega) h _ X hY,mul_zero]

theorem diffusion_control {ρ : ScalarField 2} (hν : 0 ≤ ν) (k : ℕ)
    (h : ∀ n < k+1, tr.stopped n = false) {T : ℝ} (hT : 0 ≤ T)
    (hρ : ContDiff ℝ 2 (uncurry ρ)) (hpρ : ∀ t, FactorsThrough (ρ t) PeriodicSpace.cover)
    (hρeq : ∀ t ∈ Icc (0:ℝ) T, ∀ X,
      PeriodicComparison.residual ν (field A ν k) ρ t X = source A ν (tr.address 0) k t X)
    (hinit : ∀ X, ρ 0 X = 0) :
    ∀ t ∈ Icc (0:ℝ) T, ∀ X, |ρ t X-reference A ν tr k t X| ≤ error k := by
  have hzero : reference A ν tr k 0 = 0 := by
    apply reference_zero A ν tr k (Or.inl ?_)
    unfold localTime
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k]) (duration_pos A ν hν k).le
  have hcontrol := PeriodicComparison.diffusion_error hν hT hρ
    ((contDiff_reference A ν tr k h).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    hpρ (reference_periodic A ν tr k) (contDiff_barrier A ν k) hρeq
    (fun t _ X => reference_transport A ν tr k h t X)
    (fun t _ X => reference_laplacian_barrier A ν tr hν k h t X)
    (fun X => by rw [hinit X,congrFun hzero X,Pi.zero_apply,sub_self,abs_zero]; exact (barrier_bounds A ν k 0).1)
  exact fun t ht X => (hcontrol t ht X).trans (barrier_bounds A ν k t).2

end VelocityDetection.BurstBlock
end

end OAI
