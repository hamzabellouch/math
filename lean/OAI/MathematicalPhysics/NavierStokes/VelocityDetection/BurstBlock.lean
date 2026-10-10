import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ChartRoutingPeriodicPrefixDivergence
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ChartTraceRouteIsInstalled
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.BurstSchedule
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodizationExtendAdd
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.BurstCalculus

namespace OAI

noncomputable section
namespace VelocityDetection.BurstBlock
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open ChartRouting BurstSchedule Periodization SpatialCalculus BurstCalculus
variable (A : RoutingData) (ν : ℝ)

def initial (N q : ℕ) : Coord 2 := origin + ![scale A N*q,-scale A N]

def rawField (k : ℕ) : VectorField 2 := fun t X =>
  deriv (clock A ν k) t • finiteField A (k+1) (clock A ν k t) X

def field (k : ℕ) : VectorField 2 := fun t X =>
  deriv (clock A ν k) t • periodicPrefix A (k+1) (clock A ν k t) X

def rawSource (q k : ℕ) : ScalarField 2 := fun t X =>
  deriv (weight A ν k) t * SmoothBump.packet (radius A (k+1)) (X-initial A (k+1) q)

def source (q k : ℕ) : ScalarField 2 := extend (rawSource A ν q k)

theorem contDiff_time_smul {n : ℕ} {a : ℝ → ℝ} {V : VectorField n}
    (ha : ContDiff ℝ ∞ a) (hV : ContDiff ℝ ∞ (uncurry V)) :
    ContDiff ℝ ∞ (uncurry (fun t X => deriv a t • V (a t) X)) := by
  have hd : ContDiff ℝ ∞ (fun p : ℝ × Coord n => deriv a p.1) :=
    (contDiff_infty_iff_deriv.mp ha).2.comp contDiff_fst
  have hv : ContDiff ℝ ∞ (fun p : ℝ × Coord n => V (a p.1) p.2) :=
    hV.comp ((ha.comp contDiff_fst).prodMk contDiff_snd)
  exact hd.fun_smul hv

@[fun_prop] theorem contDiff_rawField (k : ℕ) : ContDiff ℝ ∞ (uncurry (rawField A ν k)) :=
  contDiff_time_smul (contDiff_clock A ν k) (contDiff_prefix A (k+1))

@[fun_prop] theorem contDiff_field (k : ℕ) : ContDiff ℝ ∞ (uncurry (field A ν k)) :=
  contDiff_time_smul (contDiff_clock A ν k) (contDiff_periodicPrefix A (k+1))

@[fun_prop] theorem contDiff_rawSource (q k : ℕ) : ContDiff ℝ ∞ (uncurry (rawSource A ν q k)) := by
  exact ((contDiff_infty_iff_deriv.mp (contDiff_weight A ν k)).2.comp contDiff_fst).mul
    ((SmoothBump.contDiff_packet _).comp (contDiff_snd.sub contDiff_const))

theorem field_periodic (k : ℕ) (t : ℝ) :
    FactorsThrough (field A ν k t) PeriodicSpace.cover := by
  intro X Y hXY
  change deriv (clock A ν k) t • periodicPrefix A (k+1) (clock A ν k t) X = _
  rw [periodic_periodicPrefix A (k+1) (clock A ν k t) hXY]
  rfl

theorem divergence_field (k : ℕ) (t : ℝ) (X : Coord 2) : divergence (field A ν k) t X = 0 := by
  change divergence (fun s Y => deriv (clock A ν k) s • periodicPrefix A (k+1) (clock A ν k s) Y) t X = 0
  rw [divergence_time_smul,periodicPrefix_divergence,mul_zero]

theorem rawField_support (k : ℕ) (t : ℝ) (X : Coord 2)
    (h : rawField A ν k t X ≠ 0) : X ∈ chartSet := by
  apply prefix_support A (k+1) (clock A ν k t) X
  intro hz
  exact h (by simp [rawField,hz])

theorem rawSource_support (q k : ℕ) (c : A.Instruction 0) (hc : A.source 0 c = q)
    (t : ℝ) (X : Coord 2) (h : rawSource A ν q k t X ≠ 0) : X ∈ chartSet := by
  have hpacket : SmoothBump.packet (radius A (k+1)) (X-initial A (k+1) q) ≠ 0 := right_ne_zero_of_mul h
  have he : initial A (k+1) q = path A (k+1) 0 c 0 := by
    rw [path_source A _ _ c (by norm_num),hc]
    rfl
  apply path_neighborhood A (k+1) 0 c (by omega) 0 X
  intro i
  have hh : |X i-initial A (k+1) q i| < radius A (k+1) :=
    lt_of_not_ge (fun hi => hpacket (SmoothBump.packet_zero (radius_pos A (k+1)) ⟨i,hi⟩))
  rw [he] at hh
  linarith [radius_pos A (k+1)]

theorem bounded_rawSource (q k : ℕ) : ∃ C : ℝ,
    ∀ t X, rawSource A ν q k t X ≠ 0 → ∀ i, |X i| ≤ C := by
  refine ⟨radius A (k+1)+‖initial A (k+1) q‖,?_⟩
  intro t X h i
  have hpacket : SmoothBump.packet (radius A (k+1)) (X-initial A (k+1) q) ≠ 0 := right_ne_zero_of_mul h
  have hh : |X i-initial A (k+1) q i| < radius A (k+1) :=
    lt_of_not_ge (fun hi => hpacket (SmoothBump.packet_zero (radius_pos A (k+1)) ⟨i,hi⟩))
  have hi : |initial A (k+1) q i| ≤ ‖initial A (k+1) q‖ := by simpa using norm_le_pi_norm (initial A (k+1) q) i
  have ht := abs_add_le (X i-initial A (k+1) q i) (initial A (k+1) q i)
  simpa only [sub_add_cancel] using ht.trans (add_le_add hh.le hi)

@[fun_prop] theorem contDiff_source (q k : ℕ) : ContDiff ℝ ∞ (uncurry (source A ν q k)) := by
  obtain ⟨C,hC⟩ := bounded_rawSource A ν q k
  exact contDiff_extend (contDiff_rawSource A ν q k) hC

theorem field_zero (k : ℕ) {t : ℝ} (ht : localTime A ν k t ≤ 0 ∨ 1 ≤ localTime A ν k t) :
    field A ν k t = 0 := by
  have hd : deriv (clock A ν k) t = 0 := by
    rw [deriv_clock]
    rcases ht with h | h
    · rw [deriv_phase_before (k+1) (by linarith),zero_div]
    · rw [deriv_phase_after (k+1) (by linarith),zero_div]
  funext X
  change deriv (clock A ν k) t • periodicPrefix A (k+1) (clock A ν k t) X = 0
  rw [hd,zero_smul]

theorem source_zero (q k : ℕ) {t : ℝ} (ht : localTime A ν k t ≤ 0 ∨ 1 ≤ localTime A ν k t) :
    source A ν q k t = 0 := by
  have hd : deriv (weight A ν k) t = 0 := by
    rw [deriv_weight]
    rcases ht with h | h
    · rw [deriv_amplitude_before h,zero_div]
    · rw [deriv_amplitude_after h,zero_div]
  funext X
  change (∑' j : Fin 2 → ℤ, deriv (weight A ν k) t*SmoothBump.packet (radius A (k+1))
    (X-Periodization.lattice j-initial A (k+1) q)) = 0
  simp only [hd,zero_mul,tsum_zero]

end VelocityDetection.BurstBlock
end

noncomputable section
namespace VelocityDetection.BurstBlock
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open ChartRouting BurstSchedule Periodization SpatialCalculus BurstCalculus
variable (A : RoutingData) (ν : ℝ)
variable (tr : RoutingArray.Trace A)

def center (k : ℕ) (t : ℝ) : Coord 2 := ChartTrace.route A tr (k+1) (clock A ν k t)

def rawPacket (k : ℕ) : ScalarField 2 := fun t X =>
  SmoothBump.packet (radius A (k+1)) (X-center A ν tr k t)

def rawReference (k : ℕ) : ScalarField 2 := fun t X => weight A ν k t*rawPacket A ν tr k t X

def reference (k : ℕ) : ScalarField 2 := extend (rawReference A ν tr k)

@[fun_prop] theorem contDiff_center (k : ℕ) : ContDiff ℝ ∞ (center A ν tr k) :=
  (ChartTrace.contDiff_route A tr (k+1)).comp (contDiff_clock A ν k)

@[fun_prop] theorem contDiff_rawPacket (k : ℕ) : ContDiff ℝ ∞ (uncurry (rawPacket A ν tr k)) :=
  (SmoothBump.contDiff_packet _).comp (contDiff_snd.sub ((contDiff_center A ν tr k).comp contDiff_fst))

@[fun_prop] theorem contDiff_rawReference (k : ℕ) : ContDiff ℝ ∞ (uncurry (rawReference A ν tr k)) :=
  ((contDiff_weight A ν k).comp contDiff_fst).mul (contDiff_rawPacket A ν tr k)

theorem deriv_center (k : ℕ) (t : ℝ) : deriv (center A ν tr k) t =
    deriv (clock A ν k) t • deriv (ChartTrace.route A tr (k+1)) (clock A ν k t) := by
  exact (((ChartTrace.contDiff_route A tr (k+1)).differentiable (by simp) (clock A ν k t)).hasDerivAt.scomp t
    ((contDiff_clock A ν k).differentiable (by simp) t).hasDerivAt).deriv

theorem plateau (k : ℕ) (h : ∀ n < k+1, tr.stopped n = false) (t : ℝ) (X : Coord 2)
    (hX : ∀ i, |X i-center A ν tr k t i| ≤ radius A (k+1)) :
    field A ν k t X = deriv (center A ν tr k) t := by
  rw [deriv_center]
  unfold field
  congr 1
  exact ChartTrace.route_plateau A tr (k+1) h (phase_bounds (k+1) _) X hX

theorem packet_transport (k : ℕ) (h : ∀ n < k+1, tr.stopped n = false) (t : ℝ) (X : Coord 2) :
    deriv (fun r => rawPacket A ν tr k r X) t + advection (field A ν k) (rawPacket A ν tr k) t X = 0 :=
  SmoothBump.transport (radius_pos A (k+1)) ((contDiff_center A ν tr k).differentiable (by simp))
    (field A ν k) (fun X hX => plateau A ν tr k h t X hX) X

theorem source_match (k : ℕ) (h : tr.stopped 0 = false) (t : ℝ) (X : Coord 2) :
    deriv (weight A ν k) t*rawPacket A ν tr k t X = rawSource A ν (tr.address 0) k t X := by
  rcases weight_source A ν k t with hz | hz
  · simp [hz,rawSource]
  · have hc : center A ν tr k t = initial A (k+1) (tr.address 0) := by
      rw [center,hz,ChartTrace.route_before A tr (k+1) le_rfl]
      simp [ChartTrace.vertex,ChartTrace.height,h,initial]
    simp only [rawPacket,hc,rawSource]

theorem rawReference_transport (k : ℕ) (h : ∀ n < k+1, tr.stopped n = false) (t : ℝ) (X : Coord 2) :
    deriv (fun r => rawReference A ν tr k r X) t + advection (field A ν k) (rawReference A ν tr k) t X =
      rawSource A ν (tr.address 0) k t X := by
  have hdiff : ContDiff ℝ ∞ (fun r => rawPacket A ν tr k r X) :=
    (contDiff_rawPacket A ν tr k).comp (contDiff_id.prodMk contDiff_const)
  change deriv (fun r => weight A ν k r * rawPacket A ν tr k r X) t +
    advection (field A ν k) (fun r Y => weight A ν k r * rawPacket A ν tr k r Y) t X = _
  rw [deriv_fun_mul ((contDiff_weight A ν k).differentiable (by simp) t)
    (hdiff.differentiable (by simp) t),advection_time_mul]
  dsimp only
  have hh := packet_transport A ν tr k h t X
  have hm := source_match A ν tr k (h 0 (by omega)) t X
  linear_combination (weight A ν k t) * hh + hm

theorem rawReference_support (k : ℕ) (h : ∀ n < k+1, tr.stopped n = false)
    (t : ℝ) (X : Coord 2) (hX : rawReference A ν tr k t X ≠ 0) : X ∈ chartSet :=
  ChartTrace.packet_support_chart A tr (k+1) (by omega) h _ X (right_ne_zero_of_mul hX)

theorem rawReference_interior (k : ℕ) (h : ∀ n < k+1, tr.stopped n = false) :
    ∀ t X, rawReference A ν tr k t X ≠ 0 → ∀ i, X i ∈ Ioo (0:ℝ) 1 :=
  fun t X hX => chartSet_interior (rawReference_support A ν tr k h t X hX)

theorem rawReference_boundedSupport (k : ℕ) (h : ∀ n < k+1, tr.stopped n = false) :
    ∀ t X, rawReference A ν tr k t X ≠ 0 → ∀ i, |X i| ≤ 1 := by
  intro t X hX i
  have hh := rawReference_interior A ν tr k h t X hX i
  rw [abs_of_pos hh.1]
  exact hh.2.le

@[fun_prop] theorem contDiff_reference (k : ℕ) (h : ∀ n < k+1, tr.stopped n = false) :
    ContDiff ℝ ∞ (uncurry (reference A ν tr k)) :=
  contDiff_extend (contDiff_rawReference A ν tr k) (rawReference_boundedSupport A ν tr k h)

theorem reference_periodic (k : ℕ) (t : ℝ) :
    FactorsThrough (reference A ν tr k t) PeriodicSpace.cover := periodic_extend _ _

theorem reference_transport (k : ℕ) (h : ∀ n < k+1, tr.stopped n = false) (t : ℝ) (X : Coord 2) :
    deriv (fun r => reference A ν tr k r X) t + advection (field A ν k) (reference A ν tr k) t X =
      source A ν (tr.address 0) k t X :=
  transport_extend (field A ν k) (field_periodic A ν k) (contDiff_rawReference A ν tr k)
    (rawReference_boundedSupport A ν tr k h) (rawReference_transport A ν tr k h) t X

end VelocityDetection.BurstBlock
end

end OAI
