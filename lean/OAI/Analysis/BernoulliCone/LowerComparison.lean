import OAI.Analysis.BernoulliCone.SobolevIdeals

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff Laplacian
namespace Bernoulli
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)}
namespace GroundState

lemma lower_variation (c : Space d) (r : ℝ) (hr : 0<r)
    {u Y w : Space d → ℝ} {G : Space d → Space d}
    (hu : Continuous u) (hun : ∀x, 0≤u x)
    (huc : ContDiffOn ℝ ∞ u {x | 0<u x}) (hul : ∀x, 0<u x → Δ u x=0)
    (huG : H1Loc univ u (gradient u))
    (hY : ContDiffOn ℝ ∞ Y {x | 0<u x})
    (hYp : ∀x, 0<u x → 0<Y x) (hYlap : ∀x, 0<u x → Δ Y x≤0)
    (hw : H10 (Metric.ball c r) w G) (hwn : ∀x, 0≤w x)
    (hwu : ∀x, w x≤u x) (hw0 : ∀x, x∉Metric.ball c r → w x=0) :
    (∫x in Metric.ball c r, inner ℝ (gradient u x) (G x))=0 ∧
    MemLp (fun x=>G x-(w x/Y x) • gradient Y x) 2 (volume.restrict (Metric.ball c r)) ∧
    (∫x in Metric.ball c r, ‖G x-(w x/Y x) • gradient Y x‖^2) ≤
      (∫x in Metric.ball c r, ‖G x‖^2) := by
  let B := Metric.ball c r
  let S := Metric.ball c (r+1)
  let Q := {x | 0<u x} ∩ S
  let E := B.indicator G
  let L := fun x=>E x-(w x/Y x) • gradient Y x
  have hB : IsOpen B := Metric.isOpen_ball
  have hS : IsOpen S := Metric.isOpen_ball
  have hQ : IsOpen Q := (isOpen_lt continuous_const hu).inter hS
  have hBS : closure B ⊆ S := by
    change closure (Metric.ball c r) ⊆ Metric.ball c (r+1)
    exact (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball (by linarith))

  have hwQ : H10 Q w E := SobolevCalculus.h10_positive_domain_inter hS hBS hB
    (Metric.isBounded_ball.isCompact_closure) hw hu hwn hwu hw0
  have hwE : H10 univ w E := by
    have hh := hw.zero_extension hB.measurableSet (subset_univ B)
    have he : B.indicator w=w := by
      ext x
      by_cases hx:x∈B
      · simp [hx]
      · simp [hx,hw0 x hx]
    rwa [he] at hh
  have hE0 : ∀ᵐ x ∂volume, w x=0 → E x=0 := by
    simpa only [Measure.restrict_univ] using SobolevCalculus.gradient_zero_on_zero_set isOpen_univ hwE.1
  have hwQ0 : ∀x, x∉Q → w x=0 := by
    intro x hx
    by_cases hxu:0<u x
    · have hxS : x∉S := fun h=>hx ⟨hxu,h⟩
      exact hw0 x (fun h=>hxS (hBS (subset_closure h)))
    · have hu0 : u x = 0 := le_antisymm (not_lt.mp hxu) (hun x)
      exact le_antisymm (by simpa only [hu0] using hwu x) (hwn x)
  have hEint : (∫x in Q, ‖E x‖^2)=(∫x in B, ‖G x‖^2) := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero (s:=Q) (by
      filter_upwards [hE0] with x hx hy
      simp [hx (hwQ0 x hy)])]
    rw [← integral_indicator hB.measurableSet]
    apply integral_congr_ae
    exact ae_of_all _ fun x=>by by_cases hx:x∈B <;> simp [E,hx]
  have hEorth : (∫x in Q, inner ℝ (gradient u x) (E x))=(∫x in B, inner ℝ (gradient u x) (G x)) := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero (s:=Q) (by
      filter_upwards [hE0] with x hx hy
      simp [hx (hwQ0 x hy)])]
    rw [← integral_indicator hB.measurableSet]
    apply integral_congr_ae
    exact ae_of_all _ fun x=>by by_cases hx:x∈B <;> simp [E,hx]
  have hL0 : ∀ᵐ x ∂volume, x∉Q → L x=0 := by
    filter_upwards [hE0] with x hx hy
    simp [L,hwQ0 x hy,hx (hwQ0 x hy)]
  have hLQ : MemLp L 2 (volume.restrict Q) :=
    (picone_h10_eLpNorm hQ (hY.mono inter_subset_left) (fun x hx=>hYp x hx.1)
      (fun x hx=>hYlap x hx.1) hwQ).1
  have hLglobal : MemLp L 2 volume := by
    apply ((memLp_indicator_iff_restrict hQ.measurableSet).mpr hLQ).ae_eq
    filter_upwards [hL0] with x hx
    by_cases hy:x∈Q <;> simp [hy,hx]
  have hLB : MemLp (fun x=>G x-(w x/Y x) • gradient Y x) 2 (volume.restrict B) := by
    apply (hLglobal.mono_measure Measure.restrict_le_self).ae_eq
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    simp [L,E,hx]
  have hLint : (∫x in Q, ‖L x‖^2)=(∫x in B, ‖G x-(w x/Y x) • gradient Y x‖^2) := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero (s:=Q) (by
      filter_upwards [hL0] with x hx hy
      simp [hx hy])]
    rw [← integral_indicator hB.measurableSet]
    apply integral_congr_ae
    exact ae_of_all _ fun x=>by
      by_cases hx:x∈B
      · simp [L,E,hx]
      · simp [L,E,hx,hw0 x hx]
  refine ⟨?_,hLB,?_⟩
  · rw [← hEorth]
    exact harmonic_h10 hQ (huc.mono inter_subset_left) (fun x hx=>hul x hx.1)
      ((huG c (r+1) (by linarith) (subset_univ _)).2.1.mono_measure
        (Measure.restrict_mono inter_subset_right le_rfl)) hwQ
  · rw [← hLint,← hEint]
    exact picone_h10 hQ (hY.mono inter_subset_left) (fun x hx=>hYp x hx.1)
      (fun x hx=>hYlap x hx.1) hwQ

theorem lower_comparison (c : Space d) (r : ℝ) (hr : 0<r)
    {u Y v : Space d → ℝ} {V : Space d → Space d}
    (hu : Continuous u) (hun : ∀x, 0≤u x)
    (huc : ContDiffOn ℝ ∞ u {x | 0<u x}) (hul : ∀x, 0<u x → Δ u x=0)
    (huG : H1Loc univ u (gradient u))
    (hY : ContDiffOn ℝ ∞ Y {x | 0<u x})
    (hYp : ∀x, 0<u x → 0<Y x) (hYlap : ∀x, 0<u x → Δ Y x≤0)
    (hslope : ∀x, 0<u x → 1≤‖gradient u x-(u x/Y x) • gradient Y x‖^2)
    (hv : H1 (Metric.ball c r) v V)
    (hvn : ∀ᵐ x ∂volume.restrict (Metric.ball c r), 0≤v x)
    (hvu : ∀ᵐ x ∂volume.restrict (Metric.ball c r), v x≤u x)
    (htrace : H10 (Metric.ball c r) (fun x=>v x-u x) (fun x=>V x-gradient u x)) :
    energy (Metric.ball c r) u (gradient u)≤energy (Metric.ball c r) v V := by
  let B := Metric.ball c r
  let A := gradient u
  let G := fun x=>A x-V x
  let w := B.indicator (fun x=>min (max (u x-v x) 0) (u x))
  have hB : IsOpen B := Metric.isOpen_ball
  have hw0 : ∀x, x∉B → w x=0 := fun x hx=>by simp [w,hx]
  have hwn : ∀x, 0≤w x := by
    intro x
    by_cases hx:x∈B
    · simp only [w,indicator_of_mem hx]
      exact le_min (le_max_right _ _) (hun x)
    · simp [w,hx]
  have hwu : ∀x, w x≤u x := by
    intro x
    by_cases hx:x∈B
    · simp only [w,indicator_of_mem hx]
      exact min_le_right _ _
    · simpa [w,hx] using hun x
  have hweq : w =ᵐ[volume.restrict B] (fun x=>u x-v x) := by
    filter_upwards [hvn,hvu,ae_restrict_mem hB.measurableSet] with x hx hy hz
    simp [w,hz,max_eq_left (sub_nonneg.mpr hy),min_eq_left (by linarith : u x-v x≤u x)]
  have hw : H10 B w G := by
    apply htrace.neg.congr
    · filter_upwards [hweq] with x hx
      simp [hx]
    · exact ae_of_all _ fun x=>neg_sub (V x) (A x)
  obtain ⟨hort,hL,hlower⟩ := lower_variation c r hr hu hun huc hul huG hY hYp hYlap hw hwn hwu hw0
  let L := fun x=>G x-(w x/Y x) • gradient Y x
  have huB := huG c r hr (subset_univ _)
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hU2 := huB.2.1.integrable_norm_pow (by norm_num)
  have hV2 := hv.2.1.integrable_norm_pow (by norm_num)
  have hG : MemLp G 2 (volume.restrict B) := huB.2.1.sub hv.2.1
  have hG2 := hG.integrable_norm_pow (by norm_num)
  have hL2 := hL.integrable_norm_pow (by norm_num)
  have hUV := integrable_inner_of_memLp huB.2.1 hG
  have hUE := hU2.add (integrable_phase huB.1.aestronglyMeasurable)
  have hVE := hV2.add (integrable_phase hv.1.aestronglyMeasurable)
  have hz := SobolevCalculus.gradient_zero_on_zero_set hB hv
  change Integrable (fun x=>‖A x‖^2) (volume.restrict B) at hU2
  change Integrable (fun x=>‖L x‖^2) (volume.restrict B) at hL2
  change Integrable (fun x=>inner ℝ (A x) (G x)) (volume.restrict B) at hUV
  change Integrable (fun x=>‖A x‖^2+(if 0<u x then (1:ℝ) else 0)) (volume.restrict B) at hUE
  change Integrable (fun x=>‖V x‖^2+(if 0<v x then (1:ℝ) else 0)) (volume.restrict B) at hVE
  have hip : energy B u A ≤ energy B v V + 2*(∫x in B, inner ℝ (A x) (G x))+
      (∫x in B, ‖L x‖^2)-(∫x in B, ‖G x‖^2) := by
    have hint := integral_mono_ae hUE (((hVE.add (hUV.const_mul 2)).add hL2).sub hG2)
    have he := integral_sub ((hVE.add (hUV.const_mul 2)).add hL2) hG2
    have he1 := integral_add (hVE.add (hUV.const_mul 2)) hL2
    have he2 := integral_add hVE (hUV.const_mul 2)
    have he3 := integral_const_mul (μ:=volume.restrict B) 2 (fun x=>inner ℝ (A x) (G x))
    suffices hp : _ from by
      have ht := hint hp
      dsimp only [Pi.add_apply,Pi.sub_apply] at ht he he1 he2 he3
      change (∫x in B, ‖A x‖^2+(if 0<u x then (1:ℝ) else 0))≤_
      change _≤(∫x in B, ‖V x‖^2+(if 0<v x then (1:ℝ) else 0))+_+_-_
      linarith
    clear he he1 he2 he3 hint
    filter_upwards [hvn,hweq,hz] with x hxn hxw hxz
    have hphase : (if 0<u x then (1:ℝ) else 0)-(if 0<v x then (1:ℝ) else 0)≤‖L x‖^2 := by
      by_cases hu0:0<u x
      · by_cases hv0:0<v x
        · simp [hu0,hv0]
        · have hvz : v x=0 := le_antisymm (not_lt.mp hv0) hxn
          have hLx : L x=A x-(u x/Y x) • gradient Y x := by simp [L,G,hxw,hvz,hxz hvz]
          simpa [hu0,hv0,hLx] using hslope x hu0
      · by_cases hv0:0<v x
        · simp only [hu0,hv0,ite_false,ite_true,zero_sub]
          nlinarith [sq_nonneg ‖L x‖]
        · simp [hu0,hv0]
    have hid : ‖V x‖^2=‖A x‖^2+‖G x‖^2-2*inner ℝ (A x) (G x) := by
      simp only [G,inner_sub_right,real_inner_self_eq_norm_sq,norm_sub_sq_real]
      ring
    simp only [Pi.sub_apply,Pi.add_apply] at *
    linarith
  change (∫x in B, inner ℝ (A x) (G x))=0 at hort
  change (∫x in B, ‖L x‖^2)≤(∫x in B, ‖G x‖^2) at hlower
  linarith
end GroundState

namespace DeSilvaJerison
lemma U_smooth_positive : ContDiffOn ℝ ∞ U {x | 0<U x} := by
  intro x hx
  obtain ⟨hx0,ha⟩ := (U_pos_iff x).mp hx
  have hs : ContDiffAt ℝ ∞ Usigned x :=
    (signed_contDiffAt hx0 (ha.trans t7_lt_one)).const_smul κ
  exact (hs.congr_of_eventuallyEq (U_eventuallyEq_Usigned hx)).contDiffWithinAt

theorem U_lower_comparison (c : Space 7) (r : ℝ) (hr : 0<r)
    {v : Space 7 → ℝ} {V : Space 7 → Space 7}
    (hv : H1 (Metric.ball c r) v V)
    (hvn : ∀ᵐ x ∂volume.restrict (Metric.ball c r), 0≤v x)
    (hvu : ∀ᵐ x ∂volume.restrict (Metric.ball c r), v x≤U x)
    (htrace : H10 (Metric.ball c r) (fun x=>v x-U x) (fun x=>V x-gradient U x)) :
    energy (Metric.ball c r) U (gradient U)≤energy (Metric.ball c r) v V := by
  apply GroundState.lower_comparison c r hr U_continuous U_nonneg U_smooth_positive
    (fun x hx=>(U_harmonic x hx).2.self_of_nhds) U_h1loc (Y:=YSub)
    (fun x hx=>(YSub_contDiffAt ((U_pos_iff x).mp hx).1).contDiffWithinAt)
    (fun x hx=>YSub_pos ((U_pos_iff x).mp hx).1)
    (fun x hx=>YSub_superharmonic ((U_pos_iff x).mp hx).1)
    (fun x hx=>lower_groundstate_slope hx) hv hvn hvu htrace
end DeSilvaJerison
end Bernoulli

end
end

end OAI
