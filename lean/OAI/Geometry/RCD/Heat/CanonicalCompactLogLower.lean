import OAI.Geometry.RCD.Heat.CanonicalMovingLogLower

namespace OAI

/-! # Uniform sharp lower action on compact endpoint sets -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_compact_log_lower (hK : K ≤ 0)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0)) {A B : Set X} (hA : IsCompact A) (hB : IsCompact B)
    {T η : ℝ} (hT : 0 < T) (hT1 : T < 1) (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ x ∈ A, ∀ y ∈ B,
      -(dist x y)^2/(2*T)-η ≤ ε k*Real.log (hX.canonicalHeatKernel hn p (ε k*T/2) x y) := by
  classical
  by_contra hbad
  have hfreq : ∃ᶠ k in atTop, ∃ x ∈ A, ∃ y ∈ B,
      ε k*Real.log (hX.canonicalHeatKernel hn p (ε k*T/2) x y) < -(dist x y)^2/(2*T)-η := by
    rw [not_eventually] at hbad
    apply hbad.mono
    intro k hk
    by_contra hn
    apply hk
    intro x hx y hy
    exact le_of_not_gt (fun hh => hn ⟨x,hx,y,hy,hh⟩)
  obtain ⟨a,ha,hbad⟩ := extraction_of_frequently_atTop hfreq
  choose u hu v hv hf using hbad
  obtain ⟨q,hq,b,hb,hlim⟩ := (hA.prod hB).tendsto_subseq (fun k =>
    show (u k,v k) ∈ A ×ˢ B from ⟨hu k,hv k⟩)
  have hl := hX.canonicalHeatKernel_moving_log_lower hn p hK
    (fun k => ε (a (b k))) (fun k => hε (a (b k))) (fun k => hε1 (a (b k)))
    (hε0.comp (ha.comp hb).tendsto_atTop) q.1 q.2
    (fun k => u (b k)) (fun k => v (b k))
    (continuous_fst.tendsto q |>.comp hlim) (continuous_snd.tendsto q |>.comp hlim)
    hT hT1 (half_pos hη)
  have hc : Tendsto (fun k => -(dist (u (b k)) (v (b k)))^2/(2*T)-η) atTop
      (𝓝 (-(dist q.1 q.2)^2/(2*T)-η)) := by
    have hd := (continuous_fst.tendsto q |>.comp hlim).dist
      (continuous_snd.tendsto q |>.comp hlim)
    exact ((hd.pow 2).neg.div_const (2*T)).sub_const η
  have he := hc.eventually (gt_mem_nhds (by linarith :
    -(dist q.1 q.2)^2/(2*T)-η < -(dist q.1 q.2)^2/(2*T)-η/2))
  obtain ⟨k,hk,hk'⟩ := (hl.and he).exists
  have hh := hf (b k)
  linarith

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
