import Mathlib
import OAI.Analysis.BiholderTransport.Contact.MiddleExclusion

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology NNReal ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def rayBenchmarkGap (z : TangentBundle 𝓘(ℝ,Model n) M) (y : M)
    (a vy b By D r C : ℝ) (t : ℝ) : ℝ :=
  -cost (sprayFlow t z).1 y-vy-b*By+‖z.2‖^2/2+a+r-
    (‖z.2‖^2-6*D)*t+C*t^2

omit [Nonempty M] in
lemma rayBenchmarkGap_lipschitzOn (z : TangentBundle 𝓘(ℝ,Model n) M) (y : M)
    (a vy b By D r C T : ℝ) :
    ∃ K, LipschitzOnWith K (fun t => rayBenchmarkGap z y a vy b By D r C t-10*D*t)
      (Icc 0 T) := by
  obtain ⟨K,hK⟩ := neg_cost_ray_lipschitz z y
  have hc : ContDiff ℝ 1 (fun t : ℝ =>
      -vy-b*By+‖z.2‖^2/2+a+r-(‖z.2‖^2-6*D)*t+C*t^2-10*D*t) := by fun_prop
  obtain ⟨L,hL⟩ := hc.contDiffOn.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 T) isCompact_Icc
  refine ⟨K+L,?_⟩
  have he : (fun t => rayBenchmarkGap z y a vy b By D r C t-10*D*t) =
      (fun t => -cost (sprayFlow t z).1 y +
        (-vy-b*By+‖z.2‖^2/2+a+r-(‖z.2‖^2-6*D)*t+C*t^2-10*D*t)) := by
    funext t
    dsimp only [rayBenchmarkGap]
    ring
  rw [he]
  exact hK.lipschitzOnWith.add hL

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma rayBenchmarkGap_hasDerivAt {z : TangentBundle 𝓘(ℝ,Model n) M} {y : M}
    (a vy b By D r C : ℝ) {t d : ℝ}
    (hd : HasDerivAt (fun s => -cost (sprayFlow s z).1 y) d t) :
    HasDerivAt (fun s => rayBenchmarkGap z y a vy b By D r C s-10*D*s)
      (d-‖z.2‖^2-4*D+2*C*t) t := by
  have H0 := ((((hd.sub_const vy).sub_const (b*By)).add_const (‖z.2‖^2/2)).add_const a).add_const r
  have H := ((H0.sub ((hasDerivAt_id t).const_mul (‖z.2‖^2-6*D))).add
      (((hasDerivAt_id t).pow 2).const_mul C)).sub ((hasDerivAt_id t).const_mul (10*D))
  convert H using 1 <;> norm_num [id_eq] <;> first | rfl | ring

omit [Nonempty M] in
lemma benchmark_lower_switch_time {z : TangentBundle 𝓘(ℝ,Model n) M} {y : M}
    {a vy b By D r C η T : ℝ} (hb : 0≤b) (hD : 0<D) (hT : 0≤T)
    (hT1 : T≤1/2) (hC : 0≤C) (hBy : 0≤By) (hlevel : -2*η*D≤vy-a)
    (hsmall : 4*η*D+2*r+12*D*T+2*C*T^2+b≤D)
    (hsmall' : 2*C*T≤2*D)
    (hstart : rayBenchmarkGap z y a vy b By D r C 0≤-b/2)
    (hfinish : 0≤rayBenchmarkGap z y a vy b By D r C T) :
    b/(20*D)≤T := by
  obtain ⟨K,hK⟩ := rayBenchmarkGap_lipschitzOn z y a vy b By D r C T
  have hstart' : rayBenchmarkGap z y a vy b By D r C 0-10*D*0≤-b/2 := by simpa using hstart
  have H := lipschitzOn_barrier hT hK hstart'
  have hd : ∀ᵐ t : ℝ, t∈Icc 0 T → -b/2 < rayBenchmarkGap z y a vy b By D r C t-10*D*t →
      deriv (fun s => rayBenchmarkGap z y a vy b By D r C s-10*D*s) t≤0 := by
    obtain ⟨L,hL⟩ := neg_cost_ray_lipschitz z y
    filter_upwards [hL.ae_differentiableAt] with t ht htI hval
    have hDt : 0≤10*D*t := mul_nonneg (by positivity) htI.1
    have hval' : -b/2≤rayBenchmarkGap z y a vy b By D r C t := by linarith only [hval,hDt]
    have htime : 12*D*t≤12*D*T := mul_le_mul_of_nonneg_left htI.2 (by positivity)
    have hsquare : t^2≤T^2 := pow_le_pow_left₀ htI.1 htI.2 2
    have hquad : 2*C*t^2≤2*C*T^2 := mul_le_mul_of_nonneg_left hsquare (by positivity)
    have hcost : dist (sprayFlow t z).1 y^2≤(1-t)^2*‖z.2‖^2+D := by
      dsimp only [rayBenchmarkGap,cost] at hval'
      have hbB := mul_nonneg hb hBy
      have htP := mul_nonneg (sq_nonneg t) (sq_nonneg ‖z.2‖)
      nlinarith only [hval',hlevel,hsmall,htime,hquad,hbB,htP]
    have Hn := cost_norm_surplus_deriv htI.1 (htI.2.trans hT1) hD.le ht.hasDerivAt hcost
    have hlin : 2*C*t≤2*C*T := mul_le_mul_of_nonneg_left htI.2 (by positivity)
    rw [(rayBenchmarkGap_hasDerivAt a vy b By D r C ht.hasDerivAt).deriv]
    have htP := mul_nonneg htI.1 (sq_nonneg ‖z.2‖)
    nlinarith only [Hn,hlin,hsmall',htP]
  have HT := H hd T ⟨hT,le_rfl⟩
  apply (div_le_iff₀ (by positivity : 0<20*D)).mpr
  nlinarith only [HT,hfinish]

end WeakMTWTransport

end

end OAI
