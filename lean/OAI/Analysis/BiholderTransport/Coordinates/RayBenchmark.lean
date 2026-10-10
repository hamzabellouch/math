import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.SectionDiameter
import OAI.Analysis.BiholderTransport.Regularity.ModifiedData
import OAI.Analysis.BiholderTransport.Regularity.RayAnchor

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section RayBenchmark
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.section_initial_logs (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {x : M} {p q : TangentSpace 𝓘(ℝ,Model n) x} {r a D : ℝ}
    (hr : 0≤r) (hrD : r≤D/5)
    (hp : p∈liftedGapSection u v x r) (hq : q∈liftedGapSection u v x r)
    (ha : v (riemannianExp x p)=a) (ha1 : v (riemannianExp x q)=a+D)
    (hosc : sectionOscillation u v x r≤D) :
    |‖p‖^2-‖q‖^2-2*D|≤2*r ∧ ‖p-q‖^2≤8*(D+r) ∧
      ‖p‖^2-inner ℝ p q≤6*D ∧ D≤‖p‖^2 := by
  have hdiam := (hmtw.liftedGapSection_diameter_sq hu hv hdual hr hp hq).trans
    (mul_le_mul_of_nonneg_left (show r + sectionOscillation u v x r ≤ D + r by linarith only [hosc]) (by norm_num : (0:ℝ)≤8))
  have hp0 := dualPair_gap_nonneg hv hdual x (riemannianExp x p)
  have hq0 := dualPair_gap_nonneg hv hdual x (riemannianExp x q)
  have hp1 := (mem_liftedGapSection_iff.mp hp).2
  have hq1 := (mem_liftedGapSection_iff.mp hq).2
  change contactGap u v x (riemannianExp x p)≤r at hp1
  change contactGap u v x (riemannianExp x q)≤r at hq1
  rw [contactGap,cost_minimizingVector hp.1,ha] at hp0 hp1
  rw [contactGap,cost_minimizingVector hq.1,ha1] at hq0 hq1
  have hid := norm_sub_sq_real p q
  refine ⟨abs_le.mpr ⟨by linarith only [hp0,hq1],by linarith only [hp1,hq0]⟩,?_,?_,?_⟩
  · linarith only [hdiam]
  · nlinarith only [hid,hdiam,hp1,hq0,hrD]
  · nlinarith only [hp0,hq1,hrD,hr,sq_nonneg ‖q‖]

lemma ray_benchmark {v : M → ℝ} (hv : Continuous v) {x : M}
    {p q : TangentSpace 𝓘(ℝ,Model n) x} {a D r C d t : ℝ}
    (hp : p∈minimizingVectors x) (hq : q∈minimizingVectors x)
    (ha : v (riemannianExp x p)=a)
    (hgap : contactGap (cTransform v) v x (riemannianExp x q)≤r)
    (hangle : ‖p‖^2-inner ℝ p q≤6*D) (ht : 0≤t) (hsmall : ‖t • p‖<d)
    (hTaylor : ∀ p' w : TangentSpace 𝓘(ℝ,Model n) x,
      p'∈minimizingVectors x → ‖w‖<d →
      cost (riemannianExp x w) (riemannianExp x p')≤
        cost x (riemannianExp x p')-inner ℝ p' w+C*‖w‖^2) :
    -cost (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 (riemannianExp x q)-
      v (riemannianExp x q)≥
      -‖p‖^2/2-a-r+(‖p‖^2-6*D)*t-C*‖p‖^2*t^2 := by
  have HT := hTaylor q (t • p) hq hsmall
  have H0 := cTransform_gap_nonneg hv x (riemannianExp x p)
  rw [contactGap,cost_minimizingVector hp,ha] at H0
  dsimp only [contactGap] at hgap
  rw [←riemannianExp_smul x p t]
  rw [inner_smul_right,real_inner_comm p q,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht] at HT
  have Hangle := mul_le_mul_of_nonneg_right hangle ht
  nlinarith only [HT,H0,hgap,Hangle]

lemma ray_original_section_anchors {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v)
    {z : TangentBundle 𝓘(ℝ,Model n) M} (hz : z.2∈minimizingVectors z.1)
    {y1 : M} {a D b r H t C : ℝ} {B : ℝ → ℝ}
    (hB : Continuous B) (hb : 0≤b) (hbound : ∀ s,0≤B s ∧ B s≤H)
    (ha : v (riemannianExp z.1 z.2)=a) (ht : 0≤t) (ht1 : t≤1)
    (hanchor : transformRayDifference (modifiedDatum v a D b B) z a t≤r)
    (hbench : -cost (sprayFlow t z).1 y1-v y1≥
      -‖z.2‖^2/2-a-r+(‖z.2‖^2-6*D)*t-C*t^2) :
    contactGap u v (sprayFlow t z).1 (riemannianExp z.1 z.2)≤b*H+r ∧
    contactGap u v (sprayFlow t z).1 y1≤b*H+2*r+6*D*t+C*t^2 := by
  have Hg := (modified_transform_bounds (a := a) (D := D) hu hv hdual hB hb hbound (sprayFlow t z).1).1
  dsimp only [transformRayDifference] at hanchor
  constructor
  · rw [contactGap,minimizing_ray_tail_cost hz ht ht1,ha]
    linarith only [Hg,hanchor]
  · dsimp only [contactGap]
    nlinarith only [Hg,hanchor,hbench,mul_nonneg (sq_nonneg t) (sq_nonneg ‖z.2‖)]

lemma section_absolute_level_bounds {u v : M → ℝ} (hv : Continuous v)
    (hdual : IsCostDualPair u v) {x y0 y1 y : M} {r a D δ : ℝ}
    (hr : 0≤r) (hD : 0<D) (hy0 : y0∈gapSection u v x r)
    (hy1 : y1∈gapSection u v x r) (hy : y∈gapSection u v x r)
    (ha : v y0=a) (ha1 : v y1=a+D)
    (hosc : sectionOscillation u v x r≤(1+δ)*D) :
    -δ≤(v y-a)/D ∧ (v y-a)/D≤1+δ := by
  obtain ⟨ym,hym,yp,hyp,hmin,hmax,he⟩ := sectionOscillation_extrema hv hdual x hr
  have h0 := hmin y0 hy0
  have h1 := hmax y1 hy1
  have hl := hmin y hy
  have hu := hmax y hy
  rw [ha] at h0
  rw [ha1] at h1
  rw [he] at hosc
  constructor
  · apply (le_div_iff₀ hD).mpr
    nlinarith only [h0,h1,hl,hosc]
  · apply (div_le_iff₀ hD).mpr
    nlinarith only [h0,h1,hu,hosc]

end RayBenchmark
end WeakMTWTransport

end

end

end

end OAI
