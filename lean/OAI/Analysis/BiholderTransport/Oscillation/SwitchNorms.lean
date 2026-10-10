import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.LiftedSections
import OAI.Analysis.BiholderTransport.Regularity.ModifiedData
import OAI.Analysis.BiholderTransport.Regularity.RayAnchor

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section SwitchNorms
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma active_switch_norm_identity {v : M → ℝ}
    {z : TangentBundle 𝓘(ℝ,Model n) M} {a D b t : ℝ} {B : ℝ → ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) (sprayFlow t z).1}
    (hp : p∈activeLogs (modifiedDatum v a D b B) (sprayFlow t z).1) :
    ‖p‖^2=(1-t)^2*‖z.2‖^2-2*(v (riemannianExp (sprayFlow t z).1 p)-a)-
      2*b*B ((v (riemannianExp (sprayFlow t z).1 p)-a)/D)-
      2*transformRayDifference (modifiedDatum v a D b B) z a t := by
  have hc := hp.2
  rw [contactGap,cost_minimizingVector hp.1] at hc
  dsimp only [modifiedDatum] at hc
  dsimp only [transformRayDifference]
  linarith only [hc]

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma active_switch_norm_brackets {v : M → ℝ}
    {z : TangentBundle 𝓘(ℝ,Model n) M} {a D b r H t : ℝ} {B : ℝ → ℝ}
    {pm pp : TangentSpace 𝓘(ℝ,Model n) (sprayFlow t z).1}
    (hm : pm∈activeLogs (modifiedDatum v a D b B) (sprayFlow t z).1)
    (hp : pp∈activeLogs (modifiedDatum v a D b B) (sprayFlow t z).1)
    (hD : 0<D) (hb : 0≤b) (hbD : b≤D/16) (ht : 0≤t) (ht1 : t≤1/2)
    (hBo : ∀ s,0≤B s ∧ B s≤H) (hB0 : B 0≤2)
    (hl : (v (riemannianExp (sprayFlow t z).1 pm)-a)/D≤1/16)
    (hr : 7/8≤(v (riemannianExp (sprayFlow t z).1 pp)-a)/D)
    (hanchor : -b*B 0≤transformRayDifference (modifiedDatum v a D b B) z a t ∧
      transformRayDifference (modifiedDatum v a D b B) z a t≤r)
    (hsmall : 2*t*‖z.2‖^2+2*b*H+2*r≤D/4) :
    ‖pp‖^2≤‖z.2‖^2-D/2 ∧ ‖z.2‖^2-D/2≤‖pm‖^2 := by
  have Hm := active_switch_norm_identity hm
  have Hp := active_switch_norm_identity hp
  have hl' := (div_le_iff₀ hD).mp hl
  have hr' := (le_div_iff₀ hD).mp hr
  have HmB := mul_le_mul_of_nonneg_left (hBo ((v (riemannianExp (sprayFlow t z).1 pm)-a)/D)).2 hb
  have HpB := mul_nonneg hb (hBo ((v (riemannianExp (sprayFlow t z).1 pp)-a)/D)).1
  have H0 := mul_le_mul_of_nonneg_left hB0 hb
  have htP := mul_nonneg (sq_nonneg t) (sq_nonneg ‖z.2‖)
  have htime : (1-t)^2*‖z.2‖^2≤‖z.2‖^2 := by
    apply mul_le_of_le_one_left (sq_nonneg _) _
    nlinarith only [ht,ht1]
  constructor
  · nlinarith only [Hp,hr',HpB,H0,htime,hanchor.1,hbD,hD]
  · nlinarith only [Hm,hl',HmB,htP,hsmall,hanchor.2,hD]

lemma WeakMTW.active_hull_double_contact (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈convexHull ℝ (activeLogs v x)) :
    p∈minimizingVectors x ∧ contactGap (cTransform v) (cTransform (cTransform v))
      x (riemannianExp x p)=0 := by
  obtain ⟨hm,H⟩ := hmtw.active_hull_global_support hv hp
  refine ⟨hm,le_antisymm ?_ ?_⟩
  · have hh : cTransform (cTransform v) (riemannianExp x p)≤-cTransform v x-cost x (riemannianExp x p) := by
      rw [cTransform_le_iff (continuous_cTransform hv)]
      intro z
      rw [cost_symm]
      linarith only [H z]
    dsimp only [contactGap]
    linarith only [hh]
  · have hh := cTransform_gap_nonneg (continuous_cTransform hv) (riemannianExp x p) x
    dsimp only [contactGap] at hh ⊢
    rw [cost_symm (riemannianExp x p) x] at hh
    linarith only [hh]

end SwitchNorms
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section PositiveExcess
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma positive_modified_excess_at_midnorm {v : M → ℝ} (hv : Continuous v)
    {z : TangentBundle 𝓘(ℝ,Model n) M} (hz : z.2∈minimizingVectors z.1)
    {a D b r C d t : ℝ} {Bc Bo : ℝ → ℝ} (ho : Continuous Bo)
    (ha : v (riemannianExp z.1 z.2)=a)
    (hb : 0≤b) (hD : 0<D) (hbD : b≤D/16) (ht : 0≤t) (ht1 : t≤1/2)
    (htime : b/(32*D)≤t)
    (hgap0 : contactGap (cTransform v) v z.1 (riemannianExp z.1 z.2)≤r)
    (hc0 : ∀ s, -1≤Bc s) (hc1 : ∀ s≤1/2,1-1/1024≤Bc s) (ho0 : Bo 0≤1+1/1024)
    (hsmall : ‖t • z.2‖<d) (herror : r+(C+1)*t^2*‖z.2‖^2≤b/1024)
    (p : TangentSpace 𝓘(ℝ,Model n) (sprayFlow t z).1)
    (hp : p∈minimizingVectors (sprayFlow t z).1)
    (hpN : ‖p‖^2=‖z.2‖^2-D/2)
    (hpC : contactGap (cTransform (modifiedDatum v a D b Bo))
      (cTransform (cTransform (modifiedDatum v a D b Bo)))
      (sprayFlow t z).1 (riemannianExp (sprayFlow t z).1 p)=0)
    (hTaylor : ∀ p' w : TangentSpace 𝓘(ℝ,Model n) (sprayFlow t z).1,
      p'∈minimizingVectors (sprayFlow t z).1 → ‖w‖<d →
      cost (riemannianExp (sprayFlow t z).1 w) (riemannianExp (sprayFlow t z).1 p')≤
        cost (sprayFlow t z).1 (riemannianExp (sprayFlow t z).1 p')-inner ℝ p' w+C*‖w‖^2) :
    b/1024≤ modifiedExcess v a D b Bc Bo (riemannianExp (sprayFlow t z).1 p) := by
  let y := riemannianExp (sprayFlow t z).1 p
  let w := modifiedDatum v a D b Bo
  have hw : Continuous w := continuous_modifiedDatum hv a D b ho
  have Hg := cTransform_gap_nonneg hw (sprayFlow t z).1 (riemannianExp z.1 z.2)
  have hy0 : (v (riemannianExp z.1 z.2)-a)/D=0 := by rw [ha]; simp
  rw [contactGap,minimizing_ray_tail_cost hz ht (by linarith only [ht1]) ] at Hg
  change 0≤cTransform w (sprayFlow t z).1+(1-t)^2*‖z.2‖^2/2+
    (v (riemannianExp z.1 z.2)+b*Bo ((v (riemannianExp z.1 z.2)-a)/D)) at Hg
  rw [hy0,ha] at Hg
  have HE := modified_excess_at_contact (Bc := Bc) hpC
  change modifiedExcess v a D b Bc Bo y=v y+b*Bc ((v y-a)/D)+cost (sprayFlow t z).1 y+cTransform w (sprayFlow t z).1 at HE
  have hcost : cost (sprayFlow t z).1 y=‖z.2‖^2/2-D/4 := by
    rw [show y=riemannianExp (sprayFlow t z).1 p from rfl,cost_minimizingVector hp,hpN]
    ring
  change b/1024≤ modifiedExcess v a D b Bc Bo y
  by_cases hlevel : (v y-a)/D≤1/2
  · have hBc := mul_le_mul_of_nonneg_left (hc1 _ hlevel) hb
    have hBo := mul_le_mul_of_nonneg_left ho0 hb
    have hG := cTransform_gap_nonneg hv z.1 y
    rw [contactGap,cost_minimizingVector hz,ha] at hgap0
    dsimp only [contactGap] at hG
    have hback : riemannianExp (sprayFlow t z).1 ((-t) • (sprayFlow t z).2)=z.1 := by
      rw [riemannianExp_smul]
      change (sprayFlow (-t) (sprayFlow t z)).1=z.1
      rw [←sprayFlow_add,neg_add_cancel,sprayFlow_zero]
    have hwidth : ‖(-t) • (sprayFlow t z).2‖<d := by
      simpa only [norm_smul,Real.norm_eq_abs,abs_neg,sprayFlow_speed] using hsmall
    have HT := hTaylor p ((-t) • (sprayFlow t z).2) hp hwidth
    rw [hback,inner_smul_right,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg ht,sprayFlow_speed] at HT
    change cost z.1 y≤cost (sprayFlow t z).1 y-(-t)*inner ℝ p (sprayFlow t z).2+C*(t*‖z.2‖)^2 at HT
    have hcross : D/4≤‖z.2‖^2-inner ℝ p (sprayFlow t z).2 := by
      have H := norm_sub_sq_real p (sprayFlow t z).2
      rw [sprayFlow_speed,hpN] at H
      nlinarith only [H,sq_nonneg ‖p-(sprayFlow t z).2‖]
    have hcross' := mul_le_mul_of_nonneg_right hcross ht
    have htime' := (div_le_iff₀ (by positivity : 0<32*D)).mp htime
    have htP := mul_nonneg (sq_nonneg t) (sq_nonneg ‖z.2‖)
    nlinarith only [HE,Hg,hBc,hBo,hG,hgap0,HT,hcross',htime',herror,htP,hb]
  · have hl : D/2≤v y-a := by
      have H := (le_div_iff₀ hD).mp (le_of_lt (lt_of_not_ge hlevel))
      linarith only [H]
    have hBc := mul_le_mul_of_nonneg_left (hc0 ((v y-a)/D)) hb
    have hBo := mul_le_mul_of_nonneg_left ho0 hb
    have htime' : 0≤(2*t-t^2)*‖z.2‖^2 := by
      apply mul_nonneg _ (sq_nonneg _)
      nlinarith only [ht,ht1]
    nlinarith only [HE,Hg,hcost,hl,hBc,hBo,htime',hbD,hb]

end PositiveExcess
end WeakMTWTransport

end

end

end

end OAI
