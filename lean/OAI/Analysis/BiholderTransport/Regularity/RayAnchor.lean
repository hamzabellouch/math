import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.ActualParameter
import OAI.Analysis.BiholderTransport.Geodesics.RayAdvance

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

omit [Nonempty M] in
lemma minimizing_ray_tail_cost {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hp : z.2∈minimizingVectors z.1) {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
    cost (sprayFlow t z).1 (riemannianExp z.1 z.2)=(1-t)^2*‖z.2‖^2/2 := by
  have hm : dist z.1 (sprayFlow 1 z).1=1*‖z.2‖ := by
    simpa only [one_mul,riemannianExp_eq_sprayFlow] using (show dist z.1 (riemannianExp z.1 z.2)=‖z.2‖ from hp)
  have H := sprayFlow_minimizing_subinterval z ht ht1 hm
  rw [cost,riemannianExp_eq_sprayFlow]
  change dist (sprayFlow t z).1 (sprayFlow 1 z).1^2/2=_
  rw [H,mul_pow]

def transformRayDifference (v : M → ℝ) (z : TangentBundle 𝓘(ℝ,Model n) M) (a t : ℝ) : ℝ :=
  cTransform v (sprayFlow t z).1+(1-t)^2*‖z.2‖^2/2+a

lemma transformRayDifference_lipschitzOn {v : M → ℝ} (hv : Continuous v)
    (z : TangentBundle 𝓘(ℝ,Model n) M) (a T : ℝ) :
    ∃ K, LipschitzOnWith K (transformRayDifference v z a) (Icc 0 T) := by
  obtain ⟨K,hK⟩ := cTransform_ray_lipschitz hv z
  have hc : ContDiff ℝ 1 (fun t : ℝ => (1-t)^2*‖z.2‖^2/2) := by fun_prop
  obtain ⟨L,hL⟩ := hc.contDiffOn.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 T) isCompact_Icc
  refine ⟨K+L,?_⟩
  have H := (hK.lipschitzOnWith.add hL).add (LipschitzWith.const a).lipschitzOnWith
  simp only [add_zero] at H
  exact H

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma transformRayDifference_hasDerivAt {v : M → ℝ}
    {z : TangentBundle 𝓘(ℝ,Model n) M} (a : ℝ) {t d : ℝ}
    (hd : HasDerivAt (fun s=>cTransform v (sprayFlow s z).1) d t) :
    HasDerivAt (transformRayDifference v z a) (d-(1-t)*‖z.2‖^2) t := by
  have hc0 := ((((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow 2).mul_const (‖z.2‖^2)).div_const 2
  have hc : HasDerivAt (fun s : ℝ => (1-s)^2*‖z.2‖^2/2) (-(1-t)*‖z.2‖^2) t := by
    convert hc0 using 1 <;> norm_num
    first | rfl | ring
  have H := (hd.add hc).add_const a
  have he' : d+(-(1-t)*‖z.2‖^2)=d-(1-t)*‖z.2‖^2 := by ring
  rw [he'] at H
  exact H

lemma modified_ray_difference_lower {v : M → ℝ} (hv : Continuous v)
    {z : TangentBundle 𝓘(ℝ,Model n) M} (hp : z.2∈minimizingVectors z.1)
    {a D b : ℝ} {B : ℝ → ℝ} (hB : Continuous B)
    (ha : v (riemannianExp z.1 z.2)=a) {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
    -b*B 0≤transformRayDifference (modifiedDatum v a D b B) z a t := by
  have H := cTransform_gap_nonneg (continuous_modifiedDatum hv a D b hB)
    (sprayFlow t z).1 (riemannianExp z.1 z.2)
  rw [contactGap,modifiedDatum,ha,sub_self,zero_div,minimizing_ray_tail_cost hp ht ht1] at H
  dsimp only [transformRayDifference]
  linarith only [H]

omit [Nonempty M] [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma modified_active_norm_identity {v : M → ℝ}
    {z : TangentBundle 𝓘(ℝ,Model n) M} {a D b t : ℝ} {B : ℝ → ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) (sprayFlow t z).1}
    (hp : p∈activeLogs (modifiedDatum v a D b B) (sprayFlow t z).1) :
    ‖p‖^2=(1-t)^2*‖z.2‖^2-2*(v (riemannianExp (sprayFlow t z).1 p)-a)
      -2*b*B ((v (riemannianExp (sprayFlow t z).1 p)-a)/D)
      -2*transformRayDifference (modifiedDatum v a D b B) z a t := by
  have hc := hp.2
  have hd : dist (sprayFlow t z).1 (riemannianExp (sprayFlow t z).1 p)=‖p‖ := hp.1
  dsimp only [contactGap,modifiedDatum,cost] at hc
  rw [hd] at hc
  dsimp only [transformRayDifference]
  linarith only [hc]

lemma modified_right_active_deficit {v : M → ℝ} (hv : Continuous v)
    {z : TangentBundle 𝓘(ℝ,Model n) M} (hz : z.2∈minimizingVectors z.1)
    {a D b t eta : ℝ} {B : ℝ → ℝ} (hB : Continuous B)
    (ha : v (riemannianExp z.1 z.2)=a) (hb : 0≤b) (hD : 0<D)
    (hbsmall : b≤D/16) (heta : eta≤1/8) (hB0 : B 0≤2)
    (hBn : ∀ s,0≤B s) (ht : 0≤t) (ht1 : t≤1)
    {p : TangentSpace 𝓘(ℝ,Model n) (sprayFlow t z).1}
    (hp : p∈activeLogs (modifiedDatum v a D b B) (sprayFlow t z).1)
    (hs : 1-eta≤(v (riemannianExp (sprayFlow t z).1 p)-a)/D) :
    ‖p‖^2≤(1-t)^2*‖z.2‖^2-D := by
  have H := modified_active_norm_identity hp
  have HL := modified_ray_difference_lower (D := D) (b := b) hv hz hB ha ht ht1
  have HS := (le_div_iff₀ hD).mp hs
  have HB := mul_nonneg hb (hBn ((v (riemannianExp (sprayFlow t z).1 p)-a)/D))
  have HB0 := mul_le_mul_of_nonneg_left hB0 hb
  have HB1 := mul_le_mul_of_nonneg_left heta hD.le
  nlinarith only [H,HL,HS,HB,HB0,HB1,hbsmall,hD]

end WeakMTWTransport

end

end OAI
