import Mathlib
import OAI.Analysis.BiholderTransport.Oscillation.SectionOscillation
import OAI.Analysis.BiholderTransport.Regularity.TemplateRightWeight
import OAI.Analysis.BiholderTransport.Regularity.ModifiedData

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ActualLevels
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma contact_of_global_support {g : M → ℝ} (hg : Continuous g) {x y : M}
    (hs : ∀ a,g x+cost x y ≤ g a+cost a y) :
    contactGap g (cTransform g) x y=0 := by
  have hupper : cTransform g y ≤  -g x-cost x y := by
    rw [cTransform_le_iff hg]
    intro a
    rw [cost_symm y a]
    linarith only [hs a]
  have hlower := cTransform_gap_nonneg hg y x
  rw [contactGap,cost_symm y x] at hlower
  dsimp only [contactGap]
  linarith only [hupper,hlower]

lemma WeakMTW.modified_aligned_levels (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {a D b H : ℝ} {Bc Bo : ℝ → ℝ} (ho : Continuous Bo) (hb : 0 ≤ b)
    (hob : ∀ s,0 ≤ Bo s ∧ Bo s ≤ H) (hcb : ∀ s,-1 ≤ Bc s ∧ Bc s ≤ 1)
    {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (modifiedDatum v a D b Bo) x)) :
    let y := riemannianExp x p
    y ∈ gapSection u v x ((H+2)*b) ∧
    ∀ pi ∈ activeLogs (n := n) (modifiedDatum v a D b Bo) x,
      riemannianExp x pi ∈ gapSection u v x ((H+2)*b) ∧
      v (riemannianExp x pi)-v y=(‖p‖^2-‖pi‖^2)/2+
        b*(Bc ((v y-a)/D)-Bo ((v (riemannianExp x pi)-a)/D))-
        modifiedExcess v a D b Bc Bo y := by
  dsimp only
  have hw := continuous_modifiedDatum hv a D b ho
  obtain ⟨hpm,hs⟩ := hmtw.active_hull_global_support hw hp
  have hcontact := contact_of_global_support (continuous_cTransform hw) hs
  have he := modified_excess_at_contact (Bc := Bc) hcontact
  have hupp := modified_excess_upper (a := a) (D := D) hu hv hdual ho hb (fun s=>(hob s).1)
    (fun s=>(hcb s).2) (riemannianExp x p)
  have hg := (modified_transform_bounds (a := a) (D := D) hu hv hdual ho hb hob x).1
  have hc := mul_le_mul_of_nonneg_left (hcb ((v (riemannianExp x p)-a)/D)).1 hb
  refine ⟨?_,?_⟩
  · change contactGap u v x (riemannianExp x p) ≤ (H+2)*b
    dsimp only [contactGap]
    linarith only [he,hupp,hg,hc]
  · intro pi hi
    refine ⟨?_,?_⟩
    · have HA := modified_contact_original_section hu hv hdual ho hb hob hi.2
      change contactGap u v x (riemannianExp x pi) ≤ (H+2)*b
      linarith only [HA,hb]
    · have hai := hi.2
      change cTransform (modifiedDatum v a D b Bo) x+cost x (riemannianExp x pi)+
        (v (riemannianExp x pi)+b*Bo ((v (riemannianExp x pi)-a)/D))=0 at hai
      have hpn : cost x (riemannianExp x p)=‖p‖^2/2 := by rw [cost,hpm]
      have hin : cost x (riemannianExp x pi)=‖pi‖^2/2 := by rw [cost,hi.1]
      rw [hpn] at he
      rw [hin] at hai
      linarith only [he,hai]

lemma modified_positive_excess_center_level {u v : M → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {a D b : ℝ} {Bc Bo : ℝ → ℝ} (ho : Continuous Bo) (hb : 0 ≤ b)
    (hob : ∀ s,0 ≤ Bo s) (hright : ∀ s,3/4 ≤ s → Bc s ≤ 0) {y : M}
    (he : 0 < modifiedExcess v a D b Bc Bo y) : (v y-a)/D < 3/4 := by
  have hl := (modified_double_bounds (a := a) (D := D) hu hv hdual ho hb hob y).1
  by_contra h
  have hh := mul_nonpos_of_nonneg_of_nonpos hb (hright _ (le_of_not_gt h))
  dsimp only [modifiedExcess,modifiedDatum] at he
  linarith only [he,hl,hh]

lemma section_level_range {u v : M → ℝ} (hv : Continuous v) (hdual : IsCostDualPair u v)
    {x y z : M} {r a D delta : ℝ} (hr : 0 ≤ r) (hD : 0 < D)
    (hy : y ∈ gapSection u v x r) (hz : z ∈ gapSection u v x r)
    (hosc : sectionOscillation u v x r ≤ (1+delta)*D) :
    |(v y-a)/D-(v z-a)/D| ≤ 1+delta := by
  obtain ⟨y0,_,y1,_,hl,hu,he⟩ := sectionOscillation_extrema hv hdual x hr
  have hyy0 := hl y hy
  have hyy1 := hu y hy
  have hzz0 := hl z hz
  have hzz1 := hu z hz
  rw [he] at hosc
  rw [←sub_div,abs_div,abs_of_pos hD]
  apply (div_le_iff₀ hD).mpr
  apply abs_le.mpr
  constructor  <;> linarith only [hyy0,hyy1,hzz0,hzz1,hosc]

lemma limiting_levels_lower {ι : Type*} [Fintype ι] {m si : ι → ℝ}
    {Bc Bo : ℝ → ℝ} {s eta delta c : ℝ}
    (hm : ∀ i,0 ≤ m i) (hsum : ∑ i,m i=1)
    (hBo : ∀ r,0 ≤ Bo r) (hleft : ∀ r,r < 1-eta → 1 ≤ Bo r)
    (hBc : Bc s ≤ 1) (hc : 0 < c) (hparameter : c ≤ Bc s-∑ i,m i*Bo (si i))
    (hrange : ∀ i j,|si i-si j| ≤ 1+delta) (hcenter : ∀ i,|s-si i| ≤ 1+delta)
    (hdelta : delta ≤ eta) :
    -2*eta ≤ s ∧ ∀ i,-2*eta ≤ si i := by
  classical
  have H := template_right_weight hm hsum (fun i=>hBo (si i))
    (fun i=>hleft (si i)) hBc hparameter
  obtain ⟨j,hj,_⟩ := Finset.sum_pos_iff_of_nonneg (fun i _=>hm i) |>.mp (hc.trans_le H)
  have hright := (Finset.mem_filter.mp hj).2
  refine ⟨?_,?_⟩
  · have hsc := (abs_le.mp (hcenter j)).1
    linarith only [hsc,hright,hdelta]
  · intro i
    have hsi := (abs_le.mp (hrange i j)).1
    linarith only [hsi,hright,hdelta]

end ActualLevels
end WeakMTWTransport

end
end

end OAI
