import Mathlib
import OAI.Analysis.BiholderTransport.Contact.MiddleExclusion
import OAI.Analysis.BiholderTransport.Regularity.RayAnchor
import OAI.Analysis.BiholderTransport.Regularity.RestrictedTransform

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace WeakMTWTransport

lemma scalar_first_switch {f h : ℝ → ℝ} {K : ℝ≥0} {b D r : ℝ}
    (hb : 0<b) (hD : 0<D) (hr : r≤b) (hh : Continuous h) (h0 : 0<h 0)
    (hf : LipschitzOnWith K f (Icc 0 (8*b/D)))
    (hf0 : f 0≤r) (hfT : -2*b≤f (8*b/D))
    (hdrop : ∀ᵐ t : ℝ, t∈Icc 0 (8*b/D) → 0<h t → deriv f t≤-D/2) :
    ∃ τ∈Ioc 0 (8*b/D), h τ=0 ∧ ∀ t∈Ico 0 τ, 0<h t := by
  let T := 8*b/D
  have hT : 0<T := by dsimp [T]; positivity
  have hex : ∃ τ∈Icc 0 T, h τ=0 := by
    by_contra H
    have hpos : ∀ t∈Icc 0 T, 0<h t := by
      intro t ht
      by_contra ht'
      have hi := intermediate_value_Icc' ht.1 hh.continuousOn
        (show (0:ℝ)∈Icc (h t) (h 0) from ⟨le_of_not_gt ht',h0.le⟩)
      obtain ⟨s,hs,hse⟩ := hi
      exact H ⟨s,⟨hs.1,hs.2.trans ht.2⟩,hse⟩
    have Hdrop : ∀ᵐ t : ℝ, t∈Icc 0 T → deriv f t≤-D/2 := by
      filter_upwards [hdrop] with t ht hmem
      exact ht hmem (hpos t hmem)
    have Hdec := lipschitzOn_sub_le_of_ae_deriv_le hT.le hf Hdrop
    have he : (-D/2)*(T-0)=-4*b := by dsimp [T]; field_simp; ring
    rw [he] at Hdec
    linarith only [Hdec,hf0,hfT,hr,hb]
  let Z : Set ℝ := {t∈Icc 0 T | h t=0}
  have hZ : IsCompact Z := isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.inter (isClosed_eq hh continuous_const)) (fun _ ht=>ht.1)
  have hZn : Z.Nonempty := by obtain ⟨t,ht,he⟩:=hex; exact ⟨t,ht,he⟩
  obtain ⟨τ,hτ,hτmin⟩ := hZ.exists_isLeast hZn
  have hτ0 : 0<τ := lt_of_le_of_ne hτ.1.1 (by intro H; subst τ; linarith only [h0,hτ.2])
  refine ⟨τ,⟨hτ0,hτ.1.2⟩,hτ.2,?_⟩
  intro t ht
  by_contra ht'
  obtain ⟨s,hs,hse⟩ := intermediate_value_Icc' ht.1 hh.continuousOn
    (show (0:ℝ)∈Icc (h t) (h 0) from ⟨le_of_not_gt ht',h0.le⟩)
  have hsZ : s∈Z := ⟨⟨hs.1,hs.2.trans (ht.2.le.trans hτ.1.2)⟩,hse⟩
  exact (not_le_of_gt (hs.2.trans_lt ht.2)) (hτmin hsZ)

end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology NNReal ContDiff

namespace WeakMTWTransport
section FirstSwitch
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma modified_middle_not_contact {v : M → ℝ} (hv : Continuous v)
    {z : TangentBundle 𝓘(ℝ,Model n) M} (hz : z.2∈minimizingVectors z.1)
    {a D b r eta t : ℝ} {B : ℝ → ℝ} (hB : Continuous B)
    (ha : v (riemannianExp z.1 z.2)=a) (hb : 0<b) (hD : 0<D)
    (hr : r≤b/4) (ht : 0≤t) (ht1 : t≤1/2)
    (hgap : contactGap (cTransform v) v z.1 (riemannianExp z.1 z.2)≤r)
    (hbar : ∀ s∈Icc (1/16) (1-eta),B 0+1≤B s) {y : M}
    (hy : (v y-a)/D∈Icc (1/16) (1-eta)) :
    contactGap (cTransform (modifiedDatum v a D b B)) (modifiedDatum v a D b B)
      (sprayFlow t z).1 y≠0 := by
  have Hcost : cost z.1 (riemannianExp z.1 z.2)=‖z.2‖^2/2 := by
    rw [cost,show dist z.1 (riemannianExp z.1 z.2)=‖z.2‖ from hz]
  have hg := cTransform_gap_nonneg hv z.1 y
  rw [contactGap,Hcost,ha] at hgap
  have hBdiff : b≤b*(B ((v y-a)/D)-B 0) := by
    have H := mul_le_mul_of_nonneg_left (hbar _ hy) hb.le
    nlinarith only [H]
  have hs : D/16≤v y-a := by
    have H := (le_div_iff₀ hD).mp hy.1
    linarith only [H]
  have hstart : rayMountainDifference z y a (v y) b (B 0) (B ((v y-a)/D)) 0≤-b/2 := by
    dsimp only [rayMountainDifference]
    rw [sprayFlow_zero]
    norm_num only [sub_zero,one_pow,one_mul]
    dsimp only [contactGap] at hg
    linarith only [hg,hgap,hBdiff,hr,hb]
  have H := middle_mountain_barrier hb.le hD ht ht1 hs (hbar _ hy) hstart t ⟨ht,le_rfl⟩
  intro hc
  have HL := modified_ray_difference_lower (D := D) (b := b) hv hz hB ha ht (by linarith only [ht1])
  dsimp only [rayMountainDifference] at H
  dsimp only [transformRayDifference] at HL
  dsimp only [contactGap,modifiedDatum] at hc
  linarith only [H,HL,hc,hb]

lemma actual_first_switch {v : M → ℝ} (hv : Continuous v)
    {z : TangentBundle 𝓘(ℝ,Model n) M} (hz : z.2∈minimizingVectors z.1)
    {y1 : M} {a D b r eta : ℝ} {B : ℝ → ℝ} (hB : Continuous B)
    (ha : v (riemannianExp z.1 z.2)=a) (ha1 : v y1=a+D)
    (hb : 0<b) (hD : 0<D) (hr : r≤b/4) (hbD : b≤D/16) (heta0 : 0≤eta) (heta : eta≤1/8)
    (hBn : ∀ s,0≤B s) (hB0 : B 0≤2) (hB1 : B 1=0)
    (hBl : ∀ s≤1/16,1≤B s)
    (hbar : ∀ s∈Icc (1/16) (1-eta),B 0+1≤B s)
    (hgap0 : contactGap (cTransform v) v z.1 (riemannianExp z.1 z.2)≤r)
    (hgap1 : contactGap (cTransform v) v z.1 y1≤r) :
    ∃ τ∈Ioc 0 (8*b/D), ∃ ym yp : M,
      (v ym-a)/D<1/16 ∧ 1-eta≤(v yp-a)/D ∧
      contactGap (cTransform (modifiedDatum v a D b B)) (modifiedDatum v a D b B)
        (sprayFlow τ z).1 ym=0 ∧
      contactGap (cTransform (modifiedDatum v a D b B)) (modifiedDatum v a D b B)
        (sprayFlow τ z).1 yp=0 ∧
      ∀ t∈Icc 0 τ, -b*B 0≤transformRayDifference (modifiedDatum v a D b B) z a t ∧
        transformRayDifference (modifiedDatum v a D b B) z a t≤r := by
  let w := modifiedDatum v a D b B
  have hw : Continuous w := continuous_modifiedDatum hv a D b hB
  let S : Set M := {y | (v y-a)/D≤1/16}
  let R : Set M := {y | 1-eta≤(v y-a)/D}
  have hS : IsCompact S := (isClosed_le ((hv.sub continuous_const).div_const D) continuous_const).isCompact
  have hR : IsCompact R := (isClosed_le continuous_const ((hv.sub continuous_const).div_const D)).isCompact
  have hSn : S.Nonempty := ⟨riemannianExp z.1 z.2,by dsimp [S]; rw [ha]; norm_num⟩
  have hRn : R.Nonempty := ⟨y1,by dsimp [R]; simp only [ha1,add_sub_cancel_left,div_self hD.ne']; linarith only [heta0]⟩
  let L : ℝ → ℝ := fun t => restrictedTransform w S (sprayFlow t z).1
  let U : ℝ → ℝ := fun t => restrictedTransform w R (sprayFlow t z).1
  have hL : Continuous L := (continuous_restrictedTransform hw hS hSn).comp
    (lipschitz_spray_projection z).continuous
  have hU : Continuous U := (continuous_restrictedTransform hw hR hRn).comp
    (lipschitz_spray_projection z).continuous
  let T := 8*b/D
  have hT : 0<T := by dsimp [T]; positivity
  have hT1 : T≤1/2 := by dsimp [T]; apply (div_le_iff₀ hD).mpr; linarith only [hbD]
  have hcover : ∀ t∈Icc 0 T,∀ y,contactGap (cTransform w) w (sprayFlow t z).1 y=0 → y∈S∪R := by
    intro t ht y hc
    by_contra H
    have hs : 1/16<(v y-a)/D := lt_of_not_ge (fun h=>H (Or.inl h))
    have hr' : (v y-a)/D<1-eta := lt_of_not_ge (fun h=>H (Or.inr h))
    exact modified_middle_not_contact hv hz hB ha hb hD hr ht.1 (ht.2.trans hT1)
      hgap0 hbar ⟨hs.le,hr'.le⟩ hc
  have heq : ∀ t∈Icc 0 T,cTransform w (sprayFlow t z).1=max (L t) (U t) := by
    intro t ht
    exact cTransform_eq_max_restricted hw hS hSn hR hRn (hcover t ht)
  have hL0 : L 0≤cTransform v z.1-b := by
    obtain ⟨y,hy,he,H⟩ := exists_restrictedTransform_contact hw hS hSn z.1
    have Hg := cTransform_gap_nonneg hv z.1 y
    have HB := mul_le_mul_of_nonneg_left (hBl ((v y-a)/D) hy) hb.le
    dsimp only [L]
    rw [sprayFlow_zero,he]
    dsimp only [w,modifiedDatum,contactGap] at *
    linarith only [Hg,HB]
  have hU0 : cTransform v z.1-r≤U 0 := by
    obtain ⟨y,hy,he,H⟩ := exists_restrictedTransform_contact hw hR hRn z.1
    have hy1 : y1∈R := by dsimp [R]; simp only [ha1,add_sub_cancel_left,div_self hD.ne']; linarith only [heta0]
    have H1 := H y1 hy1
    have he1 : (v y1-a)/D=1 := by simp only [ha1,add_sub_cancel_left,div_self hD.ne']
    dsimp only [w,modifiedDatum] at H1
    rw [he1,hB1,mul_zero,add_zero] at H1
    dsimp only [U]
    rw [sprayFlow_zero]
    dsimp only [contactGap] at hgap1
    linarith only [H1,hgap1]
  have h0 : 0<U 0-L 0 := by linarith only [hL0,hU0,hr,hb]
  let f := transformRayDifference w z a
  obtain ⟨K,hK⟩ := transformRayDifference_lipschitzOn hw z a T
  have hf0 : f 0≤r := by
    have HG := cTransform_antitone hv hw (fun y=>by
      dsimp only [w,modifiedDatum]; exact le_add_of_nonneg_right (mul_nonneg hb.le (hBn _))) z.1
    have Hcost : cost z.1 (riemannianExp z.1 z.2)=‖z.2‖^2/2 := by rw [cost,show dist z.1 (riemannianExp z.1 z.2)=‖z.2‖ from hz]
    rw [contactGap,Hcost,ha] at hgap0
    dsimp only [f,transformRayDifference]
    rw [sprayFlow_zero]
    norm_num only [sub_zero,one_pow,one_mul]
    linarith only [HG,hgap0]
  have hfT : -2*b≤f T := by
    have H := modified_ray_difference_lower (D := D) (b := b) hv hz hB ha hT.le (by linarith only [hT1])
    have HB := mul_le_mul_of_nonneg_left hB0 hb.le
    linarith only [H,HB]
  have hdrop : ∀ᵐ t : ℝ,t∈Icc 0 T → 0<U t-L t → deriv f t≤-D/2 := by
    obtain ⟨C,hC⟩ := cTransform_ray_lipschitz hw z
    filter_upwards [hC.ae_differentiableAt] with t ht htI hpos
    have Hnorm : ∀ p∈activeLogs (n := n) w (sprayFlow t z).1,
        ‖p‖^2≤(1-t)^2*‖z.2‖^2-D := by
      intro p hp
      have hs : 1-eta≤(v (riemannianExp (sprayFlow t z).1 p)-a)/D := by
        rcases hcover t htI _ hp.2 with h|h
        · have HL := restrictedTransform_eq_of_contact hw hS hSn h hp.2
          have HU := restrictedTransform_le hw hR hRn (sprayFlow t z).1
          change L t=cTransform w (sprayFlow t z).1 at HL
          change U t≤cTransform w (sprayFlow t z).1 at HU
          linarith only [hpos,HL,HU]
        · exact h
      exact modified_right_active_deficit hv hz hB ha hb.le hD hbD heta hB0 hBn
        htI.1 (by linarith only [htI.2,hT1]) hp hs
    have H := active_norm_deficit_deriv hw htI.1 (htI.2.trans hT1) hD.le ht.hasDerivAt Hnorm
    rw [(transformRayDifference_hasDerivAt a ht.hasDerivAt).deriv]
    exact H
  obtain ⟨τ,hτ,hτe,hpre⟩ := scalar_first_switch hb hD (by linarith only [hr,hb])
    (hU.sub hL) h0 hK hf0 hfT hdrop
  have hτI : τ∈Icc 0 T := ⟨hτ.1.le,hτ.2⟩
  change U τ-L τ=0 at hτe
  have Hτ : U τ=L τ := by linarith only [hτe]
  have Hmax := heq τ hτI
  rw [Hτ,max_self] at Hmax
  obtain ⟨ym,hym,hem,_⟩ := exists_restrictedTransform_contact hw hS hSn (sprayFlow τ z).1
  obtain ⟨yp,hyp,hep,_⟩ := exists_restrictedTransform_contact hw hR hRn (sprayFlow τ z).1
  have hcm : contactGap (cTransform w) w (sprayFlow τ z).1 ym=0 := by
    dsimp only [contactGap]
    change L τ= -cost (sprayFlow τ z).1 ym-w ym at hem
    linarith only [Hmax,hem]
  have hcp : contactGap (cTransform w) w (sprayFlow τ z).1 yp=0 := by
    dsimp only [contactGap]
    change U τ= -cost (sprayFlow τ z).1 yp-w yp at hep
    linarith only [Hmax,Hτ,hep]
  refine ⟨τ,hτ,ym,yp,?_,hyp,hcm,hcp,?_⟩
  · apply lt_of_le_of_ne hym
    intro He
    have hm : (v ym-a)/D∈Icc (1/16) (1-eta) := by rw [He]; constructor <;> linarith only [heta]
    exact modified_middle_not_contact hv hz hB ha hb hD hr hτI.1 (hτI.2.trans hT1)
      hgap0 hbar hm hcm
  · intro t ht
    refine ⟨modified_ray_difference_lower hv hz hB ha ht.1
      (by linarith only [ht.2,hτI.2,hT1]),?_⟩
    have hsmall : Icc 0 t⊆Icc 0 T := Icc_subset_Icc_right (ht.2.trans hτI.2)
    have hne : ∀ᵐ s : ℝ,s≠τ := by rw [ae_iff]; simp
    have hd : ∀ᵐ s : ℝ,s∈Icc 0 t → deriv f s≤-D/2 := by
      filter_upwards [hdrop,hne] with s hs hne hsI
      exact hs (hsmall hsI) (hpre s ⟨hsI.1,lt_of_le_of_ne (hsI.2.trans ht.2) hne⟩)
    have H := lipschitzOn_sub_le_of_ae_deriv_le ht.1 (hK.mono hsmall) hd
    have Hn : (-D/2)*(t-0)≤0 := mul_nonpos_of_nonpos_of_nonneg (by linarith only [hD])
      (by linarith only [ht.1])
    change f t≤r
    linarith only [H,Hn,hf0]

end FirstSwitch
end WeakMTWTransport

end

end

end

end OAI
