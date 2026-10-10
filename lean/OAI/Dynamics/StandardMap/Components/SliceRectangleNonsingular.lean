import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Components.CurvedHolonomy

namespace OAI

section
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology

theorem rectangle_quasiMeasurePreserving {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) (β : Measure B) [SFinite α] [SFinite β]
    {I : Set ℝ} (hI : MeasurableSet I)
    (G : A → ℝ → ℝ) (hG : Measurable (fun p : A×ℝ => G p.1 p.2))
    (π : A×B → ℝ×ℝ) (hπ : Measurable π)
    (hgraph : ∀ p,(π p).2=G p.1 (π p).1)
    (haffine : ∀ x∈I,QuasiMeasurePreserving (fun a => G a x) α volume)
    (hcurved : ∀ a,QuasiMeasurePreserving (fun b => (π (a,b)).1) β (volume.restrict I)) :
    QuasiMeasurePreserving π (α.prod β) (volume : Measure (ℝ×ℝ)) := by
  refine ⟨hπ,AbsolutelyContinuous.mk fun N hN hNzero => ?_⟩
  rw [map_apply hπ hN]
  have hslice : ∀ᵐ x ∂volume.restrict I,∀ᵐ y ∂(volume : Measure ℝ),(x,y)∉N := by
    apply ae_restrict_of_ae
    apply ae_ae_of_ae_prod (p := fun p : ℝ×ℝ => p∉N)
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq,Measure.volume_eq_prod] using hNzero
  have hGEN : ∀ᵐ x ∂volume.restrict I,∀ᵐ a ∂α,(x,G a x)∉N := by
    filter_upwards [hslice,ae_restrict_mem hI] with x hx hxI
    exact (haffine x hxI).ae hx
  have hprod : ∀ᵐ p ∂(volume.restrict I).prod α,(p.1,G p.2 p.1)∉N := by
    apply (ae_prod_iff_ae_ae ((hN.preimage
      (measurable_fst.prodMk (hG.comp measurable_swap))).compl)).mpr
    exact hGEN
  have hrev : ∀ᵐ a ∂α,∀ᵐ x ∂volume.restrict I,(x,G a x)∉N := by
    exact ae_ae_of_ae_prod ((measurePreserving_swap (μ := α) (ν := volume.restrict I)).quasiMeasurePreserving.ae hprod)
  have hout : ∀ᵐ a ∂α,∀ᵐ b ∂β,π (a,b)∉N := by
    filter_upwards [hrev] with a ha
    filter_upwards [(hcurved a).ae ha] with b hb
    simpa only [←hgraph (a,b),Prod.mk.eta] using hb
  have hall := (ae_prod_iff_ae_ae ((hN.preimage hπ).compl)).mpr hout
  simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hall

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
attribute [local instance] Measure.Subtype.measureSpace

theorem compact_graph_product_nonsingular {K : Set (ℝ×ℝ)} (hK : IsCompact K)
    [SFinite (volume : Measure K)]
    (G U : K → ℝ → ℝ)
    (hG : Continuous (fun p : K×ℝ => G p.1 p.2))
    (hU : Continuous (fun p : K×ℝ => U p.1 p.2))
    (hsG : ∀ a s t,|G a s-G a t|≤(1/2)*|s-t|)
    (hsU : ∀ a s t,|U a s-U a t|≤(1/2)*|s-t|)
    {I J : Set ℝ} (hI : MeasurableSet I)
    (hIc : ∀ a : K,(a : ℝ×ℝ).1∈I) (hJc : ∀ a : K,(a : ℝ×ℝ).2∈J)
    (hcentreG : ∀ a : K,G a (a : ℝ×ℝ).1=(a : ℝ×ℝ).2)
    (hcentreU : ∀ a : K,U a (a : ℝ×ℝ).2=(a : ℝ×ℝ).1)
    {C : ℝ} (hC : 0≤C) (hGcontrol : AffineGraphControl G I C) (hUcontrol : AffineGraphControl U J C)
    (π : K×K → ℝ×ℝ) (hπ : Continuous π)
    (hπG : ∀ p,(π p).2=G p.1 (π p).1) (hπU : ∀ p,(π p).1=U p.2 (π p).2)
    (hπI : ∀ p,(π p).1∈I) (hπJ : ∀ p,(π p).2∈J) :
    QuasiMeasurePreserving π ((volume : Measure K).prod volume) (volume : Measure (ℝ×ℝ)) := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have haff (x : ℝ) (hx : x∈I) : QuasiMeasurePreserving (fun a => G a x) (volume : Measure K) volume := by
    apply label_nonsingular_of_vertical_inverse hK.measurableSet _
      (hG.comp (continuous_id.prodMk continuous_const)).measurable hIc
    intro c hc
    obtain ⟨H,hH,hHval,hHbound⟩ := hGcontrol x hx c hc
    refine ⟨H,?_,fun Z hZ hZ0 => null_image_of_pointwise_local_bound hC hHbound hZ hZ0⟩
    intro a he
    change H (G a x)=(a : ℝ×ℝ).2
    rw [hHval,←he,hcentreG]
  have hcurved (a : K) : QuasiMeasurePreserving (fun b => (π (a,b)).1)
      (volume : Measure K) (volume.restrict I) := by
    have hbase : QuasiMeasurePreserving (fun b => (π (a,b)).1) (volume : Measure K) volume := by
      apply label_nonsingular_of_horizontal_inverse hK.measurableSet _
        (continuous_fst.comp (hπ.comp (continuous_const.prodMk continuous_id))).measurable hJc
      intro c hc
      obtain ⟨H,hH,hHval,hHbound⟩ := compact_curved_inverse_control hU hC (by norm_num : (0:ℝ)≤1/2)
        (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)*(1/2)<1) hsU hUcontrol
        (G a) (hsG a) (fun b => (π (a,b)).1)
        (continuous_fst.comp (hπ.comp (continuous_const.prodMk continuous_id)))
        (fun b => by rw [←hπG (a,b)]; exact hπU (a,b))
        (fun b => by rw [←hπG (a,b)]; exact hπJ (a,b)) hc
      refine ⟨H,?_,fun Z hZ hZ0 => null_image_of_pointwise_local_bound (by positivity) hHbound hZ hZ0⟩
      intro b he
      change H (π (a,b)).1=(b : ℝ×ℝ).1
      rw [hHval,←he,hcentreU]
    simpa only [Measure.restrict_univ] using hbase.restrict
      (s := univ) (t := I) (fun b _ => hπI (a,b))
  exact rectangle_quasiMeasurePreserving volume volume hI G hG.measurable π hπ.measurable hπG haff hcurved

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology
open NonlinearStable

theorem compact_graph_rectangle {A B : Type*}
    [TopologicalSpace A] [CompactSpace A] [T2Space A]
    [TopologicalSpace B] [CompactSpace B] [T2Space B]
    (G : A → ℝ → ℝ) (U : B → ℝ → ℝ)
    (hG : Continuous (fun p : A×ℝ => G p.1 p.2))
    (hU : Continuous (fun p : B×ℝ => U p.1 p.2))
    (hsG : ∀ a s t,|G a s-G a t|≤(1/2)*|s-t|)
    (hsU : ∀ b s t,|U b s-U b t|≤(1/2)*|s-t|)
    {r : ℝ} (hr : 0<r) (hsmall : ∀ a b,|G a (U b 0)|≤r/4) :
    ∃ π : A×B → Plane, Continuous π ∧
      (∀ p, (π p).1=U p.2 (π p).2 ∧ (π p).2=G p.1 (π p).1 ∧ |(π p).2|≤r) ∧
      ∀ p q : A×B, ∀ z : Plane,
        z.1=U p.2 z.2 → z.2=G q.1 z.1 → z=π (q.1,p.2) := by
  let F (p : A×B) (s : ℝ) : Plane := (s-G p.1 (U p.2 s),0)
  have hFc : Continuous (fun p : (A×B)×Icc (-r) r => F p.1 p.2) := by
    apply Continuous.prodMk _ continuous_const
    exact (continuous_subtype_val.comp continuous_snd).sub
      (hG.comp ((continuous_fst.comp continuous_fst).prodMk
        (hU.comp ((continuous_snd.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)))))
  have herr (p : A×B) (s t : ℝ) : |(F p s).1-(F p t).1-(s-t)|≤(1/4)*|s-t| := by
    have he : (F p s).1-(F p t).1-(s-t)=G p.1 (U p.2 t)-G p.1 (U p.2 s) := by dsimp only [F]; ring
    rw [he,abs_sub_comm]
    exact ((hsG p.1 _ _).trans (mul_le_mul_of_nonneg_left (hsU p.2 s t) (by norm_num))).trans_eq (by ring)
  obtain ⟨σ,hσ,hσval⟩ := compact_graph_crossing r hr F hFc herr (fun p => by
    simpa only [F,zero_sub,abs_neg] using hsmall p.1 p.2)
  let z₀ : Icc (-r/2) (r/2) := ⟨0,by constructor <;> linarith⟩
  let t : A×B → ℝ := fun p => σ (p,z₀)
  have ht : Continuous t := continuous_subtype_val.comp (hσ.comp (continuous_id.prodMk continuous_const))
  have he (p : A×B) : t p=G p.1 (U p.2 (t p)) := by
    have hh := hσval (p,z₀)
    change t p-G p.1 (U p.2 (t p))=0 at hh
    exact sub_eq_zero.mp hh
  refine ⟨(fun p => (U p.2 (t p),t p)),(hU.comp (continuous_snd.prodMk ht)).prodMk ht,?_,?_⟩
  · intro p
    exact ⟨rfl,he p,abs_le.mpr (σ (p,z₀)).property⟩
  · intro p q z hzU hzG
    have hm := strictMono_of_linear_error (by norm_num : (1/4 : ℝ)<1) (herr (q.1,p.2))
    have hzero : (F (q.1,p.2) z.2).1=0 := by
      change z.2-G q.1 (U p.2 z.2)=0
      rw [←hzU,←hzG,sub_self]
    have hz : z.2=t (q.1,p.2) := hm.injective (hzero.trans (by
      change 0=t (q.1,p.2)-G q.1 (U p.2 (t (q.1,p.2)))
      exact (sub_eq_zero.mpr (he (q.1,p.2))).symm))
    exact Prod.ext (hzU.trans (congrArg (U p.2) hz)) hz

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable
attribute [local instance] Measure.Subtype.measureSpace

structure ReversibleGraphRectangle {k χ : ℝ} {B : ReversibleRectangleBlock k χ} (F : ReversibleGraphFamilies B) where
  point : B.coordinateCarrier×B.coordinateCarrier → RealPlane
  continuous : Continuous point
  nonsingular : QuasiMeasurePreserving point ((volume : Measure B.coordinateCarrier).prod volume) volume
  stable : ∀ p,(point p).2=F.G (B.label p.1) (point p).1
  unstable : ∀ p,(point p).1=F.U (B.label p.2) (point p).2
  x_bound : ∀ p,|(point p).1|≤B.ρ
  y_bound : ∀ p,|(point p).2|≤B.ρ

theorem reversible_graph_rectangle {k χ : ℝ} {B : ReversibleRectangleBlock k χ}
    (F : ReversibleGraphFamilies B) (hk : 0≤k) : Nonempty (ReversibleGraphRectangle F) := by
  let _ : CompactSpace B.coordinateCarrier := isCompact_iff_compactSpace.mp B.compact_coordinateCarrier
  let _ : IsFiniteMeasure (volume : Measure B.coordinateCarrier) := B.finite_coordinate_volume
  let G (a : B.coordinateCarrier) (s : ℝ) := F.G (B.label a) s
  let U (a : B.coordinateCarrier) (s : ℝ) := F.U (B.label a) s
  have hG : Continuous (fun p : B.coordinateCarrier×ℝ => G p.1 p.2) :=
    F.continuous_G.comp ((B.continuous_label.comp continuous_fst).prodMk continuous_snd)
  have hU : Continuous (fun p : B.coordinateCarrier×ℝ => U p.1 p.2) :=
    F.continuous_U.comp ((B.continuous_label.comp continuous_fst).prodMk continuous_snd)
  have hx (a : B.coordinateCarrier) : |(a : RealPlane).1|≤B.ρ/100 := by
    have hh := (norm_fst_le (B.coordinates (B.label a))).trans (B.central (B.label a) (B.label a).property)
    simpa only [B.coordinates_label,Real.norm_eq_abs] using hh
  have hy (a : B.coordinateCarrier) : |(a : RealPlane).2|≤B.ρ/100 := by
    have hh := (norm_snd_le (B.coordinates (B.label a))).trans (B.central (B.label a) (B.label a).property)
    simpa only [B.coordinates_label,Real.norm_eq_abs] using hh
  have hGc (a : B.coordinateCarrier) : G a (a : RealPlane).1=(a : RealPlane).2 := by
    simpa only [B.coordinates_label] using F.G_centre (B.label a)
  have hUc (a : B.coordinateCarrier) : U a (a : RealPlane).2=(a : RealPlane).1 := by
    simpa only [B.coordinates_label] using F.U_centre (B.label a)
  have hG0 (a : B.coordinateCarrier) : |G a 0|≤3*B.ρ/200 := by
    have hh := F.slope_G (B.label a) 0 (a : RealPlane).1
    change |G a 0-G a (a : RealPlane).1|≤_ at hh
    rw [hGc,zero_sub,abs_neg] at hh
    have htri := abs_sub_le (G a 0) (a : RealPlane).2 0
    simp only [sub_zero] at htri
    nlinarith [hx a,hy a]
  have hU0 (a : B.coordinateCarrier) : |U a 0|≤3*B.ρ/200 := by
    have hh := F.slope_U (B.label a) 0 (a : RealPlane).2
    change |U a 0-U a (a : RealPlane).2|≤_ at hh
    rw [hUc,zero_sub,abs_neg] at hh
    have htri := abs_sub_le (U a 0) (a : RealPlane).1 0
    simp only [sub_zero] at htri
    nlinarith [hx a,hy a]
  have hsmall (a b : B.coordinateCarrier) : |G a (U b 0)|≤B.ρ/4 := by
    have hh := F.slope_G (B.label a) (U b 0) 0
    change |G a (U b 0)-G a 0|≤_ at hh
    simp only [sub_zero] at hh
    have htri := abs_sub_le (G a (U b 0)) (G a 0) 0
    simp only [sub_zero] at htri
    nlinarith [hG0 a,hU0 b,B.ρ_pos]
  obtain ⟨π,hπ,hgraph,hunique⟩ := compact_graph_rectangle G U hG hU
    (fun a => F.slope_G (B.label a)) (fun a => F.slope_U (B.label a)) B.ρ_pos hsmall
  have hπx (p : B.coordinateCarrier×B.coordinateCarrier) : |(π p).1|≤B.ρ := by
    rw [(hgraph p).1]
    have hh := F.slope_U (B.label p.2) (π p).2 0
    change |U p.2 (π p).2-U p.2 0|≤_ at hh
    simp only [sub_zero] at hh
    have htri := abs_sub_le (U p.2 (π p).2) (U p.2 0) 0
    simp only [sub_zero] at htri
    nlinarith [(hgraph p).2.2,hU0 p.2,B.ρ_pos]
  have hπI (p : B.coordinateCarrier×B.coordinateCarrier) : (π p).1∈B.stableInterval :=
    B.mem_stableInterval.mpr ((hπx p).trans (by linarith [B.ρ_small,B.r_pos]))
  have hπJ (p : B.coordinateCarrier×B.coordinateCarrier) : (π p).2∈B.unstableInterval :=
    B.mem_unstableInterval.mpr ((hgraph p).2.2.trans (by linarith [B.ρ_reverse,B.ρ_pos]))
  have hNS := compact_graph_product_nonsingular B.compact_coordinateCarrier G U hG hU
    (fun a => F.slope_G (B.label a)) (fun a => F.slope_U (B.label a))
    (I := B.stableInterval) (J := B.unstableInterval) measurableSet_Icc
    (fun a => B.mem_stableInterval.mpr ((hx a).trans (by linarith [B.ρ_small,B.ρ_pos])))
    (fun a => B.mem_unstableInterval.mpr ((hy a).trans (by linarith [B.ρ_reverse,B.ρ_pos])))
    hGc hUc B.holonomyConstant_pos.le ((F.stable_control hk).comp B.label) ((F.unstable_control hk).comp B.label)
    π hπ (fun p => (hgraph p).2.1) (fun p => (hgraph p).1) hπI hπJ
  exact ⟨⟨π,hπ,hNS,fun p => (hgraph p).2.1,fun p => (hgraph p).1,hπx,fun p => (hgraph p).2.2⟩⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal

theorem complexProjection_quasiMeasurePreserving : QuasiMeasurePreserving complexProjection volume area := by
  refine ⟨continuous_complexProjection.measurable,AbsolutelyContinuous.mk fun N hN hNz => ?_⟩
  rw [Measure.map_apply continuous_complexProjection.measurable hN]
  let C (m n : ℤ) : Set ℂ := {z | z.re∈Ico (m : ℝ) ((m : ℝ)+1) ∧ z.im∈Ico (n : ℝ) ((n : ℝ)+1)}
  have hmp (m n : ℤ) : MeasurePreserving complexProjection (volume.restrict (C m n)) area := by
    have hp := (AddCircle.measurePreserving_mk (1 : ℝ) (m : ℝ)).prod (AddCircle.measurePreserving_mk (1 : ℝ) (n : ℝ))
    simp only [←restrict_Ico_eq_restrict_Ioc,Measure.prod_restrict] at hp
    have hc := Complex.volume_preserving_equiv_real_prod.restrict_preimage
      (measurableSet_Ico.prod measurableSet_Ico : MeasurableSet
        (Ico (m : ℝ) ((m : ℝ)+1) ×ˢ Ico (n : ℝ) ((n : ℝ)+1)))
    exact hp.comp hc
  have hz (m n : ℤ) : volume (complexProjection ⁻¹' N∩C m n)=0 := by
    have hh := (hmp m n).measure_preimage hN.nullMeasurableSet
    rw [Measure.restrict_apply (hN.preimage continuous_complexProjection.measurable),hNz] at hh
    exact hh
  apply measure_mono_null (t := ⋃ m : ℤ,⋃ n : ℤ,complexProjection ⁻¹' N∩C m n) _
    (measure_iUnion_null fun m => measure_iUnion_null fun n => hz m n)
  intro z hzN
  exact mem_iUnion.mpr ⟨⌊z.re⌋,mem_iUnion.mpr ⟨⌊z.im⌋,hzN,
    ⟨Int.floor_le _,Int.lt_floor_add_one _⟩,⟨Int.floor_le _,Int.lt_floor_add_one _⟩⟩⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology
open NonlinearStable

theorem fineStableCurve_contracting_tangent (k χ ε δ : ℝ) (hδ : 0<δ)
    (hq : Real.exp (-χ+ε)+δ<1) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s : ℝ} (hs : |s|<1) :
    ∃ v : ℂ,v≠0 ∧ ∀ n : ℕ,
      ‖standardDerivativeProduct k (complexProjection (fineStableCurve k χ ε δ hδ hq w hw s)) n v‖≤
        (2*fineScale k ε δ)*(Real.exp (-χ+ε)+δ)^n := by
  let f := fineStableCurve k χ ε δ hδ hq w hw
  have hsI : Ioo (-1 : ℝ) 1∈𝓝 s := isOpen_Ioo.mem_nhds (abs_lt.mp hs)
  have hf : DifferentiableAt ℝ f s :=
    (fineStableCurve_contDiffOn k χ ε δ hδ hq w hw).differentiableOn (by norm_num) |>.differentiableAt hsI
  let I := fineInverse k χ ε δ (complexProjection w)
  let L := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp I
  have he : (fun t : ℝ => L (f t-w))=id := by
    funext t
    change (I (w+fineFrame k χ ε δ (complexProjection w) (t,fineStableGraph k χ ε δ hδ hq w hw t)-w)).1=t
    rw [add_sub_cancel_left]
    dsimp [I]
    rw [fineInverse_frame k χ ε hδ _ (by simpa using (hw 0).1)]
  have hder := L.hasFDerivAt.comp_hasDerivAt s (hf.hasDerivAt.sub_const w)
  have hfirst : L (deriv f s)=1 := by
    have hder' : HasDerivAt (fun t : ℝ => L (f t-w)) (L (deriv f s)) s := hder
    rw [he] at hder'
    exact hder'.unique (hasDerivAt_id s)
  refine ⟨deriv f s,?_,?_⟩
  · intro hz
    rw [hz,map_zero] at hfirst
    norm_num at hfirst
  · intro n
    have hd := (hasFDerivAt_standardLift_iterate k n (f s)).comp_hasDerivAt s hf.hasDerivAt
    apply hd.le_of_lip' (by positivity [fineScale_pos k ε hδ])
    filter_upwards [hsI] with t ht
    exact fineStableCurve_contraction k χ ε δ hδ hq w hw (abs_lt.mpr ht).le hs.le n

lemma vectorGrowth_le_log_of_bound (k : ℝ) (z : Torus) {v : ℂ} {l C q : ℝ}
    (hg : VectorGrowth k z v l) (hC : 0<C) (hq : 0<q)
    (hb : ∀ n : ℕ,‖standardDerivativeProduct k z n v‖≤C*q^n) : l≤Real.log q := by
  have ht : Tendsto (fun n : ℕ => Real.log C/(n : ℝ)+Real.log q) atTop (𝓝 (Real.log q)) := by
    simpa only [zero_add] using
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => Real.log C/(n : ℝ)) atTop (𝓝 0)).add_const (Real.log q)
  apply le_of_tendsto_of_tendsto hg.2 ht
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ)<n := by exact_mod_cast hn
  have hp : 0<‖standardDerivativeProduct k z n v‖ :=
    PlaneLyapunov.image_norm_pos _ (standardDerivativeProduct_area k z) hg.1 n
  have hh := Real.log_le_log hp (hb n)
  rw [Real.log_mul hC.ne' (pow_pos hq n).ne',Real.log_pow] at hh
  exact (div_le_div_of_nonneg_right hh hn'.le).trans_eq (by field_simp)

theorem fineStableCurve_spectrum_positive (k χ ε δ : ℝ) (hδ : 0<δ)
    (hq : Real.exp (-χ+ε)+δ<1) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w)))
    {s l : ℝ} (hs : |s|<1)
    (hl : LyapunovSpectrumAt k (complexProjection (fineStableCurve k χ ε δ hδ hq w hw s)) l) : 0<l := by
  rcases hl.2 with ⟨he,hzero⟩|⟨hpos,_⟩
  · obtain ⟨v,hv,hbound⟩ := fineStableCurve_contracting_tangent k χ ε δ hδ hq w hw hs
    have hh := vectorGrowth_le_log_of_bound k _ (hzero v hv) (by positivity [fineScale_pos k ε hδ])
      (show 0<Real.exp (-χ+ε)+δ by positivity) hbound
    have hneg : Real.log (Real.exp (-χ+ε)+δ)<0 := Real.log_neg (by positivity) hq
    linarith
  · exact hpos

end StandardMapEntropy

end
section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace BoundedSubadditive
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

theorem continuous_birkhoff_limit {μ : Measure X} [IsFiniteMeasure μ]
    {T S : X → X} (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S μ μ)
    (hST : ∀ x,S (T x)=x) (hTS : ∀ x,T (S x)=x) (f : C(X,ℝ)) :
    ∃ F : X → ℝ, Measurable F ∧ (∀ x,F (T x)=F x) ∧
      (∀ᵐ x ∂μ,
        Tendsto (fun n : ℕ => birkhoffSum T f n x/(n : ℝ)) atTop (𝓝 (F x)) ∧
        Tendsto (fun n : ℕ => birkhoffSum S f n x/(n : ℝ)) atTop (𝓝 (F x))) ∧
      ∀ A : Set X, MeasurableSet A → T ⁻¹' A=A → ∫ x in A,F x ∂μ=∫ x in A,f x ∂μ := by
  let C := ‖f‖
  let d := 2*C+1
  have hC : 0≤C := norm_nonneg f
  have hd : 0<d := by dsimp only [d]; positivity
  let g : X → ℝ := fun x => (f x+C)/d
  have hg : Measurable g := (f.continuous.measurable.add_const C).div_const d
  have hbound (x : X) : |f x|≤C := f.norm_coe_le_norm x
  have h0 (x : X) : 0≤g x := div_nonneg (by linarith [(abs_le.mp (hbound x)).1]) hd.le
  have h1 (x : X) : g x≤1 := by
    apply (div_le_one hd).mpr
    dsimp only [d]
    linarith [(abs_le.mp (hbound x)).2]
  obtain ⟨G,hGm,hGb,hGT,hGconv⟩ := forward_backward_birkhoff hT hS hST hTS hg h0 h1
  obtain ⟨H,hHm,hHb,hHT,hHconv,hHint⟩ := exists_bounded_birkhoff_limit hT hg h0 h1
  have hGH : G=ᵐ[μ] H := by
    filter_upwards [hGconv,hHconv] with x hx hy
    exact tendsto_nhds_unique hx.1 hy
  let F : X → ℝ := fun x => d*G x-C
  have hFi : Integrable F μ := by
    apply (integrable_const (d+C)).mono' ((measurable_const.mul hGm).sub_const C).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change |d*G x-C|≤d+C
    rw [abs_le]
    constructor <;> nlinarith [(hGb x).1,(hGb x).2]
  have hconv {U : X → X} {x : X}
      (hu : Tendsto (fun n : ℕ => birkhoffSum U g n x/(n : ℝ)) atTop (𝓝 (G x))) :
      Tendsto (fun n : ℕ => birkhoffSum U f n x/(n : ℝ)) atTop (𝓝 (F x)) := by
    apply ((hu.const_mul d).sub_const C).congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (n : ℝ)≠0 := by exact_mod_cast hn
    have he : birkhoffSum U g n x=(birkhoffSum U f n x+(n : ℝ)*C)/d := by
      simp only [birkhoffSum,g]
      rw [←Finset.sum_div,Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [he]
    field_simp
    ring
  refine ⟨F,(measurable_const.mul hGm).sub_const C,fun x => by simp only [F,hGT],?_,?_⟩
  · exact hGconv.mono fun x hx => ⟨hconv hx.1,hconv hx.2⟩
  · intro A hA hTA
    have hHi : Integrable H μ := (integrable_const (1 : ℝ)).mono' hHm.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hHb x).1]; exact (hHb x).2)
    have hf : Integrable (fun x => f x) μ := (integrable_const C).mono' f.continuous.measurable.aestronglyMeasurable
      (Eventually.of_forall hbound)
    have he : (fun x => F x)=ᵐ[μ.restrict A] (fun x => d*H x-C) :=
      (ae_restrict_of_ae hGH).mono fun x hx => by simp only [F,hx]
    rw [integral_congr_ae he,integral_sub (hHi.const_mul d).integrableOn (integrable_const C),
      integral_const_mul,hHint A hA hTA]
    have hge : (∫ x in A,g x ∂μ)=((∫ x in A,f x ∂μ)+(∫ x in A,C ∂μ))/d := by
      dsimp only [g]
      rw [integral_div,integral_add hf.integrableOn (integrable_const C)]
    rw [hge]
    field_simp
    ring

end BoundedSubadditive

end
section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoundedSubadditive
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

structure ContinuousBirkhoffCode (T S : X → X) (μ : Measure X) where
  observation : ℕ → C(X,ℝ)
  dense : DenseRange observation
  value : X → ℕ → ℝ
  measurable : Measurable value
  invariant : ∀ x,value (T x)=value x
  generic : ∀ᵐ x ∂μ,∀ j : ℕ,
    Tendsto (fun n : ℕ => birkhoffSum T (observation j) n x/(n : ℝ)) atTop (𝓝 (value x j)) ∧
    Tendsto (fun n : ℕ => birkhoffSum S (observation j) n x/(n : ℝ)) atTop (𝓝 (value x j))
  integral : ∀ (A : Set X), MeasurableSet A → T ⁻¹' A=A → ∀ j : ℕ,
    ∫ x in A,value x j ∂μ=∫ x in A,observation j x ∂μ

theorem exists_continuousBirkhoffCode {μ : Measure X} [IsFiniteMeasure μ]
    {T S : X → X} (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S μ μ)
    (hST : ∀ x,S (T x)=x) (hTS : ∀ x,T (S x)=x) :
    Nonempty (ContinuousBirkhoffCode T S μ) := by
  obtain ⟨f,hf⟩ := TopologicalSpace.exists_dense_seq C(X,ℝ)
  choose F hFm hFT hFconv hFint using fun j => continuous_birkhoff_limit hT hS hST hTS (f j)
  exact ⟨{
    observation := f, dense := hf, value := fun x j => F j x,
    measurable := Measurable.of_eval hFm,
    invariant := fun x => funext fun j => hFT j x,
    generic := ae_all_iff.mpr hFconv,
    integral := fun A hA hTA j => hFint j A hA hTA }⟩

lemma continuousMap_integrable (μ : Measure X) [IsFiniteMeasure μ] (f : C(X,ℝ)) : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

lemma continuous_integral_continuousMap (μ : Measure X) [IsFiniteMeasure μ] :
    Continuous (fun f : C(X,ℝ) => ∫ x,f x ∂μ) := by
  apply (LipschitzWith.of_dist_le_mul (K := ⟨μ.real univ,ENNReal.toReal_nonneg⟩) ?_).continuous
  intro f g
  rw [dist_eq_norm,←integral_sub (continuousMap_integrable μ f) (continuousMap_integrable μ g),dist_eq_norm]
  exact (norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => (f-g).norm_coe_le_norm x)).trans_eq (mul_comm _ _)

lemma measure_eq_of_dense_continuous_integrals {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : ℕ → C(X,ℝ)} (hf : DenseRange f)
    (he : ∀ j,∫ x,f j x ∂μ=∫ x,f j x ∂ν) : μ=ν := by
  have hfun := hf.equalizer (continuous_integral_continuousMap μ) (continuous_integral_continuousMap ν) (funext he)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  exact congrFun hfun g.toContinuousMap

end BoundedSubadditive

end
end

end OAI
