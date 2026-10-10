import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Components.BoundedBirkhoff

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fine_plaque_second_bound (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w v : ℂ) (hv : ∀ n : ℕ,FineRegular k χ ε (complexProjection ((standardLift k)^[n] v)))
    {η τ : ℝ} (hη : 0≤η)
    (hclose : ‖(fineInverse k χ ε δ (complexProjection w)).comp
      (fineFrame k χ ε δ (complexProjection v))-ContinuousLinearMap.id ℝ Plane‖≤η)
    (hslope : Real.exp (-χ+ε)*δ/(1-Real.exp (-χ+ε))≤τ) (s t : ℝ) :
    |(finePlaqueInChart k χ ε δ hδ hq w v hv s).2-
      (finePlaqueInChart k χ ε δ hδ hq w v hv t).2|≤(τ+η)*|s-t| := by
  let I := fineInverse k χ ε δ (complexProjection w)
  let F := fineFrame k χ ε δ (complexProjection v)
  let g := fineStableGraph k χ ε δ hδ hq v hv
  let u : Plane := (s,g s)-(t,g t)
  have he : (finePlaqueInChart k χ ε δ hδ hq w v hv s).2-
      (finePlaqueInChart k χ ε δ hδ hq w v hv t).2=
      (((I.comp F)-ContinuousLinearMap.id ℝ Plane) u).2+(g s-g t) := by
    change (I (v+F (s,g s)-w)).2-(I (v+F (t,g t)-w)).2=_
    simp only [map_sub,map_add,Prod.snd_add,Prod.snd_sub,sub_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,u]
    ring
  rw [he]
  have herr : |(((I.comp F)-ContinuousLinearMap.id ℝ Plane) u).2|≤η*|s-t| :=
    (norm_snd_le _).trans ((ContinuousLinearMap.le_opNorm _ _).trans
      ((mul_le_mul_of_nonneg_right hclose (norm_nonneg u)).trans
        (mul_le_mul_of_nonneg_left (fine_graph_pair_bound k χ ε δ hδ hq v hv s t) hη)))
  have hg : |g s-g t|≤τ*|s-t| := (fineStableGraph_slope k χ ε δ hδ hq v hv s t).trans
    (mul_le_mul_of_nonneg_right hslope (abs_nonneg _))
  exact (abs_add_le _ _).trans ((add_le_add herr hg).trans_eq (by ring))

theorem fine_compact_chart_graph {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (v : X → ℂ) (hvc : Continuous v)
    (hv : ∀ x,∀ n : ℕ,FineRegular k χ ε (complexProjection ((standardLift k)^[n] (v x))))
    (hdata : ∀ n : ℕ,Continuous (fun x => lyapunovChartData k χ ε
      (complexProjection ((standardLift k)^[n] (v x)))))
    {r η τ : ℝ} (hr : 0<r) (hr1 : r≤1) (hη : 0≤η) (hη' : η≤1/4) (hτ : 0≤τ)
    (hclose : ∀ x,‖(fineInverse k χ ε δ (complexProjection w)).comp
      (fineFrame k χ ε δ (complexProjection (v x)))-ContinuousLinearMap.id ℝ Plane‖≤η)
    (hslope : Real.exp (-χ+ε)*δ/(1-Real.exp (-χ+ε))≤τ)
    (hcentre : ∀ x,|(fineInverse k χ ε δ (complexProjection w) (v x-w)).1|≤r/4) :
    ∃ (G σ : X → ℝ → ℝ),
      Continuous (fun p : X×ℝ => G p.1 p.2) ∧ Continuous (fun p : X×ℝ => σ p.1 p.2) ∧
      (∀ x s t,|G x s-G x t|≤((4/3)*(τ+η))*|s-t|) ∧
      (∀ x s,|σ x s|≤r) ∧
      (∀ x s,s∈Icc (-r/2) (r/2) →
        finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) (σ x s)=(s,G x s)) ∧
      (∀ x,σ x ((fineInverse k χ ε δ (complexProjection w) (v x-w)).1)=0 ∧
        G x ((fineInverse k χ ε δ (complexProjection w) (v x-w)).1)=
          (fineInverse k χ ε δ (complexProjection w) (v x-w)).2) := by
  obtain ⟨s,hs,hsval⟩ := fine_compact_graph_crossing k χ ε δ hδ hq w v hvc hv hdata hr hr1
    (fun x => (hclose x).trans hη') hcentre
  let c : ℝ → Icc (-r/2) (r/2) := projIcc (-r/2) (r/2) (by linarith)
  let σ (x : X) (t : ℝ) : ℝ := s (x,c t)
  let G (x : X) (t : ℝ) := (finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) (σ x t)).2
  have hσ : Continuous (fun p : X×ℝ => σ p.1 p.2) :=
    continuous_subtype_val.comp (hs.comp (continuous_fst.prodMk (continuous_projIcc.comp continuous_snd)))
  have hσbound (x : X) (t : ℝ) : |σ x t|≤r := abs_le.mpr (s (x,c t)).property
  have hG : Continuous (fun p : X×ℝ => G p.1 p.2) := by
    let param : X×ℝ → Icc (-1 : ℝ) 1 := fun p => ⟨σ p.1 p.2,abs_le.mp ((hσbound _ _).trans hr1)⟩
    have hparam : Continuous param := hσ.subtype_mk _
    have hc := continuous_fineStableCurve_family k χ ε δ hδ hq v hvc hv hdata
    exact continuous_snd.comp ((fineInverse k χ ε δ (complexProjection w)).continuous.comp
      ((hc.comp (continuous_fst.prodMk hparam)).sub continuous_const))
  have hσval (x : X) (t : ℝ) :
      (finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) (σ x t)).1=(c t : ℝ) := hsval (x,c t)
  have hpoint (x : X) (t : ℝ) (ht : t∈Icc (-r/2) (r/2)) :
      finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) (σ x t)=(t,G x t) := by
    refine Prod.ext ?_ rfl
    exact (hσval x t).trans (by dsimp only [c]; rw [projIcc_of_mem _ ht])
  refine ⟨G,σ,hG,hσ,?_,hσbound,hpoint,?_⟩
  · intro x a b
    have hvab := fine_plaque_linear_error k χ ε δ hδ hq w (v x) (hv x)
      ((hclose x).trans hη') (σ x a) (σ x b)
    rw [hσval,hσval] at hvab
    have hd : |σ x a-σ x b|≤(4/3)*|(c a : ℝ)-(c b : ℝ)| := by
      have hex : σ x a-σ x b=((c a : ℝ)-(c b : ℝ))-
          ((c a : ℝ)-(c b : ℝ)-(σ x a-σ x b)) := by ring
      have hh := abs_sub ((c a : ℝ)-(c b : ℝ)) ((c a : ℝ)-(c b : ℝ)-(σ x a-σ x b))
      rw [←hex] at hh
      linarith
    have hg := fine_plaque_second_bound k χ ε δ hδ hq w (v x) (hv x) hη (hclose x) hslope (σ x a) (σ x b)
    apply hg.trans
    calc
      (τ+η)*|σ x a-σ x b|≤(τ+η)*((4/3)*|(c a : ℝ)-(c b : ℝ)|) := mul_le_mul_of_nonneg_left hd (add_nonneg hτ hη)
      _ ≤ (τ+η)*((4/3)*|a-b|) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (abs_projIcc_sub_projIcc _) (by norm_num)) (add_nonneg hτ hη)
      _ = (4/3)*(τ+η)*|a-b| := by ring
  · intro x
    let t := (fineInverse k χ ε δ (complexProjection w) (v x-w)).1
    have ht : t∈Icc (-r/2) (r/2) := by have := abs_le.mp (hcentre x); constructor <;> linarith
    have hp := hpoint x t ht
    have hzero : finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) 0=
        fineInverse k χ ε δ (complexProjection w) (v x-w) := by rw [finePlaqueInChart,fineStableCurve_zero]
    have hz : σ x t=0 := fine_plaque_crossing_unique k χ ε δ hδ hq w (v x) (hv x)
      ((hclose x).trans hη') ((congrArg Prod.fst hp).trans (by change t=(finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) 0).1; rw [hzero]))
    refine ⟨hz,?_⟩
    change (finePlaqueInChart k χ ε δ hδ hq w (v x) (hv x) (σ x t)).2=_
    rw [hz,hzero]

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable

lemma shrink_fine_holonomy_delta {χ ε δ₀ τ : ℝ} (hδ₀ : 0<δ₀) (hδ₀' : δ₀≤1/2)
    (hq₀ : Real.exp (-χ+ε)+δ₀<1)
    (hslow₀ : Real.exp (4*ε)*(Real.exp (-χ+ε)+δ₀)<1) (hτ : 0<τ) :
    ∃ δ : ℝ,0<δ ∧ δ≤1/2 ∧ Real.exp (-χ+ε)+δ<1 ∧
      Real.exp (4*ε)*(Real.exp (-χ+ε)+δ)<1 ∧
      Real.exp (-χ+ε)*δ/(1-Real.exp (-χ+ε))≤τ := by
  let ℓ := Real.exp (-χ+ε)
  have hℓ : 0<ℓ := Real.exp_pos _
  have hℓ1 : ℓ<1 := by dsimp only [ℓ]; linarith
  let δ := min δ₀ (τ*(1-ℓ)/ℓ)
  have hδ : 0<δ := lt_min hδ₀ (div_pos (mul_pos hτ (sub_pos.mpr hℓ1)) hℓ)
  have hd : δ≤δ₀ := min_le_left _ _
  refine ⟨δ,hδ,hd.trans hδ₀',by dsimp only [ℓ] at *; linarith,?_,?_⟩
  · nlinarith [Real.exp_pos (4*ε)]
  · apply (div_le_iff₀ (sub_pos.mpr hℓ1)).mpr
    have h := (le_div_iff₀ hℓ).mp (show δ≤τ*(1-ℓ)/ℓ from min_le_right _ _)
    nlinarith

lemma small_chart_radius (S R : ℝ) (hS : 0≤S) (hR : 0<R) :
    ∃ r : ℝ,0<r ∧ r≤1/12 ∧ (4*S*r)/(100*R)+r≤1 := by
  let a := (4*S)/(100*R)
  have ha : 0≤a := by dsimp [a]; positivity
  let r := 1/(24*(1+a))
  have hr : 0<r := by dsimp [r]; positivity
  refine ⟨r,hr,?_,?_⟩
  · dsimp only [r]
    apply (div_le_iff₀ (by positivity : 0<24*(1+a))).mpr
    nlinarith
  · have he : (4*S*r)/(100*R)+r=r*(1+a) := by dsimp only [a]; ring
    rw [he]
    dsimp only [r]
    have : 1+a≠0 := by positivity
    field_simp
    norm_num

structure ReversibleRectangleBlock (k χ : ℝ) where
  ε : ℝ
  δ : ℝ
  ε_pos : 0<ε
  δ_pos : 0<δ
  δ_small : δ≤1/2
  contraction : Real.exp (-χ+ε)+δ<1
  slow : Real.exp (4*ε)*(Real.exp (-χ+ε)+δ)<1
  carrier : Set ℂ
  compact : IsCompact carrier
  positive : 0<volume carrier
  centre : ℂ
  centre_regular : wedge (stableVector k (complexProjection centre)) (unstableVector k (complexProjection centre))≠0
  reverse_regular : wedge (stableVector k (complexProjection (tangentReversal centre)))
    (unstableVector k (complexProjection (tangentReversal centre)))≠0
  α : ℝ
  β : ℝ
  α_ne : α≠0
  β_ne : β≠0
  swap : ∀ p : RealPlane,fineInverse k χ ε δ (complexProjection centre)
    (tangentReversal (fineFrame k χ ε δ (complexProjection (tangentReversal centre)) p))=(β*p.2,α*p.1)
  η : ℝ
  η_pos : 0<η
  η_small : η≤1/16
  slope : Real.exp (-χ+ε)*δ/(1-Real.exp (-χ+ε))≤η
  reverse_slope : (|β|/|α|)*((8/3)*η)≤1/2
  r : ℝ
  r' : ℝ
  R : ℝ
  R' : ℝ
  ρ : ℝ
  r_pos : 0<r
  r'_pos : 0<r'
  R_pos : 0<R
  R'_pos : 0<R'
  ρ_pos : 0<ρ
  r_small : r≤1/12
  r'_small : r'≤1/12
  ρ_small : ρ≤r/8
  ρ_reverse : ρ≤|α| *r'/8
  size : (4*fineScale k ε δ*r)/(100*R)+r≤1
  reverse_size : (4*fineScale k ε δ*r')/(100*R')+r'≤1
  data : ContinuousOn (fun v => (orbitChartData k χ ε (complexProjection v),
    orbitChartData k χ ε (complexProjection (tangentReversal v)))) carrier
  regular : ∀ v∈carrier,∀ n : ℕ,FineRegular k χ ε (complexProjection ((standardLift k)^[n] v))
  reversed : ∀ v∈carrier,∀ n : ℕ,FineRegular k χ ε (complexProjection ((standardLift k)^[n] (tangentReversal v)))
  radius : ∀ v∈carrier,R≤codingRadius k χ ε δ (complexProjection v)
  reverse_radius : ∀ v∈carrier,R'≤codingRadius k χ ε δ (complexProjection (tangentReversal v))
  frames : ∀ v∈carrier,
    ‖(fineInverse k χ ε δ (complexProjection centre)).comp (fineFrame k χ ε δ (complexProjection v))-
      ContinuousLinearMap.id ℝ Plane‖≤η
  reverse_frames : ∀ v∈carrier,
    ‖(fineInverse k χ ε δ (complexProjection (tangentReversal centre))).comp
      (fineFrame k χ ε δ (complexProjection (tangentReversal v)))-ContinuousLinearMap.id ℝ Plane‖≤η
  coframes : ∀ v∈carrier,
    ‖(fineInverse k χ ε δ (complexProjection v)).comp (fineFrame k χ ε δ (complexProjection centre))-
      ContinuousLinearMap.id ℝ Plane‖≤1/4
  reverse_coframes : ∀ v∈carrier,
    ‖(fineInverse k χ ε δ (complexProjection (tangentReversal v))).comp
      (fineFrame k χ ε δ (complexProjection (tangentReversal centre)))-ContinuousLinearMap.id ℝ Plane‖≤1/4
  central : ∀ v∈carrier,‖fineInverse k χ ε δ (complexProjection centre) (v-centre)‖≤ρ/100
  reverse_central : ∀ v∈carrier,
    ‖fineInverse k χ ε δ (complexProjection (tangentReversal centre)) (tangentReversal v-tangentReversal centre)‖≤r'/4

end StandardMapEntropy
end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable

namespace ReversibleRectangleBlock
variable {k χ : ℝ} (B : ReversibleRectangleBlock k χ)

noncomputable def chart (p : RealPlane) : ℂ := B.centre+fineFrame k χ B.ε B.δ (complexProjection B.centre) p
noncomputable def coordinates (v : ℂ) : RealPlane := fineInverse k χ B.ε B.δ (complexProjection B.centre) (v-B.centre)
noncomputable def reverseCoordinates (v : ℂ) : RealPlane :=
  fineInverse k χ B.ε B.δ (complexProjection (tangentReversal B.centre)) (tangentReversal v-tangentReversal B.centre)

@[simp] lemma chart_coordinates (v : ℂ) : B.chart (B.coordinates v)=v := by
  rw [chart,coordinates,fineFrame_inverse k χ B.ε B.δ_pos _ B.centre_regular]
  abel
@[simp] lemma coordinates_chart (p : RealPlane) : B.coordinates (B.chart p)=p := by
  rw [coordinates,chart,add_sub_cancel_left,fineInverse_frame k χ B.ε B.δ_pos _ B.centre_regular]
lemma coordinates_swap (v : ℂ) : B.coordinates v=(B.β*(B.reverseCoordinates v).2,B.α*(B.reverseCoordinates v).1) := by
  have h := B.swap (B.reverseCoordinates v)
  rw [reverseCoordinates,fineFrame_inverse k χ B.ε B.δ_pos _ B.reverse_regular,map_sub,tangentReversal_involutive,
    tangentReversal_involutive] at h
  exact h
lemma continuous_chart : Continuous B.chart := by unfold chart; fun_prop
lemma continuous_coordinates : Continuous B.coordinates := by unfold coordinates; fun_prop
lemma chart_injective : Function.Injective B.chart := by
  intro p q h
  simpa only [coordinates_chart] using congrArg B.coordinates h

end ReversibleRectangleBlock

structure ReversibleGraphFamilies {k χ : ℝ} (B : ReversibleRectangleBlock k χ) where
  G : B.carrier → ℝ → ℝ
  U : B.carrier → ℝ → ℝ
  stableParameter : B.carrier → ℝ → ℝ
  unstableParameter : B.carrier → ℝ → ℝ
  continuous_G : Continuous (fun p : B.carrier×ℝ => G p.1 p.2)
  continuous_U : Continuous (fun p : B.carrier×ℝ => U p.1 p.2)
  continuous_stableParameter : Continuous (fun p : B.carrier×ℝ => stableParameter p.1 p.2)
  continuous_unstableParameter : Continuous (fun p : B.carrier×ℝ => unstableParameter p.1 p.2)
  slope_G : ∀ a s t,|G a s-G a t|≤(1/2)*|s-t|
  slope_U : ∀ a s t,|U a s-U a t|≤(1/2)*|s-t|
  stable_bound : ∀ a s,|stableParameter a s|≤B.r
  unstable_bound : ∀ a s,|unstableParameter a s|≤B.r'
  stable_representation : ∀ a s,|s|≤B.r/2 → B.chart (s,G a s)=
    fineStableCurve k χ B.ε B.δ B.δ_pos B.contraction a (B.regular a a.property) (stableParameter a s)
  unstable_representation : ∀ a s,|s|≤|B.α| * B.r'/2 → B.chart (U a s,s)=
    fineUnstableCurve k χ B.ε B.δ B.δ_pos B.contraction a (B.reversed a a.property) (unstableParameter a s)
  G_centre : ∀ a,G a (B.coordinates a).1=(B.coordinates a).2
  U_centre : ∀ a,U a (B.coordinates a).2=(B.coordinates a).1

theorem reversible_graph_families {k χ : ℝ} (B : ReversibleRectangleBlock k χ) :
    Nonempty (ReversibleGraphFamilies B) := by
  let : CompactSpace B.carrier := isCompact_iff_compactSpace.mp B.compact
  have hd : Continuous (fun v : B.carrier => (orbitChartData k χ B.ε (complexProjection v),
      orbitChartData k χ B.ε (complexProjection (tangentReversal v)))) :=
    continuousOn_iff_continuous_domRestrict.mp B.data
  have hdata (n : ℕ) : Continuous (fun v : B.carrier => lyapunovChartData k χ B.ε
      (complexProjection ((standardLift k)^[n] v))) := by
    simpa only [Function.comp_def,orbitChartData,complexProjection_iterate] using ((continuous_apply n).comp hd.fst).fst
  have hdataR (n : ℕ) : Continuous (fun v : B.carrier => lyapunovChartData k χ B.ε
      (complexProjection ((standardLift k)^[n] (tangentReversal v)))) := by
    simpa only [Function.comp_def,orbitChartData,complexProjection_iterate] using ((continuous_apply n).comp hd.snd).fst
  have hη : B.η≤1/4 := B.η_small.trans (by norm_num)
  have hcent (v : B.carrier) : |(B.coordinates v).1|≤B.r/4 := by
    have hh := (norm_fst_le (B.coordinates v)).trans (B.central v v.property)
    simpa only [Real.norm_eq_abs] using hh.trans (by linarith [B.ρ_small,B.r_pos])
  have hcentR (v : B.carrier) : |(B.reverseCoordinates v).1|≤B.r'/4 :=
    (norm_fst_le _).trans (B.reverse_central v v.property)
  obtain ⟨G,σ,hG,hσ,hsG,hσb,hrep,hG0⟩ := fine_compact_chart_graph k χ B.ε B.δ B.δ_pos B.contraction
    B.centre (fun v : B.carrier => (v : ℂ)) continuous_subtype_val (fun v => B.regular v v.property)
    hdata B.r_pos (by linarith [B.r_small]) B.η_pos.le hη B.η_pos.le
    (fun v => B.frames v v.property) B.slope hcent
  obtain ⟨GR,σR,hGR,hσR,hsGR,hσRb,hrepR,hGR0⟩ := fine_compact_chart_graph k χ B.ε B.δ B.δ_pos B.contraction
    (tangentReversal B.centre) (fun v : B.carrier => tangentReversal v)
    (tangentReversal.continuous.comp continuous_subtype_val) (fun v => B.reversed v v.property)
    hdataR B.r'_pos (by linarith [B.r'_small]) B.η_pos.le hη B.η_pos.le
    (fun v => B.reverse_frames v v.property) B.slope hcentR
  let U (a : B.carrier) (s : ℝ) := B.β*GR a (s/B.α)
  let τ (a : B.carrier) (s : ℝ) := σR a (s/B.α)
  have hUc : Continuous (fun p : B.carrier×ℝ => U p.1 p.2) :=
    continuous_const.mul (hGR.comp (continuous_fst.prodMk (continuous_snd.div_const B.α)))
  have hτc : Continuous (fun p : B.carrier×ℝ => τ p.1 p.2) :=
    hσR.comp (continuous_fst.prodMk (continuous_snd.div_const B.α))
  have hUslope (a : B.carrier) (s t : ℝ) : |U a s-U a t|≤(1/2)*|s-t| := by
    have hh := mul_le_mul_of_nonneg_left (hsGR a (s/B.α) (t/B.α)) (abs_nonneg B.β)
    have he : |U a s-U a t|=|B.β| * |GR a (s/B.α)-GR a (t/B.α)| := by
      dsimp only [U]; rw [←mul_sub,abs_mul]
    rw [he]
    apply hh.trans
    rw [←sub_div,abs_div]
    have he' : |B.β| * ((4/3)*(B.η+B.η)*(|s-t|/|B.α|))=
        ((|B.β|/|B.α|)*((8/3)*B.η))*|s-t| := by ring
    rw [he']
    exact mul_le_mul_of_nonneg_right B.reverse_slope (abs_nonneg _)
  have hU0 (a : B.carrier) : U a (B.coordinates a).2=(B.coordinates a).1 := by
    have he := B.coordinates_swap a
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    change (B.coordinates a).1=B.β*(B.reverseCoordinates a).2 at he1
    change (B.coordinates a).2=B.α*(B.reverseCoordinates a).1 at he2
    dsimp only [U]
    rw [he2,mul_div_cancel_left₀ _ B.α_ne]
    have hGR0' : GR a (B.reverseCoordinates a).1=(B.reverseCoordinates a).2 := (hGR0 a).2
    rw [hGR0']
    exact he1.symm
  refine ⟨{
    G := G,U := U,stableParameter := σ,unstableParameter := τ,
    continuous_G := hG,continuous_U := hUc,continuous_stableParameter := hσ,continuous_unstableParameter := hτc,
    slope_G := fun a s t => (hsG a s t).trans (mul_le_mul_of_nonneg_right (by linarith [B.η_small]) (abs_nonneg _)),
    slope_U := hUslope,stable_bound := hσb,unstable_bound := fun a s => hσRb a (s/B.α),
    stable_representation := ?_,unstable_representation := ?_,G_centre := fun a => (hG0 a).2,U_centre := hU0 }⟩
  · intro a s hs
    have hh := hrep a s (by exact ⟨by linarith [(abs_le.mp hs).1],(abs_le.mp hs).2⟩)
    have hh' := congrArg B.chart hh
    change B.chart (B.coordinates (fineStableCurve k χ B.ε B.δ B.δ_pos B.contraction a (B.regular a a.property) (σ a s)))=_ at hh'
    rw [B.chart_coordinates] at hh'
    exact hh'.symm
  · intro a s hs
    have hdiv : |s/B.α|≤B.r'/2 := by
      rw [abs_div]
      apply (div_le_iff₀ (abs_pos.mpr B.α_ne)).mpr
      nlinarith
    have hh := hrepR a (s/B.α) ⟨by linarith [(abs_le.mp hdiv).1],(abs_le.mp hdiv).2⟩
    let z := fineUnstableCurve k χ B.ε B.δ B.δ_pos B.contraction a (B.reversed a a.property) (τ a s)
    have hzR : B.reverseCoordinates z=(s/B.α,GR a (s/B.α)) := by
      simpa only [ReversibleRectangleBlock.reverseCoordinates,z,fineUnstableCurve,tangentReversal_involutive,τ,
        finePlaqueInChart] using hh
    have hz := B.coordinates_swap z
    rw [hzR] at hz
    have hαs : B.α*(s/B.α)=s := by field_simp [B.α_ne]
    change B.coordinates z=(U a s,B.α*(s/B.α)) at hz
    rw [hαs] at hz
    have he := congrArg B.chart hz
    rw [B.chart_coordinates] at he
    exact he.symm

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

theorem actual_stable_holonomy_local_bound (k : ℝ) (hk : 0≤k) (χ ε δ : ℝ)
    (hε : 0≤ε) (hδ : 0<δ) (hδ' : δ≤1/2) (hq : Real.exp (-χ+ε)+δ<1)
    (hslow : Real.exp (4*ε)*(Real.exp (-χ+ε)+δ)<1)
    (P Q W : ℂ) (S : Set ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H S)
    (hmatch : ∀ t∈S, ∃ (v : ℂ)
      (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v))) (s u : ℝ),
      |s|≤1/12 ∧ |u|≤1/12 ∧
      |(fineInverse k χ ε δ (complexProjection v) W).1|≤
        |(fineInverse k χ ε δ (complexProjection v) W).2| ∧
      (fineInverse k χ ε δ (complexProjection v) W).2≠0 ∧
      P+t•W=fineStableCurve k χ ε δ hδ hq v hv s ∧
      Q+H t•W=fineStableCurve k χ ε δ hδ hq v hv u) :
    ∀ t∈S,∀ᶠ t' in 𝓝[S] t,
      |H t'-H t|≤(2*Real.exp (8*δ/(1-(Real.exp (-χ+ε)+δ))))*|t'-t| := by
  intro t ht
  obtain ⟨v,hv,s,u,hs,hu,hcone,hnonzero,hleft,hright⟩ := hmatch t ht
  let I := fineInverse k χ ε δ (complexProjection v)
  have he (p : ℂ) (t : ℝ) : v+fineFrame k χ ε δ (complexProjection v) (I (p-v)+t•I W)=p+t•W :=
    fine_affine_coordinates k χ ε δ hδ v p W (hv 0) t
  have hleft' : v+fineFrame k χ ε δ (complexProjection v) (I (P-v)+t•I W)=
      fineStableCurve k χ ε δ hδ hq v hv s := (he P t).trans hleft
  have hright' : v+fineFrame k χ ε δ (complexProjection v) (I (Q-v)+H t•I W)=
      fineStableCurve k χ ε δ hδ hq v hv u := (he Q (H t)).trans hright
  apply fine_stable_matching_local_bound k hk χ ε δ hε hδ hδ' hq hslow v hv
    (I (P-v)) (I (Q-v)) (I W) hcone hnonzero S H ht (hH t ht) hs hu hleft' hright'
  intro t' ht'
  obtain ⟨v',hv',s',u',hs',hu',_,_,hleft'',hright''⟩ := hmatch t' ht'
  exact ⟨v',hv',s',u',hs'.trans (by norm_num),hu'.trans (by norm_num),
    (he P t').trans hleft'',(he Q (H t')).trans hright''⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology NNReal ENNReal

theorem compact_actual_stable_holonomy_bounds {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (k : ℝ) (hk : 0≤k) (χ ε δ : ℝ) (hε : 0≤ε) (hδ : 0<δ) (hδ' : δ≤1/2)
    (hq : Real.exp (-χ+ε)+δ<1) (hslow : Real.exp (4*ε)*(Real.exp (-χ+ε)+δ)<1)
    (P Q W : ℂ) (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfib : ∀ x y, f x=f y ↔ g x=g y)
    (hplaque : ∀ x, ∃ (v : ℂ)
      (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v))) (s u : ℝ),
      |s|≤1/12 ∧ |u|≤1/12 ∧
      |(fineInverse k χ ε δ (complexProjection v) W).1|≤
        |(fineInverse k χ ε δ (complexProjection v) W).2| ∧
      (fineInverse k χ ε δ (complexProjection v) W).2≠0 ∧
      P+f x•W=fineStableCurve k χ ε δ hδ hq v hv s ∧
      Q+g x•W=fineStableCurve k χ ε δ hδ hq v hv u) :
    ∃ H J : ℝ → ℝ,
      ContinuousOn H (range f) ∧ ContinuousOn J (range g) ∧
      (∀ x, H (f x)=g x ∧ J (g x)=f x) ∧
      (∀ y∈range f, J (H y)=y) ∧ (∀ y∈range g, H (J y)=y) ∧
      (∀ t∈range f,∀ᶠ t' in 𝓝[range f] t,
        |H t'-H t|≤(2*Real.exp (8*δ/(1-(Real.exp (-χ+ε)+δ))))*|t'-t|) ∧
      (∀ t∈range g,∀ᶠ t' in 𝓝[range g] t,
        |J t'-J t|≤(2*Real.exp (8*δ/(1-(Real.exp (-χ+ε)+δ))))*|t'-t|) := by
  obtain ⟨H,hH,hHval⟩ := compact_fibre_descent hf hg (fun x y h => (hfib x y).mp h)
  obtain ⟨J,hJ,hJval⟩ := compact_fibre_descent hg hf (fun x y h => (hfib x y).mpr h)
  refine ⟨H,J,hH,hJ,fun x => ⟨hHval x,hJval x⟩,?_,?_,?_,?_⟩
  · rintro y ⟨x,rfl⟩; rw [hHval,hJval]
  · rintro y ⟨x,rfl⟩; rw [hJval,hHval]
  · apply actual_stable_holonomy_local_bound k hk χ ε δ hε hδ hδ' hq hslow P Q W (range f) H hH
    rintro t ⟨x,rfl⟩
    obtain ⟨v,hv,s,u,hs,hu,hc,hn,hp,hq'⟩ := hplaque x
    exact ⟨v,hv,s,u,hs,hu,hc,hn,hp,by rw [hHval]; exact hq'⟩
  · apply actual_stable_holonomy_local_bound k hk χ ε δ hε hδ hδ' hq hslow Q P W (range g) J hJ
    rintro t ⟨x,rfl⟩
    obtain ⟨v,hv,s,u,hs,hu,hc,hn,hp,hq'⟩ := hplaque x
    exact ⟨v,hv,u,s,hu,hs,hc,hn,hq',by rw [hJval]; exact hp⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable

theorem actual_graph_holonomy_bounds {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (k : ℝ) (hk : 0≤k) (χ ε δ : ℝ) (hε : 0≤ε) (hδ : 0<δ) (hδ' : δ≤1/2)
    (hq : Real.exp (-χ+ε)+δ<1) (hslow : Real.exp (4*ε)*(Real.exp (-χ+ε)+δ)<1)
    (w : ℂ) (hw : wedge (stableVector k (complexProjection w)) (unstableVector k (complexProjection w))≠0)
    (v : X → ℂ) (hv : ∀ a,∀ n : ℕ,FineRegular k χ ε (complexProjection ((standardLift k)^[n] (v a))))
    (G σ : X → ℝ → ℝ) (hG : Continuous (fun p : X×ℝ => G p.1 p.2))
    {r R : ℝ} (hr : 0<r) (hrsmall : r≤1/12) (hR : 0<R)
    (hRv : ∀ a,R≤codingRadius k χ ε δ (complexProjection (v a)))
    (hsize : (4*fineScale k ε δ*r)/(100*R)+r≤1)
    (hclose : ∀ a,‖(fineInverse k χ ε δ (complexProjection w)).comp (fineFrame k χ ε δ (complexProjection (v a)))-ContinuousLinearMap.id ℝ Plane‖≤1/4)
    (hclose' : ∀ a,‖(fineInverse k χ ε δ (complexProjection (v a))).comp (fineFrame k χ ε δ (complexProjection w))-ContinuousLinearMap.id ℝ Plane‖≤1/4)
    (I : Set ℝ) (hσ : ∀ a s,s∈I → |σ a s|≤r)
    (hrep : ∀ a s,s∈I → w+fineFrame k χ ε δ (complexProjection w) (s,G a s)=
      fineStableCurve k χ ε δ hδ hq (v a) (hv a) (σ a s))
    {c d : ℝ} (hc : c∈I) (hd : d∈I) :
    ∃ H J : ℝ → ℝ,
      ContinuousOn H (range (fun a => G a c)) ∧ ContinuousOn J (range (fun a => G a d)) ∧
      (∀ a,H (G a c)=G a d ∧ J (G a d)=G a c) ∧
      (∀ y∈range (fun a => G a c),J (H y)=y) ∧
      (∀ y∈range (fun a => G a d),H (J y)=y) ∧
      (∀ t∈range (fun a => G a c),∀ᶠ t' in 𝓝[range (fun a => G a c)] t,
        |H t'-H t|≤(2*Real.exp (8*δ/(1-(Real.exp (-χ+ε)+δ))))*|t'-t|) ∧
      (∀ t∈range (fun a => G a d),∀ᶠ t' in 𝓝[range (fun a => G a d)] t,
        |J t'-J t|≤(2*Real.exp (8*δ/(1-(Real.exp (-χ+ε)+δ))))*|t'-t|) := by
  have hr1 : r≤1 := by linarith
  have hslo : Real.exp (2*ε)*(Real.exp (-χ+ε)+δ)≤1 :=
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by positivity)).trans hslow.le
  have coord (a : X) (s : ℝ) (hs : s∈I) :
      finePlaqueInChart k χ ε δ hδ hq w (v a) (hv a) (σ a s)=(s,G a s) := by
    unfold finePlaqueInChart
    rw [←hrep a s hs,add_sub_cancel_left,fineInverse_frame k χ ε hδ _ hw]
  have one (c d : ℝ) (hc : c∈I) (hd : d∈I) (a b : X) (he : G a c=G b c) : G a d=G b d := by
    have meet : fineStableCurve k χ ε δ hδ hq (v a) (hv a) (σ a c)=
        fineStableCurve k χ ε δ hδ hq (v b) (hv b) (σ b c) := by rw [←hrep a c hc,←hrep b c hc,he]
    have hh := fine_small_crossings_coincide k χ ε δ hδ hq hslo w (v a) (v b) (hv a) (hv b)
      hr hr1 hR (hRv a) hsize (hclose a) (hσ a c hc) (hσ a d hd) (hσ b c hc) (hσ b d hd)
      meet (by rw [coord a d hd,coord b d hd])
    have hh' := congrArg (fun z => (fineInverse k χ ε δ (complexProjection w) (z-w)).2) hh
    change (finePlaqueInChart k χ ε δ hδ hq w (v a) (hv a) (σ a d)).2=_ at hh'
    rw [coord a d hd] at hh'
    change G a d=(finePlaqueInChart k χ ε δ hδ hq w (v b) (hv b) (σ b d)).2 at hh'
    simpa only [coord b d hd] using hh'
  let W := fineFrame k χ ε δ (complexProjection w) (0,1)
  have endpoint (a : X) (s : ℝ) (hs : s∈I) :
      (w+fineFrame k χ ε δ (complexProjection w) (s,0))+G a s•W=
      fineStableCurve k χ ε δ hδ hq (v a) (hv a) (σ a s) := by
    dsimp only [W]
    rw [←map_smul,add_assoc,←map_add]
    have he : (s,0)+(G a s)•((0,1) : Plane)=(s,G a s) := by ext <;> simp
    rw [he,hrep a s hs]
  apply compact_actual_stable_holonomy_bounds k hk χ ε δ hε hδ hδ' hq hslow
    (w+fineFrame k χ ε δ (complexProjection w) (c,0))
    (w+fineFrame k χ ε δ (complexProjection w) (d,0)) W
    (fun a => G a c) (fun a => G a d)
    (hG.comp (continuous_id.prodMk continuous_const)) (hG.comp (continuous_id.prodMk continuous_const))
    (fun a b => ⟨one c d hc hd a b,one d c hd hc a b⟩)
  intro a
  exact ⟨v a,hv a,σ a c,σ a d,(hσ a c hc).trans hrsmall,(hσ a d hd).trans hrsmall,
    (fine_transverse_cone k χ ε δ w (v a) (hclose' a)).1,
    (fine_transverse_cone k χ ε δ w (v a) (hclose' a)).2,endpoint a c hc,endpoint a d hd⟩

end StandardMapEntropy

end
end

end OAI
