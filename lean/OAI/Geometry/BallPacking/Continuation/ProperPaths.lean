import Mathlib
import OAI.Geometry.BallPacking.Moduli.SmoothZeroCharts

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def freezeTime (t : ℝ) : ℝ := Real.smoothTransition (2*t-1/2)
def frozenPath (F : ℝ × X → Y) (v : ℝ × X) : Y := F (freezeTime v.1,v.2)

lemma freezeTime_smooth : ContDiff ℝ ∞ freezeTime :=
  (show ContDiff ℝ ∞ Real.smoothTransition from contDiff_infty.mpr (fun _ => Real.smoothTransition.contDiff)).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)
lemma freezeTime_mem (t : ℝ) : freezeTime t∈Icc (0:ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
lemma freezeTime_initial {t : ℝ} (ht : t≤1/4) : freezeTime t=0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
lemma freezeTime_final {t : ℝ} (ht : 3/4≤t) : freezeTime t=1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
lemma frozenPath_smooth {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (frozenPath F) :=
  hF.comp ((freezeTime_smooth.comp contDiff_fst).prodMk contDiff_snd)

lemma ProperIndexZeroPath.frozen {F : ℝ × X → Y} {U : Set X} (h : ProperIndexZeroPath F U) :
    ProperIndexZeroPath (frozenPath F) U := by
  let K := Prod.snd '' {v : ℝ × X | v.1∈Icc (0:ℝ) 1 ∧ v.2∈U ∧ F v=0}
  have hK : IsCompact K := h.zeroSet_compact.image continuous_snd
  have hKU : K⊆U := by rintro x ⟨v,hv,rfl⟩; exact hv.2.1
  have he : {v : ℝ × X | v.1∈Icc (0:ℝ) 1 ∧ v.2∈U ∧ frozenPath F v=0} =
      (Icc (0:ℝ) 1 ×ˢ K) ∩ {v | frozenPath F v=0} := by
    ext v
    constructor
    · rintro ⟨ht,hx,hz⟩
      exact ⟨⟨ht,⟨(freezeTime v.1,v.2),⟨freezeTime_mem _,hx,hz⟩,rfl⟩⟩,hz⟩
    · rintro ⟨⟨ht,hx⟩,hz⟩
      exact ⟨ht,hKU hx,hz⟩
  refine ⟨h.domain_open,h.origin_mem,frozenPath_smooth h.smooth,?_,?_,?_⟩
  · obtain ⟨L,hL⟩ := h.initial
    refine ⟨L,fun x => ?_⟩
    change F (freezeTime 0,x)=L x
    rw [freezeTime_initial (by norm_num)]
    exact hL x
  · rw [he]
    exact (isCompact_Icc.prod hK).inter_right (isClosed_eq (frozenPath_smooth h.smooth).continuous continuous_const)
  · intro t ht x hx
    exact h.fredholm _ (freezeTime_mem t) x hx


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  (L : X ≃L[ℝ] Y) (hL : ∀ x,F (0,x)=L x)

def frozenInitialChart : ZeroGraphChart (finiteTargetAugment (frozenPath F) E) E where
  base := (0,(0,0))
  zero_base := by
    change F (freezeTime 0,0)+(0:Y)=0
    rw [freezeTime_initial (by norm_num),hL,map_zero,add_zero]
  coordinate := ContinuousLinearMap.snd ℝ X E
  reconstruct q := initialKernelGraph L E q.2
  domain := {q | q.1<1/4}
  ambient := {v | v.1<1/4}
  domain_open := isOpen_lt continuous_fst continuous_const
  ambient_open := isOpen_lt continuous_fst continuous_const
  base_domain := by norm_num
  base_ambient := by norm_num
  smooth := ((initialKernelGraph L E).contDiff.comp contDiff_snd).contDiffOn
  left_inv q := rfl
  zero q hq := by
    change F (freezeTime q.1,-L.symm (q.2:Y))+(q.2:Y)=0
    rw [freezeTime_initial (le_of_lt hq),hL,map_neg,L.apply_symm_apply,neg_add_cancel]
  image_ambient q hq := hq
  complete v hv hz := by
    change initialKernelGraph L E v.2.2=v.2
    apply (initialKernelGraph_kernel v.2).mp
    change F (freezeTime v.1,v.2.1)+(v.2.2:Y)=0 at hz
    rwa [freezeTime_initial (le_of_lt hv),hL] at hz

omit [FiniteDimensional ℝ E] in
lemma frozenInitialChart_smooth [FiniteDimensional ℝ E] : ContDiff ℝ ∞ (frozenInitialChart L hL (E := E)).reconstruct :=
  (initialKernelGraph L E).contDiff.comp contDiff_snd

omit [FiniteDimensional ℝ E] in
lemma frozenInitialChart_source [FiniteDimensional ℝ E]
    (v : {v : ℝ × (X × E) // finiteTargetAugment (frozenPath F) E v=0}) :
    v∈(frozenInitialChart L hL).partialHomeomorph.source ↔ v.val.1<1/4 := by
  change (v.val.1<1/4 ∧ v.val.1<1/4) ↔ _
  simp

omit [FiniteDimensional ℝ E] in
lemma frozenInitialChart_spatialDerivative [FiniteDimensional ℝ E] (q : ℝ × E) :
    (frozenInitialChart L hL (E := E)).spatialDerivative q=initialKernelGraph L E := by
  change (fderiv ℝ (fun q : ℝ × E => initialKernelGraph L E q.2) q).comp _=_
  have hd := (initialKernelGraph L E).hasFDerivAt.comp q (hasFDerivAt_snd (p := q))
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  ext e <;> rfl


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ × X → Y}

 def ZeroGraphChart.rebase (c : ZeroGraphChart F E) (p : {v : ℝ × X // F v=0})
    (hp : p∈c.partialHomeomorph.source) : ZeroGraphChart F E :=
  {c with base := p.val,zero_base := p.property,base_domain := hp.2,base_ambient := hp.1}

 def SmoothZeroAtlas.prescribe {s : TopologicalSpace.Opens {v : ℝ × X // F v=0}}
    (a : SmoothZeroAtlas F E s) (p : s) (c : ZeroGraphChart F E)
    (hp : p.val∈c.partialHomeomorph.source) (hc : ContDiffOn ℝ ∞ c.reconstruct c.domain) :
    SmoothZeroAtlas F E s := by
  classical
  refine {chart := fun x => if x=p then c.rebase p.val hp else a.chart x,base := ?_,smooth := ?_}
  · intro x
    by_cases hx : x=p
    · subst x; simp only; rfl
    · simp only [ite_eq_right hx]; exact a.base x
  · intro x
    by_cases hx : x=p
    · simp only [ite_eq_left hx]; exact hc
    · simp only [ite_eq_right hx]; exact a.smooth x

@[simp] lemma SmoothZeroAtlas.prescribe_at {s : TopologicalSpace.Opens {v : ℝ × X // F v=0}}
    (a : SmoothZeroAtlas F E s) (p : s) (c : ZeroGraphChart F E)
    (hp : p.val∈c.partialHomeomorph.source) (hc : ContDiffOn ℝ ∞ c.reconstruct c.domain) :
    (a.prescribe p c hp hc).chart p=c.rebase p.val hp := by
  classical
  simp [SmoothZeroAtlas.prescribe]


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

theorem ProperIndexZeroPath.smooth_framed_isolating_stabilization
    {F : ℝ × X → Y} {U : Set X} (h : ProperIndexZeroPath F U) :
    ∃ E : Submodule ℝ Y,∃ _ : FiniteDimensional ℝ E,
      ∃ V : Set (ℝ × X),IsOpen V ∧
        ∃ _ : StabilizedKernelFrame F E V,
          ∃ N : Set (ℝ × (X × E)),IsolatingStabilization F U E N ∧
            (∀ v∈closure N,finiteTargetAugment F E v=0 →(v.1,v.2.1)∈V) ∧
            (∀ v∈V,Surjective ((pathSpatialDerivative F v).coprod E.subtypeL)) := by
  obtain ⟨K,hK,hKU,h0K,hZ,E,hE,V,hVo,hKV,hs,⟨fr⟩⟩ := h.stabilized_kernel_frame
  let := hE
  let B : ℝ × X → ℝ × (X × E) := fun v => (v.1,(v.2,0))
  have hB : Continuous B := continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  let Z := B '' {v : ℝ × X | v.1∈Icc (0:ℝ) 1 ∧ v.2∈U ∧ F v=0}
  let W : Set (ℝ × (X × E)) := {v | v.2.1∈U ∧ (v.1,v.2.1)∈V}
  have hZc : IsCompact Z := h.zeroSet_compact.image hB
  have hWo : IsOpen W := (h.domain_open.preimage (continuous_fst.comp continuous_snd)).inter
    (hVo.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
  have hZW : Z⊆W := by
    rintro _ ⟨⟨t,x⟩,hv,rfl⟩
    exact ⟨hv.2.1,hKV ⟨hv.1,hZ t hv.1 x hv.2.1 hv.2.2⟩⟩
  have hg (v : ℝ × (X × E)) (hv : v∈W) (hz : finiteTargetAugment F E v=0) :
      Nonempty (FiniteZeroGerm (finiteTargetAugment F E) v.1 v.2 (Module.finrank ℝ E)) :=
    fr.zero_germ h.smooth hv.2 (hs _ hv.2) hz
  have hcharts : ∀ v∈Z,∃ m,Nonempty (FiniteZeroGerm (finiteTargetAugment F E) v.1 v.2 m) := by
    intro v hv
    refine ⟨Module.finrank ℝ E,hg v (hZW hv) ?_⟩
    rcases hv with ⟨⟨t,x⟩,hv,rfl⟩
    simpa only [B,finiteTargetAugment,ZeroMemClass.coe_zero,add_zero] using hv.2.2
  obtain ⟨N,hNo,hZN,hNc,hNW⟩ := compact_zero_isolating_neighborhood
    (finiteTargetAugment_smooth h.smooth E).continuous hZc hWo hZW hcharts
  refine ⟨E,hE,V,hVo,fr,N,⟨hNo,?_,hNc,?_,?_⟩,?_,?_⟩
  · intro t ht x hx hz
    exact hZN ⟨(t,x),⟨ht,hx,hz⟩,rfl⟩
  · intro v hv hz
    exact (hNW ⟨hv,hz⟩).1
  · intro v hv ht hz
    exact hg v (hNW ⟨hv,hz⟩) hz
  · intro v hv hz
    exact (hNW ⟨hv,hz⟩).2
  · exact hs


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {U : Set X} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {N : Set (ℝ × (X × E))}

omit [CompleteSpace X] [CompleteSpace Y] in
lemma IsolatingStabilization.small_frozen_final_collar [CompleteSpace X] [CompleteSpace Y]
    (h : IsolatingStabilization (frozenPath F) U E N) (hn : ∀ x∈U,F (1,x)≠0) :
    ∃ δ : ℝ,0<δ ∧ ∀ v∈closure N,3/4≤v.1 →‖v.2.2‖≤δ →
      finiteTargetAugment (frozenPath F) E v≠0 := by
  let C := (closure N ∩ {v | finiteTargetAugment (frozenPath F) E v=0}) ∩ {v | 3/4≤v.1}
  have hC : IsCompact C := h.compact.inter_right (isClosed_le continuous_const continuous_fst)
  let B := (fun v : ℝ × (X × E) => v.2.2) '' C
  have hB : IsCompact B := hC.image (continuous_snd.comp continuous_snd)
  have hB0 : (0:E)∉B := by
    rintro ⟨⟨t,x,e⟩,⟨⟨hcl,hz⟩,ht⟩,he⟩
    have he0 : e=0 := he
    subst e
    have hx := h.domain (t,(x,0)) hcl hz
    change F (freezeTime t,x)+(0:Y)=0 at hz
    rw [freezeTime_final ht,add_zero] at hz
    exact hn x hx hz
  obtain ⟨r,hr,hrB⟩ := Metric.isOpen_iff.mp hB.isClosed.isOpen_compl 0 hB0
  refine ⟨r/2,half_pos hr,?_⟩
  intro v hv ht he hz
  apply hrB (show v.2.2∈Metric.ball 0 r from ?_) ⟨v,⟨⟨hv,hz⟩,ht⟩,rfl⟩
  simpa only [Metric.mem_ball,dist_zero_right] using he.trans_lt (half_lt_self hr)

omit [CompleteSpace X] [CompleteSpace Y] in
lemma IsolatingStabilization.small_frozen_initial_collar [CompleteSpace X] [CompleteSpace Y]
    (h : IsolatingStabilization (frozenPath F) U E N) (hp : ProperIndexZeroPath F U)
    (L : X ≃L[ℝ] Y) (hL : ∀ x,F (0,x)=L x) :
    ∃ δ : ℝ,0<δ ∧ ∀ t∈Icc (0:ℝ) (1/4),∀ e : E,‖e‖≤δ →
      (t,(-L.symm (e:Y),e))∈N := by
  let ψ : ℝ × E → ℝ × (X × E) := fun v => (v.1,(-L.symm (v.2:Y),v.2))
  have hψ : Continuous ψ := continuous_fst.prodMk
    ((L.symm.continuous.comp (E.subtypeL.continuous.comp continuous_snd)).neg.prodMk continuous_snd)
  let K : Set (ℝ × E) := Icc (0:ℝ) (1/4) ×ˢ {0}
  have hK : IsCompact K := isCompact_Icc.prod isCompact_singleton
  have hKN : K⊆ψ ⁻¹' N := by
    rintro ⟨t,e⟩ ⟨ht,he⟩
    have he0 : e=0 := he
    subst e
    have hz : frozenPath F (t,0)=0 := by
      change F (freezeTime t,0)=0
      rw [freezeTime_initial ht.2,hL,map_zero]
    change (t,(-L.symm ((0:E):Y),0))∈N
    simpa only [ZeroMemClass.coe_zero,map_zero,neg_zero] using
      h.contains t ⟨ht.1,ht.2.trans (by norm_num)⟩ 0 hp.origin_mem hz
  obtain ⟨r,hr,hrN⟩ := hK.exists_cthickening_subset_open (h.isOpen.preimage hψ) hKN
  refine ⟨r/2,half_pos hr,?_⟩
  intro t ht e he
  change (t,e)∈ψ ⁻¹' N
  apply hrN
  apply Metric.mem_cthickening_of_dist_le (t,e) (t,0) r K ⟨ht,rfl⟩
  simpa [Prod.dist_eq,dist_zero_right] using he.trans (half_le_self (le_of_lt hr))

omit [CompleteSpace X] [CompleteSpace Y] in
lemma IsolatingStabilization.small_target_reservoir [CompleteSpace X] [CompleteSpace Y]
    (h : IsolatingStabilization F U E N) {δ : ℝ}
    (hδ : ∀ v∈frontier N,v.1∈Icc (0:ℝ) 1 →‖v.2.2‖≤δ →finiteTargetAugment F E v≠0) :
    let K := (closure N ∩ {v | finiteTargetAugment F E v=0}) ∩
      {v | v.1∈Icc (0:ℝ) 1 ∧ ‖v.2.2‖≤δ}
    IsCompact K ∧ K⊆N := by
  dsimp only
  refine ⟨h.compact.inter_right ?_,?_⟩
  · exact (isClosed_Icc.preimage continuous_fst).inter
      (isClosed_le ((continuous_snd.comp continuous_snd).norm) continuous_const)
  · intro v hv
    by_contra hn
    have hf : v∈frontier N := by
      rw [h.isOpen.frontier_eq]
      exact ⟨hv.1.1,hn⟩
    exact hδ v hf hv.2.1 hv.2.2 hv.1.2


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma orientedZeroAtlas_self_source {F : ℝ × X → Y} {E : Submodule ℝ Y}
    [FiniteDimensional ℝ E] {V : Set (ℝ × X)} (fr : StabilizedKernelFrame F E V)
    (hF : ContDiff ℝ ∞ F) (hV : IsOpen V)
    (a : SmoothZeroAtlas (finiteTargetAugment F E) E (framedZeroOpen F E V hV))
    (x : framedZeroOpen F E V hV) : x∈((fr.orientedZeroAtlas hF hV a).chart x).source := by
  change x∈(((a.localChart x).symm.restrOpen _ _).symm).source
  refine ⟨a.chartedSpace.mem_chart_source x,?_⟩
  exact (framedChart_orientation_neighborhood fr (a.chart x) hF hV
    (a.localChart_target x (framedLocalChart_base_target hV a x))
    (framedLocalChart_V hV a x (framedLocalChart_base_target hV a x))).choose_spec.2.1

 theorem ProperIndexZeroPath.endpoint_exists {F : ℝ × X → Y} {U : Set X}
    (h : ProperIndexZeroPath F U) : ∃ x∈U,F (1,x)=0 := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨E,hE,V,hV,fr,N,hN,hNV,hs⟩ := h.frozen.smooth_framed_isolating_stabilization
  let := hE
  obtain ⟨L,hL⟩ := h.initial
  let A := finiteTargetAugment (frozenPath F) E
  let M := framedZeroOpen (frozenPath F) E V hV
  let base : ℝ × (X × E) := ((1:ℝ)/8,(0,0))
  have hbz : A base=0 := by
    change F (freezeTime (1/8),0)+(0:Y)=0
    rw [freezeTime_initial (by norm_num),hL,map_zero,add_zero]
  have hbN : base∈N := by
    apply hN.contains (1/8) (by constructor <;> norm_num) 0 h.origin_mem
    change F (freezeTime (1/8),0)=0
    rw [freezeTime_initial (by norm_num),hL,map_zero]
  let p : M := ⟨⟨base,hbz⟩,hNV base (subset_closure hbN) hbz⟩
  let c := frozenInitialChart L hL (E := E)
  have hpC : p.val∈c.partialHomeomorph.source := by
    apply (frozenInitialChart_source L hL p.val).mpr
    norm_num [p,base]
  let a₀ := fr.smoothZeroAtlas (frozenPath_smooth h.smooth) hV hs
  let a := a₀.prescribe p c hpC (frozenInitialChart_smooth L hL).contDiffOn
  let atlas := fr.orientedZeroAtlas (frozenPath_smooth h.smooth) hV a
  let π := fr.physicalProjection (frozenPath_smooth h.smooth) hV a
  have hπ (z : M) : π.map z=(z.val.val.1,z.val.val.2.2) := rfl
  have hπc : Continuous π.map := (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
    (continuous_snd.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)))
  have hpi : p∈(atlas.chart p).source := orientedZeroAtlas_self_source fr (frozenPath_smooth h.smooth) hV a p
  have hπp : π.map p=((1:ℝ)/8,0) := rfl
  have hac : a.chart p=c.rebase p.val hpC := a₀.prescribe_at p c hpC (frozenInitialChart_smooth L hL).contDiffOn
  have hid : EqOn (π.map ∘ (atlas.chart p).symm) id (atlas.chart p).target := by
    intro q hq
    change ((((a.localChart p).symm q).val.val).1,(((a.localChart p).symm q).val.val).2.2)=q
    rw [a.localChart_symm_val p (orientedZeroAtlas_target fr (frozenPath_smooth h.smooth) hV a p hq),hac]
    rfl
  have hint : ∀ q∈(atlas.chart p).target,q.1<1/4 := by
    intro q hq
    have hh := a.localChart_target p (orientedZeroAtlas_target fr (frozenPath_smooth h.smooth) hV a p hq)
    rw [hac] at hh
    exact hh
  have hinj : ∀ x y : M,(π.map x).1<1/4 →(π.map y).1<1/4 →π.map x=π.map y →x=y := by
    intro x y hx hy he
    have hxx : initialKernelGraph L E x.val.val.2.2=x.val.val.2 := c.complete x.val.val hx x.val.property
    have hyy : initialKernelGraph L E y.val.val.2.2=y.val.val.2 := c.complete y.val.val hy y.val.property
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun v : ℝ × E => v.1) he
    · exact hxx.symm.trans ((congrArg (initialKernelGraph L E) (congrArg Prod.snd he)).trans hyy)
  let N₀ : Set M := {z | z.val.val∈N}
  have hN₀ : IsOpen N₀ := hN.isOpen.preimage (continuous_subtype_val.comp continuous_subtype_val)
  have hpN₀ : p∈N₀ := hbN
  obtain ⟨δB,hδB,havoid⟩ := hN.small_target_boundary_avoid
  obtain ⟨δF,hδF,hfinal⟩ := hN.small_frozen_final_collar hn
  let δ₀ := min δB δF
  have hδ₀ : 0<δ₀ := lt_min hδB hδF
  have hcompact : ∀ δ : ℝ,0<δ →δ≤δ₀ →IsCompact {z : M | z∈N₀ ∧
      (π.map z).1∈Icc (0:ℝ) 1 ∧ ‖(π.map z).2‖≤δ} := by
    intro δ hδ hd
    have hsmall : ∀ v∈frontier N,v.1∈Icc (0:ℝ) 1 →‖v.2.2‖≤δ →A v≠0 := by
      intro v hv ht he
      exact havoid v hv ht (he.trans (hd.trans (min_le_left _ _)))
    have hc := hN.small_target_reservoir hsmall
    let C : Set (ℝ × (X × E)) := (closure N ∩ {v | A v=0}) ∩
      {v | v.1∈Icc (0:ℝ) 1 ∧ ‖v.2.2‖≤δ}
    have hCc : IsCompact C := hc.1
    have hCN : C⊆N := hc.2
    let val : M → ℝ × (X × E) := fun z => z.val.val
    have hval : Topology.IsEmbedding val := Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    have hCrange : C⊆range val := by
      intro v hv
      exact ⟨⟨⟨v,hv.1.2⟩,hNV v hv.1.1 hv.1.2⟩,rfl⟩
    have hpre := (hval.isCompact_preimage_iff hCrange).mpr hCc
    have he : val ⁻¹' C={z : M | z∈N₀ ∧ (π.map z).1∈Icc (0:ℝ) 1 ∧ ‖(π.map z).2‖≤δ} := by
      ext z
      constructor
      · intro hz
        exact ⟨hCN hz,hz.2⟩
      · rintro ⟨hz,ht,he⟩
        exact ⟨⟨subset_closure hz,z.val.property⟩,ht,he⟩
    rwa [he] at hpre
  have hfinal₀ : ∀ z∈N₀,3/4≤(π.map z).1 →‖(π.map z).2‖≤δ₀ →False := by
    intro z hz ht he
    exact hfinal z.val.val (subset_closure hz) ht (he.trans (min_le_right _ _)) z.val.property
  exact Degree.isolated_collar_impossible atlas π hπc p p hpi hπp hid hint hinj N₀ hN₀ hpN₀
    δ₀ hδ₀ hcompact hfinal₀


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
