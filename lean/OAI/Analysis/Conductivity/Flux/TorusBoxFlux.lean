import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalAttachedAssembly
import OAI.Analysis.Conductivity.Fourier.AngularPeriodization

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory

def torusCellIntegral (T : ℝ) (f : Coord3 → ℝ) (t : ℝ) : ℝ :=
  ∫ y in (0:ℝ)..T,∫ z in (0:ℝ)..T,f ![t,y,z]

lemma integral_coord2_Icc {a b : Fin 2 → ℝ} (hab : a≤b) {f : (Fin 2 → ℝ) → ℝ}
    (hf : Continuous f) :
    (∫ x in Icc a b,f x)=∫ y in a 0..b 0,∫ z in a 1..b 1,f ![y,z] := by
  have hc : Continuous (fun q : ℝ×ℝ => f ![q.1,q.2]) := hf.comp (by fun_prop)
  have hi := hc.continuousOn.integrableOn_compact (μ:=volume)
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1)))
  have he := (volume_preserving_finTwoArrow ℝ).setIntegral_image_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding (fun q : ℝ×ℝ => f ![q.1,q.2]) (Icc a b)
  have hid (x : Fin 2 → ℝ) : ![x 0,x 1]=x := by ext i; fin_cases i <;> rfl
  simp only [MeasurableEquiv.finTwoArrow_apply] at he
  simp_rw [hid] at he
  have him : MeasurableEquiv.finTwoArrow '' Icc a b=Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1) := by
    ext q
    rw [MeasurableEquiv.image_eq_preimage_symm]
    simp only [mem_preimage,mem_Icc,Pi.le_def,mem_prod]
    constructor
    · intro h
      exact ⟨⟨h.1 0,h.2 0⟩,⟨h.1 1,h.2 1⟩⟩
    · intro h
      constructor <;> intro i <;> fin_cases i
      · exact h.1.1
      · exact h.2.1
      · exact h.1.2
      · exact h.2.2
  change (∫ y in (MeasurableEquiv.finTwoArrow '' Icc a b),f ![y.1,y.2])=_ at he
  rw [←he,him]
  change (∫ x in Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1),f ![x.1,x.2] ∂volume.prod volume)=_
  rw [setIntegral_prod _ hi]
  simp_rw [intervalIntegral.integral_of_le (hab 0),intervalIntegral.integral_of_le (hab 1),
    ←integral_Icc_eq_integral_Ioc]

lemma integral_coord3_Icc {a b : Coord3} (hab : a≤b) {f : Coord3 → ℝ} (hf : Continuous f) :
    (∫ x in Icc a b,f x)=∫ t in a 0..b 0,∫ y in a 1..b 1,∫ z in a 2..b 2,f ![t,y,z] := by
  have hc : Continuous (fun q : ℝ×(ℝ×ℝ) => f ![q.1,q.2.1,q.2.2]) := hf.comp (by fun_prop)
  have hi := hc.continuousOn.integrableOn_compact (μ:=volume)
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc) :
      IsCompact (Icc (a 0) (b 0) ×ˢ (Icc (a 1) (b 1) ×ˢ Icc (a 2) (b 2))))
  have he := threeArrow_volume.setIntegral_image_emb threeArrow.measurableEmbedding
    (fun q : ℝ×(ℝ×ℝ) => f ![q.1,q.2.1,q.2.2]) (Icc a b)
  simp only [threeArrow_apply] at he
  have hid (x : Coord3) : ![x 0,x 1,x 2]=x := by ext i; fin_cases i <;> rfl
  simp_rw [hid] at he
  have him : threeArrow '' Icc a b=Icc (a 0) (b 0) ×ˢ (Icc (a 1) (b 1) ×ˢ Icc (a 2) (b 2)) := by
    ext q
    rw [MeasurableEquiv.image_eq_preimage_symm]
    simp only [mem_preimage,mem_Icc,Pi.le_def,mem_prod,threeArrow_symm_apply]
    constructor
    · intro h
      exact ⟨⟨h.1 0,h.2 0⟩,⟨⟨h.1 1,h.2 1⟩,⟨h.1 2,h.2 2⟩⟩⟩
    · intro h
      constructor <;> intro i <;> fin_cases i
      · exact h.1.1
      · exact h.2.1.1
      · exact h.2.2.1
      · exact h.1.2
      · exact h.2.1.2
      · exact h.2.2.2
  change (∫ y in (threeArrow '' Icc a b),f ![y.1,y.2.1,y.2.2])=_ at he
  rw [←he,him]
  change (∫ x in Icc (a 0) (b 0) ×ˢ (Icc (a 1) (b 1) ×ˢ Icc (a 2) (b 2)),
    f ![x.1,x.2.1,x.2.2] ∂volume.prod volume)=_
  rw [setIntegral_prod _ hi]
  simp_rw [intervalIntegral.integral_of_le (hab 0),intervalIntegral.integral_of_le (hab 1),
    intervalIntegral.integral_of_le (hab 2),←integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t _
  exact setIntegral_prod _ ((hc.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc))

lemma coordinateDivergence_eq_trace {F : Coord3 → Coord3} (hF : Differentiable ℝ F) (x : Coord3) :
    coordinateDivergence F x=∑ i : Fin 3,fderiv ℝ F x (Pi.single i 1) i := by
  apply Finset.sum_congr rfl
  intro i _
  rw [(hasFDerivAt_pi'.mp (hF x).hasFDerivAt i).fderiv]
  rfl

theorem torus_band_divergence {T a b : ℝ} (hT : 0≤T) (hab : a≤b)
    {F : Coord3 → Coord3} (hF : ContDiff ℝ (↑(⊤:ℕ∞)) F) (hp : AngularPeriodic T F) :
    (∫ t in a..b,torusCellIntegral T (coordinateDivergence F) t)=
      torusCellIntegral T (fun x => F x 0) b-torusCellIntegral T (fun x => F x 0) a := by
  let A : Coord3 := ![a,0,0]
  let B : Coord3 := ![b,T,T]
  have hAB : A≤B := by intro i; fin_cases i; exact hab; exact hT; exact hT
  have hc := (coordinateDivergence_smooth hF).continuous
  have hfd := hF.differentiable (by simp)
  have hh := integral_divergence_of_hasFDerivAt_off_countable A B hAB F (fderiv ℝ F)
    ∅ countable_empty hF.continuous.continuousOn (fun x _ => (hfd x).hasFDerivAt)
    (by simpa only [←coordinateDivergence_eq_trace hfd] using (hc.continuousOn.integrableOn_compact
      (μ:=volume) (isCompact_Icc : IsCompact (Icc A B))))
  simp_rw [←coordinateDivergence_eq_trace hfd] at hh
  rw [integral_coord3_Icc hAB hc] at hh
  have h1 (q : Fin 2 → ℝ) : F ((1:Fin 3).insertNth T q) 1=F ((1:Fin 3).insertNth 0 q) 1 := by
    have he : ((1:Fin 3).insertNth 0 q)+angularShift T ![1,0]=(1:Fin 3).insertNth T q := by
      ext i; fin_cases i <;> simp [angularShift,Fin.insertNth,Fin.succAboveCases]
    have hh := hp ![1,0] ((1:Fin 3).insertNth 0 q)
    rw [he] at hh
    exact congrFun hh 1
  have h2 (q : Fin 2 → ℝ) : F ((2:Fin 3).insertNth T q) 2=F ((2:Fin 3).insertNth 0 q) 2 := by
    have he : ((2:Fin 3).insertNth 0 q)+angularShift T ![0,1]=(2:Fin 3).insertNth T q := by
      ext i; fin_cases i <;> simp [angularShift,Fin.insertNth,Fin.succAboveCases]
    have hh := hp ![0,1] ((2:Fin 3).insertNth 0 q)
    rw [he] at hh
    exact congrFun hh 2
  rw [Fin.sum_univ_succ] at hh
  simp only [Fin.sum_univ_two,Fin.succ_zero_eq_one,Fin.succ_one_eq_two] at hh
  simp only [A,B,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at hh
  simp_rw [h1,h2] at hh
  simp only [sub_self,add_zero] at hh
  have hf0 (c : ℝ) :
      (∫ q in Icc (A ∘ (0:Fin 3).succAbove) (B ∘ (0:Fin 3).succAbove),
        F ((0:Fin 3).insertNth c q) 0)=torusCellIntegral T (fun x => F x 0) c := by
    have hc0 : Continuous (fun q : Fin 2 → ℝ => F ((0:Fin 3).insertNth c q) 0) :=
      (continuous_apply 0).comp (hF.continuous.comp (by fun_prop))
    refine (integral_coord2_Icc (a:=A ∘ (0:Fin 3).succAbove) (b:=B ∘ (0:Fin 3).succAbove) (fun i => hAB ((0:Fin 3).succAbove i)) hc0).trans ?_
    change (∫ y in (0:ℝ)..T,∫ z in (0:ℝ)..T,F ((0:Fin 3).insertNth c ![y,z]) 0)=_
    apply intervalIntegral.integral_congr
    intro y _
    apply intervalIntegral.integral_congr
    intro z _
    have hi : (0:Fin 3).insertNth c ![y,z]=![c,y,z] := by
      ext i
      fin_cases i <;> simp [Fin.insertNth,Fin.succAboveCases]
    exact congrArg (fun x : Coord3 => F x 0) hi
  exact hh.trans (congrArg₂ (· - ·) (hf0 b) (hf0 a))

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory

lemma smooth_smul_of_support_in_open {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E→F} {ρ : E→ℝ} {S : Set E} (hS : IsOpen S)
    (hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f S) (hρ : ContDiff ℝ (↑(⊤:ℕ∞)) ρ)
    (hs : tsupport ρ⊆S) : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => ρ x • f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x∈tsupport ρ
  · exact hρ.contDiffAt.smul (hf.contDiffAt (hS.mem_nhds (hs hx)))
  · have he : (fun y => ρ y • f y)=ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma axial_band_smooth_extension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ a b T : ℝ} (ha : δ<a) {F : Coord3 → E}
    (hF : ContDiffOn ℝ (↑(⊤:ℕ∞)) F {x | δ<x 0}) (hp : AngularPeriodic T F) :
    ∃ G : Coord3 → E,ContDiff ℝ (↑(⊤:ℕ∞)) G ∧ AngularPeriodic T G ∧
      ∀ x : Coord3,x 0∈Icc a b → G=ᶠ[𝓝 x] F := by
  have hb : Bornology.IsBounded (Ioo δ (b+1)) :=
    (isCompact_Icc : IsCompact (Icc δ (b+1))).isBounded.subset Ioo_subset_Icc_self
  have hs : Icc a b⊆Ioo δ (b+1) := by
    intro t ht
    exact ⟨ha.trans_le ht.1,by linarith [ht.2]⟩
  obtain ⟨χ,hχ,hχc,hχs,hχb,hχ1⟩ := exists_smooth_core_cutoff
    (isCompact_Icc : IsCompact (Icc a b)) isOpen_Ioo hb hs
  let ρ : Coord3 → ℝ := fun x => χ (x 0)
  have hρ : ContDiff ℝ (↑(⊤:ℕ∞)) ρ := hχ.comp (contDiff_apply ℝ ℝ 0)
  have hρs : tsupport ρ⊆{x | δ<x 0} := by
    intro x hx
    exact (hχs (tsupport_comp_subset_preimage χ (f:=fun x : Coord3 => x 0) (continuous_apply 0) hx)).1
  refine ⟨fun x => ρ x • F x,smooth_smul_of_support_in_open
    (isOpen_lt continuous_const (continuous_apply 0)) hF hρ hρs,?_,?_⟩
  · intro n x
    change χ (x 0+0) • F (x+angularShift T n)=χ (x 0) • F x
    rw [add_zero,hp n x]
  · intro x hx
    have he : (fun y : Coord3 => χ (y 0))=ᶠ[𝓝 x] (fun _ => 1) :=
      (hχ1 (x 0) hx).comp_tendsto (continuous_apply 0).continuousAt
    filter_upwards [he] with y hy
    change χ (y 0) • F y=F y
    rw [hy,one_smul]

lemma coordinateDivergence_congr_nhds {F G : Coord3 → Coord3} {x : Coord3}
    (h : F=ᶠ[𝓝 x] G) : coordinateDivergence F x=coordinateDivergence G x := by
  unfold coordinateDivergence
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => F y i)=ᶠ[𝓝 x] (fun y => G y i) := h.mono (fun y hy => congrFun hy i)
  rw [he.fderiv_eq]

theorem torus_band_divergence_halfspace {δ T a b : ℝ} (ha : δ<a) (hT : 0≤T) (hab : a≤b)
    {F : Coord3 → Coord3} (hF : ContDiffOn ℝ (↑(⊤:ℕ∞)) F {x | δ<x 0})
    (hp : AngularPeriodic T F) :
    (∫ t in a..b,torusCellIntegral T (coordinateDivergence F) t)=
      torusCellIntegral T (fun x => F x 0) b-torusCellIntegral T (fun x => F x 0) a := by
  obtain ⟨G,hG,hGp,hGF⟩ := axial_band_smooth_extension ha hF hp (b:=b)
  have he (t : ℝ) (ht : t∈Icc a b) :
      torusCellIntegral T (coordinateDivergence G) t=torusCellIntegral T (coordinateDivergence F) t := by
    apply intervalIntegral.integral_congr
    intro y _
    apply intervalIntegral.integral_congr
    intro z _
    exact coordinateDivergence_congr_nhds (hGF ![t,y,z] ht)
  have heF (t : ℝ) (ht : t∈Icc a b) :
      torusCellIntegral T (fun x => G x 0) t=torusCellIntegral T (fun x => F x 0) t := by
    apply intervalIntegral.integral_congr
    intro y _
    apply intervalIntegral.integral_congr
    intro z _
    exact congrFun (hGF ![t,y,z] ht).self_of_nhds 0
  have hh := torus_band_divergence hT hab hG hGp
  have hl : (∫ t in a..b,torusCellIntegral T (coordinateDivergence G) t)=
      ∫ t in a..b,torusCellIntegral T (coordinateDivergence F) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact he t (by simpa only [uIcc_of_le hab] using ht)
  rw [hl,heF b (right_mem_Icc.mpr hab),heF a (left_mem_Icc.mpr hab)] at hh
  exact hh

lemma torus_flux_constant {δ T a b : ℝ} (ha : δ<a) (hT : 0≤T) (hab : a≤b)
    {F : Coord3 → Coord3} (hF : ContDiffOn ℝ (↑(⊤:ℕ∞)) F {x | δ<x 0})
    (hp : AngularPeriodic T F) (hd : ∀ x,δ<x 0 → coordinateDivergence F x=0) :
    torusCellIntegral T (fun x => F x 0) b=torusCellIntegral T (fun x => F x 0) a := by
  have hh := torus_band_divergence_halfspace ha hT hab hF hp
  have hz : (∫ t in a..b,torusCellIntegral T (coordinateDivergence F) t)=0 := by
    rw [←intervalIntegral.integral_zero (a:=a) (b:=b) (μ:=volume)]
    apply intervalIntegral.integral_congr
    intro t ht
    have hta : a≤t := (by simpa only [uIcc_of_le hab] using ht : t∈Icc a b).1
    have he (y z : ℝ) : coordinateDivergence F ![t,y,z]=0 := hd _ (ha.trans_le hta)
    simp only [torusCellIntegral,he,intervalIntegral.integral_zero]
  rw [hz] at hh
  linarith

lemma torus_flux_zero_of_tendsto {δ T a : ℝ} (ha : δ<a) (hT : 0≤T)
    {F : Coord3 → Coord3} (hF : ContDiffOn ℝ (↑(⊤:ℕ∞)) F {x | δ<x 0})
    (hp : AngularPeriodic T F) (hd : ∀ x,δ<x 0 → coordinateDivergence F x=0)
    (ht : Tendsto (fun t => torusCellIntegral T (fun x => F x 0) t) atTop (𝓝 0)) :
    torusCellIntegral T (fun x => F x 0) a=0 := by
  have he : (fun t => torusCellIntegral T (fun x => F x 0) t)=ᶠ[atTop]
      (fun _ => torusCellIntegral T (fun x => F x 0) a) := by
    filter_upwards [eventually_ge_atTop a] with b hab
    exact torus_flux_constant ha hT hab hF hp hd
  exact tendsto_nhds_unique tendsto_const_nhds (ht.congr' he)

end ScalarConductivity

end

end OAI
