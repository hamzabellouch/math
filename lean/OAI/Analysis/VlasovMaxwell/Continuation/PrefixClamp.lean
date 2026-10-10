import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.LabelOccupationDurationMass
import OAI.Analysis.VlasovMaxwell.Flow.PhaseAcceleration

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma PhaseFlowOn.flow_contDiffOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (z : Phase) :
    ContDiffOn ℝ 1 (F.flow z) (Ioo 0 T) := by
  have hf : ContinuousOn (F.flow z) (Ioo 0 T) := (F.continuousOn_time z).mono Ioo_subset_Icc_self
  have hp : ContinuousOn (fun t => (t,(F.flow z t).1)) (Ioo 0 T) := continuousOn_id.prodMk hf.fst
  have hE : ContinuousOn (fun t => s.E (t,(F.flow z t).1)) (Ioo 0 T) :=
    hs.E_smooth.continuousOn.comp hp (fun t ht => ⟨Ioo_subset_Icc_self ht,mem_univ _⟩)
  have hB : ContinuousOn (fun t => s.B (t,(F.flow z t).1)) (Ioo 0 T) :=
    hs.B_smooth.continuousOn.comp hp (fun t ht => ⟨Ioo_subset_Icc_self ht,mem_univ _⟩)
  have hu : ContinuousOn (fun t => velocity (F.flow z t).2) (Ioo 0 T) :=
    (contDiff_velocity (k:=1)).continuous.comp_continuousOn hf.snd
  have hK : ContinuousOn (fun t => s.E (t,(F.flow z t).1)+
      cross (velocity (F.flow z t).2) (s.B (t,(F.flow z t).1))) (Ioo 0 T) :=
    hE.add ((contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.prodMk hB))
  have hd (t : ℝ) (ht : t∈Ioo 0 T) := (F.ode z t (Ioo_subset_Icc_self ht)).mono Ioo_subset_Icc_self
  apply (contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn).mpr
  refine ⟨fun t ht => (hd t ht).differentiableWithinAt,?_⟩
  apply (hu.prodMk hK).congr
  intro t ht
  exact (hd t ht).derivWithin (isOpen_Ioo.uniqueDiffWithinAt ht)

lemma PhaseFlowOn.acceleration_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (z : Phase) :
    ContinuousOn (phaseAcceleration s.E s.B F.flow z) (Ioo 0 T) := by
  have hf : ContinuousOn (F.flow z) (Ioo 0 T) := (F.continuousOn_time z).mono Ioo_subset_Icc_self
  have hp : ContinuousOn (fun t => (t,(F.flow z t).1)) (Ioo 0 T) := continuousOn_id.prodMk hf.fst
  have hE : ContinuousOn (fun t => s.E (t,(F.flow z t).1)) (Ioo 0 T) :=
    hs.E_smooth.continuousOn.comp hp (fun t ht => ⟨Ioo_subset_Icc_self ht,mem_univ _⟩)
  have hB : ContinuousOn (fun t => s.B (t,(F.flow z t).1)) (Ioo 0 T) :=
    hs.B_smooth.continuousOn.comp hp (fun t ht => ⟨Ioo_subset_Icc_self ht,mem_univ _⟩)
  have hu : ContinuousOn (fun t => velocity (F.flow z t).2) (Ioo 0 T) :=
    (contDiff_velocity (k:=1)).continuous.comp_continuousOn hf.snd
  have hK : ContinuousOn (fun t => s.E (t,(F.flow z t).1)+
      cross (velocity (F.flow z t).2) (s.B (t,(F.flow z t).1))) (Ioo 0 T) :=
    hE.add ((contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.prodMk hB))
  exact (((contDiff_velocity (k:=1)).continuous_fderiv (by simp)).comp_continuousOn hf.snd).clm_apply hK

lemma PhaseFlowOn.actual_branch_regular {s : Solution} {T b c : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX zY : Phase)
    (hS : uIcc b c⊆branchDomain F.flow zX zY T)
    (hne : ∀ r∈uIcc b c, (F.flow zX r).1≠(F.flow zY r).1) :
    let τ := branchTime F.flow zX zY T
    ContDiffOn ℝ 1 (fun r => τ r-r) (uIcc b c) ∧
    ContDiffOn ℝ 1 (fun r => velocity (F.flow zX (τ r)).2) (uIcc b c) ∧
    ContDiffOn ℝ 1 (fun r => velocity (F.flow zY r).2) (uIcc b c) ∧
    ContDiffOn ℝ 1 (branchDirection F.flow zX zY T) (uIcc b c) ∧
    ContinuousOn (phaseAcceleration s.E s.B F.flow zY) (uIcc b c) ∧
    ContinuousOn (fun r => phaseAcceleration s.E s.B F.flow zX (τ r)) (uIcc b c) := by
  let τ := branchTime F.flow zX zY T
  have ht : ∀ r∈uIcc b c, τ r∈Ioo 0 T := by
    intro r hr
    have hh := F.branch_time_mem zX zY (hS hr) (hne r hr)
    exact ⟨(hS hr).1.1.trans hh.1,hh.2⟩
  have hsrc : uIcc b c⊆Ioo 0 T := fun r hr => (hS hr).1
  have hτ : ContDiffOn ℝ 1 τ (uIcc b c) := fun r hr =>
    (F.branch_differential zX zY (hS hr) (hne r hr)).1.contDiffWithinAt
  have hr : ContDiffOn ℝ 1 (fun r => τ r-r) (uIcc b c) := hτ.sub contDiffOn_id
  have hr0 : ∀ r∈uIcc b c, τ r-r≠0 := fun r hr =>
    (sub_pos.mpr (F.branch_time_mem zX zY (hS hr) (hne r hr)).1).ne'
  have hX := (F.flow_contDiffOn hs zX).comp hτ ht
  have hY := (F.flow_contDiffOn hs zY).mono hsrc
  refine ⟨hr,(contDiff_velocity (k:=1)).comp_contDiffOn hX.snd,
    (contDiff_velocity (k:=1)).comp_contDiffOn hY.snd,?_,
    (F.acceleration_continuousOn hs zY).mono hsrc,
    (F.acceleration_continuousOn hs zX).comp hτ.continuousOn ht⟩
  exact (hr.inv hr0).smul (hX.fst.sub hY.fst)

lemma PhaseFlowOn.actual_weighted_signed_identity {s : Solution} {T b c : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX zY : Phase)
    (hS : uIcc b c⊆branchDomain F.flow zX zY T)
    (hne : ∀ r∈uIcc b c, (F.flow zX r).1≠(F.flow zY r).1)
    {ψ : ℝ → ℝ} {W W' : ℝ → Vec →L[ℝ] Vec}
    (hψ : AbsolutelyContinuousOnInterval ψ b c)
    (hW : ContDiffOn ℝ 1 W (uIcc b c)) (hW' : ContinuousOn W' (uIcc b c))
    (hWd : ∀ r∈uIoo b c, HasDerivAt W (W' r) r) :
    let τ := branchTime F.flow zX zY T
    let r := fun σ => τ σ-σ
    let a := fun σ => velocity (F.flow zX (τ σ)).2
    let u := fun σ => velocity (F.flow zY σ).2
    let n := branchDirection F.flow zX zY T
    ∫ σ in b..c, ψ σ • W σ (signedForceKernel (r σ) (a σ) (u σ) (n σ)
        (phaseAcceleration s.E s.B F.flow zY σ)) =
      ψ b • W b (retardedPrimitive (r b) (a b) (u b) (n b)) -
      ψ c • W c (retardedPrimitive (r c) (a c) (u c) (n c)) +
      ∫ σ in b..c, deriv ψ σ • W σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ)) +
        ψ σ • (W' σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ)) +
          W σ (signedRemainder (r σ) (a σ) (u σ) (n σ)
            (phaseAcceleration s.E s.B F.flow zX (τ σ)))) := by
  dsimp only
  obtain ⟨hr,ha,hu,hn,hu',ha'⟩ := F.actual_branch_regular hs zX zY hS hne
  apply weighted_signed_identity_on_branch hψ hr ha hu hn hW hW' hu' ha'
  · intro r h
    exact (sub_pos.mpr (F.branch_time_mem zX zY (hS h) (hne r h)).1).ne'
  · intro r h
    exact (cone_denom_pos (F.flow zY r).2 _ (F.branchDirection_norm zX zY (hS h) (hne r h))).ne'
  · intro r h
    exact (cone_denom_pos (F.flow zX (branchTime F.flow zX zY T r)).2 _
      (F.branchDirection_norm zX zY (hS h) (hne r h))).ne'
  · intro r h
    exact (F.branch_differential zX zY (hS (Ioo_subset_Icc_self h))
      (hne r (Ioo_subset_Icc_self h))).2.sub (hasDerivAt_id r)
  · intro r h
    have hh := hS (Ioo_subset_Icc_self h)
    have ht := F.branch_time_mem zX zY hh (hne r (Ioo_subset_Icc_self h))
    exact (F.velocity_hasDerivAt zX ⟨hh.1.1.trans ht.1,ht.2⟩).scomp r
      (F.branch_differential zX zY hh (hne r (Ioo_subset_Icc_self h))).2
  · intro r h
    exact F.velocity_hasDerivAt zY (hS (Ioo_subset_Icc_self h)).1
  · intro r h
    exact F.branchDirection_hasDerivAt zX zY (hS (Ioo_subset_Icc_self h))
      (hne r (Ioo_subset_Icc_self h))
  · exact hWd

def prefixClamp (T t : ℝ) : ℝ := max 0 (min T t)

lemma prefixClamp_mem {T : ℝ} (hT : 0≤T) (t : ℝ) : prefixClamp T t∈Icc 0 T :=
  ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩

lemma prefixClamp_eq {T t : ℝ} (ht : t∈Icc 0 T) : prefixClamp T t=t := by
  simp [prefixClamp,min_eq_right ht.2,max_eq_right ht.1]

def prefixFlow (α : Phase → ℝ → Phase) (T : ℝ) (z : Phase) (t : ℝ) : Phase :=
  α z (prefixClamp T t)

lemma PhaseFlowOn.continuous_prefixFlow {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) :
    Continuous (fun p : ℝ × Phase => prefixFlow F.flow T p.2 p.1) := by
  apply (F.continuousOn_joint hT hs.E_smooth.continuousOn hs.B_smooth.continuousOn).comp_continuous
    ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
  intro p
  exact ⟨prefixClamp_mem hT p.1,mem_univ _⟩

structure ClosedConeBin where
  (rmin rmax qmin qmax wmin wmax dmin dmax Dmin Dmax emin emax : ℝ)

def InClosedConeBin (α : Phase → ℝ → Phase) (zX : Phase) (B : ClosedConeBin)
    (t r : ℝ) (z : Phase) : Prop :=
  let R := t-r
  let Δ := (α zX t).1-(α z r).1
  let u := velocity (α z r).2
  let a := velocity (α zX t).2
  R=‖Δ‖ ∧ R∈Icc B.rmin B.rmax ∧ q (α z r).2∈Icc B.qmin B.qmax ∧
    q (α zX t).2∈Icc B.wmin B.wmax ∧
    R-dot Δ u∈Icc (R*B.dmin) (R*B.dmax) ∧
    R-dot Δ a∈Icc (R*B.Dmin) (R*B.Dmax) ∧
    1-dot a u∈Icc B.emin B.emax

lemma inClosedConeBin_iff {α : Phase → ℝ → Phase} {zX z : Phase} {B : ClosedConeBin}
    {t r : ℝ} (hR : 0<t-r) :
    InClosedConeBin α zX B t r z ↔
      t-r=‖(α zX t).1-(α z r).1‖ ∧ t-r∈Icc B.rmin B.rmax ∧
      q (α z r).2∈Icc B.qmin B.qmax ∧ q (α zX t).2∈Icc B.wmin B.wmax ∧
      1-dot ((t-r)⁻¹ • ((α zX t).1-(α z r).1)) (velocity (α z r).2)∈Icc B.dmin B.dmax ∧
      1-dot ((t-r)⁻¹ • ((α zX t).1-(α z r).1)) (velocity (α zX t).2)∈Icc B.Dmin B.Dmax ∧
      1-dot (velocity (α zX t).2) (velocity (α z r).2)∈Icc B.emin B.emax := by
  have he (v : Vec) :
      1-dot ((t-r)⁻¹ • ((α zX t).1-(α z r).1)) v=
        ((t-r)-dot ((α zX t).1-(α z r).1) v)/(t-r) := by
    rw [dot_smul_left]
    field_simp
  simp only [InClosedConeBin,he,mem_Icc]
  rw [le_div_iff₀ hR,div_le_iff₀ hR,le_div_iff₀ hR,div_le_iff₀ hR]
  simp only [mul_comm]

lemma isClosed_inClosedConeBin {α : Phase → ℝ → Phase}
    (hα : Continuous (fun p : ℝ × Phase => α p.2 p.1)) (zX : Phase) (B : ClosedConeBin) :
    IsClosed {p : ℝ × ℝ × Phase | InClosedConeBin α zX B p.1 p.2.1 p.2.2} := by
  have hX := hα.comp (continuous_fst.prodMk continuous_const :
    Continuous (fun p : ℝ × ℝ × Phase => (p.1,zX)))
  have hY := hα.comp (continuous_snd.fst.prodMk continuous_snd.snd :
    Continuous (fun p : ℝ × ℝ × Phase => (p.2.1,p.2.2)))
  have hR : Continuous (fun p : ℝ × ℝ × Phase => p.1-p.2.1) := continuous_fst.sub continuous_snd.fst
  have hΔ := hX.fst.sub hY.fst
  have hu := (contDiff_velocity (k:=1)).continuous.comp hY.snd
  have ha := (contDiff_velocity (k:=1)).continuous.comp hX.snd
  have hd := hR.sub (continuous_dot.comp (hΔ.prodMk hu))
  have hD := hR.sub (continuous_dot.comp (hΔ.prodMk ha))
  have he := continuous_const.sub (continuous_dot.comp (ha.prodMk hu)) (f:=fun _ => (1:ℝ))
  have hq := (contDiff_q (k:=1)).continuous.comp hY.snd
  have hw := (contDiff_q (k:=1)).continuous.comp hX.snd
  exact (isClosed_eq hR hΔ.norm).inter
    ((isClosed_Icc.preimage hR).inter ((isClosed_Icc.preimage hq).inter
      ((isClosed_Icc.preimage hw).inter
        (((isClosed_le (hR.mul continuous_const) hd).inter (isClosed_le hd (hR.mul continuous_const))).inter
          (((isClosed_le (hR.mul continuous_const) hD).inter (isClosed_le hD (hR.mul continuous_const))).inter
            (isClosed_Icc.preimage he))))))

lemma PhaseFlowOn.compact_closed_bin_hit_labels {s : Solution} {T a b c d : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S) :
    IsCompact {z | z∈S ∧ ∃ t∈Icc 0 T, ∃ r∈Icc 0 T,
      t∈Icc a b ∧ r∈Icc c d ∧ InClosedConeBin F.flow zX B t r z} := by
  let H : Set (ℝ × ℝ × Phase) := {p | p.1∈Icc a b ∧ p.2.1∈Icc c d ∧
    InClosedConeBin (prefixFlow F.flow T) zX B p.1 p.2.1 p.2.2}
  have hH : IsClosed H := (isClosed_Icc.preimage continuous_fst).inter
    ((isClosed_Icc.preimage continuous_snd.fst).inter
      (isClosed_inClosedConeBin (F.continuous_prefixFlow hs hT) zX B))
  convert compact_hit_labels hS hH using 1
  ext z
  constructor
  · rintro ⟨hz,t,ht,r,hr,htJ,hrC,hbin⟩
    refine ⟨hz,t,ht,r,hr,htJ,hrC,?_⟩
    simpa only [InClosedConeBin,prefixFlow,prefixClamp_eq ht,prefixClamp_eq hr] using hbin
  · rintro ⟨hz,t,ht,r,hr,htJ,hrC,hbin⟩
    refine ⟨hz,t,ht,r,hr,htJ,hrC,?_⟩
    simpa only [InClosedConeBin,prefixFlow,prefixClamp_eq ht,prefixClamp_eq hr] using hbin

end RVM

end

end OAI
