import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.ArrivalDomain

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
open scoped Topology ContDiff NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal RealInnerProductSpace

namespace RVM

lemma stable_positive_projection {v w : Vec} {c : ℝ} (hc : 0<c)
    (hv : c≤‖v‖) (hw : ‖w-v‖≤c/2) :
    c/2 ≤ dot (‖v‖⁻¹ • v) w := by
  have hv0 : 0<‖v‖ := hc.trans_le hv
  have he : ‖‖v‖⁻¹ • v‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hv0),inv_mul_cancel₀ hv0.ne']
  have hdot : dot (‖v‖⁻¹ • v) v=‖v‖ := by
    rw [dot_smul_left,dot_self]
    field_simp
  have hh := dot_le_norm (‖v‖⁻¹ • v) (v-w)
  rw [he,one_mul,norm_sub_rev,dot_sub_right,hdot] at hh
  linarith

lemma PhaseFlowOn.label_energy_bound {s : Solution} {T t : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (ht : t ∈ Icc 0 T) :
    (∫⁻ z : Phase, ENNReal.ofReal (q (F.flow z t).2) * ENNReal.ofReal (s.f (0,z))) ≤
      ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
  calc
    _ = ∫⁻ z : Phase, ENNReal.ofReal (q (F.flow z t).2 * s.f (t,F.flow z t)) := by
      apply lintegral_congr
      intro z
      rw [F.transport hs.f_smooth hs.vlasov ht,ENNReal.ofReal_mul (q_pos _).le]
    _ = ∫⁻ z : Phase, ENNReal.ofReal (q z.2 * s.f (t,z)) := by
      exact F.lintegral_comp ht (fun z => ENNReal.ofReal (q z.2 * s.f (t,z)))
    _ ≤ _ := hs.phase_energy_bound ht

lemma PhaseFlowOn.label_occupation_cell_bound {s : Solution} {T t p D : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (ht : t ∈ Icc 0 T)
    {H : Phase → Set ℝ}
    (hduration : ∀ z, volume (H z) ≤ ENNReal.ofReal D)
    (hmom : ∀ z, (H z).Nonempty → p≤q (F.flow z t).2) :
    ENNReal.ofReal p * labelOccupation (fun z => s.f (0,z)) H ≤
      ENNReal.ofReal D * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
  unfold labelOccupation
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ∫⁻ z : Phase, ENNReal.ofReal D *
        (ENNReal.ofReal (q (F.flow z t).2) * ENNReal.ofReal (s.f (0,z))) := by
      apply lintegral_mono
      intro z
      by_cases hh : (H z).Nonempty
      · have hd := mul_le_mul' (ENNReal.ofReal_le_ofReal (hmom z hh)) (hduration z)
        have hh := mul_le_mul_right hd (ENNReal.ofReal (s.f (0,z)))
        simpa only [mul_assoc,mul_left_comm,mul_comm] using hh
      · have hz : H z=∅ := not_nonempty_iff_eq_empty.mp hh
        simp only [hz,measure_empty,mul_zero,zero_le]
    _ = ENNReal.ofReal D * ∫⁻ z : Phase,
        ENNReal.ofReal (q (F.flow z t).2) * ENNReal.ofReal (s.f (0,z)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_right (F.label_energy_bound hs ht) _

lemma stable_cell_duration {X Y a u : ℝ → Vec} {C H : Set ℝ} {v : Vec} {c R : ℝ}
    (hC : Convex ℝ C) (hHC : H ⊆ C) (hc : 0<c) (hv : c≤‖v‖)
    (hXc : ContinuousOn X C) (hYc : ContinuousOn Y C)
    (hX : ∀ r ∈ interior C, HasDerivAt X (a r) r)
    (hY : ∀ r ∈ interior C, HasDerivAt Y (u r) r)
    (hvel : ∀ r ∈ interior C, ‖u r-a r-v‖≤c/2)
    (hsep : ∀ r ∈ H, ‖Y r-X r‖≤R) :
    volume H ≤ ENNReal.ofReal (4*R/c) := by
  have he : ‖‖v‖⁻¹ • v‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hc.trans_le hv)),
      inv_mul_cancel₀ (hc.trans_le hv).ne']
  have hh := projected_hit_duration (e:=‖v‖⁻¹ • v) hC hHC (half_pos hc)
    hXc hYc hX hY (fun r hr => stable_positive_projection hc hv (hvel r hr))
    (fun r hr => by
      rw [dot_eq_inner]
      exact (abs_real_inner_le_norm (‖v‖⁻¹ • v) (Y r-X r)).trans (by
        simpa only [he,one_mul] using hsep r hr))
  have hid : 2*R/(c/2)=4*R/c := by ring
  simpa only [hid] using hh

lemma PhaseFlowOn.stable_cell_occupation {s : Solution} {T t p c R : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (ht : t ∈ Icc 0 T)
    (zX : Phase) {C : Set ℝ} {H : Phase → Set ℝ} {v : Phase → Vec}
    (hC : Convex ℝ C) (hCT : C ⊆ Icc 0 T) (hc : 0<c)
    (hHC : ∀ z, H z ⊆ C) (hv : ∀ z, c≤‖v z‖)
    (hvel : ∀ z r, r ∈ interior C →
      ‖velocity (F.flow z r).2-velocity (F.flow zX r).2-v z‖≤c/2)
    (hsep : ∀ z r, r ∈ H z → ‖(F.flow z r).1-(F.flow zX r).1‖≤R)
    (hmom : ∀ z, (H z).Nonempty → p≤q (F.flow z t).2) :
    ENNReal.ofReal p * labelOccupation (fun z => s.f (0,z)) H ≤
      ENNReal.ofReal (4*R/c) * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
  apply F.label_occupation_cell_bound hs ht _ hmom
  intro z
  apply stable_cell_duration hC (hHC z) hc (hv z)
    ((F.continuousOn_time zX).fst.mono hCT) ((F.continuousOn_time z).fst.mono hCT)
    _ _ (hvel z) (hsep z)
  · intro r hr
    exact ((F.ode zX r (hCT (interior_subset hr))).mono hCT).hasDerivAt
      (mem_interior_iff_mem_nhds.mp hr) |>.fst
  · intro r hr
    exact ((F.ode z r (hCT (interior_subset hr))).mono hCT).hasDerivAt
      (mem_interior_iff_mem_nhds.mp hr) |>.fst

def observationCone (Y : ℝ → Vec) (z : (ℝ × Vec) × ℝ) : ℝ :=
  (z.1.1-z.2)^2-‖z.1.2-Y z.2‖^2

lemma contDiffAt_observationCone {Y : ℝ → Vec} {p : ℝ × Vec} {s : ℝ}
    (hY : ContDiffAt ℝ 1 Y s) : ContDiffAt ℝ 1 (observationCone Y) (p,s) := by
  exact ((contDiffAt_fst.fst.sub contDiffAt_snd).pow 2).sub
    ((contDiffAt_fst.snd.sub (hY.comp (p,s) contDiffAt_snd)).norm_sq ℝ)

lemma hasDerivAt_observationCone_source {Y : ℝ → Vec} {p : ℝ × Vec} {s : ℝ} {u : Vec}
    (hY : HasDerivAt Y u s) :
    HasDerivAt (fun r => observationCone Y (p,r))
      (-2*(p.1-s)+2*dot (p.2-Y s) u) s := by
  have hh := (((hasDerivAt_const s p.1).sub (hasDerivAt_id s)).pow 2).sub
    (((hasDerivAt_const s p.2).sub hY).norm_sq)
  convert hh using 1 <;> try rfl
  simp [dot_eq_inner]

lemma observationCone_source_partial {Y : ℝ → Vec} {p : ℝ × Vec} {s : ℝ} {u : Vec}
    (hY : ContDiffAt ℝ 1 Y s) (hYd : HasDerivAt Y u s) :
    ((fderiv ℝ (observationCone Y) (p,s)).comp
      (ContinuousLinearMap.inr ℝ (ℝ × Vec) ℝ)) 1 =
        -2*(p.1-s)+2*dot (p.2-Y s) u := by
  have hi : HasFDerivAt (fun r : ℝ => (p,r))
      (ContinuousLinearMap.inr ℝ (ℝ × Vec) ℝ) s := by
    convert (hasFDerivAt_const p s).prodMk (hasFDerivAt_id s) using 1 <;> rfl
  exact (((contDiffAt_observationCone hY).differentiableAt one_ne_zero).hasFDerivAt.comp s hi).hasDerivAt.unique
    (hasDerivAt_observationCone_source hYd)

lemma exists_local_emission_branch {Y : ℝ → Vec} {p : ℝ × Vec} {s : ℝ} {u : Vec}
    (hst : s<p.1) (hcone : p.1-s=‖p.2-Y s‖)
    (hY : ContDiffAt ℝ 1 Y s) (hYd : HasDerivAt Y u s) (hu : ‖u‖<1) :
    ∃ τ : ℝ × Vec → ℝ, τ p=s ∧ ContDiffAt ℝ 1 τ p ∧
      ∀ᶠ z in 𝓝 p, τ z<z.1 ∧ z.1-τ z=‖z.2-Y (τ z)‖ := by
  have hF := contDiffAt_observationCone (p:=p) hY
  have hbound := dot_le_norm (p.2-Y s) u
  rw [← hcone] at hbound
  have hneg : -2*(p.1-s)+2*dot (p.2-Y s) u<0 := by
    have hh := mul_pos (sub_pos.mpr hst) (sub_pos.mpr hu)
    nlinarith
  have hinv : ((fderiv ℝ (observationCone Y) (p,s)).comp
      (ContinuousLinearMap.inr ℝ (ℝ × Vec) ℝ)).IsInvertible := by
    apply scalar_clm_invertible
    rw [observationCone_source_partial hY hYd]
    exact hneg.ne
  let τ := hF.implicitFunction one_ne_zero hinv
  have hτ : τ p=s := hF.implicitFunction_apply_self one_ne_zero hinv
  have hc : ContDiffAt ℝ 1 τ p := hF.contDiffAt_implicitFunction one_ne_zero hinv
  refine ⟨τ,hτ,hc,?_⟩
  have hpos : 0<p.1-τ p := by rw [hτ]; exact sub_pos.mpr hst
  have he : ∀ᶠ z in 𝓝 p, 0<z.1-τ z :=
    (continuousAt_fst.sub hc.continuousAt) (isOpen_Ioi.mem_nhds hpos)
  filter_upwards [hF.eventually_apply_implicitFunction one_ne_zero hinv,he] with z hz hzpos
  refine ⟨by linarith,?_⟩
  change (z.1-τ z)^2-‖z.2-Y (τ z)‖^2=(p.1-s)^2-‖p.2-Y s‖^2 at hz
  rw [hcone,sub_self] at hz
  nlinarith [norm_nonneg (z.2-Y (τ z))]

lemma emission_branch_fderiv {Y : ℝ → Vec} {τ : ℝ × Vec → ℝ}
    {p : ℝ × Vec} {s : ℝ} {u n : Vec}
    (hτ : τ p=s) (hτd : DifferentiableAt ℝ τ p) (hY : HasDerivAt Y u s)
    (hst : s<p.1) (hgeom : p.2-Y s=(p.1-s) • n)
    (hd : 1-dot n u≠0)
    (he : ∀ᶠ z in 𝓝 p, z.1-τ z=‖z.2-Y (τ z)‖) (e : ℝ × Vec) :
    fderiv ℝ τ p e = (e.1-dot n e.2)/(1-dot n u) := by
  have hYs : HasDerivAt Y u (τ p) := by rwa [hτ]
  have hy := hYs.hasFDerivAt.comp p hτd.hasFDerivAt
  have hf : HasFDerivAt (fun z : ℝ × Vec => z.1)
      (ContinuousLinearMap.fst ℝ ℝ Vec) p := hasFDerivAt_fst
  have hs : HasFDerivAt (fun z : ℝ × Vec => z.2)
      (ContinuousLinearMap.snd ℝ ℝ Vec) p := hasFDerivAt_snd
  have hh := ((hf.sub hτd.hasFDerivAt).pow 2).sub ((hs.sub hy).norm_sq)
  have he0 : (fun z : ℝ × Vec => (z.1-τ z)^2-‖z.2-Y (τ z)‖^2) =ᶠ[𝓝 p] fun _ => (0:ℝ) := by
    filter_upwards [he] with z hz
    rw [hz,sub_self]
  have hz := (hasFDerivAt_const (𝕜:=ℝ) (0:ℝ) p).congr_of_eventuallyEq he0
  have hid := congrArg (fun L : (ℝ × Vec) →L[ℝ] ℝ => L e) (hh.unique hz)
  have hid' : 2*(p.1-s)*(e.1-fderiv ℝ τ p e) -
      2*((p.1-s)*dot n e.2-(fderiv ℝ τ p e)*((p.1-s)*dot n u))=0 := by
    simpa [hτ,hgeom,dot_eq_inner,mul_left_comm,mul_assoc] using hid
  have hr : p.1-s≠0 := (sub_pos.mpr hst).ne'
  apply (eq_div_iff hd).mpr
  have hh : (p.1-s)*((fderiv ℝ τ p e)*(1-dot n u)-(e.1-dot n e.2))=0 := by
    nlinarith [hid']
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hr)

end RVM

end

end OAI
