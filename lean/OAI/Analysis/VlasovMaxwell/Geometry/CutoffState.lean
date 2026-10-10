import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.MomentumDirection
import OAI.Analysis.VlasovMaxwell.Retarded.RetardedRadiusSeparatedClosed

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
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma selectedDyadicCutoff_eventually {ι : Type*} [Fintype ι]
    {x : ι→ℝ} (hx : ∀ i,0<x i) (S : Set (ι→ℕ)) :
    ∃ N : ℕ, selectedDyadicCutoff S =ᶠ[𝓝 x]
      (fun y => ∑ n∈selectedDyadicBox N S,dyadicMultiFactor n y) := by
  classical
  have hp (i : ι) := pow_unbounded_of_one_lt (4/x i) (by norm_num : (1:ℝ)<2)
  choose Ns hNs using hp
  let N := ∑ i,Ns i
  have hN (i : ι) : 4<(2:ℝ)^N*x i := by
    have hNi : Ns i≤N := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    exact ((div_lt_iff₀ (hx i)).mp (hNs i)).trans_le
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hNi) (hx i).le)
  have he : ∀ᶠ y in 𝓝 x, ∀ i,x i/2<y i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (continuous_apply i).continuousAt.eventually (Ioi_mem_nhds (by linarith [hx i]))
  refine ⟨N,?_⟩
  filter_upwards [he] with y hy
  have hz : ∀ n : ι→ℕ,n∉dyadicBox ι N → dyadicMultiFactor n y=0 := by
    intro n hn
    have hb : ∃ i,N≤n i := by
      by_contra hb
      push Not at hb
      apply hn
      simpa only [dyadicBox,Fintype.mem_piFinset,Finset.mem_range] using hb
    obtain ⟨i,hi⟩ := hb
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply dyadicFactor_zero_large
    have hpN : 0<(2:ℝ)^N := by positivity
    have hpni : (2:ℝ)^N≤(2:ℝ)^(n i) := pow_le_pow_right₀ (by norm_num) hi
    have hyr : 0≤y i := le_of_lt ((by linarith [hx i] : 0<x i/2).trans (hy i))
    have hh := mul_le_mul_of_nonneg_right hpni hyr
    have hh' := mul_lt_mul_of_pos_left (hy i) hpN
    linarith [hN i]
  unfold selectedDyadicCutoff
  rw [tsum_eq_sum (s:=dyadicBox ι N) (fun n hn => ?_)]
  · simpa only [selectedDyadicBox,id_eq] using
      (Finset.sum_indicator_eq_sum_filter (dyadicBox ι N)
        (fun _ n => dyadicMultiFactor n y) (fun _ => S) id)
  · by_cases hs : n∈S
    · rw [indicator_of_mem hs,hz n hn]
    · exact indicator_of_notMem hs _

lemma contDiffAt_selectedDyadicCutoff {ι : Type*} [Fintype ι]
    {x : ι→ℝ} (hx : ∀ i,0<x i) (S : Set (ι→ℕ)) :
    ContDiffAt ℝ ∞ (selectedDyadicCutoff S) x := by
  classical
  obtain ⟨N,he⟩ := selectedDyadicCutoff_eventually hx S
  apply (ContDiffAt.sum (s:=selectedDyadicBox N S) (fun n _ => ?_)).congr_of_eventuallyEq he
  exact contDiffAt_prod (fun i _ => (contDiff_dyadicFactor (n i)).contDiffAt.comp x (contDiff_apply ℝ ℝ i).contDiffAt)

abbrev CutoffState := ℝ × Vec × Vec × Vec

def stateCutoff (T : ℝ) (Q : Set (Fin 4→ℕ)) (z : CutoffState) : ℝ :=
  selectedDyadicCutoff Q (physicalCutoffCoordinates T z.1 z.2.1 z.2.2.1 z.2.2.2)

lemma contDiffAt_stateCutoff (T : ℝ) (Q : Set (Fin 4→ℕ)) {z : CutoffState}
    (hr : 0<z.1) (hn : ‖z.2.1‖=1) : ContDiffAt ℝ ∞ (stateCutoff T Q) z := by
  have hc : ContDiffAt ℝ ∞ (fun z : CutoffState =>
      physicalCutoffCoordinates T z.1 z.2.1 z.2.2.1 z.2.2.2) z := by
    apply contDiffAt_pi.mpr
    intro i
    have hv : ContDiffAt ℝ ∞ (fun z : CutoffState=>velocity z.2.2.1) z :=
      (contDiff_velocity (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.fst
    have hw : ContDiffAt ℝ ∞ (fun z : CutoffState=>velocity z.2.2.2) z :=
      (contDiff_velocity (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.snd
    have hd := (contDiffAt_const (c:=(1:ℝ))).sub
      ((contDiff_dot_pair (k:=∞)).contDiffAt.comp z (contDiffAt_id.snd.fst.prodMk hv))
    have hD := (contDiffAt_const (c:=(1:ℝ))).sub
      ((contDiff_dot_pair (k:=∞)).contDiffAt.comp z (contDiffAt_id.snd.fst.prodMk hw))
    fin_cases i <;> simp only [physicalCutoffCoordinates]
    · exact contDiffAt_const.div ((contDiff_q (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.fst) (q_pos _).ne'
    · exact (hd.div_const 2).sqrt (div_pos (cone_denom_pos _ _ hn) (by norm_num)).ne'
    · exact (hD.div_const 2).sqrt (div_pos (cone_denom_pos _ _ hn) (by norm_num)).ne'
    · exact contDiffAt_id.fst.div_const _
  exact (contDiffAt_selectedDyadicCutoff (physicalCutoffCoordinates_pos hn hr) Q).comp z hc

lemma stateCutoff_closed_regularity {T a b : ℝ} (Q : Set (Fin 4→ℕ))
    {z z' : ℝ→CutoffState} (hz : ContinuousOn z (Icc a b))
    (hz' : ContinuousOn z' (Icc a b))
    (hr : ∀ t∈Icc a b,0<(z t).1) (hn : ∀ t∈Icc a b,‖(z t).2.1‖=1)
    (hd : ∀ t∈Ioo a b,HasDerivAt z (z' t) t) :
    ContinuousOn (fun t=>stateCutoff T Q (z t)) (Icc a b) ∧
    ContinuousOn (fun t=>fderiv ℝ (stateCutoff T Q) (z t) (z' t)) (Icc a b) ∧
    ∀ t∈Ioo a b,HasDerivAt (fun t=>stateCutoff T Q (z t))
      (fderiv ℝ (stateCutoff T Q) (z t) (z' t)) t := by
  have hsc t (ht : t∈Icc a b) := contDiffAt_stateCutoff T Q (hr t ht) (hn t ht)
  refine ⟨fun t ht => (hsc t ht).continuousAt.comp_continuousWithinAt (hz t ht),?_,?_⟩
  · apply ContinuousOn.clm_apply _ hz'
    intro t ht
    exact ((hsc t ht).continuousAt_fderiv (by simp)).comp_continuousWithinAt (hz t ht)
  · intro t ht
    exact ((hsc t (Ioo_subset_Icc_self ht)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hd t ht)

def branchCutoffState (α : Phase→ℝ→Phase) (T : ℝ) (zX zY : Phase) (σ : ℝ) : CutoffState :=
  (branchTime α zX zY T σ-σ,branchDirection α zX zY T σ,
    (α zY σ).2,(α zX (branchTime α zX zY T σ)).2)

def branchCutoffStateRate (E B : Field) (α : Phase→ℝ→Phase) (T : ℝ)
    (zX zY : Phase) (σ : ℝ) : CutoffState :=
  let τ := branchTime α zX zY T σ
  let n := branchDirection α zX zY T σ
  let ρ := branchRate α zX zY T σ
  (ρ-1,(τ-σ)⁻¹ • coneMotion (velocity (α zX τ).2) (velocity (α zY σ).2) n,
    (lorentzField E B (σ,α zY σ)).2,ρ • (lorentzField E B (τ,α zX τ)).2)

lemma PhaseFlowOn.branchCutoffState_hasDerivAt {E B : Field} {T σ : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase)
    (hσ : σ∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) :
    HasDerivAt (branchCutoffState F.flow T zX zY)
      (branchCutoffStateRate E B F.flow T zX zY σ) σ := by
  have hτ := (F.branch_differential zX zY hσ hne).2
  have hY := ((F.ode zY σ (Ioo_subset_Icc_self hσ.1)).hasDerivAt
    (Icc_mem_nhds hσ.1.1 hσ.1.2)).snd
  exact (hτ.sub (hasDerivAt_id σ)).prodMk
    ((F.branchDirection_hasDerivAt zX zY hσ hne).prodMk
      (hY.prodMk (F.retardedMomentum_hasDerivAt zX zY hσ hne)))

lemma PhaseFlowOn.momentumForce_continuousOn_closed {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (z : Phase) :
    ContinuousOn (fun t=>(lorentzField s.E s.B (t,F.flow z t)).2) (Icc 0 T) := by
  have hf := F.continuousOn_time z
  have hp : ContinuousOn (fun t => (t,(F.flow z t).1)) (Icc 0 T) := continuousOn_id.prodMk hf.fst
  have hE : ContinuousOn (fun t => s.E (t,(F.flow z t).1)) (Icc 0 T) :=
    hs.E_smooth.continuousOn.comp hp (fun t ht => ⟨ht,mem_univ _⟩)
  have hB : ContinuousOn (fun t => s.B (t,(F.flow z t).1)) (Icc 0 T) :=
    hs.B_smooth.continuousOn.comp hp (fun t ht => ⟨ht,mem_univ _⟩)
  have hu : ContinuousOn (fun t => velocity (F.flow z t).2) (Icc 0 T) :=
    (contDiff_velocity (k:=1)).continuous.comp_continuousOn hf.snd
  exact hE.add ((contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.prodMk hB))

lemma PhaseFlowOn.branchCutoffState_closed_regularity {s : Solution} {T b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX zY : Phase)
    (hb : b∈Icc 0 T) (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T)
    (hne : ∀ σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow zY σ).1) :
    ContinuousOn (branchCutoffState F.flow T zX zY) (Icc 0 b) ∧
    ContinuousOn (branchCutoffStateRate s.E s.B F.flow T zX zY) (Icc 0 b) ∧
    (∀ σ∈Icc 0 b,0<(branchCutoffState F.flow T zX zY σ).1) ∧
    (∀ σ∈Icc 0 b,‖(branchCutoffState F.flow T zX zY σ).2.1‖=1) := by
  let τ := branchTime F.flow zX zY T
  let r := fun σ=>τ σ-σ
  let a := fun σ=>velocity (F.flow zX (τ σ)).2
  let u := fun σ=>velocity (F.flow zY σ).2
  let n := branchDirection F.flow zX zY T
  have hT : 0≤T := hb.1.trans hb.2
  have hsub : Icc 0 b⊆Icc 0 T := fun _ hx=>⟨hx.1,hx.2.trans hb.2⟩
  have hclosed := F.closedBranchDomain_eq hT zX zY hb he
  have hmem : ∀ σ∈Icc 0 b,σ∈closedBranchDomain F.flow zX zY T := by
    intro σ hσ
    rwa [hclosed]
  have htmem : ∀ σ∈Icc 0 b,τ σ∈Icc 0 T := fun σ hσ=>
    ⟨hσ.1.trans (F.branch_spec_closed zX zY (hmem σ hσ)).1.1,
      (F.branch_spec_closed zX zY (hmem σ hσ)).1.2⟩
  have hτ : ContinuousOn τ (Icc 0 b) := by
    obtain ⟨C,hC⟩ := F.branch_lipschitzOn_closed hT zX zY
    simpa only [hclosed] using hC.continuousOn
  have hr : ContinuousOn r (Icc 0 b) := hτ.sub continuousOn_id
  have hX := (F.continuousOn_time zX).comp hτ htmem
  have hY := (F.continuousOn_time zY).mono hsub
  have ha : ContinuousOn a (Icc 0 b) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn hX.snd
  have hu : ContinuousOn u (Icc 0 b) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn hY.snd
  have hrp : ∀ σ∈Icc 0 b,0<r σ := fun σ hσ=>
    F.branch_radius_pos_closed zX zY (hmem σ hσ) (hne σ (hsub hσ))
  have hn : ContinuousOn n (Icc 0 b) := (hr.inv₀ (fun σ hσ=>(hrp σ hσ).ne')).smul (hX.fst.sub hY.fst)
  have hnorm : ∀ σ∈Icc 0 b,‖n σ‖=1 := fun σ hσ=>
    F.branchDirection_norm_closed zX zY (hmem σ hσ) (hne σ (hsub hσ))
  have hd : ContinuousOn (fun σ=>1-dot (n σ) (u σ)) (Icc 0 b) := by
    simp only [dot_eq_inner]
    exact (continuousOn_const (c:=(1:ℝ))).sub (hn.inner hu)
  have hD : ContinuousOn (fun σ=>1-dot (n σ) (a σ)) (Icc 0 b) := by
    simp only [dot_eq_inner]
    exact (continuousOn_const (c:=(1:ℝ))).sub (hn.inner ha)
  have hρ : ContinuousOn (branchRate F.flow zX zY T) (Icc 0 b) :=
    hd.div hD (fun σ hσ=>(cone_denom_pos _ _ (hnorm σ hσ)).ne')
  have hN : ContinuousOn (fun σ=>(r σ)⁻¹ • coneMotion (a σ) (u σ) (n σ)) (Icc 0 b) :=
    (hr.inv₀ (fun σ hσ=>(hrp σ hσ).ne')).smul
      (((hρ.smul (ha.sub hn)).add hn).sub hu)
  have hKY := (F.momentumForce_continuousOn_closed hs zY).mono hsub
  have hKX := (F.momentumForce_continuousOn_closed hs zX).comp hτ htmem
  exact ⟨hr.prodMk (hn.prodMk (hY.snd.prodMk hX.snd)),
    (hρ.sub continuousOn_const).prodMk (hN.prodMk (hKY.prodMk (hρ.smul hKX))),hrp,hnorm⟩

def branchSelectedRate (E B : Field) (α : Phase→ℝ→Phase) (T : ℝ)
    (zX zY : Phase) (Q : Set (Fin 4→ℕ)) (σ : ℝ) : ℝ :=
  fderiv ℝ (stateCutoff T Q) (branchCutoffState α T zX zY σ)
    (branchCutoffStateRate E B α T zX zY σ)

lemma PhaseFlowOn.actual_selected_closed_regularity {s : Solution} {T b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX zY : Phase)
    (hb : b∈Icc 0 T) (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T)
    (hne : ∀ σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow zY σ).1) (Q : Set (Fin 4→ℕ)) :
    let χ := fun σ=>selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX zY σ)
    let χ' := branchSelectedRate s.E s.B F.flow T zX zY Q
    ContinuousOn χ (Icc 0 b) ∧ ContinuousOn χ' (Icc 0 b) ∧
      ∀ σ∈Ioo 0 b,HasDerivAt χ (χ' σ) σ := by
  obtain ⟨hz,hz',hr,hn⟩ := F.branchCutoffState_closed_regularity hs zX zY hb he hne
  apply stateCutoff_closed_regularity Q hz hz' hr hn
  intro σ hσ
  have hdom : σ∈branchDomain F.flow zX zY T := by
    rwa [F.branchDomain_eq (hb.1.trans hb.2) zX zY hb he]
  exact F.branchCutoffState_hasDerivAt zX zY hdom (hne σ ⟨hσ.1.le,hσ.2.le.trans hb.2⟩)

lemma PhaseFlowOn.actual_selected_temporal_signed_formula {s : Solution} {T b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (zX zY : Phase) (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T)
    (hne : ∀ σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow zY σ).1)
    (Q : Set (Fin 4→ℕ))
    {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzOnWith L ψ (Icc 0 T)) (hψT : ψ T=0)
    {W W' : ℝ→Vec→L[ℝ]Vec}
    (hW : ContinuousOn W (Icc 0 b)) (hW' : ContinuousOn W' (Icc 0 b))
    (hWd : ∀ σ∈Ioo 0 b,HasDerivAt W (W' σ) σ) :
    let χ := fun σ=>selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX zY σ)
    let χ' := branchSelectedRate s.E s.B F.flow T zX zY Q
    let τ := branchTime F.flow zX zY T
    let r := fun σ=>τ σ-σ
    let a := fun σ=>velocity (F.flow zX (τ σ)).2
    let u := fun σ=>velocity (F.flow zY σ).2
    let n := branchDirection F.flow zX zY T
    ∫ σ in 0..b,(ψ (τ σ)*χ σ) • W σ
      (signedForceKernel (r σ) (a σ) (u σ) (n σ) (phaseAcceleration s.E s.B F.flow zY σ)) =
      (ψ (τ 0)*χ 0) • W 0 (retardedPrimitive (r 0) (a 0) (u 0) (n 0))+
      ∫ σ in 0..b,(deriv ψ (τ σ)*branchRate F.flow zX zY T σ*χ σ+ψ (τ σ)*χ' σ) •
        W σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ))+
        (ψ (τ σ)*χ σ) • (W' σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ))+
          W σ (signedRemainder (r σ) (a σ) (u σ) (n σ)
            (phaseAcceleration s.E s.B F.flow zX (τ σ)))) := by
  obtain ⟨hχ,hχ',hχd⟩ := F.actual_selected_closed_regularity hs zX zY hb he hne Q
  have h := F.actual_temporal_signed_formula hs zX zY hb he hne hψ hψT
    (hχ.smul hW) ((hχ.smul hW').add (hχ'.smul hW))
    (fun σ hσ=>(hχd σ hσ).smul (hWd σ hσ))
  dsimp only at h ⊢
  simp only [Pi.smul_apply',Pi.add_apply,smul_apply,smul_smul,add_apply,smul_add,add_smul] at h ⊢
  convert h using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro σ hσ
  abel_nf

end RVM

end

end OAI
