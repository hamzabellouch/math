import Mathlib
import OAI.Analysis.Conductivity.Scalarization.PhysicalScalarization
import OAI.Analysis.Conductivity.Sources.PhysicalGradient
import OAI.Analysis.Conductivity.Sources.PhysicalRoot
import OAI.Analysis.Conductivity.Variational.PhysicalTraceMean

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma le_of_transition_energy_zero (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0≤C) (hb : ∀ᵐ x∂ballMeasure,|a x|≤C)
    (hp : ∀ᵐ x∂ballMeasure,0<a x) {u : H1} (hu : u∈H10) {M : ℝ} (hM : 0≤M)
    (he : (∫ x,a x*inner ℝ (weakGradient u x)
      (weakGradient ((upperTransition M hM).onH1 u) x) ∂ballMeasure)=0) :
    ∀ᵐ x∂ballMeasure,weakValue u x≤M := by
  let F := upperTransition M hM
  have hh0 : F.onH1 u∈H10 := F.preserves_H10 hu
  have hg := F.onH1_gradient u
  have hnonneg : 0 ≤ᵐ[ballMeasure] fun x => a x*inner ℝ (weakGradient u x) (weakGradient (F.onH1 u) x) := by
    filter_upwards [hp,hg] with x ha hx
    rw [hx,real_inner_smul_right]
    exact mul_nonneg ha.le (mul_nonneg (upperTransition_deriv_nonneg M hM _) real_inner_self_nonneg)
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg
    (energy_integrable a ha C hC hb u (F.onH1 u))).mp he
  have hhg : weakGradient (F.onH1 u) =ᵐ[ballMeasure] 0 := by
    filter_upwards [hp,hg,hzero] with x ha hx hz
    rw [hx,real_inner_smul_right] at hz
    have hh : deriv F (weakValue u x)*inner ℝ (weakGradient u x) (weakGradient u x)=0 :=
      (mul_eq_zero.mp hz).resolve_left ha.ne'
    rcases mul_eq_zero.mp hh with hd | hd
    · rw [hx,hd,zero_smul]; rfl
    · rw [hx,inner_self_eq_zero.mp hd,smul_zero]; rfl
  have hF0 := zero_of_weakGradient_zero hh0 hhg
  have hval := F.onH1_value u
  filter_upwards [hval,Lp.coeFn_zero JetFiber 2 ballMeasure] with x hx hz
  apply (upperTransition_zero_iff M hM _).mp
  rw [←hx,hF0]
  change jetValue ((0:JetSpace) x)=0
  rw [hz]; rfl

theorem physical_source_le (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0≤C) (hb : ∀ᵐ x∂ballMeasure,|a x|≤C)
    (hp : ∀ᵐ x∂ballMeasure,0<a x) {u : H1} (hu : u∈H10) (κ : Fin 3 → ℝ)
    (hg : ∀ h : H1,(∫ x,a x*inner ℝ (weakGradient u x) (weakGradient h x) ∂ballMeasure)=
      constantTerminalFluxCLM κ h) {M : ℝ} (hM : 0≤M)
    (ht : ∀ i : Fin 3,∀ᵐ θ,physicalRealTraceCLM i u θ≤M) :
    ∀ᵐ x∂ballMeasure,weakValue u x≤M := by
  apply le_of_transition_energy_zero a ha C hC hb hp hu hM
  rw [hg,constantTerminalFlux_zero_of_realTrace κ _ (physicalRealTrace_transition_zero u hM ht)]

 theorem physical_source_bounded (a : R3 → ℝ) (ha : AEStronglyMeasurable a ballMeasure)
    (C : ℝ) (hC : 0≤C) (hb : ∀ᵐ x∂ballMeasure,|a x|≤C)
    (hp : ∀ᵐ x∂ballMeasure,0<a x) {u : H1} (hu : u∈H10) (κ : Fin 3 → ℝ)
    (hg : ∀ h : H1,(∫ x,a x*inner ℝ (weakGradient u x) (weakGradient h x) ∂ballMeasure)=
      constantTerminalFluxCLM κ h) {M : ℝ} (hM : 0≤M)
    (ht : ∀ i : Fin 3,∀ᵐ θ,|physicalRealTraceCLM i u θ|≤M) :
    ∀ᵐ x∂ballMeasure,|weakValue u x|≤M := by
  have hup := physical_source_le a ha C hC hb hp hu κ hg hM
    (fun i => (ht i).mono (fun _ h => (abs_le.mp h).2))
  have hneg : (∫ x,a x*inner ℝ (weakGradient (-u) x)
      (weakGradient ((upperTransition M hM).onH1 (-u)) x) ∂ballMeasure)=0 := by
    change energy a (-u) ((upperTransition M hM).onH1 (-u))=0
    rw [←energyForm_apply a ha C hC hb,map_neg,neg_apply,energyForm_apply a ha C hC hb]
    change -(∫ x,a x*inner ℝ (weakGradient u x) (weakGradient ((upperTransition M hM).onH1 (-u)) x) ∂ballMeasure)=0
    rw [hg]
    have htneg : ∀ i : Fin 3,∀ᵐ θ,physicalRealTraceCLM i (-u) θ≤M := by
      intro i
      rw [map_neg]
      filter_upwards [ht i,Lp.coeFn_neg (physicalRealTraceCLM i u)] with θ ht hn
      rw [hn]
      exact (neg_le_iff_add_nonneg).mpr (by linarith [(abs_le.mp ht).1])
    rw [constantTerminalFlux_zero_of_realTrace κ _ (physicalRealTrace_transition_zero (-u) hM htneg),neg_zero]
  have hlo := le_of_transition_energy_zero a ha C hC hb hp (H10.neg_mem hu) hM hneg
  filter_upwards [hup,hlo,weakValue_neg u] with x hx hy hz
  rw [hz,Pi.neg_apply] at hy
  exact abs_le.mpr ⟨by linarith,hx⟩

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix UnitAddTorus
attribute [local instance] Classical.propDecidable
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

structure BoundedRootSources where
  b : Coord3 → ℝ
  measurable_b : Measurable b
  c : ℝ
  C : ℝ
  K : ℝ
  c_pos : 0<c
  c_lt_C : c<C
  K_pos : 0<K
  bounds : ∀ y,b y∈Icc c C
  W : Fin 2 → H1
  W_H10 : ∀ j,W j∈H10
  W_bound : ∀ j,∀ᵐ x∂ballMeasure,|weakValue (W j) x|≤K
  W_energy : ∀ j,‖weakGradientL (W j)‖^2≤K
  W_support : ∀ j,∀ᵐ x∂ballMeasure,x∉closure sourceDomain →
    weakValue (W j) x=0 ∧ weakGradient (W j) x=0
  W_gradient : ∀ j,∀ᵐ x∂ballMeasure,WithLp.ofLp x∉physicalOpenBlock → weakGradient (W j) x=0
  green : ∀ (a : R3 → ℝ),(∀ᵐ y∂volume.restrict physicalOpenBlock,a (WithLp.toLp 2 y)=b y) →
    ∀ j (h : H1),(∫ x,a x*inner ℝ (weakGradient (W j) x) (weakGradient h x) ∂ballMeasure)=
      constantTerminalFluxCLM (centralBasisSlopes j) h

theorem boundedRootSources_nonempty : Nonempty BoundedRootSources := by
  obtain ⟨s,hs,hres⟩ := exists_nonresonant_angular_tensor
  let z : PhysicalFiniteEndingData s := Classical.choice (physicalFiniteEndingData_nonempty hs hres)
  obtain ⟨σ,c,C,w,q,hσ,hσLp,hc,hcC,hσb,hq0,hwc,hwe,⟨Z,hZ,hq⟩,hgreen⟩ := z.scalar_pair_green_exists hs
  obtain ⟨η,hη,hηc,hT⟩ := z.terminal_band_exists
  let t := η/4
  have ht : 0<t := by dsimp [t]; positivity
  have htc : 2*t<centralThickness := by dsimp [t]; linarith
  have hT' : ∀ i : Fin 3,∀ r : ℝ,|r|≤t → (z.ending i).R<z.compression i*(r-PhysicalFiniteEndingData.terminalBase i) := by
    intro i r hr
    apply hT i r
    dsimp [t] at hr
    linarith
  choose W hW hWv hWt using z.source_patch_trace_exists hs ht htc hT' w q hwe
    (Z-originalPairVoltageJet physicalOpenBlock w) hZ hq
  let b : Coord3 → ℝ := fun y => max c (min C (σ y))
  have hbm : Measurable b := measurable_const.max (measurable_const.min hσ)
  have hbb (y : Coord3) : b y∈Icc c C := ⟨le_max_left _ _,max_le hcC.le (min_le_left _ _)⟩
  have hbe : b=ᵐ[volume.restrict physicalOpenBlock] σ := by
    filter_upwards [hσb] with y hy
    exact max_eq_right (by simpa only [min_eq_right hy.2] using hy.1) |>.trans (min_eq_right hy.2)
  let a : R3 → ℝ := fun x => b (WithLp.ofLp x)
  have ham : AEStronglyMeasurable a ballMeasure :=
    (hbm.comp (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).measurable).aestronglyMeasurable
  have hC : 0≤C := (hc.trans hcC).le
  have hab : ∀ᵐ x∂ballMeasure,|a x|≤C := Eventually.of_forall (fun x => by
    rw [abs_of_pos (hc.trans_le (hbb _).1)]; exact (hbb _).2)
  have hap : ∀ᵐ x∂ballMeasure,0<a x := Eventually.of_forall (fun x => hc.trans_le (hbb _).1)
  have hae : ∀ᵐ y∂volume.restrict physicalOpenBlock,a (WithLp.toLp 2 y)=σ y := hbe
  let M : ℝ := ∑ j : Fin 2,∑ i : Fin 3,|z.terminalValue i j-z.terminalValue 0 j|
  have hM : 0≤M := Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
  have hMi (i : Fin 3) (j : Fin 2) : |z.terminalValue i j-z.terminalValue 0 j|≤M := by
    have h1 : |z.terminalValue i j-z.terminalValue 0 j|≤∑ i : Fin 3,|z.terminalValue i j-z.terminalValue 0 j| :=
      Finset.single_le_sum (f:=fun i : Fin 3 => |z.terminalValue i j-z.terminalValue 0 j|) (fun k _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : (∑ i : Fin 3,|z.terminalValue i j-z.terminalValue 0 j|)≤M :=
      Finset.single_le_sum (f:=fun j : Fin 2 => ∑ i : Fin 3,|z.terminalValue i j-z.terminalValue 0 j|) (fun k _ => Finset.sum_nonneg (fun i _ => abs_nonneg _)) (Finset.mem_univ j)
    exact h1.trans h2
  have hWb (j : Fin 2) : ∀ᵐ x∂ballMeasure,|weakValue (W j) x|≤M :=
    physical_source_bounded a ham C hC hab hap (hW j) (centralBasisSlopes j)
      (z.source_patch_green ht htc a σ (q j) (W j) j hae (hWv j) (hgreen j)) hM
      (fun i => (hWt j i).mono (fun θ hθ => by rw [hθ]; exact hMi i j))
  let K := M+(∑ j : Fin 2,‖weakGradientL (W j)‖^2)+1
  have he0 : 0≤∑ j : Fin 2,‖weakGradientL (W j)‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hMK : M≤K := by dsimp [K]; linarith
  have hWK (j : Fin 2) : ‖weakGradientL (W j)‖^2≤K := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (fun k _ => sq_nonneg ‖weakGradientL (W k)‖) (Finset.mem_univ j)
    dsimp [K]; linarith
  have hWg (j : Fin 2) := z.source_patch_gradient ht htc (q j) (W j) j (hWv j)
  refine ⟨⟨b,hbm,c,C,K,hc,hcC,(by dsimp [K]; linarith),hbb,W,hW,
    fun j => (hWb j).mono (fun _ h => h.trans hMK),hWK,?_,?_,?_⟩⟩
  · intro j
    filter_upwards [hWv j,hWg j] with x hv hg hx
    have ht0 : sourceCollarTime (WithLp.ofLp x)<0 := by
      apply lt_of_not_ge
      intro hn
      apply hx
      exact (sourceDomain_closure_time (WithLp.ofLp x)).mpr hn
    have hn : WithLp.ofLp x∉physicalOpenBlock := by
      intro hn
      have hh := (sourceOpenBlock_time_iff _).mp hn
      exact (not_lt.mpr ht0.le) hh.1
    rw [ite_eq_right hn] at hv hg
    refine ⟨?_,hg⟩
    rw [hv]
    exact z.terminalProfile_zero_outside ht htc j ht0.le
  · intro j
    filter_upwards [hWg j] with x hx hn
    simpa only [ite_eq_right hn] using hx
  · intro a ha j h
    exact z.source_patch_green ht htc a σ (q j) (W j) j (Filter.EventuallyEq.trans ha hbe) (hWv j) (hgreen j) h

end ScalarConductivity

end
end

end OAI
