import Mathlib
import OAI.Geometry.Cannon.Energy.RecordData
import OAI.Geometry.Cannon.ScalarLimits.TransformedScalarEnergyConstant
import OAI.Geometry.Cannon.Energy.GeometricLimitMeasureHolder
import OAI.Geometry.Cannon.ScalarLimits.BoundaryRecordScalarLimit
import OAI.Geometry.Cannon.Flows.ContinuousDomain
import OAI.Geometry.Cannon.Energy.ChartSquareInterior
import OAI.Geometry.Cannon.Energy.DomainImage

namespace OAI

section
section
section
noncomputable section
section
section
section
namespace CannonRelease

open CannonGraph CannonVisual CannonMagnification
open CannonPacking CannonApprox CannonGrid CannonChart CannonCharts CannonCells CannonPlanar
open Set Metric Filter Topology MeasureTheory

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryRecordDataSetoid : Setoid (BasedRay D) := raySetoid D

theorem boundary_record_data (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    let _ : MeasurableSpace (Boundary D) := borel (Boundary D)
    let a := Real.exp (2*visualExponent δ)
    let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
    ∀ d : ℝ, 0 < d → d < diam (univ : Set (Boundary D)) → d ≤ 1/(LE*3^2) →
    ∀ (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → Boundary D),
    (∀ n i j, i ≠ j → (a^n)⁻¹ ≤ dist (p n i) (p n j)) →
    (∀ n x, ∃ i, dist (p n i) x ≤ (a^n)⁻¹) →
    (∀ B : ℝ, ∃ n, B < modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)) →
    ∃ Ns : ℕ → ℕ, StrictMono Ns ∧ Nonempty (RecordData
      (boundaryHomeomorph D ⟨δ,hδ⟩) (fun n => ι (Ns n)) (fun n => p (Ns n))
        (fun n => (a^(Ns n))⁻¹)) := by
  classical
  let _ := visualMetricSpace D hδ
  let _ : MeasurableSpace (Boundary D) := borel (Boundary D)
  let _ : BorelSpace (Boundary D) := ⟨rfl⟩
  let _ : LocallyPathConnectedSpace SphereTwo := CannonPaths.sphere_locallyPathConnected
  let _ : LocallyPathConnectedSpace (Boundary D) := φ.symm.isQuotientMap.locallyPathConnectedSpace
  dsimp only
  intro d hd hdia hdc ι hι p hpsep hpnet hunbounded
  let a := Real.exp (2*visualExponent δ)
  have ha : 1 < a := Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (visualExponent_pos δ))
  let M := fun n => modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)
  obtain ⟨e,he,A,hA,N,hN,hMlim,hrecord,ρ,m,hm,hρ,hadm,henergy,hmesh,u,hu,hvar,
      ν,_hν,ψ,hψ,hflim,hμlim⟩ :=
    boundary_record_scalar_limit D hδ φ d hd hdia hdc ι p hpsep hpnet 1 le_rfl
      (by simpa only [one_pow,div_one] using hunbounded)
  let E := e ∘ squareMap
  have hE : IsEmbedding E := he.isEmbedding.comp squareMap_embedding
  let Ns := N ∘ ψ
  have hNs : StrictMono Ns := hN.comp hψ
  let w := fun n => ρ (ψ n)
  let ms := m ∘ ψ
  have hms : ∀ n, 0 < ms n := fun n => hm (ψ n)
  have hw : ∀ n i, 0 ≤ w n i := fun n => hρ (ψ n)
  have hadms : ∀ n, Admissible (fun i => E ⁻¹' ball (p (Ns n) i) (2*(a^(Ns n))⁻¹)) (w n) :=
    fun n => hadm (ψ n)
  obtain ⟨Q,CP,_hQ,hCP,hpack⟩ := relative_polynomial_packing D hδ
  obtain ⟨L,hL,hpaths⟩ := boundary_controlled_paths D hδ φ
  obtain ⟨Cm,hCm,hmeasure,_hholder⟩ := geometric_limit_measure_holder φ d hd hdia a ha Q CP
    (2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ)))
    (1/((8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ)))*3^2)) L
    hpack hCP.le (by positivity) (by positivity) hL hdc hpaths
    (boundary_smallball_expansion D hδ) ι p hpsep hpnet E hE Ns w hw hadms ms hms
    (fun n => hmesh (ψ n)) 1 le_rfl (fun n => hrecord (ψ n)) hNs A hA.le
    (fun n => henergy (ψ n)) u ν hu hflim hμlim
  let Ω := interior (range E)
  have hf : ContinuousOn (onDomain u) Ω := continuousOn_onDomain u
  obtain ⟨top,bot,htop,hbot⟩ := hvar
  have hv : ∃ v ∈ Ω, ∃ w ∈ Ω, onDomain u v ≠ onDomain u w := by
    refine ⟨top,top.property,bot,bot.property,?_⟩
    simpa only [onDomain_eq u top top.property,onDomain_eq u bot bot.property,htop,hbot] using
      (zero_ne_one : (0:ℝ) ≠ 1)
  obtain ⟨x₀,hx₀,hroot⟩ := CannonNode.exists_nonlocally_constant (onDomain u) Ω
    (chart_square_pathConnected e he).isConnected.isPreconnected hv
  obtain ⟨dK,hdK,hK⟩ := constructed_scalar_continua E hE (fun n => ι (Ns n))
    (fun n => p (Ns n)) (fun n => (a^(Ns n))⁻¹) w hw hadms ms hms u hflim
  let K : ℝ → Set (Boundary D) := fun t => if ht : t ∈ Ioo (0:ℝ) 1 then (hK t ht).choose else ∅
  have hKprop (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) := (hK t ht).choose_spec
  let r : ℕ → ℝ := fun n => (a^(Ns n))⁻¹
  have hr : ∀ n, 0 < r n := fun n => inv_pos.mpr (pow_pos (zero_lt_one.trans ha) _)
  have hrlim : Tendsto r atTop (𝓝 0) := by
    simpa only [r,inv_pow,Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr (zero_lt_one.trans ha)).le
        (inv_lt_one_of_one_lt₀ ha)).comp hNs.tendsto_atTop
  let f := fun n => scalar (fun i => E ⁻¹' ball (p (Ns n) i) (2*r n)) (w n) (ms n) (hms n)
  let H := fun n => CannonChart.extend E (f n)
  have hfprop (n : ℕ) := scalar_properties _ (w n) (hw n) (hadms n) (ms n) (hms n)
  have hHrange : ∀ n y, H n y ∈ Icc (0:ℝ) 1 := by
    intro n y
    by_cases hy : y ∈ range E
    · obtain ⟨z,rfl⟩ := hy
      change CannonChart.extend E (f n) (E z) ∈ Icc (0:ℝ) 1
      rw [CannonChart.extend_apply E hE.injective]
      exact (hfprop n).2.1 z
    · change Function.extend E (f n) (fun _ => 0) y ∈ Icc (0:ℝ) 1
      rw [Function.extend_apply' _ _ y hy]
      norm_num
  have hHcont (n : ℕ) : ContinuousOn (H n) Ω :=
    (continuousOn_extend E hE (f n) (hfprop n).1).mono interior_subset
  have hHlim : ∀ K : Set (Boundary D), IsCompact K → K ⊆ Ω →
      TendstoUniformlyOn H (onDomain u) atTop K := by
    intro K hK hKΩ
    apply uniform_onDomain H u ?_ K hK hKΩ
    exact ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hflim
  obtain ⟨d₁,hd₁,hlateral⟩ := exists_chart_lateral_diameter E hE
  have hlevels : ∀ n τ, τ ∈ Ioo (0:ℝ) 1 →
      ∃ S : Set (Boundary D), IsCompact S ∧ IsConnected S ∧ d₁ ≤ diam S ∧
        (∀ y ∈ S, H n y = τ) ∧
        ∀ v w : Boundary D, ∀ γ : Path v w, range γ ⊆ Ω →
          H n v < τ → τ < H n w → (S ∩ range γ).Nonempty := by
    intro n τ hτ
    obtain ⟨S,hS,hSc,_hSU,hSd,hSH,hhit⟩ := scalar_ambient_level E hE
      (fun i => E ⁻¹' ball (p (Ns n) i) (2*r n)) (w n) (hw n) (hadms n)
      (ms n) (hms n) d₁ hlateral τ hτ
    refine ⟨S,hS,hSc,hSd,hSH,?_⟩
    intro v w γ hγ hv hw'
    obtain ⟨v',rfl⟩ := interior_subset (hγ γ.source_mem_range)
    obtain ⟨w',rfl⟩ := interior_subset (hγ γ.target_mem_range)
    have hv' : f n v' < τ := by simpa only [H,CannonChart.extend_apply E hE.injective] using hv
    have hw'' : τ < f n w' := by simpa only [H,CannonChart.extend_apply E hE.injective] using hw'
    obtain ⟨t,ht⟩ := hhit γ (fun t => interior_subset (hγ (mem_range_self t))) hv' hw''
    exact ⟨γ t,ht,mem_range_self t⟩
  refine ⟨Ns,hNs,⟨{
    Ω := Ω
    isOpen := isOpen_interior
    f := onDomain u
    continuous := hf
    unit := fun x hx => by simpa only [onDomain_eq u x hx] using hu ⟨x,hx⟩
    x₀ := x₀
    x₀mem := hx₀
    variation := hroot
    z₀ := e (0,0)
    z₀not := chart_origin_outside_square e he
    ν := ν
    E := Cm
    E_nonneg := hCm
    Cμ := 8*a*L
    Cμ_pos := by have := zero_lt_one.trans_le hL; positivity
    measure_bound := ?_
    level := K
    diameter := dK
    diameter_pos := hdK
    level_properties := ?_
    level_hits := ?_
    H := H
    H_unit := hHrange
    H_continuous := hHcont
    H_limit := hHlim
    H_diameter := d₁
    H_diameter_pos := hd₁
    H_level := hlevels
    energy := ?_
  }⟩⟩
  · intro T hT hTΩ
    obtain ⟨s₀,hs₀,hbound⟩ := hmeasure T hT hTΩ
    refine ⟨s₀,hs₀,fun s hs hss x hx => ?_⟩
    obtain ⟨hball,hb⟩ := hbound s hs hss x hx
    refine ⟨hball,?_⟩
    simpa only [CannonCrossEnergy.oscillation,CannonScalarLimit.osc,onDomain_image_eq u _ hball] using hb
  · intro t ht
    have hh := hKprop t ht
    simp only [K,dite_eq_left ht]
    exact ⟨hh.1,hh.2.1,hh.2.2.2.1,fun y hy hyΩ => by
      rw [onDomain_eq u y hyΩ]
      exact hh.2.2.2.2.1 ⟨y,hyΩ⟩ hy⟩
  · intro t ht v w γ hγ hv hw'
    let γ' : Path (⟨v,hγ γ.source_mem_range⟩ : Ω) ⟨w,hγ γ.target_mem_range⟩ :=
      { toFun := fun s => ⟨γ s,hγ (mem_range_self s)⟩
        continuous_toFun := γ.continuous.subtype_mk _
        source' := Subtype.ext γ.source
        target' := Subtype.ext γ.target }
    have hv' : u ⟨v,hγ γ.source_mem_range⟩ < t := by
      simpa only [onDomain_eq u v (hγ γ.source_mem_range)] using hv
    have hw'' : t < u ⟨w,hγ γ.target_mem_range⟩ := by
      simpa only [onDomain_eq u w (hγ γ.target_mem_range)] using hw'
    obtain ⟨s,hs⟩ := (hKprop t ht).2.2.2.2.2 γ' hv' hw''
    change γ s ∈ (hK t ht).choose at hs
    exact ⟨γ s,by simpa only [K,dite_eq_left ht] using hs,mem_range_self s⟩
  · intro g K hK hKU J hJ
    let gg := boundaryHomeomorph D ⟨δ,hδ⟩ g
    let B := 2*Real.exp (visualExponent δ*(2*(3*D.graph.dist 1 g⁻¹+4*δ):ℕ))
    let Ag := 2*Real.exp (visualExponent δ*(2*(3*D.graph.dist 1 g+4*δ):ℕ))
    have hAg : 0 < Ag := by dsimp [Ag]; positivity
    have hB : 0 < B := by dsimp [B]; positivity
    have hupper : ∀ x y, dist (gg.symm x) (gg.symm y) ≤ B*dist x y :=
      boundaryTranslate_lipschitz_bound D hδ g⁻¹
    have hlower : ∀ x y, Ag⁻¹*dist x y ≤ dist (gg.symm x) (gg.symm y) := by
      intro x y
      have hh : dist (gg (gg.symm x)) (gg (gg.symm y)) ≤ Ag*dist (gg.symm x) (gg.symm y) :=
        boundaryTranslate_lipschitz_bound D hδ g (gg.symm x) (gg.symm y)
      simp only [gg.apply_symm_apply] at hh
      calc Ag⁻¹*dist x y = dist x y/Ag := by ring
           _ ≤ dist (gg.symm x) (gg.symm y) := (div_le_iff₀ hAg).mpr (by simpa only [mul_comm] using hh)
    obtain ⟨_C,_hC,_htail,hzero⟩ := transformed_scalar_energy_tail Q CP L J B Ag⁻¹ hpack hCP.le hL
      hJ hB (inv_pos.mpr hAg) hpaths E hE gg hlower hupper (fun n => ι (Ns n))
      (fun n => p (Ns n)) r hr hrlim (fun n => hpsep (Ns n)) w hw hadms ms hms
      (fun n => hmesh (ψ n)) (M ∘ Ns) (hMlim.comp hψ.tendsto_atTop) A hA.le
      (fun n => henergy (ψ n)) K hK hKU
    exact hzero

end CannonRelease

end

end
end
end
end
end
end

end OAI
