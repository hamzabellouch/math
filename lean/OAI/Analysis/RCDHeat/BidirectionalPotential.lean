import Mathlib
import OAI.Analysis.RCDHeat.ExistingAnalytic
import OAI.Analysis.RCDHeat.MidpointEndpoint

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: BidirectionalPotential, CompactSobolevDual, DimensionalCoreDual, DimensionalDualLimit, DimensionalH1Square. -/



namespace RegularPointCoordinates

section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [ProperSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

theorem IsOptimalCoupling.bidirectional_sobolev_potential
    (hgeo : IsGeodesicSpace X) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (hac₀ : ν₀ ≪ μ) (hac₁ : ν₁ ≪ μ)
    {π : Measure (X×X)} (hp : IsOptimalCoupling ν₀ ν₁ π)
    (p : X) {B : ℝ} (hB : 0 ≤ B)
    (h₀ : ∀ᵐ x ∂ν₀, x ∈ closedBall p B) (h₁ : ∀ᵐ x ∂ν₁, x ∈ closedBall p B) :
    ∃ (u v : SobolevSpace μ hQ) (φ ψ : X → ℝ),
      LipschitzWith ⟨5*B,by positivity⟩ φ ∧
      LipschitzWith ⟨5*B,by positivity⟩ ψ ∧
      (∀ x, |φ x| ≤ 10*B^2) ∧ (∀ x, |ψ x| ≤ 10*B^2) ∧
      tsupport φ ⊆ closedBall p (16*B) ∧ tsupport ψ ⊆ closedBall p (16*B) ∧
      HasCompactSupport φ ∧ HasCompactSupport ψ ∧
      (φ =ᵐ[μ] SobolevSpace.toLp μ hQ u) ∧
      (ψ =ᵐ[μ] SobolevSpace.toLp μ hQ v) ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ xy ∂π, φ xy.1+ψ xy.2 = dist xy.1 xy.2^2/2) ∧
      (∀ᵐ xy ∂π, SobolevSpace.minimalSlope μ hQ u xy.1 ≤ dist xy.1 xy.2) ∧
      (∀ᵐ xy ∂π, SobolevSpace.minimalSlope μ hQ v xy.2 ≤ dist xy.1 xy.2) := by
  obtain ⟨u,φ,ψ,hφ,hψ,hφB,hψB,hφS,hψS,hφc,hψc,hu,had,hc,hb⟩ :=
    hp.linear_radius_bounded_sobolev_potential μ hQ hgeo ν₀ ν₁ hac₀ p hB h₀ h₁
  let f : X → ℝ := -φ
  have hf : LipschitzWith ⟨5*B,by positivity⟩ f := hφ.neg
  have hf0 : ∀ x, B+5*B < dist p x → f x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport φ := fun h => (not_le.mpr hx) (by
      simpa only [mem_closedBall,dist_comm] using hφS h)
    simp only [f,Pi.neg_apply,image_eq_zero_of_notMem_tsupport hx',neg_zero]
  let ψ' := hopfLax f 1
  have hψ' := hopfLax_lipschitz hf hgeo (by norm_num : (0:ℝ) < 1)
  have hψ'c := hopfLax_hasCompactSupport hf p (B+5*B) hf0 (by norm_num : (0:ℝ) < 1)
  let v := SobolevSpace.ofLipschitzCompact μ hQ hψ' hψ'c
  have hv : ψ' =ᵐ[μ] SobolevSpace.toLp μ hQ v :=
    (SobolevSpace.ofLipschitzCompact_coe μ hQ hψ' hψ'c).symm
  have had' (x y : X) : φ x+ψ' y ≤ dist x y^2/2 := by
    have hh := hopfLax_le_cost hf (by norm_num : (0:ℝ) < 1) y x
    change ψ' y ≤ -φ x+dist y x^2/(2*1) at hh
    rw [dist_comm y x] at hh
    linarith
  have hc' : ∀ᵐ xy ∂π, φ xy.1+ψ' xy.2 = dist xy.1 xy.2^2/2 := by
    apply hc.mono
    intro xy hxy
    have hh := hopfLax_of_contact hφ
      (fun x y => by simpa only [add_comm,dist_comm] using had y x)
      (x := xy.2) (y := xy.1) (by simpa only [add_comm,dist_comm] using hxy)
    have he : ψ' xy.2 = ψ xy.2 := hh.1
    rw [he]
    exact hxy
  have hψ'B (x : X) : |ψ' x| ≤ 10*B^2 := by
    apply abs_le.mpr
    constructor
    · apply le_csInf ⟨_,mem_range_self x⟩
      rintro _ ⟨z,rfl⟩
      change -(10*B^2) ≤ -φ z+dist x z^2/(2*1)
      nlinarith [(hφB z).2,sq_nonneg (dist x z)]
    · have hh := (hopfLax_bounds hf (by norm_num : (0:ℝ) < 1) x).2
      change ψ' x ≤ -φ x at hh
      nlinarith [(hφB x).1,sq_nonneg B]
  have hψ'S : tsupport ψ' ⊆ closedBall p (16*B) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra h
    have hx' : 16*B < dist p x := by simpa only [mem_closedBall,dist_comm,not_le] using h
    apply hx
    apply hopfLax_zero_outside hf p (B+5*B) hf0 (by norm_num : (0:ℝ) < 1)
    change B+5*B+2*1*(5*B) < dist p x
    linarith
  have hb' : ∀ᵐ xy ∂π, SobolevSpace.minimalSlope μ hQ v xy.2 ≤ dist xy.1 xy.2 := by
    have hbound := (hopfLeftRadius_minimalSlope_bound_proper μ hQ hf hgeo p (B+5*B) hf0).filter_mono hac₁.ae_le
    rw [←hp.2.1] at hbound
    have hb' := ae_of_ae_map measurable_snd.aemeasurable hbound
    filter_upwards [hb',hc'] with xy hh hxy
    change SobolevSpace.minimalSlope μ hQ v xy.2 ≤ hopfLeftRadius f xy.2 at hh
    rw [dist_comm xy.1 xy.2]
    apply hh.trans (hopfLeftRadius_le_minimizer hf ?_)
    change ψ' xy.2 = -φ xy.1+dist xy.2 xy.1^2/(2*1)
    rw [dist_comm xy.2 xy.1]
    linarith
  refine ⟨u,v,φ,ψ',hφ,hψ',?_,hψ'B,?_,hψ'S,hφc,hψ'c,hu,hv,had',hc',hb,hb'⟩
  · intro x
    rw [abs_of_nonneg (hφB x).1]
    exact (hφB x).2
  · apply hφS.trans
    exact closedBall_subset_closedBall (by linarith)

end

 
section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

structure CompactSobolevDual (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (ν₀ ν₁ : Measure X) (p : X) (R A : ℝ) (L : ℝ≥0) where
  u : SobolevSpace μ hQ
  v : SobolevSpace μ hQ
  φ : X → ℝ
  ψ : X → ℝ
  lipφ : LipschitzWith L φ
  lipψ : LipschitzWith L ψ
  boundφ : ∀ x, |φ x| ≤ A
  boundψ : ∀ x, |ψ x| ≤ A
  supportφ : tsupport φ ⊆ closedBall p R
  supportψ : tsupport ψ ⊆ closedBall p R
  compactφ : HasCompactSupport φ
  compactψ : HasCompactSupport ψ
  repu : φ =ᵐ[μ] SobolevSpace.toLp μ hQ u
  repv : ψ =ᵐ[μ] SobolevSpace.toLp μ hQ v
  admissible : ∀ x y, φ x+ψ y ≤ dist x y^2/2
  dual : (∫x, φ x ∂ν₀)+(∫x, ψ x ∂ν₁) = (wassersteinSq ν₀ ν₁).toReal/2

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.dimensional_core_dual
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (ρ₀ ρ₁ : SobolevSpace (hausdorff n X) hX.quadratic)
    {h₀ h₁ : X → ℝ} {L₀ L₁ : ℝ≥0}
    (hh₀ : LipschitzWith L₀ h₀) (hh₁ : LipschitzWith L₁ h₁)
    (hh₀0 : ∀ x, 0 ≤ h₀ x) (hh₁0 : ∀ x, 0 ≤ h₁ x)
    (hi₀ : Integrable h₀ (hausdorff n X)) (hi₁ : Integrable h₁ (hausdorff n X))
    (hrep₀ : (SobolevSpace.toLp _ hX.quadratic ρ₀ : X → ℝ) =ᵐ[hausdorff n X] fun x => h₀ x^2)
    (hrep₁ : (SobolevSpace.toLp _ hX.quadratic ρ₁ : X → ℝ) =ᵐ[hausdorff n X] fun x => h₁ x^2)
    (hν₀ : ν₀ = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ₀ x)))
    (hν₁ : ν₁ = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ₁ x)))
    (N : ℝ) (hN : (n:ℝ) ≤ N) :
    ∃ d : CompactSobolevDual (hausdorff n X) hX.quadratic ν₀ ν₁
      p (16*R) (10*R^2) ⟨5*R,by positivity⟩,
      K*(wassersteinSq ν₀ ν₁).toReal+
        (boltzmannEntropy (hausdorff n X) ν₁-boltzmannEntropy (hausdorff n X) ν₀)^2/N ≤
        energyForm (hausdorff n X) hX.quadratic d.u ρ₀+
          energyForm (hausdorff n X) hX.quadratic d.v ρ₁ := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨π,hπ,hg,hp,hdi,hall⟩ := hX.exists_bounded_entropy_plan K n hn ν₀ ν₁ hC h0 h1 p hR hs0 hs1
  let := hπ
  have he := optimalPlan_endpoints ν₀ ν₁ π hp
  obtain ⟨u,v,φ,ψ,hφ,hψ,hφb,hψb,hφS,hψS,hφc,hψc,hu,hv,had,hcontact,hb₀,hb₁⟩ :=
    hp.bidirectional_sobolev_potential μ hX.quadratic hX.geodesic ν₀ ν₁
      (Measure.absolutelyContinuous_of_le_smul h0) (Measure.absolutelyContinuous_of_le_smul h1)
      p hR hs0 hs1
  have hm : Measurable (fun γ : C(Time,X) => (γ 0,γ 1)) :=
    (measurable_path_eval 0).prodMk (measurable_path_eval 1)
  have hcontact' := ae_of_ae_map hm.aemeasurable hcontact
  have hb₀' := ae_of_ae_map hm.aemeasurable hb₀
  have hb₁' := ae_of_ae_map hm.aemeasurable hb₁
  let D := (compressionBudget K n (2*R) C).toNNReal
  have hD : ENNReal.ofReal (D:ℝ) = compressionBudget K n (2*R) C := by
    rw [ENNReal.ofReal_coe_nnreal,ENNReal.coe_toNNReal (compressionBudget_ne_top K n (2*R) hC)]
  have hc (t : Time) : π.map (fun γ => γ t) ≤ ENNReal.ofReal (D:ℝ) • μ := by
    rw [hD]; exact (hall t).1
  have hs (t : Time) : ∀ᵐ x ∂π.map (fun γ => γ t), dist x p ≤ 3*R := by
    apply ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_closedBall |>.mpr
    exact (optimal_geodesic_plan_bounded ν₀ ν₁ π hg hp p hR hs0 hs1).mono fun γ hγ => hγ.2 t
  have hpaired := hX.compressed_plan_dimensional_core_energy (φ₀ := φ) (ψ₀ := ψ) (φ₁ := ψ) (ψ₁ := φ) K n hn π hg
    (by rwa [he.1,he.2]) D hc p (by positivity : 0 ≤ 3*R) hs
    u v ρ₀ ρ₁ hh₀ hh₁ hh₀0 hh₁0 hi₀ hi₁ hrep₀ hrep₁
    (he.1.trans hν₀) (he.2.trans hν₁) hu hv had
    (fun x y => by simpa only [add_comm,dist_comm] using had y x)
    hcontact' (hcontact'.mono fun γ hγ => by simpa only [add_comm] using hγ)
    hb₀' hb₁' N hN
  let d : CompactSobolevDual μ hX.quadratic ν₀ ν₁ p (16*R) (10*R^2) ⟨5*R,by positivity⟩ :=
    ⟨u,v,φ,ψ,hφ,hψ,hφb,hψb,hφS,hψS,hφc,hψc,hu,hv,had,
      optimal_plan_dual_eq hp hdi (hφ.continuous.integrable_of_hasCompactSupport hφc)
        (hψ.continuous.integrable_of_hasCompactSupport hψc) hcontact'⟩
  refine ⟨d,?_⟩
  simpa only [he.1,he.2] using hpaired

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

noncomputable def CompactSobolevDual.flip [SeparableSpace X]
    {μ : Measure X} {hQ : QuadraticCheegerEnergy μ} {ν₀ ν₁ : Measure X}
    {p : X} {R A : ℝ} {L : ℝ≥0} (d : CompactSobolevDual μ hQ ν₀ ν₁ p R A L) :
    CompactSobolevDual μ hQ ν₁ ν₀ p R A L where
  u := d.v
  v := d.u
  φ := d.ψ
  ψ := d.φ
  lipφ := d.lipψ
  lipψ := d.lipφ
  boundφ := d.boundψ
  boundψ := d.boundφ
  supportφ := d.supportψ
  supportψ := d.supportφ
  compactφ := d.compactψ
  compactψ := d.compactφ
  repu := d.repv
  repv := d.repu
  admissible x y := by simpa only [add_comm,dist_comm] using d.admissible y x
  dual := by rw [wassersteinSq_symm ν₁ ν₀,add_comm]; exact d.dual

theorem NoncollapsedRCD.dimensional_dual_limit
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) (νs : ℕ → Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁] [∀ i, IsProbabilityMeasure (νs i)]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (hcs : ∀ i, νs i ≤ C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (hss : ∀ i, ∀ᵐ x ∂νs i, dist x p ≤ R)
    {fs : ℕ → X → ℝ} {M : ℝ}
    (hfm : ∀ i, Measurable (fs i)) (hfn : ∀ i x, 0 ≤ fs i x ∧ fs i x ≤ M)
    (hfs : ∀ i x, fs i x ≠ 0 → x ∈ closedBall p R)
    (ρ₀ ρ₁ : SobolevSpace (hausdorff n X) hX.quadratic)
    (qs : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hq : Tendsto qs atTop (𝓝 ρ₀))
    (hρ₀ : ∀ᵐ x ∂hausdorff n X, 0 ≤ SobolevSpace.toLp _ hX.quadratic ρ₀ x)
    (hfl : ∀ᵐ x ∂hausdorff n X, Tendsto (fun i => fs i x) atTop
      (𝓝 (SobolevSpace.toLp _ hX.quadratic ρ₀ x)))
    (hd : ∀ i, νs i = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (fs i x)))
    (hd0 : ν₀ = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ₀ x)))
    (hEnt : Tendsto (fun i => boltzmannEntropy (hausdorff n X) (νs i)) atTop
      (𝓝 (boltzmannEntropy (hausdorff n X) ν₀)))
    {S A : ℝ} {L : ℝ≥0}
    (ds : ∀ i, CompactSobolevDual (hausdorff n X) hX.quadratic (νs i) ν₁ p S A L)
    (N : ℝ)
    (henergy : ∀ i, K*(wassersteinSq (νs i) ν₁).toReal+
      (boltzmannEntropy (hausdorff n X) ν₁-boltzmannEntropy (hausdorff n X) (νs i))^2/N ≤
      energyForm (hausdorff n X) hX.quadratic (ds i).u (qs i)+
        energyForm (hausdorff n X) hX.quadratic (ds i).v ρ₁) :
    ∃ d : CompactSobolevDual (hausdorff n X) hX.quadratic ν₀ ν₁ p S A L,
      K*(wassersteinSq ν₀ ν₁).toReal+
        (boltzmannEntropy (hausdorff n X) ν₁-boltzmannEntropy (hausdorff n X) ν₀)^2/N ≤
        energyForm (hausdorff n X) hX.quadratic d.u ρ₀+
          energyForm (hausdorff n X) hX.quadratic d.v ρ₁ := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨u,φ,ψ,s,hsm,hφ,hψ,hφB,hψB,hφS,hψS,hu,hφlim,hψlim,hub,hul⟩ :=
    SobolevSpace.common_support_dual_subsequence μ hX.quadratic p S A L
      (fun i => (ds i).u) (fun i => (ds i).φ) (fun i => (ds i).ψ)
      (fun i => (ds i).lipφ) (fun i => (ds i).lipψ)
      (fun i => (ds i).boundφ) (fun i => (ds i).boundψ)
      (fun i => (ds i).supportφ) (fun i => (ds i).supportψ) (fun i => (ds i).repu)
  have hφc : HasCompactSupport φ := (isCompact_closedBall p S).of_isClosed_subset (isClosed_tsupport φ) hφS
  have hψc : HasCompactSupport ψ := (isCompact_closedBall p S).of_isClosed_subset (isClosed_tsupport ψ) hψS
  let v := SobolevSpace.ofLipschitzCompact μ hX.quadratic hψ hψc
  have hv : ψ =ᵐ[μ] SobolevSpace.toLp μ hX.quadratic v :=
    (SobolevSpace.ofLipschitzCompact_coe μ hX.quadratic hψ hψc).symm
  have hvb (i : ℕ) : ‖(ds (s i)).v‖ ≤ Real.sqrt ((A^2+(L:ℝ)^2)*(μ (closedBall p S)).toReal) :=
    SobolevSpace.norm_le_of_common_support μ hX.quadratic p S A L _
      (ds (s i)).lipψ (ds (s i)).boundψ (ds (s i)).supportψ (ds (s i)).repv
  have hvl : Tendsto (fun i => SobolevSpace.toLp μ hX.quadratic (ds (s i)).v) atTop
      (𝓝 (SobolevSpace.toLp μ hX.quadratic v)) :=
    SobolevSpace.toLp_tendsto_of_common_support μ hX.quadratic p S A L
      (fun i => (ds (s i)).lipψ) hψ (fun i => (ds (s i)).boundψ) hψB
      (fun i => (ds (s i)).supportψ) hψS (fun i => (ds (s i)).repv) hv hψlim
  have had (x y : X) : φ x+ψ y ≤ dist x y^2/2 :=
    le_of_tendsto ((hφlim x).add (hψlim y)) (Eventually.of_forall fun i => (ds (s i)).admissible x y)
  have hcost := hX.bounded_density_dual_limit K n hn ν₀ ν₁ (fun i => νs (s i)) hC h0 h1
    (fun i => hcs (s i)) p hR hs0 hs1 (fun i => hss (s i))
    (fun i => hfm (s i)) (fun i => hfn (s i)) (fun i => hfs (s i))
    (Lp.stronglyMeasurable (SobolevSpace.toLp μ hX.quadratic ρ₀)).measurable hρ₀
    (hfl.mono fun x hx => hx.comp hsm.tendsto_atTop) (fun i => hd (s i)) hd0
    (fun i => (ds (s i)).lipφ) (fun i => (ds (s i)).lipψ)
    (fun i => (ds (s i)).boundφ) (fun i => (ds (s i)).boundψ)
    hφ hψ hφB hψB hφlim hψlim had (fun i => (ds (s i)).dual)
  let d : CompactSobolevDual μ hX.quadratic ν₀ ν₁ p S A L :=
    ⟨u,v,φ,ψ,hφ,hψ,hφB,hψB,hφS,hψS,hφc,hψc,hu,hv,had,hcost.2⟩
  have hE0 := SobolevSpace.energyForm_tendsto_weak_strong μ hX.quadratic hub hul
    (hq.comp hsm.tendsto_atTop)
  have hE1 := SobolevSpace.energyForm_tendsto_of_toLp_tendsto_bounded μ hX.quadratic hvb hvl ρ₁
  refine ⟨d,?_⟩
  exact le_of_tendsto_of_tendsto ((hcost.1.const_mul K).add
      (((tendsto_const_nhds (x := boltzmannEntropy μ ν₁)).sub
        (hEnt.comp hsm.tendsto_atTop)).pow 2 |>.div_const N))
    (hE0.add hE1) (Eventually.of_forall fun i => henergy (s i))

end

 

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.dimensional_H1_square_dual
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h0 : ν₀ ≤ C • hausdorff n X) (h1 : ν₁ ≤ C • hausdorff n X)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (ρ ρ₁ : SobolevSpace (hausdorff n X) hX.quadratic)
    (M : ℝ≥0)
    (hρ : ∀ᵐ x ∂hausdorff n X, 0 ≤ SobolevSpace.toLp _ hX.quadratic ρ x ∧
      SobolevSpace.toLp _ hX.quadratic ρ x ≤ M)
    (hρS : ∀ᵐ x ∂hausdorff n X, SobolevSpace.toLp _ hX.quadratic ρ x ≠ 0 → dist p x ≤ R)
    (hρM : (∫x, SobolevSpace.toLp _ hX.quadratic ρ x ∂hausdorff n X) = 1)
    (hν : ν₀ = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ x)))
    {h₁ : X → ℝ} {L₁ : ℝ≥0} (hh₁ : LipschitzWith L₁ h₁)
    (hh₁0 : ∀ x, 0 ≤ h₁ x) (hi₁ : Integrable h₁ (hausdorff n X))
    (hrep₁ : (SobolevSpace.toLp _ hX.quadratic ρ₁ : X → ℝ) =ᵐ[hausdorff n X] fun x => h₁ x^2)
    (hν₁ : ν₁ = (hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ₁ x)))
    (N : ℝ) (hN : (n:ℝ) ≤ N) :
    ∃ d : CompactSobolevDual (hausdorff n X) hX.quadratic ν₀ ν₁
      p (16*(2*(max R 0+1))) (10*(2*(max R 0+1))^2) ⟨5*(2*(max R 0+1)),by positivity⟩,
      K*(wassersteinSq ν₀ ν₁).toReal+
        (boltzmannEntropy (hausdorff n X) ν₁-boltzmannEntropy (hausdorff n X) ν₀)^2/N ≤
        energyForm (hausdorff n X) hX.quadratic d.u ρ+
          energyForm (hausdorff n X) hX.quadratic d.v ρ₁ := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨qs,hs,hq,hLip,hrep,hb,hsup,hm,hpt,hEnt⟩ :=
    SobolevSpace.quantitative_strong_probability_square_recovery μ hX.quadratic ρ M hρ p hρS hρM
  let B := 2*(max R 0+1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hRB : R ≤ B := by dsimp [B]; linarith [le_max_left R 0,le_max_right R 0]
  have hsc (i : ℕ) : HasCompactSupport (hs i) := by
    apply (isCompact_closedBall p B).of_isClosed_subset (isClosed_tsupport _) (closure_minimal _ isClosed_closedBall)
    intro x hx
    simpa only [mem_closedBall,dist_comm] using hsup i x hx
  let νs : ℕ → Measure X := fun i => μ.withDensity (fun x => ENNReal.ofReal (hs i x^2))
  let (i : ℕ) : IsProbabilityMeasure (νs i) :=
    squareDensity_probability μ (compactSquare_integrable μ (hLip i).choose_spec.continuous (hsc i)) (hm i)
  let D : ℝ≥0∞ := max C (ENNReal.ofReal (2*M))
  have hD : D ≠ ∞ := by
    simp only [D, ne_eq, max_eq_top, not_or]
    exact ⟨hC, ENNReal.ofReal_ne_top⟩
  have h0D : ν₀ ≤ D • μ := h0.trans (by gcongr; exact le_max_left _ _)
  have h1D : ν₁ ≤ D • μ := h1.trans (by gcongr; exact le_max_left _ _)
  have hDs (i : ℕ) : νs i ≤ D • μ := by
    calc
      _ ≤ μ.withDensity (fun _ => ENNReal.ofReal (2*M)) :=
        withDensity_mono (Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hb i x).2)
      _ = ENNReal.ofReal (2*M) • μ := withDensity_const _
      _ ≤ D • μ := by gcongr; exact le_max_right _ _
  have hSqs (i : ℕ) (x : X) (hx : hs i x^2 ≠ 0) : x ∈ closedBall p B := by
    have hh : hs i x ≠ 0 := by intro hz; apply hx; rw [hz]; norm_num
    simpa only [mem_closedBall,dist_comm] using hsup i x hh
  have hSs (i : ℕ) : ∀ᵐ x ∂νs i, dist x p ≤ B := by
    apply (ae_withDensity_iff ((hLip i).choose_spec.continuous.measurable.pow_const 2).ennreal_ofReal).mpr
    filter_upwards with x hx
    apply hSqs i x
    intro hz
    exact hx (by rw [hz,ENNReal.ofReal_zero])
  have hνs (i : ℕ) : νs i = μ.withDensity (fun x => ENNReal.ofReal (SobolevSpace.toLp μ hX.quadratic (qs i) x)) := by
    apply withDensity_congr_ae
    exact (hrep i).symm.fun_comp ENNReal.ofReal
  have hcore (i : ℕ) := hX.dimensional_core_dual K n hn (νs i) ν₁ hD
    (hDs i) h1D p hB (hSs i) (hs1.mono fun x hx => hx.trans hRB) (qs i) ρ₁
    (hLip i).choose_spec hh₁ (fun x => (hb i x).1) hh₁0
    ((hLip i).choose_spec.continuous.integrable_of_hasCompactSupport (hsc i)) hi₁
    (hrep i) hrep₁ (hνs i) hν₁ N hN
  choose ds henergy using hcore
  have hEL : Tendsto (fun i => boltzmannEntropy μ (νs i)) atTop (𝓝 (boltzmannEntropy μ ν₀)) := by
    have he0 : boltzmannEntropy μ ν₀ = ∫x, SobolevSpace.toLp μ hX.quadratic ρ x*
        Real.log (SobolevSpace.toLp μ hX.quadratic ρ x) ∂μ := by
      rw [hν]
      exact realDensity_entropy μ (Lp.stronglyMeasurable _).measurable (hρ.mono fun x hx => hx.1)
    have hes (i : ℕ) : boltzmannEntropy μ (νs i) = ∫x, hs i x^2*Real.log (hs i x^2) ∂μ :=
      squareDensity_entropy μ (hLip i).choose_spec.continuous.measurable
    rw [he0]
    simp_rw [hes]
    exact hEnt
  exact hX.dimensional_dual_limit K n hn ν₀ ν₁ νs hD h0D h1D hDs p hB
    (hs0.mono fun x hx => hx.trans hRB) (hs1.mono fun x hx => hx.trans hRB) hSs
    (fun i => (hLip i).choose_spec.continuous.measurable.pow_const 2)
    (M := (2*M:ℝ)) (fun i x => ⟨sq_nonneg _,(hb i x).2⟩) hSqs
    ρ ρ₁ qs hq (hρ.mono fun x hx => hx.1) hpt (fun i => rfl) hν hEL ds N henergy


end RegularPointCoordinates

end OAI
