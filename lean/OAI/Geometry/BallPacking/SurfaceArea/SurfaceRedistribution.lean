import Mathlib
import OAI.Geometry.BallPacking.Moser.AnnularFinalPacking
import OAI.Geometry.BallPacking.SurfaceArea.SurfaceInteriorBoxes

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [SigmaCompactSpace M]
  {I : Type*} [Fintype I] {K L T : Set M}

def redistributedDifference (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (D : P → ManifoldTwoForm Plane M) (χ : ManifoldTwoForm Plane M) :
    P → ManifoldTwoForm Plane M := fun p => partitionFormMass B ρ (D p) • χ-D p

theorem surface_interior_redistribution
    (hK : IsCompact K) (hc : IsPreconnected (interior K)) (hne : (interior K).Nonempty)
    (hpos : PositivePlaneTransitions M)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {D : P → ManifoldTwoForm Plane M} (hD : SmoothTwoFormFamily D)
    (hsD : ∀ p x u v,D p x u v= -D p x v u)
    (hL : IsCompact L) (hLK : L⊆interior K) (hzD : ∀ p x,x∉L→D p x=0)
    {χ : ManifoldTwoForm Plane M} (hχ : SmoothTwoForm χ)
    (hsχ : ∀ x u v,χ x u v= -χ x v u)
    (hT : IsCompact T) (hTK : T⊆interior K) (hzχ : ∀ x,x∉T→χ x=0)
    (hmχ : partitionFormMass B ρ χ=1) :
    ContDiff ℝ ∞ (fun p => partitionFormMass B ρ (D p)) ∧
      SmoothTwoFormFamily (redistributedDifference B ρ D χ) ∧
      (∀ p,partitionFormMass B ρ (redistributedDifference B ρ D χ p)=0) ∧
      HasInteriorPrimitiveFamily (interior K) (redistributedDifference B ρ D χ) := by
  have hzDK : ∀ p x,x∉K→D p x=0 :=
    fun p x hx => hzD p x (fun hl => hx (interior_subset (hLK hl)))
  have hzχK : ∀ x,x∉K→χ x=0 :=
    fun x hx => hzχ x (fun ht => hx (interior_subset (hTK ht)))
  let H : P → ℝ := fun p => partitionFormMass B ρ (D p)
  have hH : ContDiff ℝ ∞ H := partitionFormMass_smooth hK B ρ hρ hD hzDK
  have hHχ : SmoothTwoFormFamily (fun p => H p • χ) :=
    (SmoothTwoFormFamily.const hχ).smul hH
  have hΞ : SmoothTwoFormFamily (redistributedDifference B ρ D χ) := hHχ.sub hD
  have hs : ∀ p x u v,redistributedDifference B ρ D χ p x u v=
      -redistributedDifference B ρ D χ p x v u := by
    intro p x u v
    change H p*χ x u v-D p x u v= -(H p*χ x v u-D p x v u)
    rw [hsχ x u v,hsD p x u v]; ring
  have hz : ∀ p x,x∉L∪T→ redistributedDifference B ρ D χ p x=0 := by
    intro p x hx
    change H p • χ x-D p x=0
    rw [hzχ x (fun ht => hx (Or.inr ht)),hzD p x (fun hl => hx (Or.inl hl))]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change H p*0-0=0
    ring
  have hm (p : P) : partitionFormMass B ρ (redistributedDifference B ρ D χ p)=0 := by
    change partitionFormMass B ρ (H p • χ-D p)=0
    have hzHχ : ∀ x,x∉K→(H p • χ) x=0 := by
      intro x hx
      change H p • χ x=0
      rw [hzχK x hx]
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      exact mul_zero (H p)
    rw [partitionFormMass_sub hK B ρ hρ (hHχ.eval p) (hD.eval p) hzHχ (hzDK p),
      partitionFormMass_smul,hmχ,mul_one]
    exact sub_self _
  refine ⟨hH,hΞ,hm,?_⟩
  exact interior_surface_primitive isOpen_interior hc hne hpos (hL.union hT)
    (union_subset hLK hTK) ((union_subset hLK hTK).trans interior_subset)
    B ρ hρ hΞ hs hz hm


end

section
open scoped ContDiff Manifold Topology ENNReal
open Set Function Manifold MeasureTheory
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [μ.OuterRegular]

omit [BorelSpace M] in

theorem exists_small_measure_smooth_cutoff {C H : Set M}
    (hC : IsCompact C) (hnull : μ C=0) (hH : IsClosed H) (hdis : Disjoint C H)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ ζ : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧
      (∀ x, ζ x ∈ Icc (0:ℝ) 1) ∧ (∀ x ∈ H, ζ x=0) ∧
      (∀ᶠ x in 𝓝ˢ C, ζ x=1) ∧ μ (tsupport ζ) < ENNReal.ofReal δ := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  obtain ⟨U,hCU,hU,hμU⟩ := C.exists_isOpen_lt_of_lt (μ := μ) (ENNReal.ofReal δ)
    (by simpa only [hnull] using (ENNReal.ofReal_pos.mpr hδ))
  have hCV : C ⊆ U ∩ Hᶜ := fun x hx => ⟨hCU hx,disjoint_left.mp hdis hx⟩
  obtain ⟨D,hD,hCD,hDV⟩ := exists_compact_between hC (hU.inter hH.isOpen_compl) hCV
  obtain ⟨ζ,hζ1,hζ0,hζ⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (n := (⊤ : ℕ∞)) 𝓘(ℝ,E) hC.isClosed hCD
  have hsupport : tsupport (ζ : M → ℝ) ⊆ D :=
    closure_minimal (fun x hx => by by_contra hn; exact hx (hζ0 x hn)) hD.isClosed
  refine ⟨ζ,ζ.contMDiff,HasCompactSupport.of_support_subset_isCompact hD
    ((subset_tsupport ζ).trans hsupport),hζ,?_,hζ1,?_⟩
  · intro x hx
    exact hζ0 x (fun hxd => (hDV hxd).2 hx)
  · exact (measure_mono (hsupport.trans (hDV.trans inter_subset_left))).trans_lt hμU


end

section
open scoped ContDiff Manifold Topology ENNReal
open Set Function Manifold MeasureTheory
variable {E P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [μ.OuterRegular] [IsFiniteMeasureOnCompacts μ]

theorem exists_uniform_small_area_density {Y : Set P} {K C H : Set M}
    (hY : IsCompact Y) (hK : IsCompact K) (hC : IsCompact C) (hnull : μ C=0)
    (hH : IsClosed H) (hdis : Disjoint C H)
    {a : P × M → ℝ} (ha : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ a)
    (hapos : ∀ p ∈ Y, ∀ x ∈ K, 0<a (p,x)) {ε : ℝ} (hε : 0<ε) :
    ∃ (e : ℝ) (b : P × M → ℝ), 0<e ∧
      ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ b ∧
      (∀ p ∈ Y, ∀ x ∈ K, 0<b (p,x)) ∧
      (∃ U : Set M, IsOpen U ∧ C ⊆ U ∧ ∀ p x, x ∈ U → b (p,x)=a (p,x)) ∧
      (∀ p x, x ∈ H → b (p,x)=e) ∧
      (∀ p ∈ Y, (∫ x in K, b (p,x) ∂μ)<ε) := by
  obtain ⟨A₀,hA₀⟩ := (hY.prod hK).bddAbove_image ha.continuous.continuousOn
  let A : ℝ := max A₀ 1
  have hA1 : 1≤A := le_max_right _ _
  have hA : 0<A := lt_of_lt_of_le zero_lt_one hA1
  have hbound : ∀ p ∈ Y, ∀ x ∈ K, a (p,x)≤A := by
    intro p hp x hx
    exact (hA₀ ⟨(p,x),⟨hp,hx⟩,rfl⟩).trans (le_max_left _ _)
  let δ : ℝ := ε/(4*A)
  have hδ : 0<δ := div_pos hε (by positivity)
  have hAδ : A*δ=ε/4 := by dsimp [δ]; field_simp
  obtain ⟨ζ,hζ,hζc,hζrange,hζH,hζC,hζμ⟩ :=
    exists_small_measure_smooth_cutoff (E := E) hC hnull hH hdis hδ
  obtain ⟨U,hU,hCU,hUζ⟩ := mem_nhdsSet_iff_exists.mp hζC
  let e : ℝ := ε/(4*((μ K).toReal+1))
  have hμK : 0≤(μ K).toReal := ENNReal.toReal_nonneg
  have he : 0<e := div_pos hε (by positivity)
  have hem : e*((μ K).toReal+1)=ε/4 := by
    dsimp [e]
    field_simp
  have hesmall : e*(μ K).toReal<ε/4 := by nlinarith
  let b : P × M → ℝ := fun q => ζ q.2*a q+(1-ζ q.2)*e
  have hb : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ b :=
    ((hζ.comp contMDiff_snd).mul ha).add
      ((contMDiff_const.sub (hζ.comp contMDiff_snd)).mul contMDiff_const)
  refine ⟨e,b,he,hb,?_,⟨U,hU,hCU,?_⟩,?_,?_⟩
  · intro p hp x hx
    have hc := hζrange x
    have hap := hapos p hp x hx
    change 0<ζ x*a (p,x)+(1-ζ x)*e
    by_cases hz : ζ x=0
    · simp only [hz,zero_mul,sub_zero,one_mul,zero_add]; exact he
    · have hzp : 0<ζ x := lt_of_le_of_ne hc.1 (Ne.symm hz)
      exact add_pos_of_pos_of_nonneg (mul_pos hzp hap) (mul_nonneg (sub_nonneg.mpr hc.2) he.le)
  · intro p x hx
    change ζ x*a (p,x)+(1-ζ x)*e=a (p,x)
    rw [hUζ hx]; ring
  · intro p x hx
    change ζ x*a (p,x)+(1-ζ x)*e=e
    rw [hζH x hx]; ring
  · intro p hp
    have hζsmall : (∫ x in K, ζ x ∂μ)<δ := by
      apply (ENNReal.ofReal_lt_ofReal_iff hδ).mp
      apply lt_of_le_of_lt _ hζμ
      apply le_trans (integral_le_measure (μ := μ.restrict K)
        (s := tsupport ζ) (fun x _ => (hζrange x).2)
        (fun x hx => le_of_eq (image_eq_zero_of_notMem_tsupport hx)))
      exact Measure.restrict_apply_le _ _
    have hζint : IntegrableOn ζ K μ := hζ.continuous.continuousOn.integrableOn_compact hK
    have hbint : IntegrableOn (fun x => b (p,x)) K μ :=
      (hb.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact hK
    have hcint : IntegrableOn (fun _ : M => e) K μ :=
      continuousOn_const.integrableOn_compact hK
    have hle : (∫ x in K, b (p,x) ∂μ) ≤ ∫ x in K, (A*ζ x+e) ∂μ := by
      apply setIntegral_mono_on hbint ((hζint.const_mul A).add hcint) hK.measurableSet
      intro x hx
      have hmul := mul_le_mul_of_nonneg_left (hbound p hp x hx) (hζrange x).1
      dsimp [b]
      nlinarith [(hζrange x).1]
    have heq : (∫ x in K, (A*ζ x+e) ∂μ) = A*(∫ x in K, ζ x ∂μ)+e*(μ K).toReal := by
      rw [integral_add (hζint.const_mul A) hcint,integral_const_mul,setIntegral_const]
      change A*(∫ x in K, ζ x ∂μ)+(μ K).toReal*e = _
      ring
    rw [heq] at hle
    have hh := mul_lt_mul_of_pos_left hζsmall hA
    nlinarith


end

section

open scoped ContDiff Manifold Topology ENNReal
open Set Function Manifold MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [TopologicalSpace.PseudoMetrizableSpace M] [MeasurableSpace M] [BorelSpace M]
  {I : Type*} [Fintype I] {K : Set M}

theorem exists_uniform_small_area_form
    (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0<chartTwoForm Λ c y (1,0) (0,1))
    {Y : Set P} {C H : Set M} (hY : IsCompact Y) (hK : IsCompact K)
    (hC : IsCompact C)
    (hnull : ∀ i,volume ((extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
      (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' C)=0)
    (hH : IsClosed H) (hdis : Disjoint C H)
    {a : P × M → ℝ} (ha : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ a)
    (hapos : ∀ p∈Y,∀ x∈K,0<a (p,x)) {ε : ℝ} (hε : 0<ε) :
    ∃ (e : ℝ) (b : P × M → ℝ), 0<e ∧
      ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ b ∧
      SmoothTwoFormFamily (fun p x => b (p,x) • Λ x) ∧
      (∀ p∈Y,∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
        (extChartAt 𝓘(ℝ,Plane) c).symm y∈K→
        0<chartTwoForm (fun x => b (p,x) • Λ x) c y (1,0) (0,1)) ∧
      (∃ U : Set M,IsOpen U ∧ C⊆U ∧ ∀ p x,x∈U→b (p,x) • Λ x=a (p,x) • Λ x) ∧
      (∀ p x,x∈H→b (p,x) • Λ x=e • Λ x) ∧
      (∀ p∈Y,restrictedPartitionFormMass B ρ K (fun x => b (p,x) • Λ x)<ε) := by
  let μ := partitionAreaMeasure B ρ Λ
  let := partitionAreaMeasure_finite B ρ hρ hΛ
  have hn : μ C=0 := partitionAreaMeasure_null B ρ Λ hC.measurableSet hnull
  obtain ⟨e,b,he,hb,hbp,hU,hH',hsmall⟩ :=
    exists_uniform_small_area_density (μ := μ) hY hK hC hn hH hdis ha hapos hε
  refine ⟨e,b,he,hb,(SmoothTwoFormFamily.const hΛ).coefficient_smul hb,?_,?_,?_,?_⟩
  · intro p hp c y hy hk
    rw [chartTwoForm_spatial_smul]
    exact mul_pos (hbp p hp _ hk) (hpos c y hy)
  · obtain ⟨U,hU,hCU,hUa⟩ := hU
    exact ⟨U,hU,hCU,fun p x hx => congrArg (fun r : ℝ => r • Λ x) (hUa p x hx)⟩
  · intro p x hx
    rw [hH' p x hx]
  · intro p hp
    have hbs : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (fun x => b (p,x)) :=
      hb.comp (contMDiff_const.prodMk contMDiff_id)
    rw [← integral_partitionAreaMeasure_restrict B ρ hρ hΛ (fun c y hy => (hpos c y hy).le)
      hK.measurableSet hbs]
    exact hsmall p hp



theorem exists_uniform_small_area_coefficient
    (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0≤chartTwoForm Λ c y (1,0) (0,1))
    {Y : Set P} {C H : Set M} (hY : IsCompact Y) (hK : IsCompact K)
    (hC : IsCompact C)
    (hnull : ∀ i,volume ((extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
      (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' C)=0)
    (hH : IsClosed H) (hdis : Disjoint C H)
    {a : P × M → ℝ} (ha : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ a)
    (hapos : ∀ p∈Y,∀ x∈K,0<a (p,x)) {ε : ℝ} (hε : 0<ε) :
    ∃ (e : ℝ) (b : P × M → ℝ), 0<e ∧
      ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ b ∧
      (∀ p∈Y,∀ x∈K,0<b (p,x)) ∧
      (∃ U : Set M,IsOpen U ∧ C⊆U ∧ ∀ p x,x∈U→b (p,x)=a (p,x)) ∧
      (∀ p x,x∈H→b (p,x)=e) ∧
      (∀ p∈Y,restrictedPartitionFormMass B ρ K (fun x => b (p,x) • Λ x)<ε) := by
  let μ := partitionAreaMeasure B ρ Λ
  let := partitionAreaMeasure_finite B ρ hρ hΛ
  have hn : μ C=0 := partitionAreaMeasure_null B ρ Λ hC.measurableSet hnull
  obtain ⟨e,b,he,hb,hbp,hU,hH',hsmall⟩ :=
    exists_uniform_small_area_density (μ := μ) hY hK hC hn hH hdis ha hapos hε
  refine ⟨e,b,he,hb,hbp,hU,hH',?_⟩
  intro p hp
  have hbs : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (fun x => b (p,x)) :=
    hb.comp (contMDiff_const.prodMk contMDiff_id)
  rw [← integral_partitionAreaMeasure_restrict B ρ hρ hΛ hpos hK.measurableSet hbs]
  exact hsmall p hp


end


open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [TopologicalSpace.PseudoMetrizableSpace M] [MeasurableSpace M] [BorelSpace M]
  {I : Type*} [Fintype I] {K T Z : Set M}

theorem exists_surface_area_redistribution
    (hK : IsCompact K) (hc : IsPreconnected (interior K)) (hne : (interior K).Nonempty)
    (hor : PositivePlaneTransitions M)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    (hnull : ∀ i,volume ((extChartAt 𝓘(ℝ,Plane) (B i).center).target ∩
      (extChartAt 𝓘(ℝ,Plane) (B i).center).symm ⁻¹' frontier K)=0)
    (hZ : IsClosed Z) (hdis : Disjoint (frontier K) Z)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    (hpΛ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0<chartTwoForm Λ c y (1,0) (0,1))
    {a : P × M → ℝ} (ha : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ a)
    {Y : Set P} (hY : IsCompact Y) (hapos : ∀ p∈Y,∀ x∈K,0<a (p,x))
    {χ : ManifoldTwoForm Plane M} (hχ : SmoothTwoForm χ)
    (hsχ : ∀ x u v,χ x u v= -χ x v u)
    (hpχ : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0≤chartTwoForm χ c y (1,0) (0,1))
    (hT : IsCompact T) (hTK : T⊆interior K) (hzχ : ∀ x,x∉T→χ x=0)
    (hmχ : partitionFormMass B ρ χ=1)
    {A : P → ℝ} {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p∈Y,2*ε<A p)
    (herr : ∀ p∈Y,|restrictedPartitionFormMass B ρ K (fun x => a (p,x) • Λ x)-A p|<ε) :
    ∃ (e : ℝ) (b : P × M → ℝ) (H : P → ℝ) (Ξ : P → ManifoldTwoForm Plane M),
      0<e ∧ ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ b ∧
      ContDiff ℝ ∞ H ∧ SmoothTwoFormFamily Ξ ∧
      (∀ p,H p=restrictedPartitionFormMass B ρ K (fun x => a (p,x) • Λ x)-
        restrictedPartitionFormMass B ρ K (fun x => b (p,x) • Λ x)) ∧
      (∀ p∈Y,0<H p ∧ |H p-A p|<2*ε) ∧
      (∀ p x,x∈K→a (p,x) • Λ x+Ξ p x=b (p,x) • Λ x+H p • χ x) ∧
      (∀ p∈Y,∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
        (extChartAt 𝓘(ℝ,Plane) c).symm y∈K→
        0<chartTwoForm (fun x => a (p,x) • Λ x+Ξ p x) c y (1,0) (0,1)) ∧
      (∀ p x,x∈Z→b (p,x)=e) ∧
      HasInteriorPrimitiveFamily (interior K) Ξ ∧
      (∀ p∈Y,∀ x∈K,0<b (p,x)) ∧
      (∀ p∈Y,restrictedPartitionFormMass B ρ K (fun x => b (p,x) • Λ x)<ε) ∧
      (∃ U : Set M,IsOpen U ∧ frontier K⊆U ∧ ∀ p x,x∈U→b (p,x)=a (p,x)) := by
  have hpΛ' := fun c y hy => (hpΛ c y hy).le
  obtain ⟨e,b,he,hb,hbp,⟨V,hV,hCV,hba⟩,hbZ,hbm⟩ :=
    exists_uniform_small_area_coefficient B ρ hρ hΛ hpΛ' hY hK (hK.of_isClosed_subset isClosed_frontier
      (by simpa only [hK.isClosed.closure_eq] using (frontier_subset_closure : frontier K ⊆ closure K)))
      hnull hZ hdis ha hapos hε
  obtain ⟨L,d,hL,hLK,hd,hde,hdz⟩ :=
    exists_interior_coefficient_difference hK hV hCV ha hb
      (fun p x hx => (hba p x hx).symm)
  let D : P → ManifoldTwoForm Plane M := fun p x => d (p,x) • Λ x
  have hD : SmoothTwoFormFamily D := (SmoothTwoFormFamily.const hΛ).coefficient_smul hd
  have hsD : ∀ p x u v,D p x u v= -D p x v u := by
    intro p x u v
    change d (p,x)*Λ x u v= -(d (p,x)*Λ x v u)
    rw [hsΛ x u v]; ring
  have hzD : ∀ p x,x∉L→D p x=0 := by
    intro p x hx
    change d (p,x) • Λ x=0
    rw [hdz p x hx]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    exact zero_mul _
  obtain ⟨hH,hΞ,_,hprimitive⟩ := surface_interior_redistribution hK hc hne hor B ρ hρ
    hD hsD hL hLK hzD hχ hsχ hT hTK hzχ hmχ
  let H : P → ℝ := fun p => partitionFormMass B ρ (D p)
  let Ξ := redistributedDifference B ρ D χ
  have hmass (p : P) : H p=restrictedPartitionFormMass B ρ K (fun x => a (p,x) • Λ x)-
      restrictedPartitionFormMass B ρ K (fun x => b (p,x) • Λ x) :=
    interior_difference_mass B ρ hρ hK.measurableSet hΛ hpΛ' ha hb hd
      (hLK.trans interior_subset) hdz hde p
  have hbound (p : P) (hp : p∈Y) : 0<H p ∧ |H p-A p|<2*ε := by
    have hm0 : 0≤restrictedPartitionFormMass B ρ K (fun x => b (p,x) • Λ x) :=
      restricted_form_mass_nonneg B ρ hρ hK.measurableSet hΛ hpΛ'
        (hb.comp (contMDiff_const.prodMk contMDiff_id)) (fun x hx => (hbp p hp x hx).le)
    have herr' := abs_lt.mp (herr p hp)
    have hh := hmass p
    have hhsmall := hbm p hp
    have hlarge := hA p hp
    constructor
    · linarith
    · exact abs_lt.mpr ⟨by linarith,by linarith⟩
  have hformula (p : P) (x : M) (hx : x∈K) :
      a (p,x) • Λ x+Ξ p x=b (p,x) • Λ x+H p • χ x := by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change a (p,x)*Λ x u v+(H p*χ x u v-d (p,x)*Λ x u v)=
      b (p,x)*Λ x u v+H p*χ x u v
    rw [hde p x hx]; ring
  refine ⟨e,b,H,Ξ,he,hb,hH,hΞ,hmass,hbound,hformula,?_,hbZ,hprimitive,hbp,hbm,⟨V,hV,hCV,hba⟩⟩
  intro p hp c y hy hk
  have heq : chartTwoForm (fun x => a (p,x) • Λ x+Ξ p x) c y=
      chartTwoForm (fun x => b (p,x) • Λ x+H p • χ x) c y := by
    dsimp only [chartTwoForm]
    rw [hformula p _ hk]
  rw [heq]
  change 0<chartTwoForm ((fun x => b (p,x) • Λ x)+H p • χ) c y (1,0) (0,1)
  rw [chartTwoForm_add,chartTwoForm_spatial_smul,chartTwoForm_smul]
  change 0<b (p,(extChartAt 𝓘(ℝ,Plane) c).symm y)*chartTwoForm Λ c y (1,0) (0,1)+
    H p*chartTwoForm χ c y (1,0) (0,1)
  exact add_pos_of_pos_of_nonneg (mul_pos (hbp p hp _ hk) (hpΛ c y hy))
    (mul_nonneg (hbound p hp).1.le (hpχ c y hy))



end PackingSufficiencySupport.Hamiltonian
end

end OAI
