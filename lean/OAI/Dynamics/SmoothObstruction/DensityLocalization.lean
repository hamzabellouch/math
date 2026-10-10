import OAI.Dynamics.SmoothObstruction.Selection
import OAI.Dynamics.SmoothObstruction.GlobalSwitching

namespace OAI

section

namespace SmoothObstruction.ChartDomination
open MeasureTheory Set Filter Topology
open scoped ENNReal
variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma density_two {a b j : ℝ} (ha : 0≤a) (hb : 3/4*a≤b) (hj : 81/121≤j) :
    ENNReal.ofReal a≤2*(ENNReal.ofReal j*ENNReal.ofReal b) := by
  have hj0 : 0≤j := by linarith
  have hb0 : 0≤b := by linarith
  have hmul := mul_le_mul_of_nonneg_left hb hj0
  have hja := mul_nonneg (sub_nonneg.mpr hj) ha
  have hh : a≤2*(j*b) := by nlinarith
  simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat,
    ENNReal.ofReal_mul hj0] using ENNReal.ofReal_le_ofReal hh

/-- A concrete relative local branch and the two numerical lower bounds give
unnormalized domination by TWO in the original carrier measure. No choice of
local derivative or branch has to be measurable. -/
theorem local_two (μ : Measure X) (m : Measure E) [Measure.IsAddHaarMeasure m]
    (d : E → ℝ) (Q G : Set X) (hQ : μ Qᶜ=0) (hGQ : G⊆Q) (hG : MeasurableSet G)
    (e : X → E) (r : E → X) (he : Measurable e) (hr : Measurable r)
    (hleft : ∀ x∈Q,r (e x)=x) (hcoords : μ.map e=m.withDensity (fun u => ENNReal.ofReal (d u)))
    (f : X → X) (_ : Measurable f) (hfQ : MapsTo f G Q) (hinj : InjOn f G)
    (hlocal : ∀ u∈coordinateSet e r G,∃ g : E → E,
      HasFDerivAt g (fderiv ℝ g u) u ∧ (81/121:ℝ)≤|(fderiv ℝ g u).det| ∧
      g =ᶠ[𝓝[coordinateSet e r G] u] (e ∘ f ∘ r))
    (hd : ∀ u∈coordinateSet e r G,0≤d u ∧ (3/4:ℝ)*d u≤d (e (f (r u)))) :
    (μ.restrict G).map f≤(2 : ℝ≥0∞) • μ := by
  classical
  let s := coordinateSet e r G
  choose g hg hj heq using hlocal
  let J (u : E) : E →L[ℝ] E := if hu : u∈s then fderiv ℝ (g u hu) u else 0
  have hφ : InjOn (e ∘ f ∘ r) s := by
    intro u hu v hv huv
    have hfu := hfQ hu.1
    have hfv := hfQ hv.1
    have he' : f (r u)=f (r v) := by
      have hh := congrArg r huv
      change r (e (f (r u)))=r (e (f (r v))) at hh
      rwa [hleft _ hfu,hleft _ hfv] at hh
    exact hu.2.symm.trans ((congrArg e (hinj hu.1 hv.1 he')).trans hv.2)
  obtain ⟨F,hF,hFf,hdom⟩ := local_domination μ m (fun u => ENNReal.ofReal (d u))
    Q G hQ hGQ hG e r he hr hleft hcoords f hfQ (e ∘ f ∘ r) J
    (fun x hx => by simp only [Function.comp_apply,hleft x (hGQ hx)])
    (fun u hu => ⟨g u hu,by simpa only [J,s,dite_eq_left hu] using hg u hu,heq u hu⟩)
    hφ 2 (by norm_num) (fun u hu => by
      simpa only [J,s,dite_eq_left hu,Function.comp_apply] using
        density_two (hd u hu).1 (hd u hu).2 (hj u hu))
  have hFF : F=ᵐ[μ.restrict G] f := ae_restrict_of_forall_mem hG (fun _ hx => hFf hx)
  rwa [Measure.map_congr hFF] at hdom
end SmoothObstruction.ChartDomination

namespace SmoothObstruction.ChartDensity
open MeasureTheory Set
open scoped ENNReal Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- Product coordinates carry exactly the product of the ORIGINAL cell
measures, with its unchanged chart density and no normalization. -/
theorem pair_cell_density (hclosed : IsClosed (range I)) (μ : Measure M) [IsFiniteMeasure μ]
    (hμ : SmoothPositiveDensity I μ) (a : M) :
    ∃ f : E₀ → ℝ,ContDiffOn ℝ ∞ f (extChartAt I a).target ∧
      (∀ u∈(extChartAt I a).target,0<f u) ∧
      ∀ Q : Set M,MeasurableSet Q → Q⊆(extChartAt I a).source →
        let W := ChartDomination.coordinateSet (coordinates I a) (inverse I a) Q
        let dQ := W.indicator f
        ((μ.restrict Q).prod (μ.restrict Q)).map (Prod.map (coordinates I a) (coordinates I a))=
          volume.withDensity (fun u : E₀×E₀ => ENNReal.ofReal (dQ u.1*dQ u.2)) := by
  classical
  obtain ⟨f,hf,hpos,hm⟩ := cell_density I hclosed μ hμ a
  refine ⟨f,hf,hpos,fun Q hQ hQU => ?_⟩
  dsimp only
  let W := ChartDomination.coordinateSet (coordinates I a) (inverse I a) Q
  let eQ := W.indicator (fun u => ENNReal.ofReal (f u))
  obtain ⟨heQ,hmap⟩ := hm Q hQ hQU
  have hmap' : (μ.restrict Q).map (coordinates I a)=volume.withDensity eQ := hmap
  rw [←Measure.map_prod_map _ _ (measurable_coordinates I a) (measurable_coordinates I a),hmap',
    prod_withDensity heQ heQ]
  congr 1
  funext u
  have he (v : E₀) : eQ v=ENNReal.ofReal (W.indicator f v) := by
    by_cases hv : v∈W <;> simp [eQ,Set.indicator,hv]
  have hn : 0≤W.indicator f u.1 := by
    by_cases hu : u.1∈W
    · rw [Set.indicator_of_mem hu]
      have him := ChartDomination.coordinateSet_eq_image (coordinates I a) (inverse I a) Q
        (fun x hx => inverse_coordinates I a x (hQU hx))
      obtain ⟨x,hx,he⟩ := (him ▸ hu : u.1∈coordinates I a '' Q)
      rw [←he,coordinates_eq I a x (hQU hx)]
      exact (hpos _ ((extChartAt I a).map_source (hQU hx))).le
    · simp only [Set.indicator_of_notMem hu,le_refl]
  change eQ u.1*eQ u.2=ENNReal.ofReal (W.indicator f u.1*W.indicator f u.2)
  rw [he,he,ENNReal.ofReal_mul hn]
end SmoothObstruction.ChartDensity

namespace SmoothObstruction.ChartDensity
open MeasureTheory Set Filter Topology
open scoped ENNReal Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- The original-cell change of variables. The density is selected ONCE per
atlas chart, before cells or retained pairs. Local branches are only required
on the retained relative neighborhood, at every rank including zero. -/
theorem pair_cell_two (hclosed : IsClosed (range I)) (μ : Measure M) [IsFiniteMeasure μ]
    (hμ : SmoothPositiveDensity I μ) (a : M) :
    ∃ f : E₀ → ℝ,ContDiffOn ℝ ∞ f (extChartAt I a).target ∧
      (∀ u∈(extChartAt I a).target,0<f u) ∧
      ∀ Q : Set M,MeasurableSet Q → Q⊆(extChartAt I a).source →
      ∀ G : Set (M×M),MeasurableSet G → G⊆Q×ˢQ →
      ∀ Φ : M×M → M×M,Measurable Φ → MapsTo Φ G (Q×ˢQ) → InjOn Φ G →
        let e := Prod.map (coordinates I a) (coordinates I a)
        let r := Prod.map (inverse I a) (inverse I a)
        (∀ u∈ChartDomination.coordinateSet e r G,∃ Ψ : E₀×E₀ → E₀×E₀,
          HasFDerivAt Ψ (fderiv ℝ Ψ u) u ∧ (81/121:ℝ)≤|(fderiv ℝ Ψ u).det| ∧
          Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e r G] u] (e ∘ Φ ∘ r)) →
        (∀ x∈G,(3/4:ℝ)*(f ((e x).1)*f ((e x).2))≤
          f ((e (Φ x)).1)*f ((e (Φ x)).2)) →
        (((μ.restrict Q).prod (μ.restrict Q)).restrict G).map Φ≤
          (2 : ℝ≥0∞) • (μ.restrict Q).prod (μ.restrict Q) := by
  classical
  obtain ⟨f,hf,hpos,hm⟩ := pair_cell_density I hclosed μ hμ a
  refine ⟨f,hf,hpos,?_⟩
  intro Q hQ hQU G hG hGQ Φ hΦ hout hinj e r hlocal hd
  let W := ChartDomination.coordinateSet (coordinates I a) (inverse I a) Q
  let dQ := W.indicator f
  have he : Measurable e := (measurable_coordinates I a).prodMap (measurable_coordinates I a)
  have hr : Measurable r := (measurable_inverse I hclosed a).prodMap (measurable_inverse I hclosed a)
  have hleft : ∀ x∈Q×ˢQ,r (e x)=x := by
    intro x hx
    exact Prod.ext (inverse_coordinates I a x.1 (hQU hx.1))
      (inverse_coordinates I a x.2 (hQU hx.2))
  have hfull : ((μ.restrict Q).prod (μ.restrict Q)) (Q×ˢQ)ᶜ=0 := by
    rw [Measure.prod_restrict,Measure.restrict_apply (hQ.prod hQ).compl,
      compl_inter_self,measure_empty]
  have hcoord (x : M×M) (hx : x∈Q×ˢQ) :
      dQ (e x).1=f (e x).1 ∧ dQ (e x).2=f (e x).2 := by
    change W.indicator f (coordinates I a x.1)=f (coordinates I a x.1) ∧
      W.indicator f (coordinates I a x.2)=f (coordinates I a x.2)
    constructor
    · apply Set.indicator_of_mem
      exact ⟨by simpa only [Prod.map_fst,inverse_coordinates I a x.1 (hQU hx.1)] using hx.1,
        by simp only [inverse_coordinates I a x.1 (hQU hx.1)]⟩
    · apply Set.indicator_of_mem
      exact ⟨by simpa only [Prod.map_snd,inverse_coordinates I a x.2 (hQU hx.2)] using hx.2,
        by simp only [inverse_coordinates I a x.2 (hQU hx.2)]⟩
  let : Measure.IsAddHaarMeasure (volume : Measure (E₀×E₀)) := by
    change Measure.IsAddHaarMeasure ((volume : Measure E₀).prod volume)
    infer_instance
  apply ChartDomination.local_two (E := E₀×E₀) ((μ.restrict Q).prod (μ.restrict Q)) volume
    (fun u : E₀×E₀ => dQ u.1*dQ u.2) (Q×ˢQ) G hfull hGQ hG e r he hr hleft
    (hm Q hQ hQU) Φ hΦ hout hinj hlocal
  intro u hu
  have hx := hGQ hu.1
  have hy := hout hu.1
  have hin := hcoord (r u) hx
  have hot := hcoord (Φ (r u)) hy
  have hin' : dQ u.1=f u.1 ∧ dQ u.2=f u.2 := by simpa only [hu.2] using hin
  rw [hin'.1,hin'.2,hot.1,hot.2]
  refine ⟨?_,?_⟩
  · have hu₁ : u.1∈(extChartAt I a).target := by
      rw [←hu.2]
      change coordinates I a (r u).1∈(extChartAt I a).target
      rw [coordinates_eq I a _ (hQU hx.1)]
      exact (extChartAt I a).map_source (hQU hx.1)
    have hu₂ : u.2∈(extChartAt I a).target := by
      rw [←hu.2]
      change coordinates I a (r u).2∈(extChartAt I a).target
      rw [coordinates_eq I a _ (hQU hx.2)]
      exact (extChartAt I a).map_source (hQU hx.2)
    exact mul_nonneg (hpos _ hu₁).le (hpos _ hu₂).le
  · simpa only [hu.2] using hd (r u) hu.1
end SmoothObstruction.ChartDensity

namespace SmoothObstruction.DensityUniform
open Set Metric
variable {E : Type*} [PseudoMetricSpace E]

/-- Positive compact smooth-chart densities admit uniform relative, rather
than absolute, estimates. Only continuity is used, valid up to boundary. -/
theorem relative (K : Set E) (hK : IsCompact K) (f : E → ℝ)
    (hf : ContinuousOn f K) (hpos : ∀ x∈K,0<f x) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ x∈K,∀ y∈K,dist x y<δ → |f y-f x|≤ε*f x := by
  by_cases hem : K.Nonempty
  · obtain ⟨x₀,hx₀,hmin⟩ := hK.exists_isMinOn hem hf
    have hmc : 0<ε*f x₀ := mul_pos hε (hpos x₀ hx₀)
    obtain ⟨δ,hδ,huc⟩ := Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous hf)
      (ε*f x₀) hmc
    refine ⟨δ,hδ,fun x hx y hy hxy => ?_⟩
    have hh := huc x hx y hy hxy
    have hle := mul_le_mul_of_nonneg_left (hmin hx) hε.le
    have hh' : |f y-f x|≤ε*f x₀ := by simpa only [Real.dist_eq,abs_sub_comm] using hh.le
    exact hh'.trans hle
  · refine ⟨1,zero_lt_one,fun x hx => ?_⟩
    exact (hem ⟨x,hx⟩).elim

/-- The density portion of the joint switch has a uniform three-quarter
lower bound once both matched point pairs are sufficiently close. -/
theorem pair_lower (K : Set E) (hK : IsCompact K) (f : E → ℝ)
    (hf : ContinuousOn f K) (hpos : ∀ x∈K,0<f x) :
    ∃ δ : ℝ,0<δ ∧ ∀ x∈K,∀ y∈K,∀ z∈K,∀ w∈K,
      dist x z<δ → dist y w<δ → (3/4:ℝ)*(f x*f y)≤f z*f w := by
  obtain ⟨δ,hδ,hrel⟩ := relative K hK f hf hpos (by norm_num : 0<(1/10:ℝ))
  refine ⟨δ,hδ,fun x hx y hy z hz w hw hxz hyw => ?_⟩
  have hx' : (9/10:ℝ)*f x≤f z := by
    have h := abs_le.mp (hrel x hx z hz hxz); linarith
  have hy' : (9/10:ℝ)*f y≤f w := by
    have h := abs_le.mp (hrel y hy w hw hyw); linarith
  have hp := mul_le_mul hx' hy' (mul_nonneg (by norm_num) (hpos y hy).le) (hpos z hz).le
  nlinarith [mul_pos (hpos x hx) (hpos y hy)]
end SmoothObstruction.DensityUniform

namespace SmoothObstruction.ChartDensity
open Set Metric MeasureTheory Filter Topology
open scoped ENNReal Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- The authentic local coordinate germs yield domination of the ORIGINAL
cell-weighted experiment. Compact positive density is controlled before any
partition or retained set is chosen. Zero-weight cells require no exception,
and neither cells nor retained pairs are conditionally renormalized. -/
theorem original_law_two (hclosed : IsClosed (range I))
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : SmoothPositiveDensity I μ)
    (a : ι → M) (K : ι → Set M) (hK : ∀ i,IsCompact (K i))
    (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r : ℝ,0<r ∧ ∀ {J : Type*} [Fintype J] [MeasurableSpace J]
      [MeasurableSingletonClass J] (L : M → J) (c : M → ι) (chart : J → ι),
      Measurable L → (∀ x,x∈K (c x)) → (∀ x,chart (L x)=c x) →
      (∀ x y,L x=L y → ‖coordinates I (a (c x)) x-coordinates I (a (c x)) y‖<r) →
      ∀ (G : Set (M×M)) (Φ : M×M → M×M),MeasurableSet G → Measurable Φ →
      (∀ u∈G,L u.1=L u.2 ∧ L (Φ u).1=L u.1 ∧ L (Φ u).2=L u.2) →
      InjOn Φ G →
      (∀ (j : J),let Q := L ⁻¹' {j}
        let A := G∩(Q×ˢQ)
        let e := Prod.map (coordinates I (a (chart j))) (coordinates I (a (chart j)))
        let s := Prod.map (inverse I (a (chart j))) (inverse I (a (chart j)))
        ∀ u∈ChartDomination.coordinateSet e s A,∃ Ψ : E₀×E₀ → E₀×E₀,
          HasFDerivAt Ψ (fderiv ℝ Ψ u) u ∧ (81/121:ℝ)≤|(fderiv ℝ Ψ u).det| ∧
          Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e s A] u] (e ∘ Φ ∘ s)) →
      ((PairLaw.law μ L).restrict G).map Φ≤(2 : ℝ≥0∞) • PairLaw.law μ L ∧
      ((PairLaw.law μ L).restrict G).map (fun u => (Φ u).1)≤(2 : ℝ≥0∞) • μ := by
  classical
  choose f hf hpos hcell using fun i => pair_cell_two I hclosed μ hμ (a i)
  let K' (i : ι) := (extChartAt I (a i)) '' K i
  have hsrc (i : ι) : K i⊆(extChartAt I (a i)).source := by
    simpa only [extChartAt_source] using hKU i
  have hKt (i : ι) : K' i⊆(extChartAt I (a i)).target :=
    image_subset_iff.mpr (fun _ hx => (extChartAt I (a i)).map_source (hsrc i hx))
  have hcompact (i : ι) : IsCompact (K' i) :=
    (hK i).image_of_continuousOn ((continuousOn_extChartAt (a i)).mono (hsrc i))
  choose r hr hd using fun i => DensityUniform.pair_lower (K' i) (hcompact i) (f i)
    ((hf i).continuousOn.mono (hKt i)) (fun x hx => hpos i x (hKt i hx))
  obtain ⟨r₀,hr₀,hr₀r⟩ := CarriedCharts.finite_positive_lower r hr
  refine ⟨r₀,hr₀,?_⟩
  intro J _ _ _ L c chart hL hc hchart hdiam G Φ hG hΦ hkeep hinj hgerm
  have hdom : ((PairLaw.law μ L).restrict G).map Φ≤(2 : ℝ≥0∞) • PairLaw.law μ L := by
    apply PairLaw.law_domination μ L G Φ hΦ 2
    intro j
    let Q := L ⁻¹' {j}
    let A := G∩(Q×ˢQ)
    have hQ : MeasurableSet Q := hL (measurableSet_singleton _)
    have hA : MeasurableSet A := hG.inter (hQ.prod hQ)
    have hchartQ {x : M} (hx : x∈Q) : c x=chart j := by
      rw [←hchart x]; exact congrArg chart hx
    have hQK : Q⊆K (chart j) := by
      intro x hx; rw [←hchartQ hx]; exact hc x
    have hQU : Q⊆(extChartAt I (a (chart j))).source := hQK.trans (hsrc _)
    have hout : MapsTo Φ A (Q×ˢQ) := by
      rintro u ⟨hu,hux,huy⟩
      have hh := hkeep u hu
      exact ⟨hh.2.1.trans hux,hh.2.2.trans huy⟩
    have hdensity : ∀ x∈A,(3/4:ℝ)*(f (chart j) (coordinates I (a (chart j)) x.1)*
        f (chart j) (coordinates I (a (chart j)) x.2))≤
        f (chart j) (coordinates I (a (chart j)) (Φ x).1)*
          f (chart j) (coordinates I (a (chart j)) (Φ x).2) := by
      intro x hx
      have ho := hout hx
      have mem {y : M} (hy : y∈Q) : coordinates I (a (chart j)) y∈K' (chart j) := by
        rw [coordinates_eq I _ _ (hQU hy)]
        exact mem_image_of_mem _ (hQK hy)
      apply hd (chart j) _ (mem hx.2.1) _ (mem hx.2.2) _ (mem ho.1) _ (mem ho.2)
      · have he := hdiam x.1 (Φ x).1 (hkeep x hx.1).2.1.symm
        rw [hchartQ hx.2.1] at he
        apply lt_of_lt_of_le _ (hr₀r _)
        simpa only [dist_eq_norm] using he
      · have he := hdiam x.2 (Φ x).2 (hkeep x hx.1).2.2.symm
        rw [hchartQ hx.2.2] at he
        apply lt_of_lt_of_le _ (hr₀r _)
        simpa only [dist_eq_norm] using he
    have hh := hcell (chart j) Q hQ hQU A hA (fun _ hx => hx.2) Φ hΦ hout
      (hinj.mono inter_subset_left) (hgerm j) hdensity
    have he : (((μ.restrict Q).prod (μ.restrict Q)).restrict A)=
        (((μ.restrict Q).prod (μ.restrict Q)).restrict G) := by
      rw [Measure.prod_restrict,Measure.restrict_restrict hA,Measure.restrict_restrict hG]
      congr 1
      exact inter_eq_self_of_subset_left inter_subset_right
    rw [he] at hh
    exact hh
  exact ⟨hdom,PairLaw.first_output_domination μ L hL G Φ hΦ 2 hdom⟩
end SmoothObstruction.ChartDensity

namespace SmoothObstruction.ChartDensity
open Set Metric MeasureTheory Filter Topology
open scoped ENNReal Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- Physical retained-pair germs in their old starting charts suffice for the
original cell-weighted, unnormalized domination. The germ is only shrunk when
passing to the original cell; no new partition labels are introduced. -/
theorem physical_original_law_two (hclosed : IsClosed (range I))
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : SmoothPositiveDensity I μ)
    (a : ι → M) (K : ι → Set M) (hK : ∀ i,IsCompact (K i))
    (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r : ℝ,0<r ∧ ∀ {J : Type*} [Fintype J] [MeasurableSpace J]
      [MeasurableSingletonClass J] (L : M → J) (c : M → ι) (chart : J → ι),
      Measurable L → (∀ x,x∈K (c x)) → (∀ x,chart (L x)=c x) →
      (∀ x y,L x=L y → ‖coordinates I (a (c x)) x-coordinates I (a (c x)) y‖<r) →
      ∀ (G : Set (M×M)) (Φ : M×M → M×M),MeasurableSet G → Measurable Φ →
      (∀ u∈G,L u.1=L u.2 ∧ L (Φ u).1=L u.1 ∧ L (Φ u).2=L u.2) →
      InjOn Φ G →
      (∀ x y,(x,y)∈G →
        let e := Prod.map (coordinates I (a (c x))) (coordinates I (a (c x)))
        let s := Prod.map (inverse I (a (c x))) (inverse I (a (c x)))
        let u := ((extChartAt I (a (c x))) x,(extChartAt I (a (c x))) y)
        ∃ Ψ : E₀×E₀ → E₀×E₀,HasFDerivAt Ψ (fderiv ℝ Ψ u) u ∧
          (81/121:ℝ)≤|(fderiv ℝ Ψ u).det| ∧
          Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e s G] u] (e ∘ Φ ∘ s)) →
      ((PairLaw.law μ L).restrict G).map Φ≤(2 : ℝ≥0∞) • PairLaw.law μ L ∧
      ((PairLaw.law μ L).restrict G).map (fun u => (Φ u).1)≤(2 : ℝ≥0∞) • μ := by
  obtain ⟨r,hr,hh⟩ := original_law_two I hclosed μ hμ a K hK hKU
  refine ⟨r,hr,?_⟩
  intro J _ _ _ L c chart hL hc hchart hdiam G Φ hG hΦ hkeep hinj hgerm
  apply hh L c chart hL hc hchart hdiam G Φ hG hΦ hkeep hinj
  intro j Q A e s u hu
  let z := s u
  have hz : z∈G := hu.1.1
  have hzQ : z.1∈Q ∧ z.2∈Q := hu.1.2
  have hcz : c z.1=chart j := by rw [←hchart z.1]; exact congrArg chart hzQ.1
  have hcz' : c z.2=chart j := by rw [←hchart z.2]; exact congrArg chart hzQ.2
  have hsrc₁ : z.1∈(extChartAt I (a (chart j))).source := by
    rw [←hcz,extChartAt_source]; exact hKU _ (hc z.1)
  have hsrc₂ : z.2∈(extChartAt I (a (chart j))).source := by
    rw [←hcz',extChartAt_source]; exact hKU _ (hc z.2)
  have he : ((extChartAt I (a (chart j))) z.1,(extChartAt I (a (chart j))) z.2)=u := by
    have h := hu.2
    change (coordinates I (a (chart j)) z.1,coordinates I (a (chart j)) z.2)=u at h
    rwa [coordinates_eq I _ _ hsrc₁,coordinates_eq I _ _ hsrc₂] at h
  obtain ⟨Ψ,hΨ,hd,hag⟩ := hgerm z.1 z.2 hz
  rw [hcz,he] at hΨ hd hag
  refine ⟨Ψ,hΨ,hd,?_⟩
  apply hag.filter_mono
  apply nhdsWithin_mono
  intro v hv
  exact ⟨hv.1.1,hv.2⟩
end SmoothObstruction.ChartDensity

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    {ι C : Type*}
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- The original coarse partition is locally constant at every retained
one-point input. This uses the original grid margin and fixed chart core only. -/
lemma original_coarse_germ (a : ι → M) (c : M → ι) (P : M → C)
    (x : M) (hx : x∈(chartAt H (a (c x))).source) (s δ : ℝ) (hs : 0<s) (hδ : 0<δ)
    (hcore : ∀ y,dist y x ≤ s → c y=c x)
    (hrec : ∀ y,c y=c x →
      ‖(extChartAt I (a (c x))) y-(extChartAt I (a (c x))) x‖≤δ/4 → P y=P x) :
    ∀ᶠ y in 𝓝 x,P y=P x := by
  have hcont : ContinuousAt (fun y => ‖(extChartAt I (a (c x))) y-(extChartAt I (a (c x))) x‖) x :=
    (((continuousOn_extChartAt (a (c x))).continuousAt
      (by simpa only [extChartAt_source] using (chartAt H (a (c x))).open_source.mem_nhds hx)).sub continuousAt_const).norm
  have hz : ‖(extChartAt I (a (c x))) x-(extChartAt I (a (c x))) x‖<δ/4 := by
    simpa using (show (0:ℝ)<δ/4 by positivity)
  filter_upwards [Metric.ball_mem_nhds x hs,hcont.eventually (gt_mem_nhds hz),
    (chartAt H (a (c x))).open_source.mem_nhds hx] with y hy hdist hys
  apply hrec y (hcore y (Metric.mem_ball.mp hy).le)
  exact hdist.le

/-- Only the six original start/end labels are fixed near an input pair.
No intermediate orbit-code refinement is used. -/
lemma six_original_labels (S : Diffeomorph I I M M ∞) (P : M → C)
    (a₀ x y : M) (n : ℕ)
    (hx : x∈(extChartAt I a₀).source) (hy : y∈(extChartAt I a₀).source)
    (hiX : (extChartAt I a₀) x∈interior (range I))
    (hiY : (extChartAt I a₀) y∈interior (range I))
    (hx₀ : ∀ᶠ z in 𝓝 x,P z=P x) (hy₀ : ∀ᶠ z in 𝓝 y,P z=P y)
    (hxF : ∀ᶠ z in 𝓝 (S^[n] x),P z=P (S^[n] x))
    (hyF : ∀ᶠ z in 𝓝 (S^[n] y),P z=P (S^[n] y))
    (hxB : ∀ᶠ z in 𝓝 (S.symm^[n] x),P z=P (S.symm^[n] x))
    (hyB : ∀ᶠ z in 𝓝 (S.symm^[n] y),P z=P (S.symm^[n] y)) :
    ∀ᶠ t in 𝓝 ((extChartAt I a₀ x),(extChartAt I a₀ y)),
      P ((extChartAt I a₀).symm t.1)=P x ∧ P ((extChartAt I a₀).symm t.2)=P y ∧
      P (S^[n] ((extChartAt I a₀).symm t.1))=P (S^[n] x) ∧
      P (S^[n] ((extChartAt I a₀).symm t.2))=P (S^[n] y) ∧
      P (S.symm^[n] ((extChartAt I a₀).symm t.1))=P (S.symm^[n] x) ∧
      P (S.symm^[n] ((extChartAt I a₀).symm t.2))=P (S.symm^[n] y) := by
  have hix := inverse_continuousAt_interior I a₀ _ ((extChartAt I a₀).map_source hx) hiX
  have hiy := inverse_continuousAt_interior I a₀ _ ((extChartAt I a₀).map_source hy) hiY
  have hcx : Tendsto (fun t : E₀×E₀ => (extChartAt I a₀).symm t.1)
      (𝓝 ((extChartAt I a₀ x),(extChartAt I a₀ y))) (𝓝 x) := by
    have ht := hix.tendsto.comp (continuous_fst.tendsto ((extChartAt I a₀ x),(extChartAt I a₀ y)))
    simpa only [Function.comp_def,(extChartAt I a₀).left_inv hx] using ht
  have hcy : Tendsto (fun t : E₀×E₀ => (extChartAt I a₀).symm t.2)
      (𝓝 ((extChartAt I a₀ x),(extChartAt I a₀ y))) (𝓝 y) := by
    have ht := hiy.tendsto.comp (continuous_snd.tendsto ((extChartAt I a₀ x),(extChartAt I a₀ y)))
    simpa only [Function.comp_def,(extChartAt I a₀).left_inv hy] using ht
  have hF := S.continuous.iterate n
  have hB := S.symm.continuous.iterate n
  filter_upwards [hcx.eventually hx₀,hcy.eventually hy₀,
    ((hF.tendsto x).comp hcx).eventually hxF,((hF.tendsto y).comp hcy).eventually hyF,
    ((hB.tendsto x).comp hcx).eventually hxB,((hB.tendsto y).comp hcy).eventually hyB] with t h₀ h₁ h₂ h₃ h₄ h₅
  exact ⟨h₀,h₁,h₂,h₃,h₄,h₅⟩
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric MeasureTheory Filter Topology EndpointFrame FiniteGreen ShortBin
open scoped Manifold ContDiff ENNReal
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MeasurableSpace M] [BorelSpace M] [StandardBorelSpace M] [Nonempty M]
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- The genuine global pair switch at one scale. Every constant precedes the
partition alphabets and ranks. Inputs are actual bilateral gauges, original
grid margins, and explicit scalar budgets; the conclusion is unnormalized
ORIGINAL-law domination, not an assumed Jacobian or switch certificate. -/
theorem genuine_pair_switch (hclosed : IsClosed (range I))
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : SmoothPositiveDensity I μ)
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    (s Dg : ℝ) (hs : 0<s) (hDg : 0≤Dg) :
    ∃ r₀ C₀ σ r₁ C₁ rg Cg β K₀F CreF C₁F K₀B CreB C₁B rμ : ℝ,
      0<r₀ ∧ 1≤C₀ ∧ 0<σ ∧ 0<r₁ ∧ 1≤C₁ ∧ 0<rg ∧ 1≤Cg ∧ 0<β ∧
      1≤K₀F ∧ 0≤CreF ∧ 0≤C₁F ∧ 1≤K₀B ∧ 0≤CreB ∧ 0≤C₁B ∧ 0<rμ ∧
      ∀ {C J : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
        [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
        (c : M → ι) (P : M → C) (L : M → J) (π : J → C) (chart : C → ι)
        (G R V Wc Wp : Set M) (n : ℕ) (b R₀ Cext ε g α r δc δp H₀ : ℝ)
        (γ : C → ℝ),
        let B := Dg*(b*n)
        let δ := Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)
        let ρ := 2*C₀*bvpInverseBound B α n*r
        let E := 4*Real.exp (2*B)*(2*Real.exp (2*B))*(ε+2*Real.exp (2*B)^2*Real.exp (-2*g*n))*(C₀*r)+
          bvpInverseBound B α n*C₀*ρ^2
        ∀ (A : ∀ x:G,BilateralGauge I S a c n B R₀ x) (T : G → Finset (Fin d)) (ref : G → G)
          (Wf Wb : C×C → Submodule ℝ E₀),
        Measurable c → Measurable P → Measurable L → MeasurableSet R → (hRG : R⊆G) →
        (∀ x,x∈K (c x)) → (∀ x,π (L x)=P x) → (∀ x,chart (P x)=c x) →
        (∀ x∈R,I.IsInteriorPoint x) →
        (∀ x:G,P (ref x)=P x) → (∀ x y:G,P x=P y → (T x).card=(T y).card) →
        (∀ x y:G,P x=P y → ref x=ref y) →
        (∀ x:G,
          ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))ᶜ).starProjection-
            ((A x).forwardSpace I S a c 0 (T x)ᶜ).starProjection‖≤ε ∧
          ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))).starProjection-
            ((A x).forwardSpace I S a c 0 (T x)).starProjection‖≤ε) →
        (∀ x:G,
          Module.finrank ℝ (Wf (P x,P (S^[n] x)))=(T x).card ∧
          Module.finrank ℝ (Wb (P x,P (S.symm^[n] x)))=d-(T x).card ∧
          ‖((A x).forwardSpace I S a c n (T x)).starProjection-
            (Wf (P x,P (S^[n] x))).starProjection‖≤1/2 ∧
          ‖((A x).backwardSpace I S a c n (T x)ᶜ).starProjection-
            (Wb (P x,P (S.symm^[n] x))).starProjection‖≤1/2) →
        0≤b → 1≤b*n → 0≤R₀ → 0≤Cext → 0≤ε → ε≤1/2 →
        Real.exp (2*B)*(2*ε)≤1/2 → 0≤g →
        (∀ x:G,∀ j∈(T x)ᶜ,(A x).lam j≤γ (P x)-g) →
        (∀ x:G,∀ j∈T x,γ (P x)+g≤(A x).lam j) →
        (2*Real.exp (2*B))*(2*(2*Real.exp (2*B)^2*Real.exp (-2*g*n)))≤1/2 →
        (∀ x:G,|γ (P x)|+|g|≤α) → 0≤r → δ≤r₀ → δ≤rg →
        0≤ρ → ρ≤δ → ρ≤σ → ρ≤δc/4 → ρ≤r₁ → C₁*ρ≤δ → Cg*ρ<δ →
        K₀F*δ≤1 → K₀B*δ≤1 → 0<δc → 0≤H₀ → H₀*E≤δp/4 →
        (∀ p≤d,∀ F : E₀ →L[ℝ] E₀,‖ExteriorStability.exterior p F‖≤Cext*(max 1 ‖F‖)^p) →
        (∀ p≤d,EndpointBudget.admissible d p Dg R₀ Cext K₀F CreF C₁F b n g ε β) →
        (∀ p≤d,EndpointBudget.admissible d p Dg R₀ Cext K₀B CreB C₁B b n g ε β) →
        (∀ x∈R,∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) δ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) δ⊆interior (range I)) →
        (∀ x∈R,∀ y∈R,L x=L y →
          ‖(extChartAt I (a (c y))) y-(extChartAt I (a (c x))) x‖≤C₀*r) →
        bvpInverseBound B α n*C₀*δ≤1/4 → bvpInverseBound B α n*C₀*r≤δ/4 →
        (∀ x y,L x=L y → ‖ChartDensity.coordinates I (a (c x)) x-ChartDensity.coordinates I (a (c x)) y‖<rμ) →
        (∀ x∈V,∀ z,dist z x ≤ s → c z=c x) →
        (∀ x z,x∉Wc → c z=c x →
          ‖ChartDensity.coordinates I (a (c x)) z-ChartDensity.coordinates I (a (c x)) x‖≤δc/4 → P z=P x) →
        (∀ x y z,(hx : x∈R) → L x=L y → x∉Wp → y∉Wp → P z=P x →
          H₀*‖ChartDensity.coordinates I (a (c x)) z-(ChartDensity.coordinates I (a (c x)) x+
            (((A (ref ⟨x,hRG hx⟩)).forward I S a c).splitting (T (ref ⟨x,hRG hx⟩))ᶜ).slow 0
              (ChartDensity.coordinates I (a (c x)) y-ChartDensity.coordinates I (a (c x)) x))‖≤δp/4 → L z=L x) →
        (∀ x∈R,x∈V ∧ x∉Wc ∧ x∉Wp ∧
          S^[n] x∈V ∧ S^[n] x∉Wc ∧ S.symm^[n] x∈V ∧ S.symm^[n] x∉Wc) →
        let Gp := {u : M×M | u.1∈R ∧ u.2∈R ∧ L u.1=L u.2}
        ∃ Φ : M×M → M×M,Measurable Φ ∧ MeasurableSet Gp ∧ InjOn Φ Gp ∧
          ((PairLaw.law μ L).restrict Gp).map Φ≤(2 : ℝ≥0∞) • PairLaw.law μ L ∧
          ((PairLaw.law μ L).restrict Gp).map (fun u => (Φ u).1)≤(2 : ℝ≥0∞) • μ ∧
          ∀ u∈Gp,originalTube I S a c (n:=n) ρ u.1 (Φ u).1 ∧
            originalTube I S.symm a c (n:=n) ρ u.2 (Φ u).1 := by
  classical
  obtain ⟨r₀,C₀,hr₀,hC₀,hcanonical⟩ := canonical_original_switch_complete I hclosed S a K hK hKU
  obtain ⟨σ,r₁,C₁,hσ,hr₁,hC₁,hrecover⟩ := recovered_original_pair I hclosed a K hK hKU hs
  obtain ⟨rg,Cg,β,K₀F,CreF,C₁F,K₀B,CreB,C₁B,hrg,hCg,hβ,hKF,hCrF,hCF,hKB,hCrB,hCB,hgerm⟩ :=
    gauge_original_germ_sharp I hclosed S a K hK hKU Dg hDg
  obtain ⟨rμ,hrμ,hlaw⟩ := ChartDensity.physical_original_law_two I hclosed μ hμ a K hK hKU
  refine ⟨r₀,C₀,σ,r₁,C₁,rg,Cg,β,K₀F,CreF,C₁F,K₀B,CreB,C₁B,rμ,
    hr₀,hC₀,hσ,hr₁,hC₁,hrg,hCg,hβ,hKF,hCrF,hCF,hKB,hCrB,hCB,hrμ,?_⟩
  intro C J _ _ _ _ _ _ c P L π chart G R V Wc Wp n b R₀ Cext ε g α r δc δp H₀ γ B δ ρ E
    A T ref Wf Wb hc hP hL hR hRG hcover hπ hchart hint href hcard hreff hstart hend
    hb hbn hR₀ hCext hε hεhalf hsmall hg hslow hfast hgap hα hr hδr hδrg
    hρ hρδ hρσ hρc hρr₁ hρC hρCg hδF hδB hδc hH₀ hE hpoly hbudF hbudB
    hsafe hnear hcontract hdata hdiam hcore hcoarse hprod hret Gp
  have hδ : 0<δ := Real.exp_pos _
  have hLP (x y : M) (h : L x=L y) : P x=P y := by rw [←hπ x,←hπ y,h]
  have hPc (x y : M) (h : P x=P y) : c x=c y := by rw [←hchart x,←hchart y,h]
  have hsrc (x : M) : x∈(extChartAt I (a (c x))).source := by
    rw [extChartAt_source]; exact hKU _ (hcover x)
  have hend' (x : G) :
      Module.finrank ℝ ((A x).forwardSpace I S a c n (T x))=Module.finrank ℝ (Wf (P x,P (S^[n] x))) ∧
      Module.finrank ℝ ((A x).backwardSpace I S a c n (T x)ᶜ)=Module.finrank ℝ (Wb (P x,P (S.symm^[n] x))) ∧
      ‖((A x).forwardSpace I S a c n (T x)).starProjection-(Wf (P x,P (S^[n] x))).starProjection‖≤1/2 ∧
      ‖((A x).backwardSpace I S a c n (T x)ᶜ).starProjection-(Wb (P x,P (S.symm^[n] x))).starProjection‖≤1/2 := by
    refine ⟨(EuclideanSplitting.finrank_groupSpace _ _ _ _ _).trans (hend x).1.symm,?_,(hend x).2.2⟩
    calc
      _ = (T x)ᶜ.card := EuclideanSplitting.finrank_groupSpace _ _ _ _ _
      _ = d-(T x).card := by rw [Finset.card_compl]; simp only [Fintype.card_fin]
      _ = _ := (hend x).2.1.symm
  obtain ⟨Φ,hΦ,hswitch,hself,huniq⟩ := hcanonical C J c P L G R n B R₀ ε g α r δ γ A T ref Wf Wb
    hc hP hL hR hRG hcover hLP hPc hint href hcard hreff hstart hend' hε hεhalf hsmall hslow hfast hgap
    hα hr hδ hδr hsafe hnear hcontract hdata
  have hpair (u : M×M) (hx : u.1∈R) (hy : u.2∈R) (he : L u.1=L u.2) :=
    hswitch ⟨u.1,hRG hx⟩ ⟨u.2,hRG hy⟩ hx hy he
  let U (x : M) : E₀ →L[ℝ] E₀ := if hx : x∈G then
    (((A (ref ⟨x,hx⟩)).forward I S a c).splitting (T (ref ⟨x,hx⟩))ᶜ).slow 0 else 0
  have hU (x : M) (hx : x∈G) : U x=
      (((A (ref ⟨x,hx⟩)).forward I S a c).splitting (T (ref ⟨x,hx⟩))ᶜ).slow 0 := by simp only [U,dite_eq_left hx]
  have hsharp (u : M×M) (hx : u.1∈R) (hy : u.2∈R) (he : L u.1=L u.2) :
      originalTube I S a c (n:=n) ρ u.1 (Φ u).1 ∧
      originalTube I S.symm a c (n:=n) ρ u.2 (Φ u).1 ∧
      originalTube I S a c (n:=n) ρ u.2 (Φ u).2 ∧
      originalTube I S.symm a c (n:=n) ρ u.1 (Φ u).2 ∧
      ‖(extChartAt I (a (c u.1))) (Φ u).1-(extChartAt I (a (c u.1))) u.1-
        U u.1 ((extChartAt I (a (c u.2))) u.2-(extChartAt I (a (c u.1))) u.1)‖≤E ∧
      ‖(extChartAt I (a (c u.2))) (Φ u).2-(extChartAt I (a (c u.2))) u.2-
        U u.2 ((extChartAt I (a (c u.1))) u.1-(extChartAt I (a (c u.2))) u.2)‖≤E := by
    rw [hU u.1 (hRG hx),hU u.2 (hRG hy)]
    exact (hpair u hx hy he).2.2.2.2.2.2.2.2
  have heqs (u : M×M) (hx : u.1∈R) (hy : u.2∈R) (he : L u.1=L u.2) :
      originalEndpoint I S a c (n:=n) (Wf (P u.1,P (S^[n] u.1))) u.1 (Φ u).1 ∧
      originalEndpoint I S.symm a c (n:=n) (Wb (P u.1,P (S.symm^[n] u.1))) u.1 (Φ u).2 ∧
      originalEndpoint I S a c (n:=n) (Wf (P u.2,P (S^[n] u.2))) u.2 (Φ u).2 ∧
      originalEndpoint I S.symm a c (n:=n) (Wb (P u.2,P (S.symm^[n] u.2))) u.2 (Φ u).1 := by
    have h := hpair u hx hy he
    exact ⟨h.2.2.2.2.1,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.1⟩
  obtain ⟨hkeep,hlabels,hinj⟩ := hrecover S c P L π chart hπ hchart n δ ρ δc δp H₀ E R V Wc Wp U Φ Wf Wb
    hcover hρ hρσ hρc hρr₁ hρC hH₀ hE hcore hcoarse
    (fun x y z hx he hxW hyW hz herr => hprod x y z hx he hxW hyW hz (by rwa [hU x (hRG hx)] at herr))
    hret hsafe hsharp heqs hself
  have hGp : MeasurableSet Gp :=
    (hR.preimage measurable_fst).inter ((hR.preimage measurable_snd).inter
      (measurableSet_eq_fun (hL.comp measurable_fst) (hL.comp measurable_snd)))
  have hlc (x : M) (hxV : x∈V) (hxW : x∉Wc) : ∀ᶠ z in 𝓝 x,P z=P x := by
    apply original_coarse_germ I a c P x (by simpa only [extChartAt_source] using hsrc x) s δc hs hδc (hcore x hxV)
    intro y hcy hdist
    apply hcoarse x y hxW hcy
    have hsy : y∈(extChartAt I (a (c x))).source := by rw [←hcy]; exact hsrc y
    rwa [ChartDensity.coordinates_eq I _ _ hsy,ChartDensity.coordinates_eq I _ _ (hsrc x)]
  have hgerms (x y : M) (hxy : (x,y)∈Gp) :
      let e := Prod.map (ChartDensity.coordinates I (a (c x))) (ChartDensity.coordinates I (a (c x)))
      let si := Prod.map (ChartDensity.inverse I (a (c x))) (ChartDensity.inverse I (a (c x)))
      let u := ((extChartAt I (a (c x))) x,(extChartAt I (a (c x))) y)
      ∃ Ψ : E₀×E₀ → E₀×E₀,HasFDerivAt Ψ (fderiv ℝ Ψ u) u ∧
        (81/121:ℝ)≤|(fderiv ℝ Ψ u).det| ∧
        Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e si Gp] u] (e ∘ Φ ∘ si) := by
    have hx := hxy.1
    have hy := hxy.2.1
    have hLxy := hxy.2.2
    have hPxy := hLP x y hLxy
    have hcxy := hPc x y hPxy
    let X : G := ⟨x,hRG hx⟩
    let Y : G := ⟨y,hRG hy⟩
    let Z : G := ref X
    have hZx : P Z=P x := href X
    have hTx : (T X).card=(T Z).card := hcard X Z hZx.symm
    have hTy : (T Y).card=(T Z).card := hcard Y Z (hPxy.symm.trans hZx.symm)
    have hrefY : ref Y=Z := hreff Y X hPxy.symm
    have hSX := hstart X
    have hSY := hstart Y
    rw [hrefY] at hSY
    have ht := hsharp (x,y) hx hy hLxy
    have he := heqs (x,y) hx hy hLxy
    apply hgerm c P L R Wf Wb n b R₀ Cext δ ε (γ (P x)) g ρ Φ Gp x y hcover hPc hcxy
      hb hbn hR₀ hCext hε hg hρ hρδ hδrg hρCg hδF hδB hpoly hbudF hbudB
      (fun u hu => hu) huniq
      (fun u hu v hv huv => ⟨originalTube_mono I S a c n hρδ (hsharp (u,v) hu hv huv).2.2.1,
        originalTube_mono I S.symm a c n hρδ (hsharp (u,v) hu hv huv).2.2.2.1,
        (heqs (u,v) hu hv huv).2.2.1,(heqs (u,v) hu hv huv).2.1⟩)
      (fun t => ⟨(hsafe x hx t).1,(hsafe x hx t).2,(hsafe y hy t).1,(hsafe y hy t).2⟩)
      ht.1 ht.2.1 ht.2.2.1 ht.2.2.2.1 Z (A Z) (A X) (A Y) (T Z) (T X) (T Y) hTx hTy
      (hfast X) (fun j hj => hslow X j (Finset.mem_compl.mpr hj))
      (by simpa only [hPxy] using hfast Y) (by simpa only [hPxy] using fun j hj => hslow Y j (Finset.mem_compl.mpr hj))
      ((hend X).1.trans hTx) ((hend Y).1.trans hTy)
      ((hend X).2.1.trans (congrArg (d-·) hTx)) ((hend Y).2.1.trans (congrArg (d-·) hTy))
      (hend X).2.2.1 (hend Y).2.2.1 (hend X).2.2.2 (hend Y).2.2.2
      (by rw [norm_sub_rev]; exact hSX.2) (by rw [norm_sub_rev]; exact hSY.2)
      (by rw [norm_sub_rev]; exact hSX.1) (by rw [norm_sub_rev]; exact hSY.1)
      he.1 he.2.2.1 he.2.1 he.2.2.2
    have hsy : y∈(extChartAt I (a (c x))).source := by rw [hcxy]; exact hsrc y
    have hiX : (extChartAt I (a (c x))) x∈interior (range I) :=
      (hsafe x hx ⟨0,by omega⟩).1 (by simpa only [Function.iterate_zero_apply] using mem_closedBall_self hδ.le)
    have hiY : (extChartAt I (a (c x))) y∈interior (range I) := by
      rw [hcxy]
      exact (hsafe y hy ⟨0,by omega⟩).1 (by simpa only [Function.iterate_zero_apply] using mem_closedBall_self hδ.le)
    exact six_original_labels I S P (a (c x)) x y n (hsrc x) hsy hiX hiY
      (hlc x (hret x hx).1 (hret x hx).2.1) (hlc y (hret y hy).1 (hret y hy).2.1)
      (hlc _ (hret x hx).2.2.2.1 (hret x hx).2.2.2.2.1)
      (hlc _ (hret y hy).2.2.2.1 (hret y hy).2.2.2.2.1)
      (hlc _ (hret x hx).2.2.2.2.2.1 (hret x hx).2.2.2.2.2.2)
      (hlc _ (hret y hy).2.2.2.2.2.1 (hret y hy).2.2.2.2.2.2)
  have hlaw' := hlaw L c (chart ∘ π) hL hcover (fun x => by simp only [Function.comp_apply,hπ,hchart])
    hdiam Gp Φ hGp hΦ (fun u hu => ⟨hu.2.2,hkeep u hu⟩) hinj hgerms
  exact ⟨Φ,hΦ,hGp,hinj,hlaw'.1,hlaw'.2,fun u hu => ⟨(hsharp u hu.1 hu.2.1 hu.2.2).1,(hsharp u hu.1 hu.2.1 hu.2.2).2.1⟩⟩
end SmoothObstruction.ManifoldCoordinates

end

end OAI
