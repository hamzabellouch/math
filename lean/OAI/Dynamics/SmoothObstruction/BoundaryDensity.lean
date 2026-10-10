import OAI.Dynamics.SmoothObstruction.DensityBounds

namespace OAI

section

namespace SmoothObstruction.HalfspaceCollar
open Set MeasureTheory Metric
open scoped ENNReal Manifold

/-- Positive normal coordinate margin keeps the entire nonlinear tube in
 the original half-space. No extension across the boundary is used. -/
theorem closedBall_interior {d : ℕ} [NeZero d] (x : EuclideanSpace ℝ (Fin d))
    {δ : ℝ} (hx : δ<x 0) : closedBall x δ⊆interior (Set.range (𝓡∂ d)) := by
  intro y hy
  rw [interior_range_modelWithCornersEuclideanHalfSpace]
  have hh := PiLp.norm_apply_le (y-x) 0
  have hd : ‖y-x‖≤δ := by simpa only [mem_closedBall,dist_eq_norm] using hy
  change 0<y 0
  simp only [PiLp.sub_apply,Real.norm_eq_abs] at hh
  have h := (abs_le.mp (hh.trans hd)).1
  linarith

/-- The elementary quantitative codimension-one collar bound. Merely
knowing that the boundary is null would not imply the simultaneous
`[-n,n]` retained-mass estimate required in smooth switching. -/
theorem slab_volume_le {d : ℕ} (j : Fin d) (R ε : ℝ) :
    volume {x : EuclideanSpace ℝ (Fin d) | ‖x‖≤R ∧ 0≤x j ∧ x j≤ε}≤
      ENNReal.ofReal ε*(ENNReal.ofReal (2*R))^(d-1) := by
  classical
  let a : Fin d → ℝ := fun i => if i=j then 0 else -R
  let b : Fin d → ℝ := fun i => if i=j then ε else R
  have hsub : {x : EuclideanSpace ℝ (Fin d) | ‖x‖≤R ∧ 0≤x j ∧ x j≤ε}⊆
      WithLp.ofLp ⁻¹' Icc a b := by
    intro x hx
    constructor <;> intro i
    · by_cases hi : i=j
      · simpa [a,hi] using hx.2.1
      · have hh := (abs_le.mp ((PiLp.norm_apply_le x i).trans hx.1)).1
        simpa only [a,ite_eq_right hi] using hh
    · by_cases hi : i=j
      · simpa [b,hi] using hx.2.2
      · have hh := (abs_le.mp ((PiLp.norm_apply_le x i).trans hx.1)).2
        simpa only [b,ite_eq_right hi] using hh
  calc
    _ ≤ volume (WithLp.ofLp ⁻¹' Icc a b) := measure_mono hsub
    _ = ∏ i,ENNReal.ofReal (b i-a i) := by
      rw [(PiLp.volume_preserving_ofLp (Fin d)).measure_preimage measurableSet_Icc.nullMeasurableSet,
        Real.volume_Icc_pi]
    _ = ENNReal.ofReal ε*(ENNReal.ofReal (2*R))^(d-1) := by
      rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
      have he : ∀ i∈Finset.univ.erase j,ENNReal.ofReal (b i-a i)=ENNReal.ofReal (2*R) := by
        intro i hi
        have hj : i≠j := (Finset.mem_erase.mp hi).1
        simp only [a,b,ite_eq_right hj,sub_neg_eq_add,←two_mul]
      rw [Finset.prod_congr rfl he]
      simp [a,b,Finset.card_erase_of_mem]

end SmoothObstruction.HalfspaceCollar

namespace SmoothObstruction.HalfspaceCollar
open Set MeasureTheory Metric
open scoped ENNReal

/-- A bounded ORIGINAL chart density supported in a bounded patch retains
 the linear collar bound; the density is neither renormalized nor replaced
 by a uniform conditional law. -/
theorem supported_density_slab {d : ℕ} (j : Fin d) (R ε : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (A : ℝ≥0∞)
    (hf : ∀ x,f x≤A) (hzero : ∀ x,R<‖x‖ → f x=0) :
    (volume.withDensity f) {x | 0≤x j ∧ x j≤ε}≤
      A*(ENNReal.ofReal ε*(ENNReal.ofReal (2*R))^(d-1)) := by
  classical
  have hdom : volume.withDensity f≤
      volume.withDensity ((closedBall (0 : EuclideanSpace ℝ (Fin d)) R).indicator (fun _ => A)) := by
    apply withDensity_mono
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x∈closedBall (0 : EuclideanSpace ℝ (Fin d)) R
    · simpa only [indicator_of_mem hx] using hf x
    · rw [indicator_of_notMem hx,hzero x (by simpa only [mem_closedBall_zero_iff,not_le] using hx)]
  rw [withDensity_indicator isClosed_closedBall.measurableSet,withDensity_const] at hdom
  have hs : MeasurableSet {x : EuclideanSpace ℝ (Fin d) | 0≤x j ∧ x j≤ε} := by
    exact (measurableSet_le measurable_const (show Measurable (fun x : EuclideanSpace ℝ (Fin d) => x j) by fun_prop)).inter
      (measurableSet_le (show Measurable (fun x : EuclideanSpace ℝ (Fin d) => x j) by fun_prop) measurable_const)
  calc
    _ ≤ (A • volume.restrict (closedBall (0 : EuclideanSpace ℝ (Fin d)) R)) {x | 0≤x j ∧ x j≤ε} :=
      hdom _
    _ = A*volume {x : EuclideanSpace ℝ (Fin d) | ‖x‖≤R ∧ 0≤x j ∧ x j≤ε} := by
      rw [Measure.smul_apply,Measure.restrict_apply hs]
      change A * volume (_ ∩ _) = A * volume _
      congr 1
      congr 1
      ext x
      simp only [mem_inter_iff,mem_ofPred_eq,mem_closedBall_zero_iff]
      tauto
    _ ≤ _ := by gcongr; exact slab_volume_le j R ε
end SmoothObstruction.HalfspaceCollar

namespace SmoothObstruction.ChartDensity
open Set MeasureTheory Metric
open scoped Manifold ContDiff ENNReal
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M]

/-- Quantitative collar estimate in an authentic compact coordinate patch.
The measure is the original smooth measure restricted to that patch. -/
theorem compact_chart_slab (hclosed : IsClosed (range I)) (μ : Measure M)
    (hμ : SmoothPositiveDensity I μ) (a : M) (K : Set M) (hK : IsCompact K)
    (hKU : K⊆(extChartAt I a).source) (j : Fin d) :
    ∃ R A : ℝ,0<R ∧ 0<A ∧ ∀ ε : ℝ,
      μ {x | x∈K ∧ 0≤coordinates I a x j ∧ coordinates I a x j≤ε}≤
        ENNReal.ofReal A*(ENNReal.ofReal ε*(ENNReal.ofReal (2*R))^(d-1)) := by
  classical
  obtain ⟨f,hf,_,hcell⟩ := cell_density I hclosed μ hμ a
  have hKm : MeasurableSet K := hK.measurableSet
  obtain ⟨_,hmap⟩ := hcell K hKm hKU
  let e := coordinates I a
  let W := ChartDomination.coordinateSet e (inverse I a) K
  have him : W=(extChartAt I a) '' K := by
    change ChartDomination.coordinateSet e (inverse I a) K=_
    rw [ChartDomination.coordinateSet_eq_image e (inverse I a) K
      (fun x hx => inverse_coordinates I a x (hKU hx))]
    apply image_congr
    intro x hx
    exact coordinates_eq I a x (hKU hx)
  have hW : IsCompact W := by
    rw [him]
    exact hK.image_of_continuousOn ((continuousOn_extChartAt a).mono hKU)
  have hWV : W⊆(extChartAt I a).target := by
    rw [him]
    rintro u ⟨x,hx,rfl⟩
    exact (extChartAt I a).map_source (hKU hx)
  obtain ⟨R₀,hR₀⟩ := hW.bddAbove_image continuous_norm.continuousOn
  obtain ⟨A₀,hA₀⟩ := hW.bddAbove_image (hf.continuousOn.mono hWV)
  let R := max R₀ 0+1
  let A := max A₀ 0+1
  have hR : 0<R := by dsimp [R]; positivity
  have hA : 0<A := by dsimp [A]; positivity
  have hnorm (u) (hu : u∈W) : ‖u‖≤R := by
    have hh := hR₀ (mem_image_of_mem (fun u => ‖u‖) hu)
    exact hh.trans ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  have hbound (u) (hu : u∈W) : f u≤A := by
    have hh := hA₀ (mem_image_of_mem f hu)
    exact hh.trans ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  refine ⟨R,A,hR,hA,fun ε => ?_⟩
  let V : Set (EuclideanSpace ℝ (Fin d)) := {u | 0≤u j ∧ u j≤ε}
  have hV : MeasurableSet V :=
    (measurableSet_le measurable_const (show Measurable (fun u : EuclideanSpace ℝ (Fin d) => u j) by fun_prop)).inter
      (measurableSet_le (show Measurable (fun u : EuclideanSpace ℝ (Fin d) => u j) by fun_prop) measurable_const)
  have he : Measurable e := measurable_coordinates I a
  have hid : μ {x | x∈K ∧ 0≤e x j ∧ e x j≤ε} =
      ((μ.restrict K).map e) V := by
    rw [Measure.map_apply he hV,Measure.restrict_apply (hV.preimage he)]
    congr 1
    ext x
    simp only [mem_ofPred_eq,mem_inter_iff,mem_preimage,V]
    tauto
  rw [hid,hmap]
  apply HalfspaceCollar.supported_density_slab j R ε
  · intro u
    change W.indicator (fun u => ENNReal.ofReal (f u)) u≤ENNReal.ofReal A
    by_cases hu : u∈W
    · simpa only [indicator_of_mem hu] using ENNReal.ofReal_le_ofReal (hbound u hu)
    · simp only [indicator_of_notMem hu,zero_le]
  · intro u hu
    exact indicator_of_notMem (fun hw => (not_lt_of_ge (hnorm u hw)) hu) _
end SmoothObstruction.ChartDensity

namespace SmoothObstruction.ChartDensity
open Set MeasureTheory Metric
open scoped Manifold ContDiff ENNReal
variable {d : ℕ} [NeZero d]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanHalfSpace d) M]
    [MeasurableSpace M] [BorelSpace M]
    {ι : Type*} [Fintype ι]

/-- A GLOBAL quantitative boundary exclusion from the given original
positive smooth density and authentic finite compact atlas. The same set
works for every selected chart containing the point; its mass is O(δ), not
merely o(1), so all 2n+1 tests can be charged to invariant volume. -/
theorem global_halfspace_collar (μ : Measure M) [IsFiniteMeasure μ]
    (hμ : SmoothPositiveDensity (𝓡∂ d) μ) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt (EuclideanHalfSpace d) (a i)).source) :
    ∃ C : ℝ,0<C ∧ ∀ δ : ℝ,0≤δ →
      ∃ W : Set M,MeasurableSet W ∧ μ.real W≤C*δ ∧
        ∀ i x,x∈K i → x∉W →
          closedBall ((extChartAt (𝓡∂ d) (a i)) x) δ⊆interior (range (𝓡∂ d)) := by
  classical
  have hclosed : IsClosed (range (𝓡∂ d)) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact isClosed_le continuous_const (by fun_prop)
  have hs (i : ι) := compact_chart_slab (𝓡∂ d) hclosed μ hμ (a i) (K i) (hK i)
    (by simpa only [extChartAt_source] using hKU i) (0 : Fin d)
  choose R A hR hA hm using hs
  let D (i : ι) := A i*(2*R i)^(d-1)
  let C := (∑ i,D i)+1
  have hD (i : ι) : 0≤D i := by exact mul_nonneg (hA i).le (pow_nonneg (by linarith [hR i]) _)
  have hC : 0<C := by have := Finset.sum_nonneg (fun i (_ : i∈Finset.univ) => hD i); dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro δ hδ
  let V (i : ι) : Set M := {x | x∈K i ∧ 0≤coordinates (𝓡∂ d) (a i) x 0 ∧
    coordinates (𝓡∂ d) (a i) x 0≤δ}
  let W := ⋃ i,V i
  have hV (i : ι) : MeasurableSet (V i) := by
    have hf : Measurable (fun x => coordinates (𝓡∂ d) (a i) x 0) := by
      exact (show Measurable (fun u : EuclideanSpace ℝ (Fin d) => u 0) by fun_prop).comp (measurable_coordinates (𝓡∂ d) (a i))
    exact (hK i).measurableSet.inter ((measurableSet_le measurable_const hf).inter
      (measurableSet_le hf measurable_const))
  have hVm (i : ι) : μ (V i)≤ENNReal.ofReal (D i*δ) := by
    have hh := hm i δ
    have he : ENNReal.ofReal (A i)*(ENNReal.ofReal δ*(ENNReal.ofReal (2*R i))^(d-1))=
        ENNReal.ofReal (D i*δ) := by
      rw [ENNReal.ofReal_mul (hD i),ENNReal.ofReal_mul (hA i).le,ENNReal.ofReal_pow (by linarith [hR i])]
      ring
    exact hh.trans_eq he
  have hWm : μ W≤ENNReal.ofReal (C*δ) := by
    calc
      μ W ≤ ∑ i,μ (V i) := by simpa only [tsum_fintype] using measure_iUnion_le (μ:=μ) V
      _ ≤ ∑ i,ENNReal.ofReal (D i*δ) := Finset.sum_le_sum (fun i _ => hVm i)
      _ = ENNReal.ofReal ((∑ i,D i)*δ) := by
        rw [Finset.sum_mul,ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hD i) hδ)]
      _ ≤ ENNReal.ofReal (C*δ) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hδ)
  refine ⟨W,MeasurableSet.iUnion hV,?_,?_⟩
  · exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hWm).trans_eq (ENNReal.toReal_ofReal (mul_nonneg hC.le hδ))
  · intro i x hx hxW
    have hxs : x∈(extChartAt (𝓡∂ d) (a i)).source := by simpa only [extChartAt_source] using hKU i hx
    have hxrange := (extChartAt (𝓡∂ d) (a i)).map_source hxs
    rw [extChartAt,OpenPartialHomeomorph.extend_target] at hxrange
    have hxnonneg : 0≤(extChartAt (𝓡∂ d) (a i) x) 0 := by
      have hh := hxrange.2
      rw [range_modelWithCornersEuclideanHalfSpace] at hh
      exact hh
    have hxnot : x∉V i := fun hh => hxW (mem_iUnion.mpr ⟨i,hh⟩)
    apply HalfspaceCollar.closedBall_interior
    by_contra hle
    apply hxnot
    refine ⟨hx,?_,?_⟩ <;> rw [coordinates_eq (𝓡∂ d) _ _ hxs]
    · exact hxnonneg
    · exact le_of_not_gt hle
end SmoothObstruction.ChartDensity

end

end OAI
