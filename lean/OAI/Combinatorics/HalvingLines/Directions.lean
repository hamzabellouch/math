import OAI.Combinatorics.HalvingLines.Windows

namespace OAI

open Filter Topology

namespace PlanarHalving.Directions
open MeasureTheory Set

abbrev Plane := ℝ × ℝ

def simplex (x : ℝ) : Plane := (x,1-x)

lemma simplex_ne_zero (x : ℝ) : simplex x ≠ 0 := by
  intro h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp [simplex] at h₁ h₂
  linarith

lemma simplex_affine (x y a b : ℝ) (hab : a+b=1) :
    simplex (a*x+b*y) = a • simplex x+b • simplex y := by
  ext <;> dsimp [simplex]
  nlinarith

def allowed {ι : Type*} (Q : Plane ≃L[ℝ] Plane) (g : ι → Plane →L[ℝ] ℝ)
    (lo hi : ι → ℝ) (t : ℝ) : Set ℝ :=
  {x | x∈Icc 0 1 ∧ ∀ i, (hi i<t → 0≤g i (Q (simplex x))) ∧
    (t<lo i → g i (Q (simplex x))≤0)}

lemma allowed_convex {ι : Type*} (Q : Plane ≃L[ℝ] Plane) (g : ι → Plane →L[ℝ] ℝ)
    (lo hi : ι → ℝ) (t : ℝ) : Convex ℝ (allowed Q g lo hi t) := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_Icc (0:ℝ) 1 hx.1 hy.1 ha hb hab,?_⟩
  intro i
  change (hi i<t → 0≤g i (Q (simplex (a*x+b*y)))) ∧
    (t<lo i → g i (Q (simplex (a*x+b*y)))≤0)
  rw [simplex_affine x y a b hab,map_add,map_smul,map_smul,map_add,map_smul,map_smul]
  simp only [smul_eq_mul]
  exact ⟨fun h => add_nonneg (mul_nonneg ha ((hx.2 i).1 h))
    (mul_nonneg hb ((hy.2 i).1 h)),fun h => add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos ha ((hx.2 i).2 h))
      (mul_nonpos_of_nonneg_of_nonpos hb ((hy.2 i).2 h))⟩

lemma allowed_disjoint {ι : Type*} (Q : Plane ≃L[ℝ] Plane) (g : ι → Plane →L[ℝ] ℝ)
    (lo hi : ι → ℝ) {s t : ℝ} (i j : ι)
    (hsi : s<lo i) (hit : hi i<t) (hsj : s<lo j) (hjt : hi j<t)
    (hij : Function.Injective (fun v : Plane => (g i v,g j v))) :
    Disjoint (allowed Q g lo hi s) (allowed Q g lo hi t) := by
  apply Set.disjoint_left.mpr
  intro x hs ht
  have hi₀ : g i (Q (simplex x))=0 := le_antisymm ((hs.2 i).2 hsi) ((ht.2 i).1 hit)
  have hj₀ : g j (Q (simplex x))=0 := le_antisymm ((hs.2 j).2 hsj) ((ht.2 j).1 hjt)
  have hv : Q (simplex x)=0 := hij (by simp only [hi₀,hj₀,map_zero])
  exact simplex_ne_zero x (Q.injective (by simpa only [map_zero] using hv))

theorem three_allowed_directions {ι : Type*} (μ : Measure ℝ) [NullSingletonClass μ]
    (K : Set ℝ) (hK : Bornology.IsBounded K) (hpos : 0<μ K)
    (Q : Plane ≃L[ℝ] Plane) (g : ι → Plane →L[ℝ] ℝ) (lo hi : ι → ℝ)
    (hne : ∀ t∈K, (allowed Q g lo hi t).Nonempty)
    (hgap : ∀ s∈K, ∀ t∈K, s<t → 0<μ (Ioo s t) →
      ∃ i j, s<lo i ∧ hi i<t ∧ s<lo j ∧ hi j<t ∧
        Function.Injective (fun v : Plane => (g i v,g j v))) :
    ∃ t₁ t₂ t₃ d₁ d₂ d₃ : ℝ,
      t₁∈K ∧ t₂∈K ∧ t₃∈K ∧ t₁<t₂ ∧ t₂<t₃ ∧
      allowed Q g lo hi t₁={d₁} ∧ allowed Q g lo hi t₂={d₂} ∧
      allowed Q g lo hi t₃={d₃} ∧ d₁≠d₂ ∧ d₂≠d₃ ∧ d₁≠d₃ := by
  apply exists_three_singletons μ K hK hpos _ hne (fun t _ => allowed_convex Q g lo hi t)
  intro s hs t ht hst hp
  obtain ⟨i,j,hsi,hit,hsj,hjt,hij⟩ := hgap s hs t ht hst hp
  exact allowed_disjoint Q g lo hi i j hsi hit hsj hjt hij

end PlanarHalving.Directions

namespace PlanarHalving.TimeWindows
open MeasureTheory Set Filter UniformPartition Limits
open scoped Topology unitInterval NNReal

lemma time_mem_cell (m : ℕ) [NeZero m] (i : Fin m) : time m i∈cell m i := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have h₁ : (i : ℝ)/(m : ℝ)≤((i : ℝ)+1/2)/(m : ℝ) := by gcongr; norm_num
  have h₂ : ((i : ℝ)+1/2)/(m : ℝ)<((i : ℝ)+1)/(m : ℝ) := by gcongr; norm_num
  unfold cell
  split_ifs
  · constructor
    · exact h₁
    · change ((i : ℝ)+1/2)/(m : ℝ)≤((i.val+1 : ℕ):ℝ)/(m : ℝ)
      simpa only [Nat.cast_add,Nat.cast_one] using h₂.le
  · constructor
    · exact h₁
    · change ((i : ℝ)+1/2)/(m : ℝ)<((i.val+1 : ℕ):ℝ)/(m : ℝ)
      simpa only [Nat.cast_add,Nat.cast_one] using h₂

noncomputable def midpointGrid (m : ℕ) [NeZero m] (t : I) : I := time m (index m t)

lemma midpointGrid_measurable (m : ℕ) [NeZero m] : Measurable (midpointGrid m) :=
  (measurable_of_finite (time m)).comp (index_measurable m)

lemma midpointGrid_dist (m : ℕ) [NeZero m] (t : I) : dist (midpointGrid m t) t≤1/(m : ℝ) :=
  cell_diameter_bound m (index m t) (time_mem_cell m _) (mem_cell_index m t)

lemma midpointGrid_tendsto (m : ℕ → ℕ) [∀ n, NeZero (m n)]
    (hm : Tendsto m atTop atTop) (t : I) :
    Tendsto (fun n => midpointGrid (m n) t) atTop (𝓝 t) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => midpointGrid_dist (m n) t)
  have hnat : Tendsto (fun n => (m n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hnat

lemma integral_midpointGrid (m : ℕ) [NeZero m] (f : I → ℝ) :
    ∫ t, f (midpointGrid m t) = (∑ i : Fin m, f (time m i))/(m : ℝ) := by
  change ∫ t, (fun i : Fin m => f (time m i)) (index m t) = _
  rw [integral_partition volume (cell m) (cell_measurable m) (index m) (index_eq m) (fun i : Fin m => f (time m i))]
  simp only [measureReal_def,cell_volume,ENNReal.toReal_ofReal (by positivity : 0≤1/(m : ℝ))]
  rw [← Finset.mul_sum]
  ring

lemma midpoint_riemann_tendsto (m : ℕ → ℕ) [∀ n, NeZero (m n)] (hm : Tendsto m atTop atTop)
    (f : BoundedContinuousFunction I ℝ) :
    Tendsto (fun n => (∑ i : Fin (m n), f (time (m n) i))/(m n : ℝ)) atTop
      (𝓝 (∫ t : I, f t)) := by
  simp_rw [← integral_midpointGrid]
  apply tendsto_integral_of_dominated_convergence (fun _ : I => ‖f‖)
  · intro n
    exact (f.continuous.measurable.comp (midpointGrid_measurable (m n))).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall (fun _ => f.norm_coe_le_norm _)
  · exact Eventually.of_forall (fun t => (f.continuous.tendsto t).comp (midpointGrid_tendsto m hm t))

lemma timeMeasure_tendsto (m : ℕ → ℕ) [∀ n, NeZero (m n)] (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => weightedAtoms (m n : ℝ≥0)⁻¹ (time (m n))) atTop
      (𝓝 (⟨volume,inferInstance⟩ : FiniteMeasure I)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  change Tendsto (fun n => ∫ x, f x ∂(weightedAtoms (m n : ℝ≥0)⁻¹ (time (m n)) : Measure I))
    atTop (𝓝 (∫ t : I, f t))
  simpa only [integral_weightedAtoms,NNReal.coe_inv,NNReal.coe_natCast,
    ← div_eq_inv_mul] using midpoint_riemann_tendsto m hm f

end PlanarHalving.TimeWindows

namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [Nonempty X] [MeasurableSpace X] [BorelSpace X]

lemma restriction_limit_eq {μ lam : FiniteMeasure X} {μs lams : ℕ → FiniteMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hlam : Tendsto lams atTop (𝓝 lam))
    {S : Set X} (_hS : MeasurableSet S) (hbd : (μ : Measure X) (frontier S)=0)
    (he : ∀ n, (lams n : Measure X)=(μs n : Measure X).restrict S) :
    (lam : Measure X)=(μ : Measure X).restrict S := by
  let ν : FiniteMeasure X := ⟨(μ : Measure X).restrict S,inferInstance⟩
  have hclosed (F : Set X) (hF : IsClosed F) : lam F=ν F := by
    obtain ⟨r,hr,hnull⟩ := exists_null_frontiers_thickening ((μ : Measure X)+(lam : Measure X)) F
    have hval (j : ℕ) : lam (Metric.thickening (r j) F)=ν (Metric.thickening (r j) F) := by
      let U := Metric.thickening (r j) F
      have hU : MeasurableSet U := Metric.isOpen_thickening.measurableSet
      have hnullμ : (μ : Measure X) (frontier U)=0 := by
        have hh := (hnull j).2
        rw [Measure.add_apply] at hh
        exact (add_eq_zero.mp hh).1
      have hnullLam : (lam : Measure X) (frontier U)=0 := by
        have hh := (hnull j).2
        rw [Measure.add_apply] at hh
        exact (add_eq_zero.mp hh).2
      have hnullUS : (μ : Measure X) (frontier (U∩S))=0 :=
        measure_mono_null ((frontier_inter_subset U S).trans
          (union_subset_union inter_subset_left inter_subset_right)) (measure_union_null hnullμ hbd)
      have h₁ := finiteMeasure_tendsto_apply hlam hnullLam
      have h₂ := finiteMeasure_tendsto_apply hμ hnullUS
      have h₂' : Tendsto (fun n => lams n U) atTop (𝓝 (ν U)) := by
        convert h₂ using 1
        · funext n
          change ((lams n : Measure X) U).toNNReal = _
          rw [he n,Measure.restrict_apply hU]
          rfl
        · change 𝓝 (((μ : Measure X).restrict S U).toNNReal) = _
          rw [Measure.restrict_apply hU]
          rfl
      exact tendsto_nhds_unique h₁ h₂'
    have h₁ := finiteMeasure_tendsto_thickening lam hF hr (fun j => (hnull j).1)
    have h₂ := finiteMeasure_tendsto_thickening ν hF hr (fun j => (hnull j).1)
    exact tendsto_nhds_unique (h₁.congr (fun j => hval j)) h₂
  have heF (F : Set X) (hF : IsClosed F) : (lam : Measure X) F=(ν : Measure X) F := by
    simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) (hclosed F hF)
  change (lam : Measure X)=(ν : Measure X)
  apply Measure.OuterRegular.ext_isOpen
  intro U hU
  rw [← compl_compl U,measure_compl hU.isClosed_compl.measurableSet (measure_ne_top _ _),
    measure_compl hU.isClosed_compl.measurableSet (measure_ne_top _ _),
    heF univ isClosed_univ,heF Uᶜ hU.isClosed_compl]

end PlanarHalving.Limits
namespace PlanarHalving.RankCoordinates
open Set
open scoped ENNReal

lemma smoothed_eVariation {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ → ℝ)
    (hg : ∀ j, ConvexOn ℝ univ (g j)) {f : ℝ → ℝ} (hf : ConcaveOn ℝ univ f)
    {ε : ℝ} (hε : 0 < ε) :
    eVariationOn (fun x => smoothed g ε (x,f x)) univ ≤ 2 := by
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n,x,hx,_⟩
  have h := smoothed_variation hm g hg hf hε x hx n
  simpa only [edist_dist,Real.dist_eq,ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _),
    ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal h

lemma sum_interval_eVariation {N : ℕ} {f : ℝ → ℝ}
    (x : Fin (N+1) → ℝ) (hx : Monotone x) :
    ∑ i : Fin N, eVariationOn f (Icc (x i.castSucc) (x i.succ)) ≤ eVariationOn f univ := by
  let y : ℕ → ℝ := fun n => x ⟨min n N,by omega⟩
  have hy : Monotone y := fun i j hij => hx (by
    show min i N ≤ min j N
    exact min_le_min_right N hij)
  have he : ∑ i : Fin N, eVariationOn f (Icc (x i.castSucc) (x i.succ)) =
      ∑ i ∈ Finset.range N, eVariationOn f (Icc (y i) (y (i+1))) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have hi := i.isLt
    congr 3 <;> apply Fin.ext <;> dsimp [y] <;> omega
  rw [he,eVariationOn.sum' f hy]
  exact eVariationOn.mono f (subset_univ _)

end PlanarHalving.RankCoordinates
namespace PlanarHalving.Limits
open MeasureTheory
open scoped NNReal

lemma map_weightedAtoms {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    {α : Type*} [Fintype α] (w : ℝ≥0) (x : α → X) {f : X → Y} (hf : Measurable f) :
    (weightedAtoms w x).map f=weightedAtoms w (f∘x) := by
  classical
  apply FiniteMeasure.toMeasure_injective
  change Measure.map f (w • (∑ i, Measure.dirac (x i) : Measure X))=
    w • (∑ i, Measure.dirac (f (x i)) : Measure Y)
  rw [Measure.map_smul _ hf.aemeasurable,Measure.map_finset_sum hf.aemeasurable]
  simp only [Measure.map_dirac]

end PlanarHalving.Limits
namespace PlanarHalving.Batches
open MeasureTheory Set Filter Limits TimeWindows
open scoped Topology NNReal ENNReal unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.sum_edgeTime (S : @System n R k a P) [NeZero R] [NeZero a] (f : I → ℝ) :
    ∑ e : ↥S.edges, f (S.edgeTime e) = (a : ℝ)^2 * ∑ b : Fin R, f (time R b) := by
  classical
  change ∑ e : ↥S.edges, f (time R (S.trace e.property).batch)=_
  rw [← Finset.sum_fiberwise' Finset.univ (fun e : ↥S.edges => (S.trace e.property).batch)
    (fun b => f (time R b))]
  simp only [Finset.sum_const,S.edgeTime_distribution,nsmul_eq_mul,Nat.cast_pow]
  exact (Finset.mul_sum ..).symm

lemma System.edgeTime_atoms (S : @System n R k a P) [NeZero R] [NeZero a] :
    weightedAtoms ((R : ℝ≥0)*(a : ℝ≥0)^2)⁻¹ S.edgeTime=
      weightedAtoms (R : ℝ≥0)⁻¹ (time R) := by
  apply FiniteMeasure.ext_of_forall_integral_eq
  intro f
  simp only [integral_weightedAtoms,S.sum_edgeTime,NNReal.coe_inv,NNReal.coe_mul,
    NNReal.coe_pow,NNReal.coe_natCast]
  have hR : (R : ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne R)
  have ha : (a : ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne a)
  field_simp

noncomputable def System.labelTimeMeasure (S : @System n R k a P) [NeZero R] [NeZero a]
    {X : Type*} [MeasurableSpace X] (z : Fin n → X) : FiniteMeasure (X×I) :=
  weightedAtoms ((R : ℝ≥0)*(a : ℝ≥0)^2)⁻¹ (fun e : ↥S.edges => (z e.val.1,S.edgeTime e))

lemma System.labelTimeMeasure_time (S : @System n R k a P) [NeZero R] [NeZero a]
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] (z : Fin n → X) :
    (S.labelTimeMeasure z).map Prod.snd=weightedAtoms (R : ℝ≥0)⁻¹ (time R) := by
  rw [System.labelTimeMeasure,map_weightedAtoms _ _ measurable_snd]
  exact S.edgeTime_atoms

lemma System.labelTimeMeasure_space (S : @System n R k a P) [NeZero R] [NeZero a]
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] (z : Fin n → X) :
    (S.labelTimeMeasure z).map Prod.fst=S.endpointMeasure z ((R : ℝ≥0)*(a : ℝ≥0)^2) := by
  rw [System.labelTimeMeasure,map_weightedAtoms _ _ measurable_fst]
  rfl

lemma System.labelTimeMeasure_mass (S : @System n R k a P) [NeZero R] [NeZero a]
    {X : Type*} [MeasurableSpace X] (z : Fin n → X) :
    (S.labelTimeMeasure z).mass=1 := by
  rw [System.labelTimeMeasure,mass_weightedAtoms]
  simp only [Fintype.card_coe,S.card_edges,Nat.cast_mul,Nat.cast_pow]
  exact inv_mul_cancel₀ (mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne R))
    (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne a))))

end PlanarHalving.Batches
namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates
open scoped ENNReal
variable {R n k a : ℕ} {P : Fin n → Point}

lemma ConvexPath.x_monotone (C : ConvexPath R) : Monotone (fun i => (C.point i).1) := by
  intro i j hij
  apply fin_between_le i j hij
  intro b _ _
  rcases C.right b with he | he
  · exact le_of_eq (congrArg Prod.fst he)
  · exact he.le

lemma segment_fst_mem {p q z : Point} (hpq : p.1 ≤ q.1)
    (hz : z∈segment ℝ p q) : z.1∈Icc p.1 q.1 := by
  rw [segment_eq_image] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  simp only [Prod.fst_add,Prod.smul_fst,smul_eq_mul,mem_Icc]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hpq) ht.1,
    mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr ht.2)]

lemma ConvexPath.sum_rank_oscillation (C : ConvexPath R) {l u : ℝ}
    (hsl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧
      slope (C.point b.castSucc) (C.point b.succ) ≤ u)
    {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ → ℝ)
    (hg : ∀ j, ConvexOn ℝ univ (g j)) {ε : ℝ} (hε : 0 < ε) :
    ∑ b : Fin R, Metric.ediam ((fun z => smoothed g ε (-z)) ''
      segment ℝ (C.point b.castSucc) (C.point b.succ))  ≤  2 := by
  let f := C.extension l u
  let g' : Fin m → ℝ → ℝ := fun j x => g j (-x)
  let F : ℝ → ℝ := fun x => smoothed g' ε (x,-f x)
  have hg' (j : Fin m) : ConvexOn ℝ univ (g' j) := by
    simpa only [Set.preimage_univ,Function.comp_def,LinearMap.neg_apply,LinearMap.id_apply]
      using (hg j).comp_linearMap (-LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  have hf : ConcaveOn ℝ univ (fun x => -f x) :=
    (convexOn_envelope (C.extensionSlopes l u) (C.extensionIntercepts l u)).neg
  have hF : eVariationOn F univ ≤ 2 := smoothed_eVariation hm g' hg' hf hε
  have hpiece (b : Fin R) :
      Metric.ediam ((fun z => smoothed g ε (-z)) ''
        segment ℝ (C.point b.castSucc) (C.point b.succ))  ≤
      eVariationOn F (Icc (C.point b.castSucc).1 (C.point b.succ).1) := by
    by_cases hb : C.point b.castSucc=C.point b.succ
    · simp only [hb,segment_same,image_singleton,Metric.ediam_singleton]
      exact zero_le
    · apply Metric.ediam_image_le_iff.mpr
      intro z hz w hw
      have hz' := C.extension_edge hsl b hb hz
      have hw' := C.extension_edge hsl b hb hw
      have hze : smoothed g ε (-z)=F z.1 := by
        dsimp [F,f,g',smoothed]
        rw [hz']
      have hwe : smoothed g ε (-w)=F w.1 := by
        dsimp [F,f,g',smoothed]
        rw [hw']
      rw [hze,hwe]
      exact eVariationOn.edist_le F (segment_fst_mem (C.x_monotone (Fin.castSucc_le_succ b)) hz)
        (segment_fst_mem (C.x_monotone (Fin.castSucc_le_succ b)) hw)
  exact (Finset.sum_le_sum (fun b _ => hpiece b)).trans
    ((sum_interval_eVariation (fun i => (C.point i).1) C.x_monotone).trans hF)

lemma System.sum_edges_le_paths (S : @System n R k a P) [NeZero a]
    (W : Point → Point → ℝ≥0∞) (hpath : ∀ j : Fin a, ∀ u : ↥(S.marks 0),
      ∑ b : Fin R, W ((S.tokenPath j u).point b.castSucc)
        ((S.tokenPath j u).point b.succ) ≤ 2) :
    ∑ e : ↥S.edges, W (P e.val.1) (P e.val.2)  ≤  2*a*n := by
  classical
  let ι := Fin a × (↥(S.marks 0) × Fin R)
  let T (e : ↥S.edges) := S.trace e.property
  let tag : ↥S.edges → ι := fun e => ((T e).number,((T e).token,(T e).batch))
  let w : ι → ℝ≥0∞ := fun i => W ((S.tokenPath i.1 i.2.1).point i.2.2.castSucc)
    ((S.tokenPath i.1 i.2.1).point i.2.2.succ)
  have ht : Function.Injective tag := by
    intro e f h
    have hn := congrArg Prod.fst h
    have hu := congrArg (fun i : ι => i.2.1) h
    have hb := congrArg (fun i : ι => i.2.2) h
    dsimp only [tag] at hn hu hb
    apply Subtype.ext
    apply Prod.ext
    · rw [← (T e).source,←(T f).source]
      rw [hn,hu,hb]
    · rw [← (T e).target,←(T f).target]
      rw [hn,hu,hb]
  have hw (e : ↥S.edges) : W (P e.val.1) (P e.val.2)=w (tag e) := by
    dsimp [w,tag,System.tokenPath]
    rw [(T e).source,(T e).target]
  calc
    _ = ∑ e : ↥S.edges, w (tag e) := Fintype.sum_congr _ _ hw
    _ = ∑ i ∈ Finset.univ.image tag, w i := (Finset.sum_image (fun _ _ _ _ h => ht h)).symm
    _  ≤  ∑ i : ι, w i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ∑ j : Fin a, ∑ u : ↥(S.marks 0), ∑ b : Fin R,
        W ((S.tokenPath j u).point b.castSucc) ((S.tokenPath j u).point b.succ) := by
      dsimp only [ι]
      simp only [Fintype.sum_prod_type,w]
    _  ≤  ∑ _j : Fin a, ∑ _u : ↥(S.marks 0), (2 : ℝ≥0∞) := by
      gcongr with j u
      exact hpath j u
    _ = 2*a*(S.marks 0).card := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Fintype.card_coe,nsmul_eq_mul]
      ring
    _  ≤  2*a*n := by
      have hc : (S.marks 0).card ≤ n := (S.marks 0).card_le_univ.trans (by simp)
      gcongr

theorem System.rank_oscillation (S : @System n R k a P) [NeZero a]
    {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ → ℝ)
    (hg : ∀ j, ConvexOn ℝ univ (g j)) {ε : ℝ} (hε : 0 < ε) :
    ∑ e : ↥S.edges, Metric.ediam (smoothed g ε '' segment ℝ (P e.val.1) (P e.val.2))  ≤  2*a*n := by
  classical
  let W : Point → Point → ℝ≥0∞ := fun p q =>
    Metric.ediam ((fun z => smoothed g ε (-z)) '' segment ℝ p q)
  have hp (j : Fin a) (v : ↥(S.flip.marks 0)) :
      ∑ b : Fin R, W ((S.flip.tokenPath j v).point b.castSucc)
        ((S.flip.tokenPath j v).point b.succ) ≤ 2 := by
    apply (S.flip.tokenPath j v).sum_rank_oscillation
      (l := S.slope 0) (u := S.slope (Fin.last R)) _ hm g hg hε
    intro b hb
    exact ⟨(S.flip.tokenPath_bounds j v b hb).1.le,(S.flip.tokenPath_bounds j v b hb).2.le⟩
  have hb := S.flip.sum_edges_le_paths W hp
  let e : ↥S.edges ≃ ↥S.flip.edges :=
    { toFun := fun e => ⟨e.val.swap,(S.flip_edge _).mpr e.property⟩
      invFun := fun e => ⟨e.val.swap,(S.flip_edge _).mp (by simp only [Prod.swap_swap]; exact e.property)⟩
      left_inv := by intro x; apply Subtype.ext; exact Prod.swap_swap _
      right_inv := by intro x; apply Subtype.ext; exact Prod.swap_swap _ }
  have hsum : (∑ v : ↥S.edges, Metric.ediam (smoothed g ε '' segment ℝ (P v.val.1) (P v.val.2))) =
      ∑ v : ↥S.flip.edges, W (-P v.val.1) (-P v.val.2) := by
    apply Fintype.sum_equiv e
    intro v
    change Metric.ediam (smoothed g ε '' segment ℝ (P v.val.1) (P v.val.2)) =
      Metric.ediam ((fun z => smoothed g ε (-z)) '' segment ℝ (-P v.val.2) (-P v.val.1))
    have hseg : (fun z : Point => -z) '' segment ℝ (-P v.val.2) (-P v.val.1) =
        segment ℝ (P v.val.2) (P v.val.1) := by
      simpa using image_segment ℝ ((-LinearMap.id : Point →ₗ[ℝ] Point).toAffineMap)
        (-P v.val.2) (-P v.val.1)
    congr 1
    calc
      _ = smoothed g ε '' ((fun z : Point => -z) '' segment ℝ (-P v.val.2) (-P v.val.1)) := by
        rw [hseg,segment_symm]
      _ = _ := Set.image_image _ _ _
  rw [hsum]
  exact hb

end PlanarHalving.Batches

end OAI
