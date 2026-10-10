import OAI.Geometry.PinnedDistances.ConditionalIntegral

namespace OAI

section
/- A non-atomic obstruction for bounded cross-ratio energy. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal

namespace WeakPinned.Bounded

def crossKernel (a c : ℂ) (zw : ℂ × ℂ) : ℝ :=
  min 1 ‖(c - a) * (zw.2 - zw.1) / ((zw.1 - a) * (c - zw.2))‖

def targetKernel (d : ℂ) (zw : ℂ × ℂ) : ℝ :=
  min 1 ‖(zw.1 - zw.2) / (zw.2 - d)‖

def crossEnergy (μ : Measure ℂ) (a c : ℂ) : ℝ :=
  ∫ zw, crossKernel a c zw ∂ μ.prod μ

def targetEnergy (ν : Measure ℂ) (d : ℂ) : ℝ :=
  ∫ zw, targetKernel d zw ∂ ν.prod ν

lemma measurable_crossKernel (a c : ℂ) : Measurable (crossKernel a c) := by
  unfold crossKernel
  fun_prop

lemma measurable_targetKernel (d : ℂ) : Measurable (targetKernel d) := by
  unfold targetKernel
  fun_prop

lemma crossKernel_nonneg (a c : ℂ) (zw : ℂ × ℂ) : 0 ≤ crossKernel a c zw := by
  exact le_min zero_le_one (norm_nonneg _)

lemma crossKernel_le_one (a c : ℂ) (zw : ℂ × ℂ) : crossKernel a c zw ≤ 1 :=
  min_le_left _ _

lemma targetKernel_nonneg (d : ℂ) (zw : ℂ × ℂ) : 0 ≤ targetKernel d zw := by
  exact le_min zero_le_one (norm_nonneg _)

lemma targetKernel_le_one (d : ℂ) (zw : ℂ × ℂ) : targetKernel d zw ≤ 1 :=
  min_le_left _ _

lemma integrable_crossKernel (μ : Measure ℂ) [IsFiniteMeasure μ] (a c : ℂ) :
    Integrable (crossKernel a c) (μ.prod μ) := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_crossKernel a c).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun zw => by
    rw [Real.norm_eq_abs, abs_of_nonneg (crossKernel_nonneg a c zw)]
    exact crossKernel_le_one a c zw

lemma integrable_targetKernel (ν : Measure ℂ) [IsFiniteMeasure ν] (d : ℂ) :
    Integrable (targetKernel d) (ν.prod ν) := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_targetKernel d).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun zw => by
    rw [Real.norm_eq_abs, abs_of_nonneg (targetKernel_nonneg d zw)]
    exact targetKernel_le_one d zw

lemma crossKernel_tendsto (c : ℂ) (zw : ℂ × ℂ)
    (hz : zw.1 ≠ c) (hw : zw.2 ≠ c) :
    Tendsto (fun a => crossKernel a c zw) (nhds c) (nhds 0) := by
  have hd : (zw.1 - c) * (c - zw.2) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hz) (sub_ne_zero.mpr hw.symm)
  have hc : ContinuousAt (fun a : ℂ => crossKernel a c zw) c := by
    unfold crossKernel
    fun_prop
  simpa [crossKernel] using hc.tendsto

lemma ae_pair_ne (μ : Measure ℂ) [NullSingletonClass μ] [SFinite μ] (c : ℂ) :
    ∀ᵐ zw ∂ μ.prod μ, zw.1 ≠ c ∧ zw.2 ≠ c := by
  rw [Measure.ae_prod_iff_ae_ae]
  · filter_upwards [μ.ae_ne c] with z hz
    filter_upwards [μ.ae_ne c] with w hw
    exact ⟨hz, hw⟩
  · exact ((measurableSet_eq_fun measurable_fst measurable_const).compl).inter
      ((measurableSet_eq_fun measurable_snd measurable_const).compl)

lemma crossEnergy_tendsto (μ : Measure ℂ) [IsFiniteMeasure μ] [NullSingletonClass μ] (c : ℂ) :
    Tendsto (fun a => crossEnergy μ a c) (nhds c) (nhds 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := μ.prod μ) (l := nhds c) (F := fun a zw => crossKernel a c zw)
    (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (Filter.Eventually.of_forall fun a => (measurable_crossKernel a c).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun a => Filter.Eventually.of_forall fun zw => by
      rw [Real.norm_eq_abs, abs_of_nonneg (crossKernel_nonneg a c zw)]
      exact crossKernel_le_one a c zw)
    (integrable_const (1 : ℝ))
    ((ae_pair_ne μ c).mono fun zw hzw => crossKernel_tendsto c zw hzw.1 hzw.2)
  simpa [crossEnergy] using h

lemma ae_distinct_pair (μ : Measure ℂ) [NullSingletonClass μ] [SFinite μ] :
    ∀ᵐ zw ∂ μ.prod μ, zw.1 ≠ zw.2 := by
  apply (Measure.ae_prod_iff_ae_ae (p := fun zw : ℂ × ℂ => zw.1 ≠ zw.2)
    (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
  exact Filter.Eventually.of_forall fun z =>
    (μ.ae_ne z).mono fun w hw => hw.symm

lemma targetEnergy_pos (ν : Measure ℂ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (d : ℂ) : 0 < targetEnergy ν d := by
  have hp : ∀ᵐ zw ∂ ν.prod ν, 0 < targetKernel d zw := by
    filter_upwards [ae_distinct_pair ν, ae_pair_ne ν d] with zw hzw hd
    exact lt_min zero_lt_one (norm_pos_iff.mpr
      (div_ne_zero (sub_ne_zero.mpr hzw) (sub_ne_zero.mpr hd.2)))
  have hn : 0 ≤ targetEnergy ν d := integral_nonneg (targetKernel_nonneg d)
  apply lt_of_le_of_ne hn
  intro he
  have hz : targetKernel d =ᵐ[ν.prod ν] 0 :=
    (integral_eq_zero_iff_of_nonneg (targetKernel_nonneg d)
      (integrable_targetKernel ν d)).mp he.symm
  have hf : ∀ᵐ zw ∂ ν.prod ν, False := hp.and hz |>.mono fun zw h => by
    simpa [h.2] using h.1
  simpa using (ae_iff.mp hf)

lemma not_ae_energy_eq (μ ν : Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass μ] [NullSingletonClass ν]
    (c d : ℂ) (hc : c ∈ μ.support) :
    ¬ (∀ᵐ a ∂ μ, crossEnergy μ a c = targetEnergy ν d) := by
  intro he
  have ht := targetEnergy_pos ν d
  have hn : {a | crossEnergy μ a c < targetEnergy ν d} ∈ nhds c :=
    (crossEnergy_tendsto μ c).eventually (eventually_lt_nhds ht)
  have hpos := (Measure.mem_support_iff_forall c).mp hc _ hn
  have hzero : μ {a | crossEnergy μ a c < targetEnergy ν d} = 0 := by
    have hnot : ∀ᵐ a ∂ μ, ¬ crossEnergy μ a c < targetEnergy ν d :=
      he.mono fun a ha => by simp [ha]
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hnot
  exact (ne_of_gt hpos) hzero

lemma measurable_crossEnergy (μ : Measure ℂ) [SFinite μ] :
    Measurable (fun ac : ℂ × ℂ => crossEnergy μ ac.1 ac.2) := by
  have hm : Measurable (fun v : (ℂ × ℂ) × (ℂ × ℂ) =>
      crossKernel v.1.1 v.1.2 v.2) := by
    unfold crossKernel
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma measurable_targetEnergy (ν : Measure ℂ) [SFinite ν] :
    Measurable (targetEnergy ν) := by
  have hm : Measurable (fun v : ℂ × (ℂ × ℂ) => targetKernel v.1 v.2) := by
    unfold targetKernel
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

def mobius (a b c d z : ℂ) : ℂ := b + (c - a) * (d - b) / (z - a)

lemma measurable_mobius (a b c d : ℂ) : Measurable (mobius a b c d) := by
  unfold mobius
  fun_prop

lemma mobius_sub_target (a b c d z : ℂ) (hz : z ≠ a) :
    mobius a b c d z - d = (d - b) * (c - z) / (z - a) := by
  unfold mobius
  field_simp
  ring

lemma mobius_ne_target (a b c d w : ℂ) (hbd : b ≠ d)
    (hwa : w ≠ a) (hwc : w ≠ c) : mobius a b c d w ≠ d := by
  apply sub_ne_zero.mp
  rw [mobius_sub_target a b c d w hwa]
  exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hbd.symm)
    (sub_ne_zero.mpr hwc.symm)) (sub_ne_zero.mpr hwa)

lemma kernel_mobius (a b c d : ℂ) (zw : ℂ × ℂ) (hbd : b ≠ d)
    (hz : zw.1 ≠ a) (hw : zw.2 ≠ a) (hwc : zw.2 ≠ c) :
    targetKernel d (mobius a b c d zw.1, mobius a b c d zw.2) =
      crossKernel a c zw := by
  unfold targetKernel crossKernel
  congr 2
  have hma := sub_ne_zero.mpr hz
  have hwa := sub_ne_zero.mpr hw
  have hc := sub_ne_zero.mpr hwc.symm
  have hdb := sub_ne_zero.mpr hbd.symm
  rw [mobius_sub_target a b c d zw.2 hw]
  unfold mobius
  field_simp
  ring

lemma energy_of_mobius_map (μ ν : Measure ℂ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (a b c d : ℂ) (hbd : b ≠ d)
    (hmap : Measure.map (mobius a b c d) μ = ν) :
    crossEnergy μ a c = targetEnergy ν d := by
  unfold targetEnergy
  rw [← hmap, Measure.map_prod_map μ μ (measurable_mobius a b c d)
    (measurable_mobius a b c d)]
  rw [integral_map_of_stronglyMeasurable
    ((measurable_mobius a b c d).prodMap (measurable_mobius a b c d))
    (measurable_targetKernel d).stronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [ae_pair_ne μ a, ae_pair_ne μ c] with zw ha hc
  exact (kernel_mobius a b c d zw hbd ha.1 ha.2 hc.2).symm

attribute [local irreducible] crossEnergy targetEnergy

lemma measurableSet_energy_eq (μ ν : Measure ℂ) [SFinite μ] [SFinite ν] :
    MeasurableSet {v : ℂ × (ℂ × ℂ) |
      crossEnergy μ v.1 v.2.1 = targetEnergy ν v.2.2} := by
  have h₁ : Measurable (fun v : ℂ × (ℂ × ℂ) => crossEnergy μ v.1 v.2.1) :=
    (measurable_crossEnergy μ).comp
      (show Measurable (fun v : ℂ × (ℂ × ℂ) => (v.1, v.2.1)) from by fun_prop)
  have h₂ : Measurable (fun v : ℂ × (ℂ × ℂ) => targetEnergy ν v.2.2) :=
    (measurable_targetEnergy ν).comp
      (show Measurable (fun v : ℂ × (ℂ × ℂ) => v.2.2) from by fun_prop)
  exact measurableSet_eq_fun h₁ h₂

/-- The finite-plane non-atomic obstruction. -/

theorem no_finite_law (μ ν : Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass μ] [NullSingletonClass ν]
    (Q : Measure (ℂ × ℂ × ℂ × ℂ)) [IsProbabilityMeasure Q]
    (hlaw : Q.map (fun q => q.1) = μ)
    (hind : ProbabilityTheory.IndepFun (fun q => q.1) (fun q => q.2.2) Q)
    (hsupp : ∀ᵐ q ∂ Q, q.2.2.1 ∈ μ.support)
    (hbd : ∀ᵐ q ∂ Q, q.2.1 ≠ q.2.2.2)
    (hmap : ∀ᵐ q ∂ Q, μ.map (mobius q.1 q.2.1 q.2.2.1 q.2.2.2) = ν) : False := by
  let τ : Measure (ℂ × ℂ) := Q.map (fun q => q.2.2)
  have : IsProbabilityMeasure τ := inferInstance
  have hp : MeasurableSet {v : ℂ × (ℂ × ℂ) |
      crossEnergy μ v.1 v.2.1 = targetEnergy ν v.2.2} :=
    measurableSet_energy_eq μ ν
  have he : ∀ᵐ q ∂ Q,
      crossEnergy μ q.1 q.2.2.1 = targetEnergy ν q.2.2.2 := by
    filter_upwards [hbd, hmap] with q hd hm
    exact energy_of_mobius_map μ ν q.1 q.2.1 q.2.2.1 q.2.2.2 hd hm
  have hj : Q.map (fun q => (q.1, q.2.2)) = μ.prod τ := by
    rw [hind.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop), hlaw]
  have he' : ∀ᵐ v ∂ μ.prod τ, crossEnergy μ v.1 v.2.1 = targetEnergy ν v.2.2 := by
    rw [← hj]
    exact (ae_map_iff (by fun_prop) hp).mpr he
  have hf : ∀ᵐ cd ∂ τ, ∀ᵐ a ∂ μ, crossEnergy μ a cd.1 = targetEnergy ν cd.2 :=
    (Measure.ae_ae_comm hp).mp ((Measure.ae_prod_iff_ae_ae hp).mp he')
  have hs : ∀ᵐ cd ∂ τ, cd.1 ∈ μ.support := by
    exact (ae_map_iff (by fun_prop)
      (μ.isClosed_support.measurableSet.preimage measurable_fst)).mpr hsupp
  obtain ⟨cd, hc, hcd⟩ := (hs.and hf).exists
  exact not_ae_energy_eq μ ν cd.1 cd.2 hc hcd

/-- The Riemann sphere as the one-point compactification of the complex plane. -/
abbrev Sphere := OnePoint ℂ
local instance : MeasurableSpace Sphere := borel Sphere
local instance : BorelSpace Sphere := ⟨rfl⟩

lemma measurableEmbedding_sphere_coe : MeasurableEmbedding ((↑) : ℂ → Sphere) :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding

/-- The sphere Möbius map has its pole at infinity and its value at infinity is b;
    no finite-valued division convention is used there. -/
def sphereMobius (a b c d : ℂ) : Sphere → Sphere :=
  OnePoint.rec (b : Sphere) (fun z => if z = a then OnePoint.infty
    else (mobius a b c d z : Sphere))

@[simp] lemma sphereMobius_coe (a b c d z : ℂ) (hz : z ≠ a) :
    sphereMobius a b c d (z : Sphere) = (mobius a b c d z : Sphere) := by
  simp [sphereMobius, OnePoint.rec, hz]

@[simp] lemma sphereMobius_pole (a b c d : ℂ) :
    sphereMobius a b c d (a : Sphere) = OnePoint.infty := by
  simp [sphereMobius, OnePoint.rec]

@[simp] lemma sphereMobius_infty (a b c d : ℂ) :
    sphereMobius a b c d OnePoint.infty = (b : Sphere) := rfl

lemma map_sphereMobius (μ : Measure ℂ) [NullSingletonClass μ] (a b c d : ℂ) :
    (μ.map ((↑) : ℂ → Sphere)).map (sphereMobius a b c d) =
      (μ.map (mobius a b c d)).map ((↑) : ℂ → Sphere) := by
  have he : ((fun z : ℂ => (mobius a b c d z : Sphere))) =ᵐ[μ]
      (sphereMobius a b c d ∘ ((↑) : ℂ → Sphere)) := by
    filter_upwards [μ.ae_ne a] with z hz
    exact (sphereMobius_coe a b c d z hz).symm
  have hm0 : Measurable (fun z : ℂ => (mobius a b c d z : Sphere)) :=
    measurableEmbedding_sphere_coe.measurable.comp (measurable_mobius a b c d)
  have hm : AEMeasurable (sphereMobius a b c d ∘ ((↑) : ℂ → Sphere)) μ :=
    hm0.aemeasurable.congr he
  rw [AEMeasurable.map_map_of_aemeasurable (measurableEmbedding_sphere_coe.aemeasurable_map_iff.mpr hm)
    measurableEmbedding_sphere_coe.measurable.aemeasurable]
  rw [Measure.map_map measurableEmbedding_sphere_coe.measurable (measurable_mobius a b c d)]
  exact Measure.map_congr he.symm

lemma finite_map_of_sphere_map (μ ν : Measure ℂ) [NullSingletonClass μ] (a b c d : ℂ)
    (hmap : (μ.map ((↑) : ℂ → Sphere)).map (sphereMobius a b c d) =
      ν.map ((↑) : ℂ → Sphere)) : μ.map (mobius a b c d) = ν := by
  apply measurableEmbedding_sphere_coe.map_injective
  rw [← map_sphereMobius μ a b c d]
  exact hmap

/-- The non-atomic Möbius obstruction with its pushforward identity on the Riemann sphere. -/

theorem bounded_mobius (μ ν : Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass μ] [NullSingletonClass ν]
    (Q : Measure (ℂ × ℂ × ℂ × ℂ)) [IsProbabilityMeasure Q]
    (hsep : ∀ᵐ q ∂ Q, q.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2)
    (hsupp : ∀ᵐ q ∂ Q, q.2.2.1 ∈ μ.support ∧ q.2.2.2 ∈ ν.support)
    (hlaw : Q.map (fun q => q.1) = μ)
    (hind : ProbabilityTheory.IndepFun (fun q => q.1) (fun q => q.2.2) Q)
    (hmap : ∀ᵐ q ∂ Q, (μ.map ((↑) : ℂ → Sphere)).map
      (sphereMobius q.1 q.2.1 q.2.2.1 q.2.2.2) = ν.map ((↑) : ℂ → Sphere)) : False := by
  apply no_finite_law μ ν Q hlaw hind (hsupp.mono fun _ h => h.1)
    (hsep.mono fun _ h => h.2)
  exact hmap.mono fun q h => finite_map_of_sphere_map μ ν q.1 q.2.1 q.2.2.1 q.2.2.2 h

end WeakPinned.Bounded

namespace WeakPinned.Bounded
open TopologicalSpace
local instance : MeasurableSpace Sphere := borel Sphere
local instance : BorelSpace Sphere := ⟨rfl⟩

/-- The one-point compactification of the complex plane has a countable basis. -/
instance sphereSecondCountable : SecondCountableTopology Sphere := by
  let B : Set (Set Sphere) :=
    (fun U : Set ℂ => OnePoint.some '' U) '' countableBasis ℂ ∪
      Set.range (fun n : ℕ => (OnePoint.some '' Metric.closedBall (0:ℂ) (n:ℝ))ᶜ)
  have hcount : B.Countable := (countable_countableBasis ℂ).image _ |>.union (Set.countable_range _)
  have hbase : IsTopologicalBasis B := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · intro U hU
      rcases hU with ⟨V,hV,rfl⟩ | ⟨n,rfl⟩
      · exact OnePoint.isOpen_image_coe.mpr ((isBasis_countableBasis ℂ).isOpen hV)
      · exact OnePoint.isOpen_compl_image_coe.mpr ⟨Metric.isClosed_closedBall,isCompact_closedBall _ _⟩
    · intro a U ha hU
      induction a using OnePoint.rec with
      | coe a =>
        have hp : IsOpen (OnePoint.some ⁻¹' U : Set ℂ) := hU.preimage OnePoint.continuous_coe
        obtain ⟨V,hV,haV,hVU⟩ := (isBasis_countableBasis ℂ).mem_nhds_iff.mp (hp.mem_nhds ha)
        refine ⟨OnePoint.some '' V,Or.inl ⟨V,hV,rfl⟩,⟨a,haV,rfl⟩,?_⟩
        rintro z ⟨w,hw,rfl⟩
        exact hVU hw
      | infty =>
        have hc := ((OnePoint.isOpen_iff_of_mem ha).mp hU).2
        obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0:ℂ)
        obtain ⟨n,hn⟩ := exists_nat_gt R
        refine ⟨(OnePoint.some '' Metric.closedBall (0:ℂ) (n:ℝ))ᶜ,Or.inr ⟨n,rfl⟩,?_,?_⟩
        · exact OnePoint.infty_notMem_image_coe
        · intro z hz
          induction z using OnePoint.rec with
          | infty => exact ha
          | coe z =>
            by_contra hnot
            have hzR := hR hnot
            have hzn := Metric.closedBall_subset_closedBall hn.le hzR
            exact hz ⟨z,hzn,rfl⟩
  exact hbase.secondCountableTopology hcount

lemma sphere_pair_subsequence (α : ℕ → ProbabilityMeasure Sphere × ProbabilityMeasure Sphere) :
    ∃ β : ProbabilityMeasure Sphere × ProbabilityMeasure Sphere,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (α ∘ φ) atTop (𝓝 β) := by
  obtain ⟨β,_,φ,hφ,hT⟩ := isCompact_univ.tendsto_subseq (fun n => Set.mem_univ (α n))
  exact ⟨β,φ,hφ,hT⟩

/-- A useful Portmanteau consequence with an eventual bound; measures, not
    arbitrary test function samples, are passed to the limit. -/
lemma weak_open_bound {α : ℕ → ProbabilityMeasure Sphere} {β : ProbabilityMeasure Sphere}
    (hT : Tendsto α atTop (𝓝 β)) {U : Set Sphere} (hU : IsOpen U) (b : ℝ≥0∞)
    (hbound : ∀ᶠ n in atTop, (α n : Measure Sphere) U ≤ b) :
    (β : Measure Sphere) U ≤ b := by
  have hp := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hT hU
  exact hp.trans (liminf_le_of_frequently_le hbound.frequently)

/-- Neighborhood control is enough to remove a possible atom in a weak limit. -/
lemma weak_singleton_zero {α : ℕ → ProbabilityMeasure Sphere} {β : ProbabilityMeasure Sphere}
    (hT : Tendsto α atTop (𝓝 β)) (z : Sphere)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ U : Set Sphere, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, (α n : Measure Sphere) U ≤ ENNReal.ofReal ε) :
    (β : Measure Sphere) {z}=0 := by
  apply le_antisymm _ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hεtop
  have hεR : (0:ℝ) < ε := by exact_mod_cast hε
  obtain ⟨U,hU,hz,hB⟩ := hsmall (ε:ℝ) hεR
  have hb := weak_open_bound hT hU (ENNReal.ofReal (ε:ℝ)) hB
  rw [ENNReal.ofReal_coe_nnreal] at hb
  simpa only [zero_add] using (measure_mono (Set.singleton_subset_iff.mpr hz)).trans hb

/-- Finiteness and nonatomicity on the sphere follow from open-tail and disk
    bounds through the Portmanteau inequality. -/
theorem weak_limit_nonatomic {α : ℕ → ProbabilityMeasure Sphere} {β : ProbabilityMeasure Sphere}
    (hT : Tendsto α atTop (𝓝 β))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ᶠ n in atTop,
      (α n : Measure Sphere) (OnePoint.some '' Metric.closedBall (0:ℂ) R)ᶜ ≤ ENNReal.ofReal ε)
    (hball : ∀ z : ℂ, ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop,
      (α n : Measure Sphere) (OnePoint.some '' Metric.ball z r) ≤ ENNReal.ofReal ε) :
    NullSingletonClass (β : Measure Sphere) := by
  constructor
  intro z
  apply weak_singleton_zero hT z
  intro ε hε
  induction z using OnePoint.rec with
  | infty =>
    obtain ⟨R,hR⟩ := htail ε hε
    exact ⟨_,OnePoint.isOpen_compl_image_coe.mpr ⟨Metric.isClosed_closedBall,isCompact_closedBall _ _⟩,
      OnePoint.infty_notMem_image_coe,hR⟩
  | coe z =>
    obtain ⟨r,hr,hR⟩ := hball z ε hε
    exact ⟨_,OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball,⟨z,Metric.mem_ball_self hr,rfl⟩,hR⟩

/-- Restriction of a sphere probability measure to the complex plane.
    This is a probability measure when there is no mass at infinity. -/
def finitePart (β : ProbabilityMeasure Sphere) : Measure ℂ :=
  Measure.comap ((↑) : ℂ → Sphere) (β : Measure Sphere)

lemma finitePart_probability (β : ProbabilityMeasure Sphere)
    (hinfty : (β : Measure Sphere) {OnePoint.infty}=0) : IsProbabilityMeasure (finitePart β) := by
  constructor
  rw [finitePart,measurableEmbedding_sphere_coe.comap_apply,Set.image_univ]
  have hh : (β : Measure Sphere) (Set.range ((↑) : ℂ → Sphere))ᶜ=0 := by
    simpa only [OnePoint.compl_range_coe] using hinfty
  exact measure_eq_measure_of_null_sdiff (Set.subset_univ _) (by simpa only [← Set.compl_eq_univ_sdiff] using hh) |>.trans (measure_univ)

lemma finitePart_nonatomic (β : ProbabilityMeasure Sphere) [NullSingletonClass (β : Measure Sphere)] :
    NullSingletonClass (finitePart β) := by
  constructor
  intro z
  rw [finitePart,measurableEmbedding_sphere_coe.comap_apply,Set.image_singleton,measure_singleton]

lemma finitePart_map (β : ProbabilityMeasure Sphere)
    (hinfty : (β : Measure Sphere) {OnePoint.infty}=0) :
    (finitePart β).map ((↑) : ℂ → Sphere)=(β : Measure Sphere) := by
  rw [finitePart,measurableEmbedding_sphere_coe.map_comap]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  change (β : Measure Sphere) (Set.range ((↑) : ℂ → Sphere))ᶜ=0
  simpa only [OnePoint.compl_range_coe] using hinfty

end WeakPinned.Bounded

end
end

end OAI
