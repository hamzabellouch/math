import OAI.Combinatorics.HalvingLines.AtomicBounds

namespace OAI

open Filter Topology

namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology
variable {X ι : Type*} [MeasurableSpace X]

lemma probability_overlap_bound (μ : FiniteMeasure X) (S : Finset ι) (p : ι → X → ℝ)
    (hp : ∀ i ∈ S, Measurable (p i)) (hp0 : ∀ i ∈ S, ∀ z, 0 ≤ p i z)
    (hsum : ∀ z, ∑ i ∈ S, p i z ≤ 1) {β : ℝ} (hβ : 0 < β) :
    ∑ i ∈ S, (μ {z | β < p i z} : ℝ) ≤ (μ.mass : ℝ)/β := by
  classical
  let A : ι → Set X := fun i => {z | β < p i z}
  have hm i (hi : i ∈ S) : MeasurableSet (A i) := measurableSet_lt measurable_const (hp i hi)
  have hInt i (hi : i ∈ S) : Integrable ((A i).indicator (fun _ : X => (1 : ℝ))) (μ : Measure X) :=
    (integrable_const 1).indicator (hm i hi)
  have he i (hi : i ∈ S) : ∫ z, (A i).indicator (fun _ : X => (1 : ℝ)) z ∂(μ : Measure X) =
      (μ (A i) : ℝ) := by
    rw [integral_indicator_const 1 (hm i hi)]
    simp
  have hbound (z : X) : (∑ i ∈ S, (A i).indicator (fun _ : X => (1 : ℝ)) z) ≤ 1/β := by
    have hh : β*(∑ i ∈ S, (A i).indicator (fun _ : X => (1 : ℝ)) z) ≤ 1 := by
      calc
        _ = ∑ i ∈ S, β*(A i).indicator (fun _ : X => (1 : ℝ)) z := Finset.mul_sum ..
        _ ≤ ∑ i ∈ S, p i z := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hz : z ∈ A i
          · simpa only [Set.indicator_of_mem hz,mul_one] using (show β < p i z from hz).le
          · simpa only [Set.indicator_of_notMem hz,mul_zero] using hp0 i hi z
        _ ≤ 1 := hsum z
    exact (le_div_iff₀ hβ).mpr (by simpa only [mul_comm] using hh)
  have hh := integral_mono (integrable_finsetSum S hInt) (integrable_const (1/β)) hbound
  rw [integral_finsetSum S hInt] at hh
  rw [Finset.sum_congr rfl he] at hh
  simpa [integral_const,div_eq_mul_inv,FiniteMeasure.mass] using hh

lemma finite_bad_cover_mass (μ : FiniteMeasure X) (S : Finset ι) (p : ι → X → ℝ)
    (hp : ∀ i ∈ S, Measurable (p i)) (hp0 : ∀ i ∈ S, ∀ z, 0 ≤ p i z)
    (hp1 : ∀ i ∈ S, ∀ z, p i z ≤ 1) {β : ℝ}
    {B : Set X} (hB : MeasurableSet B)
    (hcover : ∀ z ∈ B, ∃ i ∈ S, β < p i z) :
    β*(μ B : ℝ) ≤ ∑ i ∈ S, ∫ z in {z | β < p i z}, p i z ∂(μ : Measure X) := by
  classical
  let A : ι → Set X := fun i => {z | β < p i z}
  have hm i (hi : i ∈ S) : MeasurableSet (A i) := measurableSet_lt measurable_const (hp i hi)
  have hInt i (hi : i ∈ S) : Integrable (p i) (μ : Measure X) :=
    (integrable_const (1 : ℝ)).mono' (hp i hi).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hp0 i hi z)] using hp1 i hi z))
  have hInd i (hi : i ∈ S) := (hInt i hi).indicator (hm i hi)
  have hpoint (z : X) : B.indicator (fun _ : X => β) z ≤ ∑ i ∈ S, (A i).indicator (p i) z := by
    have hnn i (hi : i ∈ S) : 0 ≤ (A i).indicator (p i) z := by
      exact Set.indicator_nonneg (fun x _ => hp0 i hi x) z
    by_cases hz : z ∈ B
    · obtain ⟨i,hi,hip⟩ := hcover z hz
      rw [Set.indicator_of_mem hz]
      calc
        β ≤ (A i).indicator (p i) z := by rw [Set.indicator_of_mem (show z ∈ A i from hip)]; exact hip.le
        _ ≤ ∑ i ∈ S, (A i).indicator (p i) z := Finset.single_le_sum hnn hi
    · rw [Set.indicator_of_notMem hz]
      exact Finset.sum_nonneg hnn
  have hh := integral_mono ((integrable_const β).indicator hB) (integrable_finsetSum S hInd) hpoint
  rw [integral_indicator_const β hB,integral_finsetSum S hInd] at hh
  rw [Finset.sum_congr rfl (fun i hi => integral_indicator (hm i hi))] at hh
  simpa [mul_comm] using hh

end PlanarHalving.Limits

namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology

theorem ae_exists_partition_small {X ι : Type*} [MeasurableSpace X]
    (lam μ : FiniteMeasure X) (S : ℕ → Finset ι) (p : ℕ → ι → X → ℝ)
    (mu nu : ℕ → ι → FiniteMeasure X) (s : ℕ → ι → ℝ) (q : ℕ → ℝ)
    {A H : ℝ} (hA : 0 ≤ A)
    (hq : ∀ n, 0 < q n) (hqtop : Tendsto q atTop atTop)
    (hcard : ∀ n, ((S n).card : ℝ) ≤ q n)
    (hp : ∀ n i, i ∈ S n → Measurable (p n i))
    (hp0 : ∀ n i, i ∈ S n → ∀ z, 0 ≤ p n i z)
    (hp1 : ∀ n i, i ∈ S n → ∀ z, p n i z ≤ 1)
    (hsum : ∀ n z, ∑ i ∈ S n, p n i z ≤ 1)
    (hs0 : ∀ n i, i ∈ S n → 0 ≤ s n i)
    (hmu : ∀ n i, i ∈ S n → ∀ B, mu n i B ≤ μ B)
    (hnu : ∀ n i, i ∈ S n → ∀ B, MeasurableSet B →
      (nu n i B : ℝ) = ∫ z in B, p n i z ∂(lam : Measure X))
    (hnuMass : ∀ n i, i ∈ S n → ((nu n i).mass : ℝ) ≤ (q n)⁻¹)
    (hmass : ∀ n i, i ∈ S n → ∀ B, MeasurableSet B →
      (nu n i B : ℝ)^3 ≤ A*(s n i)^3*(mu n i B : ℝ))
    (htail : ∀ n u, 0 < u → ((S n |>.filter fun i => u < s n i).card : ℝ) ≤
      H*u^(-(4:ℝ)/3)) {β : ℝ} (hβ : 0 < β) :
    ∀ᵐ z ∂(lam : Measure X), ∃ n, ∀ i ∈ S n, p n i z ≤ β := by
  classical
  let B : Set X := ⋂ n, ⋃ i ∈ S n, {z | β < p n i z}
  have hm n i (hi : i ∈ S n) : MeasurableSet {z | β < p n i z} :=
    measurableSet_lt measurable_const (hp n i hi)
  have hB : MeasurableSet B := by
    apply MeasurableSet.iInter
    intro n
    exact (S n).finite_toSet.measurableSet_biUnion (fun i hi => hm n i hi)
  have hcover n z (hz : z ∈ B) : ∃ i ∈ S n, β < p n i z := by
    have hz' := mem_iInter.mp hz n
    simpa only [mem_iUnion,mem_ofPred_eq,exists_prop] using hz'
  have hz := persistent_mass_zero S
    (fun n i => (nu n i {z | β < p n i z} : ℝ))
    (fun n i => (mu n i {z | β < p n i z} : ℝ)) s q
    (L := β*(lam B : ℝ)) (A := A) (H := H) (U := (μ.mass : ℝ)/β)
    (mul_nonneg hβ.le (NNReal.coe_nonneg _)) hA hq hqtop hcard
    (fun _ _ _ => NNReal.coe_nonneg _) ?_
    (fun _ _ _ => NNReal.coe_nonneg _) hs0 ?_ ?_ htail ?_
  · have hzero : (lam B : ℝ) = 0 := (mul_eq_zero.mp hz).resolve_left hβ.ne'
    have hzero' : (lam : Measure X) B = 0 := by
      apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
      simpa using hzero
    rw [ae_iff]
    have he : {z | ¬ ∃ n, ∀ i ∈ S n, p n i z ≤ β} = B := by
      ext z
      simp only [mem_ofPred_eq,not_exists,not_forall,not_le,B,mem_iInter,mem_iUnion,
        exists_prop]
    rw [he]
    exact hzero'
  · intro n i hi
    exact (show (nu n i {z | β < p n i z} : ℝ) ≤ ((nu n i).mass : ℝ) from
      NNReal.coe_le_coe.mpr ((nu n i).apply_le_mass _)).trans (hnuMass n i hi)
  · intro n i hi
    exact hmass n i hi _ (hm n i hi)
  · intro n
    exact (Finset.sum_le_sum (fun i hi => NNReal.coe_le_coe.mpr (hmu n i hi _))).trans
      (probability_overlap_bound μ (S n) (p n) (hp n) (hp0 n) (hsum n) hβ)
  · intro n
    have hc := finite_bad_cover_mass lam (S n) (p n) (hp n) (hp0 n) (hp1 n) hB (hcover n)
    simpa only [Finset.sum_congr rfl (fun i hi => hnu n i hi _ (hm n i hi))] using hc

end PlanarHalving.Limits

namespace PlanarHalving.Limits
open MeasureTheory Set Filter ProbabilityTheory

lemma kernel_nullSingleton_of_cells {X T ι : Type*} [MeasurableSpace X]
    [MeasurableSpace T] (lam : Measure X) (h : Kernel X T) [IsMarkovKernel h]
    (S : ℕ → Finset ι) (cell : ℕ → ι → Set T)
    (hcover : ∀ n t, ∃ i ∈ S n, t ∈ cell n i)
    (hsmall : ∀ m : ℕ, ∀ᵐ z ∂lam, ∃ n, ∀ i ∈ S n,
      (h z).real (cell n i) ≤ 1/((m : ℝ)+1)) :
    ∀ᵐ z ∂lam, NullSingletonClass (h z) := by
  have hh := (ae_all_iff.mpr hsmall)
  filter_upwards [hh] with z hz
  constructor
  intro t
  apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
  by_contra hpos
  have htpos : 0 < (h z).real {t} := lt_of_le_of_ne (measureReal_nonneg) (Ne.symm hpos)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt htpos
  obtain ⟨n, hn⟩ := hz m
  obtain ⟨i, hi, hit⟩ := hcover n t
  have hh : (h z).real {t} ≤ (h z).real (cell n i) :=
    measureReal_mono (singleton_subset_iff.mpr hit)
  linarith [hn i hi]

end PlanarHalving.Limits
namespace PlanarHalving.UniformPartition
open MeasureTheory Set
open scoped unitInterval

noncomputable def boundary (m : ℕ) [NeZero m] (i : Fin (m+1)) : I :=
  ⟨(i : ℝ)/(m : ℝ), by
    have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
    constructor
    · positivity
    · apply (div_le_one hm).mpr
      exact_mod_cast (Nat.le_of_lt_succ i.isLt)⟩

noncomputable def cell (m : ℕ) [NeZero m] (i : Fin m) : Set I :=
  if i.val+1=m then Icc (boundary m i.castSucc) (boundary m i.succ)
  else Ico (boundary m i.castSucc) (boundary m i.succ)

lemma cell_measurable (m : ℕ) [NeZero m] (i : Fin m) : MeasurableSet (cell m i) := by
  unfold cell
  split_ifs <;> measurability

lemma cell_lower (m : ℕ) [NeZero m] (i : Fin m) {t : I} (ht : t ∈ cell m i) :
    (i : ℝ)/(m : ℝ) ≤ (t : ℝ) := by
  unfold cell at ht
  split_ifs at ht <;> exact ht.1

lemma cell_upper (m : ℕ) [NeZero m] (i : Fin m) {t : I} (ht : t ∈ cell m i) :
    (t : ℝ) ≤ ((i : ℝ)+1)/(m : ℝ) := by
  unfold cell at ht
  split_ifs at ht
  · simpa [boundary] using (show (t : ℝ) ≤ (boundary m i.succ : ℝ) from ht.2)
  · simpa [boundary] using (show (t : ℝ) ≤ (boundary m i.succ : ℝ) from ht.2.le)

lemma cell_upper_lt (m : ℕ) [NeZero m] (i : Fin m) (hi : i.val+1≠m)
    {t : I} (ht : t ∈ cell m i) : (t : ℝ) < ((i : ℝ)+1)/(m : ℝ) := by
  rw [cell,ite_eq_right hi] at ht
  simpa [boundary] using (show (t : ℝ) < (boundary m i.succ : ℝ) from ht.2)

lemma cells_disjoint (m : ℕ) [NeZero m] : Pairwise (fun i j : Fin m => Disjoint (cell m i) (cell m j)) := by
  have hh (i j : Fin m) (hlt : i.val < j.val) : Disjoint (cell m i) (cell m j) := by
    apply Set.disjoint_left.mpr
    intro t hti htj
    have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
    have hu := cell_upper_lt m i (by omega) hti
    have hl := cell_lower m j htj
    have hij' : (i : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast hlt
    have hc := div_le_div_of_nonneg_right hij' hm.le
    linarith
  intro i j hij
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · exact hh i j h
  · exact (hh j i h).symm

lemma mem_some_cell (m : ℕ) [NeZero m] (t : I) : ∃ i : Fin m, t ∈ cell m i := by
  have hm : 0 < m := NeZero.pos m
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  by_cases ht : (t : ℝ)=1
  · let i : Fin m := ⟨m-1, by omega⟩
    refine ⟨i, ?_⟩
    have hi : i.val+1=m := by dsimp [i]; omega
    rw [cell,ite_eq_left hi]
    constructor
    · change (i : ℝ)/(m : ℝ) ≤ (t : ℝ)
      rw [ht]
      apply (div_le_one hm').mpr
      exact_mod_cast i.isLt.le
    · change (t : ℝ) ≤ ((i.val+1 : ℕ) : ℝ)/(m : ℝ)
      rw [Nat.cast_add,Nat.cast_one,ht]
      have he : (i : ℝ)+1=(m : ℝ) := by exact_mod_cast hi
      rw [he,div_self hm'.ne']
  · have ht' : (t : ℝ)<1 := lt_of_le_of_ne t.property.2 ht
    have hx : 0 ≤ (m : ℝ)*(t : ℝ) := mul_nonneg hm'.le t.property.1
    have hi : ⌊(m : ℝ)*(t : ℝ)⌋₊ < m := by
      apply (Nat.floor_lt hx).mpr
      nlinarith
    let i : Fin m := ⟨⌊(m : ℝ)*(t : ℝ)⌋₊, hi⟩
    have hlo : (i : ℝ)/(m : ℝ) ≤ (t : ℝ) := by
      apply (div_le_iff₀ hm').mpr
      simpa [i,mul_comm] using Nat.floor_le hx
    have hup : (t : ℝ) < ((i : ℝ)+1)/(m : ℝ) := by
      apply (lt_div_iff₀ hm').mpr
      simpa [i,mul_comm] using Nat.lt_floor_add_one ((m : ℝ)*(t : ℝ))
    refine ⟨i, ?_⟩
    unfold cell
    split_ifs
    · refine ⟨hlo, ?_⟩
      change (t : ℝ) ≤ ((i.val+1 : ℕ) : ℝ)/(m : ℝ)
      simpa only [Nat.cast_add,Nat.cast_one] using hup.le
    · refine ⟨hlo, ?_⟩
      change (t : ℝ) < ((i.val+1 : ℕ) : ℝ)/(m : ℝ)
      simpa only [Nat.cast_add,Nat.cast_one] using hup

lemma cells_cover (m : ℕ) [NeZero m] : (⋃ i : Fin m, cell m i) = univ := by
  ext t
  simp only [mem_iUnion,mem_univ,iff_true]
  exact mem_some_cell m t

lemma cell_volume (m : ℕ) [NeZero m] (i : Fin m) :
    volume (cell m i) = ENNReal.ofReal (1/(m : ℝ)) := by
  have he : ((boundary m i.succ : I) : ℝ) - ((boundary m i.castSucc : I) : ℝ) =
      1/(m : ℝ) := by simp [boundary]; ring
  unfold cell
  split_ifs
  · rw [unitInterval.volume_Icc,he]
  · rw [unitInterval.volume_Ico,he]

lemma cell_diameter_bound (m : ℕ) [NeZero m] (i : Fin m) {s t : I}
    (hs : s ∈ cell m i) (ht : t ∈ cell m i) : dist s t ≤ 1/(m : ℝ) := by
  rw [Subtype.dist_eq,Real.dist_eq]
  apply abs_le.mpr
  have hs0 := cell_lower m i hs
  have hs1 := cell_upper m i hs
  have ht0 := cell_lower m i ht
  have ht1 := cell_upper m i ht
  have he : ((i : ℝ)+1)/(m : ℝ) = (i : ℝ)/(m : ℝ)+1/(m : ℝ) := by ring
  rw [he] at hs1 ht1
  constructor <;> linarith

end PlanarHalving.UniformPartition

namespace PlanarHalving.UniformPartition
open MeasureTheory Set Filter
open scoped unitInterval Topology

noncomputable def index (m : ℕ) [NeZero m] (t : I) : Fin m :=
  (mem_some_cell m t).choose

lemma mem_cell_index (m : ℕ) [NeZero m] (t : I) : t ∈ cell m (index m t) :=
  (mem_some_cell m t).choose_spec

lemma index_eq (m : ℕ) [NeZero m] (t : I) (i : Fin m) : index m t = i ↔ t ∈ cell m i := by
  constructor
  · intro h; rw [← h]; exact mem_cell_index m t
  · intro ht
    by_contra hne
    exact Set.disjoint_left.mp (cells_disjoint m hne) (mem_cell_index m t) ht

lemma index_measurable (m : ℕ) [NeZero m] : Measurable (index m) := by
  apply measurable_to_countable'
  intro i
  have he : (index m) ⁻¹' {i} = cell m i := by ext t; exact index_eq m t i
  rw [he]
  exact cell_measurable m i

noncomputable def grid (m : ℕ) [NeZero m] (t : I) : I := boundary m (index m t).castSucc

lemma grid_measurable (m : ℕ) [NeZero m] : Measurable (grid m) :=
  (measurable_of_finite (fun i : Fin m => boundary m i.castSucc)).comp (index_measurable m)

lemma dist_grid (m : ℕ) [NeZero m] (t : I) : dist (grid m t) t ≤ 1/(m : ℝ) := by
  have ht := mem_cell_index m t
  have hl := cell_lower m (index m t) ht
  have hu := cell_upper m (index m t) ht
  rw [Subtype.dist_eq,Real.dist_eq,abs_sub_comm]
  change |(t : ℝ)-(index m t : ℝ)/(m : ℝ)| ≤ _
  rw [abs_of_nonneg (sub_nonneg.mpr hl)]
  change (t : ℝ)-(index m t : ℝ)/(m : ℝ) ≤ 1/(m : ℝ)
  have he : ((index m t : ℝ)+1)/(m : ℝ) = (index m t : ℝ)/(m : ℝ)+1/(m : ℝ) := by ring
  rw [he] at hu
  linarith

lemma grid_tendsto (t : I) : Tendsto (fun n : ℕ => grid (n+1) t) atTop (𝓝 t) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => dist_grid (n+1) t)
  simpa only [Nat.cast_add,Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat

lemma grid_pair_tendsto (t : I × I) :
    Tendsto (fun n : ℕ => (grid (n+1) t.1,grid (n+1) t.2)) atTop (𝓝 t) :=
  (grid_tendsto t.1).prodMk_nhds (grid_tendsto t.2)

lemma integral_partition {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) [IsFiniteMeasure μ] (C : ι → Set X)
    (hC : ∀ i, MeasurableSet (C i))
    (idx : X → ι) (hi : ∀ x i, idx x = i ↔ x ∈ C i) (v : ι → ℝ) :
    ∫ x, v (idx x) ∂μ = ∑ i, μ.real (C i)*v i := by
  classical
  have he : (fun x => v (idx x)) = fun x => ∑ i, (C i).indicator (fun _ => v i) x := by
    funext x
    symm
    rw [Finset.sum_eq_single (idx x)]
    · exact Set.indicator_of_mem ((hi x (idx x)).mp rfl) _
    · intro j _ hj
      rw [Set.indicator_of_notMem]
      intro hx
      exact hj ((hi x j).mpr hx).symm
    · simp
  rw [he,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator_const _ (hC i)]
    simp only [smul_eq_mul]
  · intro i _
    exact (integrable_const (v i)).indicator (hC i)

lemma integral_grid (m : ℕ) [NeZero m] (f : I → ℝ) :
    ∫ t, f (grid m t) = (∑ i : Fin m, f (boundary m i.castSucc))/(m : ℝ) := by
  rw [show (fun t => f (grid m t)) = fun t =>
    (fun i : Fin m => f (boundary m i.castSucc)) (index m t) from rfl]
  rw [integral_partition volume (cell m) (cell_measurable m)
    (index m) (index_eq m) (fun i : Fin m => f (boundary m i.castSucc))]
  simp only [measureReal_def,cell_volume,ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/(m : ℝ))]
  rw [← Finset.mul_sum]
  ring

lemma integral_grid_pair (m : ℕ) [NeZero m] (f : I × I → ℝ) :
    ∫ t : I × I, f (grid m t.1,grid m t.2) =
      (∑ i : Fin m × Fin m, f (boundary m i.1.castSucc,boundary m i.2.castSucc))/(m : ℝ)^2 := by
  let C : Fin m × Fin m → Set (I × I) := fun i => cell m i.1 ×ˢ cell m i.2
  have hC i : MeasurableSet (C i) := (cell_measurable m i.1).prod (cell_measurable m i.2)
  let idx : I × I → Fin m × Fin m := fun t => (index m t.1,index m t.2)
  have hi t i : idx t = i ↔ t ∈ C i := by
    rcases i with ⟨i,j⟩
    simp only [idx,C,Prod.mk.injEq,index_eq,mem_prod]
  change ∫ t, (fun i : Fin m × Fin m => f (boundary m i.1.castSucc,boundary m i.2.castSucc)) (idx t) = _
  rw [integral_partition volume C hC idx hi (fun i => f (boundary m i.1.castSucc,boundary m i.2.castSucc))]
  have hv i : volume.real (C i) = 1/(m : ℝ)^2 := by
    rw [measureReal_def]
    change ((volume.prod volume) (cell m i.1 ×ˢ cell m i.2)).toReal = _
    rw [Measure.prod_prod,cell_volume,cell_volume,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/(m : ℝ))]
    ring
  simp_rw [hv]
  rw [← Finset.mul_sum]
  ring

end PlanarHalving.UniformPartition

namespace PlanarHalving.UniformPartition
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped unitInterval Topology

lemma grid_tendsto_seq (m : ℕ → ℕ) [∀ n, NeZero (m n)] (hm : Tendsto m atTop atTop) (t : I) :
    Tendsto (fun n => grid (m n) t) atTop (𝓝 t) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => dist_grid (m n) t)
  have hnat : Tendsto (fun n => (m n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hnat

lemma riemann_tendsto (m : ℕ → ℕ) [∀ n, NeZero (m n)] (hm : Tendsto m atTop atTop)
    (f : BoundedContinuousFunction (I × I) ℝ) :
    Tendsto (fun n => (∑ i : Fin (m n) × Fin (m n),
      f (boundary (m n) i.1.castSucc,boundary (m n) i.2.castSucc))/(m n : ℝ)^2)
      atTop (𝓝 (∫ t : I × I, f t)) := by
  simp_rw [← integral_grid_pair]
  apply tendsto_integral_of_dominated_convergence (fun _ : I × I => ‖f‖)
  · intro n
    exact (f.continuous.measurable.comp
      (((grid_measurable (m n)).comp measurable_fst).prodMk
        ((grid_measurable (m n)).comp measurable_snd))).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Filter.Eventually.of_forall (fun _ => f.norm_coe_le_norm _)
  · exact Filter.Eventually.of_forall (fun t => (f.continuous.tendsto t).comp
      ((grid_tendsto_seq m hm t.1).prodMk_nhds (grid_tendsto_seq m hm t.2)))

end PlanarHalving.UniformPartition

namespace PlanarHalving.Limits
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology

lemma measure_le_of_test {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ ν : FiniteMeasure X)
    (h : ∀ f : BoundedContinuousFunction X ℝ, (∀ x, 0 ≤ f x) → ∫ x, f x ∂(μ : Measure X) ≤ ∫ x, f x ∂(ν : Measure X)) :
    (μ : Measure X) ≤ (ν : Measure X) := by
  have hn (f : BoundedContinuousFunction X NNReal) : ∫⁻ x, f x ∂(μ : Measure X) ≤ ∫⁻ x, f x ∂(ν : Measure X) := by
    let g : BoundedContinuousFunction X ℝ := ⟨⟨fun x => (f x : ℝ), continuous_subtype_val.comp f.continuous⟩,f.map_bounded'⟩
    apply (ENNReal.toReal_le_toReal (f.lintegral_lt_top_of_nnreal _).ne
      (f.lintegral_lt_top_of_nnreal _).ne).mp
    rw [toReal_lintegral_coe_eq_integral f μ,toReal_lintegral_coe_eq_integral f ν]
    exact h g (fun x => NNReal.coe_nonneg _)
  have hclosed (F : Set X) (hF : IsClosed F) : (μ : Measure X) F ≤ (ν : Measure X) F := by
    exact le_of_tendsto_of_tendsto (HasOuterApproxClosed.tendsto_lintegral_apprSeq hF (μ : Measure X))
      (HasOuterApproxClosed.tendsto_lintegral_apprSeq hF (ν : Measure X)) (Filter.Eventually.of_forall (fun n => hn (hF.apprSeq n)))
  apply Measure.le_iff.mpr
  intro F hF
  rw [hF.measure_eq_iSup_isCompact (μ : Measure X)]
  exact iSup_le (fun K => iSup_le (fun hKF => iSup_le (fun hK =>
    (hclosed K hK.isClosed).trans (measure_mono hKF))))

end PlanarHalving.Limits

namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology unitInterval NNReal ENNReal

noncomputable def weightedAtoms {X : Type*} [MeasurableSpace X] {α : Type*} [Fintype α]
    (w : ℝ≥0) (x : α → X) : FiniteMeasure X :=
  ⟨w • (∑ i, Measure.dirac (x i) : Measure X), inferInstance⟩

lemma integral_weightedAtoms {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {α : Type*} [Fintype α] (w : ℝ≥0) (x : α → X) (f : X → ℝ) :
    ∫ t, f t ∂(weightedAtoms w x : Measure X) = (w : ℝ) * ∑ i, f (x i) := by
  classical
  change ∫ t, f t ∂((w : ℝ≥0∞) • ∑ i, Measure.dirac (x i)) = _
  rw [integral_smul_measure,integral_finsetSum_measure]
  · simp only [integral_dirac,ENNReal.coe_toReal,smul_eq_mul]
  · intro i _
    exact integrable_dirac (by simp)

lemma mass_weightedAtoms {X : Type*} [MeasurableSpace X] {α : Type*} [Fintype α]
    (w : ℝ≥0) (x : α → X) :
    (weightedAtoms w x).mass = w * Fintype.card α := by
  classical
  simp [weightedAtoms,FiniteMeasure.mass,FiniteMeasure.mk_apply,Measure.smul_apply,
    Measure.finsetSum_apply]

end PlanarHalving.Limits

namespace PlanarHalving.UniformPartition
open MeasureTheory Set Filter PlanarHalving.Limits
open scoped Topology unitInterval NNReal ENNReal

noncomputable def gridPoint (m : ℕ) [NeZero m] (i : Fin m × Fin m) : I × I :=
  (boundary m i.1.castSucc,boundary m i.2.castSucc)

lemma grid_sum_le {m c : ℕ} [NeZero m] (slots : Fin c → Fin m × Fin m)
    (hs : Function.Injective slots) (f : I × I → ℝ) (hf : ∀ t, 0 ≤ f t) :
    (∑ i, f (gridPoint m (slots i))) ≤ ∑ j, f (gridPoint m j) := by
  classical
  rw [← Finset.sum_image (f := fun j => f (gridPoint m j)) hs.injOn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hf _)

lemma normalized_perturbed_sum_le {m c : ℕ} [NeZero m]
    (slots : Fin c → Fin m × Fin m) (hs : Function.Injective slots)
    (x : Fin c → I × I) (f : I × I → ℝ) (hf : ∀ t, 0 ≤ f t)
    {ε : ℝ} (hε : 0 ≤ ε) (hclose : ∀ i, f (x i) ≤ f (gridPoint m (slots i)) + ε) :
    (∑ i, f (x i))/(m : ℝ)^2 ≤
      (∑ j : Fin m × Fin m, f (gridPoint m j))/(m : ℝ)^2 + ε := by
  have hm : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m
  have hc : (c : ℝ) ≤ (m : ℝ)^2 := by
    have h := Fintype.card_le_of_injective slots hs
    simp only [Fintype.card_fin,Fintype.card_prod] at h
    simpa only [pow_two] using (show (c : ℝ) ≤ (m : ℝ)*(m : ℝ) by exact_mod_cast h)
  have hsum : (∑ i, f (x i)) ≤ (∑ j : Fin m × Fin m, f (gridPoint m j)) + (c : ℝ)*ε := by
    calc
      _ ≤ ∑ i, (f (gridPoint m (slots i)) + ε) := Finset.sum_le_sum (fun i _ => hclose i)
      _ = (∑ i, f (gridPoint m (slots i))) + (c : ℝ)*ε := by simp [Finset.sum_add_distrib]
      _ ≤ _ := add_le_add (grid_sum_le slots hs f hf) le_rfl
  have hεc : (c : ℝ)*ε ≤ (m : ℝ)^2*ε := mul_le_mul_of_nonneg_right hc hε
  apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
  nlinarith [div_mul_cancel₀ (∑ j : Fin m × Fin m, f (gridPoint m j)) (ne_of_gt (sq_pos_of_pos hm))]

lemma perturbed_grid_limit_le_volume (m c : ℕ → ℕ) [∀ n, NeZero (m n)]
    (hm : Tendsto m atTop atTop) (x : ∀ n, Fin (c n) → I × I)
    (slots : ∀ n, Fin (c n) → Fin (m n) × Fin (m n))
    (hs : ∀ n, Function.Injective (slots n))
    (d : ℕ → ℝ) (hd : Tendsto d atTop (𝓝 0))
    (hclose : ∀ n i, dist (x n i) (gridPoint (m n) (slots n i)) ≤ d n)
    (μ : FiniteMeasure (I × I))
    (hμ : Tendsto (fun n => weightedAtoms ((m n : ℝ≥0)^2)⁻¹ (x n)) atTop (𝓝 μ)) :
    (μ : Measure (I × I)) ≤ volume := by
  let ν : FiniteMeasure (I × I) := ⟨volume,inferInstance⟩
  apply measure_le_of_test μ ν
  intro f hf
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ,hδ,hfδ⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) ε hε
  have hdδ : ∀ᶠ n in atTop, d n < δ := (tendsto_order.mp hd).2 δ hδ
  have hineq : ∀ᶠ n in atTop,
      ∫ t, f t ∂(weightedAtoms ((m n : ℝ≥0)^2)⁻¹ (x n) : Measure (I × I)) ≤
        (∑ j : Fin (m n) × Fin (m n), f (gridPoint (m n) j))/(m n : ℝ)^2 + ε := by
    filter_upwards [hdδ] with n hn
    rw [integral_weightedAtoms]
    simp only [NNReal.coe_inv,NNReal.coe_pow,NNReal.coe_natCast]
    rw [← div_eq_inv_mul]
    apply normalized_perturbed_sum_le (slots n) (hs n) (x n) f hf hε.le
    intro i
    have h := hfδ ((hclose n i).trans_lt hn)
    rw [Real.dist_eq,abs_lt] at h
    linarith [h.2]
  have hlim := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) f
  have hgrid := (riemann_tendsto m hm f).add_const ε
  apply le_of_tendsto_of_tendsto hlim hgrid
  filter_upwards [hineq] with n hn
  exact hn

end PlanarHalving.UniformPartition

end OAI
