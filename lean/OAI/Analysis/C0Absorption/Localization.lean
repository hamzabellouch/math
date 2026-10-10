import OAI.Analysis.C0Absorption.Pairings

namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

open Set Filter Topology

theorem dist_le_of_local_interval {Y : Type*} [PseudoMetricSpace Y]
    {a b K : ℝ} (hab : a ≤ b) {f : ℝ → Y}
    (hf : ContinuousOn f (Icc a b))
    (hloc : ∀ x ∈ Icc a b, ∀ᶠ y in nhdsWithin x (Icc a b),
      dist (f x) (f y) ≤ K * dist x y) :
    dist (f a) (f b) ≤ K * (b-a) := by
  let s : Set ℝ := {x | dist (f a) (f x) ≤ K * (x-a)}
  have hclosed : IsClosed (s ∩ Icc a b) := by
    have hc : ContinuousOn (fun x => (dist (f a) (f x), K * (x-a))) (Icc a b) :=
      (show ContinuousOn (fun x => dist (f a) (f x)) (Icc a b) from
        fun x hx => tendsto_const_nhds.dist (hf x hx)).prodMk (continuousOn_const.mul
        (continuousOn_id.sub continuousOn_const))
    simpa only [s, inter_comm, Set.preimage_ofPred_eq] using hc.preimage_isClosed_of_isClosed isClosed_Icc
      OrderClosedTopology.isClosed_le'
  have ha : a ∈ s := by simp [s]
  have hs := hclosed.Icc_subset_of_forall_exists_gt ha
  apply hs ?_ ⟨hab, le_rfl⟩
  rintro x ⟨hx : dist (f a) (f x) ≤ K * (x-a), hxab⟩ y hxy
  have hh : ∀ᶠ z in nhdsWithin x (Ioi x), dist (f x) (f z) ≤ K * dist x z :=
    nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem hxab) (hloc x ⟨hxab.1, hxab.2.le⟩)
  obtain ⟨z, hz, hxz, hzy⟩ := (hh.and (Ioc_mem_nhdsGT hxy)).exists
  refine ⟨z, ?_, hxz, hzy⟩
  change dist (f a) (f z) ≤ K * (z-a)
  have hdist : dist x z = z-x := by rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxz.le)]; ring
  rw [hdist] at hz
  calc
    dist (f a) (f z) ≤ dist (f a) (f x) + dist (f x) (f z) := dist_triangle _ _ _
    _ ≤ K * (x-a) + K * (z-x) := add_le_add hx hz
    _ = K * (z-a) := by ring

theorem lipschitzOn_convex_of_local {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Y]
    {B : Set E} (hB : Convex ℝ B) {f : E → Y} {K : ℝ≥0}
    (hf : ContinuousOn f B)
    (hloc : ∀ x ∈ B, ∀ᶠ y in nhdsWithin x B, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzOnWith K f B := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let g : ℝ → E := AffineMap.lineMap x y
  have hg : Continuous g := by
    change Continuous (fun t : ℝ => t • (y-x) + x)
    fun_prop
  have hmap : MapsTo g (Icc 0 1) B := fun t ht => hB.lineMap_mem hx hy ht
  have hc : ContinuousOn (f ∘ g) (Icc 0 1) := hf.comp hg.continuousOn hmap
  have hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ u in nhdsWithin t (Icc 0 1),
      dist ((f ∘ g) t) ((f ∘ g) u) ≤ (K * dist x y) * dist t u := by
    intro t ht
    have hgt := (hg.continuousAt (x := t)).continuousWithinAt.tendsto_nhdsWithin hmap
    filter_upwards [hgt (hloc (g t) (hmap ht))] with u hu
    change dist (f (g t)) (f (g u)) ≤ _
    calc
      dist (f (g t)) (f (g u)) ≤ K * dist (g t) (g u) := hu
      _ = (K * dist x y) * dist t u := by
        rw [show dist (g t) (g u) = dist t u * dist x y from dist_lineMap_lineMap x y t u]
        ring
  have h := dist_le_of_local_interval (by norm_num : (0 : ℝ) ≤ 1) hc hh
  simpa [g, Function.comp_def] using h

theorem lipschitz_convex_subtype_of_local {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Y]
    {B : Set E} (hB : Convex ℝ B) {f : B → Y} {K : ℝ≥0}
    (hf : Continuous f)
    (hloc : ∀ x, ∀ᶠ y in nhds x, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzWith K f := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let F : E → Y := fun z => if h : z ∈ B then f ⟨z, h⟩ else f x
  have hF (z : B) : F z = f z := by simp [F]
  have hc : ContinuousOn F B := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert hf using 1
    exact funext hF
  have hl : ∀ z ∈ B, ∀ᶠ w in nhdsWithin z B,
      dist (F z) (F w) ≤ K * dist z w := by
    intro z hz
    rw [nhdsWithin_eq_map_subtype_coe hz]
    change ∀ᶠ w : B in nhds ⟨z, hz⟩, dist (F z) (F w) ≤ K * dist z (w : E)
    simpa only [show F z = f ⟨z, hz⟩ from hF ⟨z, hz⟩, hF, Subtype.dist_eq] using hloc ⟨z, hz⟩
  have hh := (lipschitzOn_convex_of_local hB hc hl).dist_le_mul x x.property y y.property
  simpa only [hF, Subtype.dist_eq] using hh

theorem eventually_zero_of_not_tsupport {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {x : X} (hx : x ∉ tsupport f) : ∀ᶠ y in nhds x, f y = 0 := by
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
  exact image_eq_zero_of_notMem_tsupport hy

theorem disjoint_supports_signed_lipschitz {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E} (hB : Convex ℝ B)
    {ι : Type*} [Fintype ι] (f : ι → B → ℝ) (K : ℝ≥0)
    (hf : ∀ i, LipschitzWith K (f i))
    (hdisj : Pairwise (fun i j => Disjoint (tsupport (f i)) (tsupport (f j))))
    (ε : ι → ℝ) (hε : ∀ i, |ε i| = 1) :
    LipschitzWith K (fun x => ∑ i, ε i * f i x) := by
  classical
  apply lipschitz_convex_subtype_of_local hB
  · exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hf i).continuous)
  intro x
  by_cases hex : ∃ j, x ∈ tsupport (f j)
  · obtain ⟨j, hj⟩ := hex
    have hz : ∀ i, i ≠ j → ∀ᶠ y in nhds x, f i y = 0 := by
      intro i hij
      apply eventually_zero_of_not_tsupport
      intro hi
      exact Set.disjoint_left.mp (hdisj hij) hi hj
    have he : ∀ᶠ y in nhds x, ∀ i, i ≠ j → f i y = 0 :=
      Filter.eventually_all.mpr (fun i => if hi : i = j then by simp [hi] else
        (hz i hi).mono (fun y hy _ => hy))
    filter_upwards [he] with y hy
    have hx (i) (hi : i ≠ j) : f i x = 0 := (hz i hi).self_of_nhds
    have sx : (∑ i, ε i * f i x) = ε j * f j x := by
      apply Finset.sum_eq_single j
      · intro i hi hij; simp [hx i hij]
      · simp
    have sy : (∑ i, ε i * f i y) = ε j * f j y := by
      apply Finset.sum_eq_single j
      · intro i hi hij; simp [hy i hij]
      · simp
    rw [sx, sy, Real.dist_eq, ← mul_sub, abs_mul, hε, one_mul, ← Real.dist_eq]
    exact (hf j).dist_le_mul x y
  · push Not at hex
    have he : ∀ᶠ y in nhds x, ∀ i, f i y = 0 :=
      Filter.eventually_all.mpr (fun i => eventually_zero_of_not_tsupport (hex i))
    filter_upwards [he] with y hy
    have hx (i) : f i x = 0 := image_eq_zero_of_notMem_tsupport (hex i)
    simp only [hx, hy, mul_zero, Finset.sum_const_zero, dist_self]
    positivity

theorem nested_supports_signed_lipschitz {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E} (hB : Convex ℝ B)
    (n : ℕ) (u b : Fin n → B → ℝ) (e : Fin n → ℝ)
    (C : Fin n → Set B) (K : ℝ≥0) (Kb : Fin n → ℝ≥0)
    (_hu : ∀ i, Continuous (u i)) (hb : ∀ i, LipschitzWith (Kb i) (b i))
    (hF : ∀ i, LipschitzWith K (fun x => u i x * b i x))
    (hC : ∀ i, IsOpen (C i)) (hc : ∀ i, ∀ x ∈ C i, u i x = e i)
    (hnest : ∀ i j, i < j → tsupport (u j) ⊆ C i)
    (ε : Fin n → ℝ) (hε : ∀ i, |ε i| = 1) :
    LipschitzWith (K + ∑ i, ‖e i‖₊ * Kb i)
      (fun x => ∑ i, ε i * (u i x * b i x)) := by
  classical
  apply lipschitz_convex_subtype_of_local hB
  · exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hF i).continuous)
  intro x
  let H : Finset (Fin n) := Finset.univ.filter (fun i => x ∈ tsupport (u i))
  by_cases hH : H.Nonempty
  · let j := H.max' hH
    have hj : x ∈ tsupport (u j) := (Finset.mem_filter.mp (H.max'_mem hH)).2
    have he (i) (hij : i < j) : ∀ᶠ y in nhds x, u i y = e i := by
      filter_upwards [(hC i).mem_nhds (hnest i j hij hj)] with y hy
      exact hc i y hy
    have hz (i) (hji : j < i) : ∀ᶠ y in nhds x, u i y = 0 := by
      apply eventually_zero_of_not_tsupport
      intro hi
      have hiH : i ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      exact (not_lt_of_ge (H.le_max' i hiH)) hji
    have hall : ∀ᶠ y in nhds x, ∀ i,
        (i < j → u i y = e i) ∧ (j < i → u i y = 0) := by
      apply Filter.eventually_all.mpr
      intro i
      rcases lt_trichotomy i j with hij | rfl | hji
      · filter_upwards [he i hij] with y hy
        exact ⟨fun _ => hy, fun h => (not_lt_of_ge hij.le h).elim⟩
      · exact Filter.Eventually.of_forall (by simp)
      · filter_upwards [hz i hji] with y hy
        exact ⟨fun h => (not_lt_of_ge hji.le h).elim, fun _ => hy⟩
    filter_upwards [hall] with y hy
    have hi (i : Fin n) :
        dist (ε i * (u i x * b i x)) (ε i * (u i y * b i y)) ≤
          ((if i = j then (K : ℝ) else 0) + |e i| * Kb i) * dist x y := by
      rcases lt_trichotomy i j with hij | rfl | hji
      · have hx := (he i hij).self_of_nhds
        rw [hx, (hy i).1 hij, ite_eq_right (ne_of_lt hij), zero_add,
          Real.dist_eq, ← mul_sub, ← mul_sub, abs_mul, abs_mul, hε i, one_mul]
        calc
          |e i| * |b i x - b i y| ≤ |e i| * (Kb i * dist x y) := by
            apply mul_le_mul_of_nonneg_left ((hb i).dist_le_mul x y) (abs_nonneg _)
          _ = |e i| * Kb i * dist x y := by ring
      · rw [ite_eq_left rfl, Real.dist_eq, ← mul_sub, abs_mul, hε, one_mul,
          ← Real.dist_eq]
        exact ((hF j).dist_le_mul x y).trans
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (dist_nonneg))
      · rw [(hz i hji).self_of_nhds, (hy i).2 hji]
        simp only [zero_mul, mul_zero, dist_self]
        positivity
    calc
      dist (∑ i, ε i * (u i x * b i x)) (∑ i, ε i * (u i y * b i y))
          ≤ ∑ i, dist (ε i * (u i x * b i x)) (ε i * (u i y * b i y)) :=
        dist_sum_sum_le _ _ _
      _ ≤ ∑ i, ((if i = j then (K : ℝ) else 0) + |e i| * Kb i) * dist x y :=
        Finset.sum_le_sum (fun i _ => hi i)
      _ = (K + ∑ i, ‖e i‖₊ * Kb i : ℝ≥0) * dist x y := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib]
        simp [Real.norm_eq_abs]
  · have hz (i : Fin n) : ∀ᶠ y in nhds x, u i y = 0 := by
      apply eventually_zero_of_not_tsupport
      intro hi
      exact hH ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    filter_upwards [Filter.eventually_all.mpr hz] with y hy
    have hx (i : Fin n) : u i x = 0 := (hz i).self_of_nhds
    simp only [hx, hy, zero_mul, mul_zero, Finset.sum_const_zero, dist_self]
    positivity

noncomputable section

def chi (t : ℝ) : ℝ := min 1 (max 0 (2*t-1))

def cutoff {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (x : X) : ℝ :=
  1 - chi (dist x q / ε)

def localG {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (u : X → ℝ) (x : X) : ℝ :=
  u q + chi (dist x q / ε) * (u x-u q)

def localR {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (u : X → ℝ) (x : X) : ℝ :=
  localG q ε u x-u x

theorem cutoff_nonneg {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (x : X) :
    0 ≤ cutoff q ε x := by
  dsimp [cutoff, chi]
  have := min_le_left (1 : ℝ) (max 0 (2 * (dist x q / ε) - 1))
  linarith

theorem cutoff_le_one {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (x : X) :
    cutoff q ε x ≤ 1 := by
  dsimp [cutoff, chi]
  have : 0 ≤ min (1 : ℝ) (max 0 (2 * (dist x q / ε) - 1)) := by positivity
  linarith

theorem localR_eq {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (u : X → ℝ) (x : X) :
    localR q ε u x = cutoff q ε x * (u q-u x) := by
  dsimp [localR, localG, cutoff]
  ring

theorem localG_eq {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) (u : X → ℝ) (x : X) :
    localG q ε u x = u x + localR q ε u x := by
  simp [localR]

theorem cutoff_eq_zero {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ} (hε : 0 < ε)
    (x : X) (hx : ε ≤ dist x q) : cutoff q ε x = 0 := by
  have hh : 1 ≤ dist x q / ε := (le_div_iff₀ hε).mpr (by simpa using hx)
  simp [cutoff, chi, max_eq_right (by linarith : 0 ≤ 2*(dist x q/ε)-1),
    min_eq_left (by linarith : (1:ℝ) ≤ 2*(dist x q/ε)-1)]

theorem dist_lt_of_cutoff_ne_zero {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ}
    (hε : 0 < ε) (x : X) (hx : cutoff q ε x ≠ 0) : dist x q < ε := by
  by_contra! hh
  exact hx (cutoff_eq_zero q hε x hh)

theorem localG_plateau {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ} (hε : 0 < ε)
    (u : X → ℝ) (x : X) (hx : dist x q ≤ ε/2) : localG q ε u x = u q := by
  have hh : dist x q / ε ≤ 1/2 := (div_le_iff₀ hε).mpr (by linarith)
  simp [localG, chi, max_eq_left (by linarith : 2*(dist x q/ε)-1 ≤ 0)]

theorem chi_lipschitz : LipschitzWith 2 chi := by
  have h : LipschitzWith 2 (fun t : ℝ => 2*t-1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq, show (2*x-1)-(2*y-1)=2*(x-y) by ring, abs_mul]
    norm_num
  change LipschitzWith 2 (fun t : ℝ => min 1 (max 0 (2*t-1)))
  exact (h.const_max 0).const_min 1

theorem cutoff_dist_le {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ}
    (hε : 0 < ε) (x y : X) :
    |cutoff q ε x-cutoff q ε y| ≤ (2 / ε) * dist x y := by
  have h := chi_lipschitz.dist_le_mul (dist x q / ε) (dist y q / ε)
  simp only [Real.dist_eq, NNReal.coe_ofNat] at h
  have heq : |cutoff q ε x-cutoff q ε y| =
      |chi (dist x q/ε)-chi (dist y q/ε)| := by
    rw [cutoff, cutoff, sub_sub_sub_cancel_left, abs_sub_comm]
  rw [heq]
  calc
    |chi (dist x q/ε)-chi (dist y q/ε)| ≤ 2 * |dist x q/ε-dist y q/ε| := h
    _ = (2/ε)*|dist x q-dist y q| := by rw [← sub_div, abs_div, abs_of_pos hε]; ring
    _ ≤ (2/ε)*dist x y := mul_le_mul_of_nonneg_left
      (abs_dist_sub_le x y q) (by positivity)

theorem localR_sup_lip {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ}
    (hε : 0 < ε) (u : X → ℝ) {L : ℝ≥0} (hu : LipschitzWith L u) (x : X) :
    |localR q ε u x| ≤ ε * L := by
  rw [localR_eq, abs_mul, abs_of_nonneg (cutoff_nonneg _ _ _)]
  by_cases hx : cutoff q ε x = 0
  · rw [hx, zero_mul]; positivity
  have hd := (dist_lt_of_cutoff_ne_zero q hε x hx).le
  have hb : |u q-u x| ≤ ε * L := by
    calc
      |u q-u x| ≤ L * dist q x := hu.dist_le_mul q x
      _ ≤ L * ε := mul_le_mul_of_nonneg_left (by rwa [dist_comm]) L.coe_nonneg
      _ = ε*L := mul_comm _ _
  exact (mul_le_mul_of_nonneg_right (cutoff_le_one q ε x) (abs_nonneg _)).trans (by simpa using hb)

theorem localR_lipschitz {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ}
    (hε : 0 < ε) (u : X → ℝ) {L : ℝ≥0} (hu : LipschitzWith L u) :
    LipschitzWith (3*L) (localR q ε u) := by
  have hb (x y : X) (hy : cutoff q ε y ≠ 0) :
      |localR q ε u x-localR q ε u y| ≤ (3*L : ℝ≥0)*dist x y := by
    have hd := (dist_lt_of_cutoff_ne_zero q hε y hy).le
    have huq : |u q-u y| ≤ ε*L := by
      calc
        |u q-u y| ≤ L*dist q y := hu.dist_le_mul q y
        _ ≤ L*ε := mul_le_mul_of_nonneg_left (by rwa [dist_comm]) L.coe_nonneg
        _ = ε*L := mul_comm _ _
    have heq : localR q ε u x-localR q ε u y =
        cutoff q ε x*(u y-u x)+(cutoff q ε x-cutoff q ε y)*(u q-u y) := by
      simp only [localR_eq]; ring
    rw [heq]
    calc
      |cutoff q ε x*(u y-u x)+(cutoff q ε x-cutoff q ε y)*(u q-u y)|
          ≤ |cutoff q ε x*(u y-u x)| + |(cutoff q ε x-cutoff q ε y)*(u q-u y)| := abs_add_le _ _
      _ = cutoff q ε x*|u y-u x| + |cutoff q ε x-cutoff q ε y| * |u q-u y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (cutoff_nonneg _ _ _)]
      _ ≤ 1 * (L*dist x y) + ((2/ε)*dist x y)*(ε*L) := by
        apply add_le_add
        · apply mul_le_mul (cutoff_le_one q ε x)
          · have hd := hu.dist_le_mul y x
            rw [dist_comm y x] at hd
            exact hd
          · exact abs_nonneg _
          · norm_num
        · exact mul_le_mul (cutoff_dist_le q hε x y) huq (abs_nonneg _) (by positivity)
      _ = (3*L : ℝ≥0)*dist x y := by
        push_cast
        field_simp
        ; ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  by_cases hy : cutoff q ε y = 0
  · by_cases hx : cutoff q ε x = 0
    · simp [localR_eq, hx, hy]; positivity
    · simpa only [abs_sub_comm, dist_comm] using hb y x hx
  · exact hb x y hy

theorem localG_lipschitz {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ}
    (hε : 0 < ε) (u : X → ℝ) {L : ℝ≥0} (hu : LipschitzWith L u) :
    LipschitzWith (4*L) (localG q ε u) := by
  have heq : localG q ε u = fun x => u x+localR q ε u x := funext (localG_eq q ε u)
  rw [heq]
  have hc : L+3*L=4*L := by ring
  rw [← hc]
  exact hu.add (localR_lipschitz q hε u hu)

theorem localG_sup {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ)
    (u : X → ℝ) (A : ℝ) (hu : ∀ x, |u x| ≤ A) (x : X) :
    |localG q ε u x| ≤ A := by
  have ha := cutoff_nonneg q ε x
  have ha' := cutoff_le_one q ε x
  have heq : localG q ε u x = (1-cutoff q ε x)*u x+cutoff q ε x*u q := by
    rw [localG_eq, localR_eq]; ring
  rw [heq]
  calc
    |(1-cutoff q ε x)*u x+cutoff q ε x*u q|
        ≤ |(1-cutoff q ε x)*u x|+|cutoff q ε x*u q| := abs_add_le _ _
    _ = (1-cutoff q ε x)*|u x|+cutoff q ε x*|u q| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg (by linarith : 0 ≤ 1-cutoff q ε x)]
    _ ≤ (1-cutoff q ε x)*A+cutoff q ε x*A := add_le_add
      (mul_le_mul_of_nonneg_left (hu x) (by linarith)) (mul_le_mul_of_nonneg_left (hu q) ha)
    _ = A := by ring

theorem localR_sup {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ)
    (u : X → ℝ) (A : ℝ) (hu : ∀ x, |u x| ≤ A) (x : X) :
    |localR q ε u x| ≤ 2*A := by
  calc
    |localR q ε u x| = |localG q ε u x-u x| := rfl
    _ ≤ |localG q ε u x|+|u x| := abs_sub _ _
    _ ≤ A+A := add_le_add (localG_sup q ε u A hu x) (hu x)
    _ = 2*A := by ring

def localGLinear {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) :
    (X → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun := localG q ε
  map_add' u v := by ext x; simp only [localG, Pi.add_apply]; ring
  map_smul' c u := by ext x; simp only [localG, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def localRLinear {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ) :
    (X → ℝ) →ₗ[ℝ] (X → ℝ) := localGLinear q ε - LinearMap.id

@[simp] theorem localRLinear_apply {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ)
    (u : X → ℝ) : localRLinear q ε u = localR q ε u := rfl

def localOp {X : Type*} [PseudoMetricSpace X] (isG : Bool) (q : X) (ε : ℝ) :
    (X → ℝ) →ₗ[ℝ] (X → ℝ) := if isG then localGLinear q ε else localRLinear q ε

theorem localOp_nonzero_old {X : Type*} [PseudoMetricSpace X] (isG : Bool) (q : X)
    {ε : ℝ} (hε : 0 < ε) (u : X → ℝ) (x : X) (hx : localOp isG q ε u x ≠ 0) :
    ∃ y, u y ≠ 0 ∧ dist x y ≤ ε := by
  by_cases hu : u x = 0
  · refine ⟨q, ?_, ?_⟩
    · intro hq
      cases isG <;> simp [localOp, localGLinear, localRLinear, localG, hu, hq] at hx
    · have ha : cutoff q ε x ≠ 0 := by
        intro ha
        cases isG
        · change localR q ε u x ≠ 0 at hx
          simp [localR_eq, ha] at hx
        · change localG q ε u x ≠ 0 at hx
          simp [localG_eq, localR_eq, hu, ha] at hx
      exact (dist_lt_of_cutoff_ne_zero q hε x ha).le
  · exact ⟨x, hu, by simpa using hε.le⟩

theorem localOp_support {X : Type*} [PseudoMetricSpace X] (isG : Bool) (q : X)
    {ε : ℝ} (hε : 0 < ε) (u : X → ℝ) :
    tsupport (localOp isG q ε u) ⊆ Metric.cthickening ε (tsupport u) := by
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  obtain ⟨y, hy, hd⟩ := localOp_nonzero_old isG q hε u x hx
  exact Metric.mem_cthickening_of_dist_le x y ε (tsupport u) (subset_tsupport u hy) hd

theorem localR_support_ball {X : Type*} [PseudoMetricSpace X] (q : X)
    {ε : ℝ} (hε : 0 < ε) (u : X → ℝ) :
    tsupport (localR q ε u) ⊆ Metric.closedBall q ε := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have ha : cutoff q ε x ≠ 0 := by
    intro ha
    have hx' : localR q ε u x ≠ 0 := hx
    simp [localR_eq, ha] at hx'
  exact (dist_lt_of_cutoff_ne_zero q hε x ha).le

theorem localOp_support_bound {X : Type*} [PseudoMetricSpace X] (isG : Bool) (q : X)
    {ε : ℝ} (hε : 0 < ε) (u v : X → ℝ) {K : ℝ≥0} (hv : LipschitzWith K v)
    (a : ℝ) (ha : ∀ x ∈ tsupport u, v x ≤ a) :
    ∀ x ∈ tsupport (localOp isG q ε u), v x ≤ a+ε*K := by
  have hclosed : IsClosed {x | v x ≤ a+ε*K} := isClosed_le hv.continuous continuous_const
  apply closure_minimal _ hclosed
  intro x hx
  obtain ⟨y, hy, hd⟩ := localOp_nonzero_old isG q hε u x hx
  have hb := ha y (subset_tsupport u hy)
  have hd' := hv.dist_le_mul x y
  rw [Real.dist_eq] at hd'
  have hle : v x-v y ≤ K*ε := (le_abs_self _).trans (hd'.trans
    (mul_le_mul_of_nonneg_left hd K.coe_nonneg))
  change v x ≤ a+ε*K
  nlinarith

end

end
end C0Absorption

end OAI
