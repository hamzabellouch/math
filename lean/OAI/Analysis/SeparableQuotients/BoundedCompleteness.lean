import OAI.Analysis.SeparableQuotients.CoordinatePredual

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

@[reducible] local instance dualEGroup4 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace4 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance predualGroup4 : NormedAddCommGroup X₀ := inferInstance
@[reducible] local instance predualSpace4 : NormedSpace ℝ X₀ := inferInstance
@[reducible] local instance dualPredualGroup4 : NormedAddCommGroup (StrongDual ℝ X₀) := inferInstance
@[reducible] local instance dualPredualSpace4 : NormedSpace ℝ (StrongDual ℝ X₀) := inferInstance

/-- Coordinates of a proposed prefix or interval coincide with the fixed g. -/
def IsPiece (g : StrongDual ℝ X₀) (S : Set Γ) (x : E) : Prop :=
  ∀ a, coordinate a x = if a ∈ S then g (coordinate₀ a) else 0

lemma IsPiece.zero_off {g : StrongDual ℝ X₀} {S : Set Γ} {x : E}
    (h : IsPiece g S x) (a : Γ) (ha : a ∉ S) : coordinate a x = 0 := by
  rw [h a, ite_eq_right ha]

lemma IsPiece.projection {g : StrongDual ℝ X₀} {S : Set Γ} {x : E}
    (h : IsPiece g S x) (A : Crop) :
    IsPiece g (S ∩ A.set .mixed) (projection A x) := by
  intro a
  rw [coordinate_projection, h a]
  by_cases ha : a ∈ S <;> by_cases hb : a ∈ A.set .mixed <;> simp [ha, hb]

lemma IsPiece.eval_eq {g : StrongDual ℝ X₀} {S : Set Γ} {x : E}
    (h : IsPiece g S x) (f : Array) (hf : (f.support : Set Γ) ⊆ S) :
    g (norming.rationalPredual f) = norming.evaluateArray x f := by
  apply predual_array_eq_evaluate
  intro a ha
  rw [h a, ite_eq_left (hf ha)]

lemma exists_piece_normer (g : StrongDual ℝ X₀) (A : Crop) (x : E)
    (hx : IsPiece g (A.set .mixed) x) (r : ℝ) (hr : 0 ≤ r) (hxr : r < ‖x‖) :
    ∃ f ∈ Full, (f.support : Set Γ) ⊆ A.set .mixed ∧
      r < g (norming.rationalPredual f) := by
  obtain ⟨f, hf, hfx⟩ := exists_full_normer x r hr hxr
  let f' := restrict (A.set .mixed) f
  have hs : (f'.support : Set Γ) ⊆ A.set .mixed := by
    intro a ha
    by_contra hn
    have hz : f' a = 0 := by simp [f', hn]
    exact Finsupp.mem_support_iff.mp ha hz
  refine ⟨f', full_crop A f hf, hs, ?_⟩
  rw [hx.eval_eq f' hs, evaluateArray_crop_of_zero (A.set .mixed) x hx.zero_off]
  exact hfx

lemma exists_pure_piece_normer (g : StrongDual ℝ X₀) (I : Set Γ)
    (hI : Set.OrdConnected I) (k : ℕ) (x : E)
    (hx : IsPiece g (I ∩ colorSet k) x) (r : ℝ) (hr : 0 ≤ r) (hxr : r < ‖x‖) :
    ∃ f ∈ Pure k, (f.support : Set Γ) ⊆ I ∧
      r < g (norming.rationalPredual f) := by
  have hc : ∀ a, Colors.color a ≠ k → coordinate a x = 0 := by
    intro a ha
    apply hx.zero_off
    simp [colorSet, ha]
  obtain ⟨f, hf, hfx⟩ := exists_pure_normer k x hc r hr hxr
  let f' := restrict I f
  have hf' : f' ∈ Pure k := pure_crop k (Crop.ordinalSet I hI) f hf
  have hs : (f'.support : Set Γ) ⊆ I := by
    intro a ha
    by_contra hn
    exact Finsupp.mem_support_iff.mp ha (by simp [f', hn])
  have hs' : (f'.support : Set Γ) ⊆ I ∩ colorSet k := by
    intro a ha
    refine ⟨hs ha, ?_⟩
    by_contra hn
    exact Finsupp.mem_support_iff.mp ha (pure_vanish k f' hf' a hn)
  refine ⟨f', hf', hs, ?_⟩
  rw [hx.eval_eq f' hs', evaluateArray_crop_of_zero I x]
  · exact hfx
  · intro a ha
    apply hx.zero_off
    simp [ha]

lemma projection_colorsBelow_sum (n : ℕ) (x : E) :
    projection (Crop.colorsBelow n) x = ∑ k ∈ Finset.range n, projection (Crop.oneColor k) x := by
  apply coordinate_ext
  intro a
  simp only [coordinate_projection, Crop.colorsBelow_set, Set.mem_ofPred_eq, map_sum,
    Crop.oneColor_set, colorSet]
  simp [eq_comm]

lemma tendsto_low_colors {v : ℕ → E}
    (h : ∀ k, Tendsto (fun i => projection (Crop.oneColor k) (v i)) atTop (𝓝 0)) (n : ℕ) :
    Tendsto (fun i => projection (Crop.colorsBelow n) (v i)) atTop (𝓝 0) := by
  simpa only [projection_colorsBelow_sum, Finset.sum_const_zero] using
    (tendsto_finsetSum (Finset.range n) fun k _ => h k)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.OrderedCauchy
open Filter
open scoped Classical
universe u v
variable {ι : Type u} [LinearOrder ι] [Nonempty ι]
variable {Z : Type v} [PseudoMetricSpace Z]

/-- Failure of the Cauchy condition on a linearly ordered directed set yields
successive separated pairs. This applies equally to countable ordinal prefixes
and to an uncountable limit; no countable cofinality is assumed. -/
lemma separated_pairs_of_not_cauchy (u : ι → Z) (hu : ¬ CauchySeq u) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ a b : ℕ → ι,
      (∀ i, a i < b i) ∧ (∀ i j, i < j → b i ≤ a j) ∧
      ∀ i, ε ≤ dist (u (b i)) (u (a i)) := by
  rw [Metric.cauchySeq_iff] at hu
  push Not at hu
  obtain ⟨ε, hε, hu⟩ := hu
  have hex : ∀ N : ι, ∃ a b : ι, N ≤ a ∧ a < b ∧ ε ≤ dist (u b) (u a) := by
    intro N
    obtain ⟨m, hm, n, hn, hmn⟩ := hu N
    by_cases h : m ≤ n
    · refine ⟨m, n, hm, lt_of_le_of_ne h ?_, ?_⟩
      · intro heq
        rw [heq, dist_self] at hmn
        exact (not_le_of_gt hε) hmn
      · simpa only [dist_comm] using hmn
    · exact ⟨n, m, hn, lt_of_not_ge h, hmn⟩
  choose a b hab hlt hdist using hex
  let p : ℕ → ι × ι := fun n => Nat.rec
    (a (Classical.arbitrary ι), b (Classical.arbitrary ι))
    (fun _ prev => (a prev.2, b prev.2)) n
  have hp0 : ∀ n, (p n).1 < (p n).2 := by
    intro n
    cases n with
    | zero => exact hlt _
    | succ n => exact hlt _
  have hp1 : ∀ n, (p n).2 ≤ (p (n+1)).1 := fun n => hab _
  have hp2 : Monotone (fun n => (p n).2) := monotone_nat_of_le_succ fun n =>
    (hp1 n).trans (hp0 (n+1)).le
  refine ⟨ε, hε, (fun n => (p n).1), (fun n => (p n).2), hp0, ?_, ?_⟩
  · intro i j hij
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (hp2 (by omega : i ≤ l)).trans (hp1 l)
  · intro n
    cases n <;> exact hdist _

end SeparableQuotient.OrderedCauchy

namespace SeparableQuotient.OrderedCauchy
open Filter
open scoped Classical Topology
universe u
variable {Z : Type u} [SeminormedAddCommGroup Z]

lemma norm_large_subsequence (v : ℕ → Z) (hv : ¬ Tendsto v atTop (𝓝 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ε ≤ ‖v (φ i)‖ := by
  rw [Metric.tendsto_atTop] at hv
  push Not at hv
  obtain ⟨ε, hε, hv⟩ := hv
  obtain ⟨φ, hφ, hlarge⟩ := Nat.exists_strictMono_subsequence (P := fun i => ε ≤ ‖v i‖) (by
    intro N
    obtain ⟨n, hn, hdist⟩ := hv (N+1)
    exact ⟨n, by omega, by simpa only [dist_zero_right] using hdist⟩)
  exact ⟨ε, hε, φ, hφ, hlarge⟩

end SeparableQuotient.OrderedCauchy

namespace SeparableQuotient.Norming
open scoped Classical

def Crop.colorWindow (lo hi : ℕ) : Crop := Crop.colorSet (Set.Ico lo hi) Set.ordConnected_Ico

@[simp] lemma Crop.colorWindow_set (lo hi : ℕ) :
    (Crop.colorWindow lo hi).set .mixed = {a | lo ≤ Colors.color a ∧ Colors.color a < hi} := by
  ext a
  simp [Crop.colorWindow, Crop.colorSet, Crop.set]

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

@[reducible] local instance dualEGroup5 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace5 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance predualGroup5 : NormedAddCommGroup X₀ := inferInstance
@[reducible] local instance predualSpace5 : NormedSpace ℝ X₀ := inferInstance
@[reducible] local instance dualPredualGroup5 : NormedAddCommGroup (StrongDual ℝ X₀) := inferInstance
@[reducible] local instance dualPredualSpace5 : NormedSpace ℝ (StrongDual ℝ X₀) := inferInstance

lemma successive_pieces_color_tendsto (g : StrongDual ℝ X₀) (I : ℕ → Set Γ)
    (hI : ∀ i, (I i).OrdConnected) (v : ℕ → E) (hv : ∀ i, IsPiece g (I i) (v i))
    (hord : ∀ i j, i < j → ∀ a ∈ I i, ∀ b ∈ I j, a < b) (k : ℕ) :
    Tendsto (fun i => projection (Crop.oneColor k) (v i)) atTop (𝓝 0) := by
  by_contra hn
  obtain ⟨ε, hε, φ, hφ, hlarge⟩ := OrderedCauchy.norm_large_subsequence _ hn
  have hp : ∀ i, IsPiece g (I (φ i) ∩ colorSet k) (projection (Crop.oneColor k) (v (φ i))) := by
    intro i
    simpa only [Crop.oneColor_set] using (hv (φ i)).projection (Crop.oneColor k)
  have hex : ∀ i, ∃ f ∈ Pure k, (f.support : Set Γ) ⊆ I (φ i) ∧
      ε/2 < g (norming.rationalPredual f) := by
    intro i
    exact exists_pure_piece_normer g _ (hI _) k _ (hp i) _ (by positivity)
      ((half_lt_self hε).trans_le (hlarge i))
  choose f hf hs he using hex
  apply no_successive_positive_normers g (.pure k) f hf _ (ε/2) (by positivity) (fun i => (he i).le)
  intro i j hij a ha b hb
  exact ⟨hord (φ i) (φ j) (hφ hij) a (hs i ha) b (hs j hb), by simp⟩

lemma projection_colorWindow_eq (lo hi : ℕ) (h : lo ≤ hi) (x : E) :
    projection (Crop.colorWindow lo hi) x =
      projection (Crop.colorsBelow hi) x - projection (Crop.colorsBelow lo) x := by
  apply coordinate_ext
  intro a
  simp only [map_sub, coordinate_projection, Crop.colorWindow_set, Crop.colorsBelow_set,
    Set.mem_ofPred_eq]
  by_cases hl : Colors.color a < lo
  · have hh : Colors.color a < hi := hl.trans_le h
    simp [hl, hh, not_le_of_gt hl]
  · by_cases hh : Colors.color a < hi <;> simp [hl, hh, le_of_not_gt hl]

lemma exists_large_colorWindow (v : ℕ → E) (δ : ℝ) (hδ : 0 < δ)
    (hv : ∀ i, δ ≤ ‖v i‖)
    (hc : ∀ k, Tendsto (fun i => projection (Crop.oneColor k) (v i)) atTop (𝓝 0))
    (lo N : ℕ) : ∃ n hi : ℕ, N < n ∧ lo < hi ∧
      δ/2 < ‖projection (Crop.colorWindow lo hi) (v n)‖ := by
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp (tendsto_low_colors hc lo) (δ/4) (by positivity)
  let n := max (N+1) N₀
  have hlow : ‖projection (Crop.colorsBelow lo) (v n)‖ < δ/4 := by
    simpa only [dist_zero_right] using hN₀ n (le_max_right _ _)
  obtain ⟨H, hH⟩ := Metric.tendsto_atTop.mp (tendsto_colorsBelow (v n)) (δ/4) (by positivity)
  let hi := max (lo+1) H
  have hhigh : ‖v n - projection (Crop.colorsBelow hi) (v n)‖ < δ/4 := by
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using hH hi (le_max_right _ _)
  have hlohi : lo < hi := lt_of_lt_of_le (Nat.lt_succ_self lo) (le_max_left _ _)
  refine ⟨n, hi, lt_of_lt_of_le (Nat.lt_succ_self N) (le_max_left _ _), hlohi, ?_⟩
  rw [projection_colorWindow_eq lo hi hlohi.le]
  have hb : ‖v n‖ ≤ ‖v n - projection (Crop.colorsBelow hi) (v n)‖ +
      ‖projection (Crop.colorsBelow hi) (v n) - projection (Crop.colorsBelow lo) (v n)‖ +
      ‖projection (Crop.colorsBelow lo) (v n)‖ := by
    calc
      _ = ‖(v n - projection (Crop.colorsBelow hi) (v n)) +
          (projection (Crop.colorsBelow hi) (v n) - projection (Crop.colorsBelow lo) (v n)) +
          projection (Crop.colorsBelow lo) (v n)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have := hv n
  linarith

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

@[reducible] local instance dualEGroup6 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace6 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance predualGroup6 : NormedAddCommGroup X₀ := inferInstance
@[reducible] local instance predualSpace6 : NormedSpace ℝ X₀ := inferInstance
@[reducible] local instance dualPredualGroup6 : NormedAddCommGroup (StrongDual ℝ X₀) := inferInstance
@[reducible] local instance dualPredualSpace6 : NormedSpace ℝ (StrongDual ℝ X₀) := inferInstance

/-- The limit-step contradiction for vector pieces, with normers cropped after norm approximation. -/
lemma no_large_successive_pieces (g : StrongDual ℝ X₀) (I : ℕ → Set Γ)
    (hI : ∀ i, (I i).OrdConnected) (v : ℕ → E) (hv : ∀ i, IsPiece g (I i) (v i))
    (hord : ∀ i j, i < j → ∀ a ∈ I i, ∀ b ∈ I j, a < b)
    (δ : ℝ) (hδ : 0 < δ) (hlarge : ∀ i, δ ≤ ‖v i‖) : False := by
  have hc := successive_pieces_color_tendsto g I hI v hv hord
  have hex := exists_large_colorWindow v δ hδ hlarge hc
  choose n h hn hh hw using hex
  let p : ℕ → ℕ × ℕ := fun i => Nat.rec (0, 0)
    (fun _ prev => (n prev.2 prev.1, h prev.2 prev.1)) i
  have hp1 : StrictMono (fun i => (p i).1) := strictMono_nat_of_lt_succ fun i => hn _ _
  have hp2 : StrictMono (fun i => (p i).2) := strictMono_nat_of_lt_succ fun i => hh _ _
  let idx : ℕ → ℕ := fun i => (p (i+1)).1
  have hidx : StrictMono idx := fun i j hij => hp1 (Nat.add_lt_add_right hij 1)
  let A : ℕ → Crop := fun i => {
    ordinal := I (idx i)
    ordinal_convex := hI (idx i)
    colors := Set.Ico (p i).2 (p (i+1)).2
    colors_convex := Set.ordConnected_Ico }
  let w : ℕ → E := fun i => projection (Crop.colorWindow (p i).2 (p (i+1)).2) (v (idx i))
  have hp : ∀ i, IsPiece g ((A i).set .mixed) (w i) := by
    intro i
    simpa only [w, A, Crop.set, Crop.colorWindow, Crop.colorSet, Set.univ_inter] using
      (hv (idx i)).projection (Crop.colorWindow (p i).2 (p (i+1)).2)
  have hl : ∀ i, δ/2 < ‖w i‖ := fun i => hw (p i).2 (p i).1
  have hex' : ∀ i, ∃ f ∈ Full, (f.support : Set Γ) ⊆ (A i).set .mixed ∧
      δ/4 < g (norming.rationalPredual f) := by
    intro i
    exact exists_piece_normer g (A i) (w i) (hp i) (δ/4) (by positivity)
      (lt_trans (by linarith) (hl i))
  choose f hf hs he using hex'
  apply no_successive_positive_normers g .mixed f hf _ (δ/4) (by positivity) (fun i => (he i).le)
  intro i j hij a ha b hb
  have ha' := hs i ha
  have hb' := hs j hb
  change a ∈ I (idx i) ∧ (p i).2 ≤ Colors.color a ∧ Colors.color a < (p (i+1)).2 at ha'
  change b ∈ I (idx j) ∧ (p j).2 ≤ Colors.color b ∧ Colors.color b < (p (j+1)).2 at hb'
  refine ⟨hord (idx i) (idx j) (hidx hij) a ha'.1 b hb'.1, fun _ => ?_⟩
  exact (ha'.2.2.trans_le (hp2.monotone (by omega : i+1 ≤ j))).trans_le hb'.2.1

lemma IsPiece.sub_Iic {g : StrongDual ℝ X₀} {a b : Γ} {x y : E}
    (hx : IsPiece g (Set.Iic a) x) (hy : IsPiece g (Set.Iic b) y) (hab : a ≤ b) :
    IsPiece g (Set.Ioc a b) (y-x) := by
  intro c
  rw [map_sub, hx c, hy c]
  by_cases hca : c ≤ a
  · have hcb : c ≤ b := hca.trans hab
    simp [hca, hcb, not_lt_of_ge hca]
  · by_cases hcb : c ≤ b <;> simp [hca, hcb, lt_of_not_ge hca]

/-- The ordinal-prefix net is Cauchy at every limit. It also works at successor
limits and at ω₁, without any cofinality assumption. -/
lemma prefixes_cauchy {ι : Type*} [LinearOrder ι] [Nonempty ι]
    (g : StrongDual ℝ X₀) (a : ι ↪o Γ) (v : ι → E)
    (hv : ∀ i, IsPiece g (Set.Iic (a i)) (v i)) : CauchySeq v := by
  by_contra hn
  obtain ⟨δ, hδ, b, c, hbc, hs, hdist⟩ := OrderedCauchy.separated_pairs_of_not_cauchy v hn
  let I : ℕ → Set Γ := fun i => Set.Ioc (a (b i)) (a (c i))
  let w : ℕ → E := fun i => v (c i) - v (b i)
  have hp : ∀ i, IsPiece g (I i) (w i) := fun i =>
    (hv (b i)).sub_Iic (hv (c i)) (a.monotone (hbc i).le)
  apply no_large_successive_pieces g I (fun _ => Set.ordConnected_Ioc) w hp _ δ hδ
  · intro i
    simpa only [w, dist_eq_norm] using hdist i
  · intro i j hij α hα β hβ
    exact (hα.2.trans (a.monotone (hs i j hij))).trans_lt hβ.1

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

@[reducible] local instance dualEGroup7 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace7 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance predualGroup7 : NormedAddCommGroup X₀ := inferInstance
@[reducible] local instance predualSpace7 : NormedSpace ℝ X₀ := inferInstance
@[reducible] local instance dualPredualGroup7 : NormedAddCommGroup (StrongDual ℝ X₀) := inferInstance
@[reducible] local instance dualPredualSpace7 : NormedSpace ℝ (StrongDual ℝ X₀) := inferInstance

lemma coordinate_e (a b : Γ) : coordinate a (e b) = if a = b then 1 else 0 := by
  simp [coordinate, e, NormingSet.generator, Finsupp.single_apply, eq_comm]

lemma IsPiece.append {g : StrongDual ℝ X₀} {β : Γ} {x : E}
    (hx : IsPiece g (Set.Iio β) x) :
    IsPiece g (Set.Iic β) (x + g (coordinate₀ β) • e β) := by
  intro a
  rw [map_add, map_smul, hx a, coordinate_e]
  by_cases ha : a = β
  · subst a
    simp
  · by_cases hab : a < β
    · simp [ha, hab, hab.le]
    · have hba : ¬ a ≤ β := fun h => hab (lt_of_le_of_ne h ha)
      simp [ha, hab, hba]

/-- Every strict prefix is the limit of its already constructed inclusive
prefixes. This handles empty, successor, and limit initial segments uniformly. -/
lemma exists_strict_prefix (g : StrongDual ℝ X₀) (β : Γ)
    (h : ∀ a : Γ, a < β → ∃ x : E, IsPiece g (Set.Iic a) x) :
    ∃ x : E, IsPiece g (Set.Iio β) x := by
  by_cases hn : Nonempty (Set.Iio β)
  · let := hn
    choose v hv using (fun a : Set.Iio β => h a.val a.property)
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete
      (prefixes_cauchy g (OrderEmbedding.subtype (· ∈ Set.Iio β)) v hv)
    refine ⟨x, fun a => ?_⟩
    have ht := (coordinate a).continuous.tendsto x |>.comp hx
    simp only [Set.mem_Iio]
    by_cases ha : a < β
    · rw [ite_eq_left ha]
      have he : ∀ᶠ i : Set.Iio β in atTop, coordinate a (v i) = g (coordinate₀ a) := by
        filter_upwards [eventually_ge_atTop (⟨a, ha⟩ : Set.Iio β)] with i hi
        change a ≤ (i : Γ) at hi
        rw [hv i a, Set.mem_Iic, ite_eq_left hi]
      exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (he.mono fun _ h => h.symm))
    · rw [ite_eq_right ha]
      have he : ∀ i : Set.Iio β, coordinate a (v i) = 0 := by
        intro i
        rw [hv i a, Set.mem_Iic, ite_eq_right (fun hai => ha (lt_of_le_of_lt hai i.property))]
      exact tendsto_nhds_unique ht
        (tendsto_const_nhds.congr' (Filter.Eventually.of_forall
          (fun i : Set.Iio β => (he i).symm)))
  · refine ⟨0, fun a => ?_⟩
    have ha : ¬ a < β := fun ha => hn ⟨⟨a, ha⟩⟩
    simp [ha]

lemma exists_prefix (g : StrongDual ℝ X₀) (β : Γ) :
    ∃ x : E, IsPiece g (Set.Iic β) x := by
  refine (wellFounded_lt : WellFounded ((· < ·) : Γ → Γ → Prop)).induction (C := fun β => ∃ x : E, IsPiece g (Set.Iic β) x) β ?_
  intro β ih
  obtain ⟨x, hx⟩ := exists_strict_prefix g β ih
  exact ⟨_, hx.append⟩

lemma exists_all_coordinates (g : StrongDual ℝ X₀) :
    ∃ x : E, ∀ a, coordinate a x = g (coordinate₀ a) := by
  choose v hv using (fun a => exists_prefix g a)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete
    (prefixes_cauchy g ((OrderIso.refl Γ).toOrderEmbedding) v hv)
  refine ⟨x, fun a => ?_⟩
  have ht := (coordinate a).continuous.tendsto x |>.comp hx
  have he : ∀ᶠ i : Γ in atTop, coordinate a (v i) = g (coordinate₀ a) := by
    filter_upwards [eventually_ge_atTop a] with i hi
    rw [hv i a, Set.mem_Iic, ite_eq_left hi]
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (he.mono fun _ h => h.symm))

lemma dense_span_coordinate₀ : Dense (Submodule.span ℝ (Set.range coordinate₀) : Set X₀) := by
  have him : Subtype.val '' (Submodule.span ℝ (Set.range coordinate₀) : Set X₀) =
      (Submodule.span ℝ (Set.range coordinate) : Set (StrongDual ℝ E)) := by
    change ((Submodule.span ℝ (Set.range coordinate₀)).map X₀.subtype : Set (StrongDual ℝ E)) = _
    rw [Submodule.map_span]
    congr 2
    rw [← Set.range_comp]
    rfl
  intro x
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, him]
  exact x.property

lemma predual_dual_ext (g h : StrongDual ℝ X₀)
    (he : ∀ a, g (coordinate₀ a) = h (coordinate₀ a)) : g = h := by
  apply ContinuousLinearMap.ext_on dense_span_coordinate₀
  rintro _ ⟨a, rfl⟩
  exact he a

/-- Evaluation onto the dual of the coordinate predual is surjective. -/
lemma evaluation_surjective : Function.Surjective norming.evaluation := by
  intro g
  obtain ⟨x, hx⟩ := exists_all_coordinates g
  refine ⟨x, predual_dual_ext _ _ (fun a => ?_)⟩
  exact hx a

def predualIsometry : E ≃ₗᵢ[ℝ] StrongDual ℝ X₀ :=
  LinearIsometryEquiv.ofSurjective norming.evaluationIsometry evaluation_surjective

end SeparableQuotient.ActualSpace

end

end OAI
