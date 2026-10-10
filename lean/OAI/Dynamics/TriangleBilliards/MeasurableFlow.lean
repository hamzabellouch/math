import OAI.Dynamics.TriangleBilliards.CollisionEscape

namespace OAI

universe uAlpha

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
namespace TriangularBilliards
open Filter
open scoped Topology

/-! Borel realization of full chains.  Countable collision data, rather than
an uncountable trajectory selector, permit a standard-Borel inverse. -/
namespace Triangle

lemma side_coords_nonneg (Q : Triangle) {x : ℂ} {i : Fin 3}
    (hx : x ∈ Q.side i) (k : Fin 3) : 0 ≤ Q.basis.coord k x := by
  rw [side, openSegment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  change 0 ≤ Q.basis.coord k (AffineMap.lineMap (Q.basis i) (Q.basis (i + 1)) t)
  rw [AffineMap.apply_lineMap, Q.basis.coord_apply, Q.basis.coord_apply,
    AffineMap.lineMap_apply_module]
  split_ifs <;> simp only [smul_eq_mul] <;> nlinarith [ht.1, ht.2]

lemma measurableSet_side (Q : Triangle) (i : Fin 3) : MeasurableSet (Q.side i) := by
  rw [side, openSegment_eq_image_lineMap]
  have hne : Q.vertex i ≠ Q.vertex (i + 1) :=
    Q.nondegenerate.injective.ne (by decide +revert)
  have hc : Continuous (fun t : ℝ => AffineMap.lineMap (Q.vertex i) (Q.vertex (i + 1)) t) := by
    fun_prop
  exact (hc.measurableEmbedding (AffineMap.lineMap_injective ℝ hne)).measurableSet_image.mpr
    measurableSet_Ioo

lemma inside_of_midpoint (Q : Triangle) {x v : ℂ} {a b : ℝ} {i j : Fin 3}
    (ha : x ∈ Q.side i) (hb : x + (b - a) • v ∈ Q.side j)
    (hm : x + ((a + b) / 2 - a) • v ∈ Q.table)
    {t : ℝ} (hat : a < t) (htb : t < b) : x + (t - a) • v ∈ Q.table := by
  rw [Q.table_iff_coords] at hm ⊢
  intro k
  have h0 := Q.side_coords_nonneg ha k
  have h1 := Q.side_coords_nonneg hb k
  have hmid := hm k
  rw [Q.coord_shift] at h1 hmid ⊢
  by_cases hd : 0 ≤ Q.slope k v
  · by_cases hz : Q.slope k v = 0
    · simp only [hz, mul_zero, add_zero] at hmid ⊢
      exact hmid
    · exact add_pos_of_nonneg_of_pos h0 (mul_pos (sub_pos.mpr hat) (lt_of_le_of_ne hd (Ne.symm hz)))
  · have hp : 0 < (b - t) * (-Q.slope k v) :=
      mul_pos (sub_pos.mpr htb) (neg_pos.mpr (lt_of_not_ge hd))
    nlinarith

end Triangle

abbrev ChainData := (ℤ → ℝ) × (ℤ → ℂ) × (ℤ → Circle) × (ℤ → Fin 3)

namespace ChainData

def time (c : ChainData) := c.1
def point (c : ChainData) := c.2.1
def direction (c : ChainData) := c.2.2.1
def wall (c : ChainData) := c.2.2.2

/-- Every predicate is a countable combination of Borel coordinate predicates.
Midpoint membership entails the entire open-flight condition by convexity. -/
def Valid (Q : Triangle) (z : Phase) (c : ChainData) : Prop :=
  (∀ n : ℤ, c.time n < c.time (n + 1)) ∧
  (∀ k : ℤ, ∃ n : ℤ, c.time n < k) ∧
  (∀ k : ℤ, ∃ n : ℤ, (k : ℝ) < c.time n) ∧
  c.time 0 < 0 ∧ 0 < c.time 1 ∧
  (∀ n : ℤ, c.point n ∈ Q.side (c.wall n)) ∧
  (∀ n : ℤ, c.point (n + 1) = c.point n +
    (c.time (n + 1) - c.time n) • (c.direction n : ℂ)) ∧
  (∀ n : ℤ, c.point n + ((c.time n + c.time (n + 1)) / 2 - c.time n) •
    (c.direction n : ℂ) ∈ Q.table) ∧
  z.1 = c.point 0 + (-c.time 0) • (c.direction 0 : ℂ) ∧
  z.2 = c.direction 0 ∧
  (∀ n : ℤ, (c.direction n : ℂ) = reflect (Q.tangent (c.wall n))
    (c.direction (n - 1) : ℂ))

def toChain {Q : Triangle} {z : Phase} {c : ChainData} (h : c.Valid Q z) : FlightChain Q z where
  time := c.time
  point := c.point
  direction := c.direction
  wall := c.wall
  increasing := strictMono_int_of_lt_succ h.1
  unbounded_below := fun t => by
    obtain ⟨k, hk⟩ := exists_int_lt t
    obtain ⟨n, hn⟩ := h.2.1 k
    exact ⟨n, hn.trans hk⟩
  unbounded_above := fun t => by
    obtain ⟨k, hk⟩ := exists_int_gt t
    obtain ⟨n, hn⟩ := h.2.2.1 k
    exact ⟨n, hk.trans hn⟩
  zero_before := h.2.2.2.1
  zero_after := h.2.2.2.2.1
  on_side := h.2.2.2.2.2.1
  flight := h.2.2.2.2.2.2.1
  inside := fun n t ht ht' => by
    apply Q.inside_of_midpoint (j := c.wall (n + 1))
      (h.2.2.2.2.2.1 n) _ (h.2.2.2.2.2.2.2.1 n) ht ht'
    rw [← h.2.2.2.2.2.2.1 n]
    exact h.2.2.2.2.2.1 (n + 1)
  start_point := h.2.2.2.2.2.2.2.2.1
  start_direction := h.2.2.2.2.2.2.2.2.2.1
  specular := h.2.2.2.2.2.2.2.2.2.2

end ChainData

namespace FlightChain

def data {Q : Triangle} {z : Phase} (c : FlightChain Q z) : ChainData :=
  (c.time, c.point, c.direction, c.wall)

lemma data_valid {Q : Triangle} {z : Phase} (c : FlightChain Q z) : c.data.Valid Q z := by
  refine ⟨fun n => c.increasing (by omega), fun k => c.unbounded_below k,
    fun k => c.unbounded_above k, c.zero_before, c.zero_after, c.on_side,
    c.flight, ?_, c.start_point, c.start_direction, c.specular⟩
  intro n
  have h := c.increasing (show n < n + 1 by omega)
  exact c.inside n ((c.time n + c.time (n + 1)) / 2) (by linarith) (by linarith)

end FlightChain

namespace ChainData

@[fun_prop] lemma continuous_time (n : ℤ) : Continuous (fun c : ChainData => c.time n) := by
  unfold time
  fun_prop

@[fun_prop] lemma continuous_point (n : ℤ) : Continuous (fun c : ChainData => c.point n) := by
  unfold point
  fun_prop

@[fun_prop] lemma continuous_direction (n : ℤ) : Continuous (fun c : ChainData => c.direction n) := by
  unfold direction
  fun_prop

@[fun_prop] lemma continuous_wall (n : ℤ) : Continuous (fun c : ChainData => c.wall n) := by
  unfold wall
  fun_prop

lemma measurableSet_side_mem {α : Type uAlpha} [MeasurableSpace α] (Q : Triangle)
    {p : α → ℂ} {w : α → Fin 3} (hp : Measurable p) (hw : Measurable w) :
    MeasurableSet {a | p a ∈ Q.side (w a)} := by
  have he : {a | p a ∈ Q.side (w a)} =
      ⋃ i : Fin 3, {a | w a = i} ∩ p ⁻¹' Q.side i := by
    ext a
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage]
    exact ⟨fun h => ⟨w a, rfl, h⟩, fun ⟨i, hi, hs⟩ => hi ▸ hs⟩
  rw [he]
  exact MeasurableSet.iUnion fun i =>
    (measurableSet_eq_fun hw measurable_const).inter ((Q.measurableSet_side i).preimage hp)

lemma measurableSet_valid (Q : Triangle) :
    MeasurableSet {a : Phase × ChainData | a.2.Valid Q a.1} := by
  have ht (n : ℤ) : Measurable (fun a : Phase × ChainData => a.2.time n) :=
    (continuous_time n).measurable.comp measurable_snd
  have hp (n : ℤ) : Measurable (fun a : Phase × ChainData => a.2.point n) :=
    (continuous_point n).measurable.comp measurable_snd
  have hd (n : ℤ) : Measurable (fun a : Phase × ChainData => a.2.direction n) :=
    (continuous_direction n).measurable.comp measurable_snd
  have hv (n : ℤ) : Measurable (fun a : Phase × ChainData => (a.2.direction n : ℂ)) := by
    exact (show Continuous (fun z : Circle => (z : ℂ)) by fun_prop).measurable.comp (hd n)
  have hw (n : ℤ) : Measurable (fun a : Phase × ChainData => a.2.wall n) :=
    (continuous_wall n).measurable.comp measurable_snd
  simp only [Valid, ofPred_and, ofPred_forall, ofPred_exists]
  refine (MeasurableSet.iInter fun n => measurableSet_lt (ht n) (ht (n + 1))).inter ?_
  refine (MeasurableSet.iInter fun k : ℤ => MeasurableSet.iUnion fun n =>
    measurableSet_lt (ht n) measurable_const).inter ?_
  refine (MeasurableSet.iInter fun k : ℤ => MeasurableSet.iUnion fun n =>
    measurableSet_lt measurable_const (ht n)).inter ?_
  refine (measurableSet_lt (ht 0) measurable_const).inter ?_
  refine (measurableSet_lt measurable_const (ht 1)).inter ?_
  refine (MeasurableSet.iInter fun n => measurableSet_side_mem Q (hp n) (hw n)).inter ?_
  refine (MeasurableSet.iInter fun n => measurableSet_eq_fun (hp (n + 1))
    ((hp n).add (((ht (n + 1)).sub (ht n)).smul (hv n)))).inter ?_
  refine (MeasurableSet.iInter fun n => Q.measurableSet_table.preimage
    ((hp n).add (((((ht n).add (ht (n + 1))).div_const 2).sub (ht n)).smul (hv n)))).inter ?_
  refine (measurableSet_eq_fun (measurable_fst.comp measurable_fst)
    ((hp 0).add ((ht 0).neg.smul (hv 0)))).inter ?_
  refine (measurableSet_eq_fun (measurable_snd.comp measurable_fst) (hd 0)).inter ?_
  apply MeasurableSet.iInter
  intro n
  have he : Measurable (fun a : Phase × ChainData => Q.tangent (a.2.wall n)) :=
    (measurable_of_countable Q.tangent).comp (hw n)
  exact measurableSet_eq_fun (hv n) ((he.div (Complex.continuous_conj.measurable.comp he)).mul
    (Complex.continuous_conj.measurable.comp (hv (n - 1))))

end ChainData

/-- Standard-Borel coding of the exact complete trajectories. -/
abbrev CodedChain (Q : Triangle) := {a : Phase × ChainData // a.2.Valid Q a.1}

namespace CodedChain

instance standardBorel (Q : Triangle) : StandardBorelSpace (CodedChain Q) :=
  (ChainData.measurableSet_valid Q).standardBorel

def initial {Q : Triangle} (c : CodedChain Q) : Phase := c.val.1

def chain {Q : Triangle} (c : CodedChain Q) : FlightChain Q c.initial := ChainData.toChain c.property

instance nonempty (Q : Triangle) : Nonempty (CodedChain Q) := by
  obtain ⟨z, ⟨c⟩⟩ := (ae_exists_chain Q).exists
  exact ⟨⟨(z, c.data), c.data_valid⟩⟩

lemma initial_injective (Q : Triangle) : Function.Injective (initial (Q := Q)) := by
  rintro ⟨⟨z, c⟩, hc⟩ ⟨⟨w, d⟩, hd⟩ h
  change z = w at h
  subst w
  have he := congrArg FlightChain.data (FlightChain.unique (ChainData.toChain hc) (ChainData.toChain hd))
  apply Subtype.ext
  change c = d at he
  exact congrArg (fun x : ChainData => (z, x)) he

lemma initial_embedding (Q : Triangle) : MeasurableEmbedding (initial (Q := Q)) :=
  (measurable_fst.comp measurable_subtype_coe).measurableEmbedding (initial_injective Q)

lemma range_initial (Q : Triangle) :
    range (initial (Q := Q)) = {z | Nonempty (FlightChain Q z)} := by
  ext z
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.chain⟩
  · rintro ⟨c⟩
    exact ⟨⟨(z, c.data), c.data_valid⟩, rfl⟩

lemma measurableSet_regular (Q : Triangle) : MeasurableSet {z | Nonempty (FlightChain Q z)} := by
  rw [← range_initial]
  exact (initial_embedding Q).measurableSet_range

/-- The inverse is Borel by Lusin--Souslin, not by choice of arbitrary
unmeasurable representatives. It agrees with every exact chain at its initial state. -/
def fromPhase (Q : Triangle) : Phase → CodedChain Q := (initial_embedding Q).invFun

@[fun_prop] lemma measurable_fromPhase (Q : Triangle) : Measurable (fromPhase Q) :=
  (initial_embedding Q).measurable_invFun

lemma fromPhase_initial (Q : Triangle) (c : CodedChain Q) : fromPhase Q c.initial = c :=
  (initial_embedding Q).leftInverse_invFun c

def index {Q : Triangle} (a : CodedChain Q × ℝ) : ℤ :=
  Classical.choose (a.1.chain.exists_flight a.2)

lemma index_spec {Q : Triangle} (a : CodedChain Q × ℝ) :
    a.1.chain.time (index a) ≤ a.2 ∧ a.2 < a.1.chain.time (index a + 1) :=
  Classical.choose_spec (a.1.chain.exists_flight a.2)

lemma index_eq_iff {Q : Triangle} (a : CodedChain Q × ℝ) (n : ℤ) :
    index a = n ↔ a.1.chain.time n ≤ a.2 ∧ a.2 < a.1.chain.time (n + 1) := by
  constructor
  · rintro rfl
    exact index_spec a
  · intro h
    exact a.1.chain.flight_index_unique (index_spec a) h

@[fun_prop] lemma measurable_time (Q : Triangle) (n : ℤ) :
    Measurable (fun c : CodedChain Q => c.chain.time n) :=
  (ChainData.continuous_time n).measurable.comp (measurable_snd.comp measurable_subtype_coe)

@[fun_prop] lemma measurable_point (Q : Triangle) (n : ℤ) :
    Measurable (fun c : CodedChain Q => c.chain.point n) :=
  (ChainData.continuous_point n).measurable.comp (measurable_snd.comp measurable_subtype_coe)

@[fun_prop] lemma measurable_direction (Q : Triangle) (n : ℤ) :
    Measurable (fun c : CodedChain Q => c.chain.direction n) :=
  (ChainData.continuous_direction n).measurable.comp (measurable_snd.comp measurable_subtype_coe)

@[fun_prop] lemma measurable_index (Q : Triangle) : Measurable (index (Q := Q)) := by
  apply measurable_to_countable
  intro a
  have he : index ⁻¹' {index a} =
      {b : CodedChain Q × ℝ | b.1.chain.time (index a) ≤ b.2} ∩
      {b : CodedChain Q × ℝ | b.2 < b.1.chain.time (index a + 1)} := by
    ext b
    exact index_eq_iff b (index a)
  rw [he]
  exact (measurableSet_le ((measurable_time Q _).comp measurable_fst) measurable_snd).inter
    (measurableSet_lt measurable_snd ((measurable_time Q _).comp measurable_fst))

@[fun_prop] lemma measurable_at (Q : Triangle) :
    Measurable (fun a : CodedChain Q × ℝ => a.1.chain.at a.2) := by
  have hf (n : ℤ) : Measurable (fun a : CodedChain Q × ℝ =>
      (a.1.chain.point n + (a.2 - a.1.chain.time n) • (a.1.chain.direction n : ℂ),
        a.1.chain.direction n)) := by
    have hv : Measurable (fun a : CodedChain Q × ℝ => (a.1.chain.direction n : ℂ)) :=
      (show Continuous (fun v : Circle => (v : ℂ)) by fun_prop).measurable.comp
        ((measurable_direction Q n).comp measurable_fst)
    exact (((measurable_point Q n).comp measurable_fst).add
      ((measurable_snd.sub ((measurable_time Q n).comp measurable_fst)).smul hv)).prodMk
        ((measurable_direction Q n).comp measurable_fst)
  have heval : Measurable (fun b : (CodedChain Q × ℝ) × ℤ =>
      (b.1.1.chain.point b.2 + (b.1.2 - b.1.1.chain.time b.2) •
        (b.1.1.chain.direction b.2 : ℂ), b.1.1.chain.direction b.2)) :=
    measurable_from_prod_countable_left hf
  convert heval.comp (measurable_id.prodMk (measurable_index Q)) using 1
  funext a
  exact a.1.chain.at_of_flight (index_spec a)

lemma fromPhase_at {Q : Triangle} {z : Phase} (c : FlightChain Q z) (t : ℝ) :
    (fromPhase Q z).chain.at t = c.at t := by
  let d : CodedChain Q := ⟨(z, c.data), c.data_valid⟩
  have hd : fromPhase Q z = d := fromPhase_initial Q d
  rw [hd]
  have hc : d.chain = c := FlightChain.unique _ _
  exact congrArg (fun e : FlightChain Q z => e.at t) hc

end CodedChain

/-- Joint Borel measurability of the actual chosen billiard flow, obtained
from the unique exact chain, including the singular-set identity convention. -/
lemma measurable_billiardFlow (Q : Triangle) :
    Measurable (fun a : ℝ × Phase => billiardFlow Q a.1 a.2) := by
  classical
  have hm : Measurable (fun a : ℝ × Phase =>
      (CodedChain.fromPhase Q a.2).chain.at a.1) :=
    (CodedChain.measurable_at Q).comp
      (((CodedChain.measurable_fromPhase Q).comp measurable_snd).prodMk measurable_fst)
  have hr : MeasurableSet {a : ℝ × Phase | Nonempty (FlightChain Q a.2)} :=
    (CodedChain.measurableSet_regular Q).preimage measurable_snd
  have he : (fun a : ℝ × Phase => billiardFlow Q a.1 a.2) =
      (fun a : ℝ × Phase => if Nonempty (FlightChain Q a.2) then
        (CodedChain.fromPhase Q a.2).chain.at a.1 else a.2) := by
    funext ⟨t, z⟩
    change billiardFlow Q t z = if Nonempty (FlightChain Q z) then
      (CodedChain.fromPhase Q z).chain.at t else z
    by_cases h : Nonempty (FlightChain Q z)
    · simp only [ite_eq_left h]
      rw [billiardFlow_eq_chain (Classical.choice h), CodedChain.fromPhase_at]
    · simp only [billiardFlow, dite_eq_right h, ite_eq_right h]
  rw [he]
  exact Measurable.ite hr hm measurable_snd

lemma measurable_billiardFlow_time (Q : Triangle) (t : ℝ) : Measurable (billiardFlow Q t) :=
  (measurable_billiardFlow Q).comp (measurable_const.prodMk measurable_id)

end TriangularBilliards

end

end OAI
