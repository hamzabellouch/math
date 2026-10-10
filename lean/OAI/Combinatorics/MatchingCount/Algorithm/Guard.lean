import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.OutputLengthBound

namespace OAI

namespace MatchingFPRAS.WeightedOptions
open Finset FiniteChoice

lemma draw_law_pos {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (c : WeightedOptions Ω) (k : ℕ) (bits : Fin k → Bool) :
    0 < c.law (c.draw k bits) := by
  let i := chooseBits c.mass c.total k bits
  have hi : 0 < c.mass i := chooseBits_pos c.mass c.total k bits
  apply hi.trans_le
  unfold law
  calc
    c.mass i = (if c.out i = c.draw k bits then c.mass i else 0) := by simp [draw, i]
    _ ≤ ∑ j, if c.out j = c.draw k bits then c.mass j else 0 :=
      single_le_sum (f := fun j => if c.out j = c.draw k bits then c.mass j else 0)
        (fun j _ => by split_ifs <;> [exact c.nonneg j; exact le_rfl]) (mem_univ i)

end MatchingFPRAS.WeightedOptions

namespace MatchingFPRAS.Enlargement
open Finset Switching Subdivision RealGeometry MatchingFPRAS.Representation

theorem intact_partition_identity_even {V : Type*} [Fintype V] [LinearOrder V]
    (he : Even (Fintype.card V)) (w : V → V → ℝ)
    (p : ℕ) (B Hu Hv : LogicalEdge V → ℝ) :
    realHolePartition source target (4*p) ∅ (fun _ => ∅)
      (pathActivity p B Hu Hv (logicalActivity w)) =
      (∏ e, pathConstant p (B e) (Hu e) (Hv e)) * partition w ∅ := by
  classical
  have hz := StageAnalysis.partition_pos_of_even (fun _ _ : V => (1:ℝ)) (by intros; norm_num) ∅
    (by simpa using he)
  have hn : (matchings (∅ : Finset V)).Nonempty := by
    by_contra hn
    have hz0 : partition (fun _ _ : V => (1:ℝ)) ∅ = 0 := by
      simp [partition, Finset.not_nonempty_iff_eq_empty.mp hn]
    linarith
  obtain ⟨m, hm⟩ := hn
  let b := fun (e : LogicalEdge V) (i : Fin (4*p+1)) => alternating (select m e) i.val
  have hb := intact_family p m ((mem_matchings m ∅).mp hm)
  have hid := deletion_partition_identity (show Even (4*p) from ⟨2*p,by omega⟩)
    source target ∅ (fun _ => ∅) b hb (pathActivity p B Hu Hv (logicalActivity w))
    (fun e => List.ofFn fun r : Fin p => max (B e) (Hu e/2^r.val))
    (fun e => (List.ofFn fun r : Fin p => max (B e) (Hv e/2^r.val)).reverse) _
    (fun e => profileActivity_ofFn p (B e) (Hu e) (Hv e) (logicalActivity w e))
  simpa [residualHoles, broken, deletionConstant, List.prod_ofFn, pathConstant,
    logical_partition_eq] using hid

open Transport
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
noncomputable local instance (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _
noncomputable local instance (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

theorem frozenPortion_full_even (he : Even (Fintype.card V))
    (w w₁ : V → V → ℝ) (K : ℕ) :
    Transport.partitionWeight BagEdge.Incident (frozenPortion w w₁ K) Finset.univ =
      sourceC w K * Switching.partition w₁ ∅ := by
  rw [←survivors_empty (V:=V) K, frozenPortion_partition,
    intact_partition_identity_even he w₁]
  rfl

theorem observableD_mean_even (he : Even (Fintype.card V))
    (w w₁ : V → V → ℝ) (hw : ∀ x y, 0 < w x y) (K D : ℕ) :
    (∑ a : SourceMarked w K, sourceLaw w K D a * observableD w w₁ K a) =
      sourceC w K * Switching.partition w₁ ∅ / sourceBagZ w K D := by
  classical
  have h := Marking.allReal_mean BagEdge.Incident (sourcePortions w K D) (0 : Fin 3) (bagReweight w w₁ K)
  simp only [sourcePortions, Matrix.cons_val_zero] at h
  rw [bagReweight_identity w w₁ hw K, frozenPortion_full_even he w w₁] at h
  simpa only [sourceLaw, observableD, sourcePortions_collapse, sourceBagZ] using h

theorem observableD_zero_of_partition_zero (he : Even (Fintype.card V))
    (w w₁ : V → V → ℝ) (hw : ∀ x y, 0 < w x y)
    (hw₁ : ∀ x y, 0 ≤ w₁ x y) (hle : ∀ x y, w₁ x y ≤ w x y)
    (hz : 0 < Switching.partition w ∅) (K D : ℕ)
    (hz₁ : Switching.partition w₁ ∅ = 0) (a : SourceMarked w K)
    (ha : 0 < sourceLaw w K D a) : observableD w w₁ K a = 0 := by
  have hB : 0 < sourceBagZ w K D := sourceBagZ_pos w hw hz K D
  have hmean := observableD_mean_even he w w₁ hw K D
  rw [hz₁, mul_zero, zero_div] at hmean
  have hnonneg (b : SourceMarked w K) : 0 ≤ sourceLaw w K D b * observableD w w₁ K b :=
    mul_nonneg (sourceLaw_nonneg w hw K D hB.le b)
      (observableD_range w w₁ hw hw₁ hle K b).1
  have hz' := (sum_eq_zero_iff_of_nonneg (fun b _ => hnonneg b)).mp hmean a (mem_univ a)
  exact (mul_eq_zero.mp hz').resolve_left ha.ne'

end MatchingFPRAS.Enlargement

namespace MatchingFPRAS.TableMarking
open Finset Transport Variation

variable {V E I : Type*} [Fintype V] [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
variable (inc : E → V → Prop)
variable {A : Type*} [Fintype A] [Nonempty A]

omit [Fintype A] [Nonempty A] [DecidableEq E] in
lemma draw_law_pos [DecidableEq E] (f : A → PM inc) (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (c : E → WeightedOptions I) (k : ℕ) (bits : A × (E → Fin k → Bool)) :
    0 < law inc w c (draw inc f c k bits) := by
  classical
  change 0 < gibbs w (f bits.1) * ∏ e : (f bits.1).val, ((c e.val).law ((c e.val).draw k (bits.2 e.val)) : ℝ)
  apply mul_pos (gibbs_pos w hw _)
  exact Finset.prod_pos fun e _ => by exact_mod_cast (c e.val).draw_law_pos k (bits.2 e.val)

end MatchingFPRAS.TableMarking

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagPM (bags w K)) := Fintype.ofFinite _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (Marked w K) := Fintype.ofFinite _

lemma marking_law_eq (w : V → V → ℚ) (hw : ∀ x y, 0 < w x y)
    (K D : ℕ) (hD : 0 < D) :
    TableMarking.law BagEdge.Incident (fun e => (bagWeight w K D e : ℝ))
      (markingTable w hw K D hD) = markedLaw w K D := by
  funext a
  simp only [TableMarking.law, markedLaw, Variation.sigmaLift, Variation.product, TableMarking.portion, markingTable_law]

theorem source_draw_support {A : Type*} [Fintype A] [Nonempty A]
    (w : V → V → ℚ) (hw : ∀ x y, 0 < w x y) (K D k : ℕ) (hD : 0 < D)
    (f : A → BagPM (bags w K)) (bits : A × (BagEdge (bags w K) → Fin k → Bool)) :
    0 < sourceLaw (fun x y => (w x y : ℝ)) K D
      ((sourceMarkedEquiv w K).symm
        (TableMarking.draw BagEdge.Incident f (markingTable w hw K D hD) k bits)) := by
  rw [←markedLaw_equiv w hw K D hD, Equiv.apply_symm_apply, ←marking_law_eq w hw K D hD]
  apply TableMarking.draw_law_pos
  intro e
  exact_mod_cast bagWeight_pos w hw K D hD e

end MatchingFPRAS.RationalSource

namespace MatchingFPRAS.GraphBridge
open Finset Switching

lemma unpadded_partition (G : GraphInput) :
    partition (rawActivity G 0) ∅ = (Z G : ℝ) := by
  have h := raw_padding_bound G 0 (by norm_num) (by norm_num)
  have he : rawPartition G 0 = (Z G : ℚ) := le_antisymm (by simpa using h.2) h.1
  have hc := raw_partition G 0
  rw [he] at hc
  simpa using hc.symm

end MatchingFPRAS.GraphBridge

namespace MatchingFPRAS.Trial
open Finset Switching Transport Enlargement StageAnalysis
open scoped Classical

variable {G : GraphInput} {j K : ℕ} [Nontrivial (Fin G.n)]
noncomputable local instance (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) :
    DecidableEq (SourceLabel w K) := Classical.decEq _
noncomputable local instance (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) :
    Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

noncomputable def ScaleState.certificateActivity (s : ScaleState G j) : Fin G.n → Fin G.n → ℝ :=
  fun a b => GraphBridge.rawActivity G 0 a b * s.scale a * s.scale b

omit [Nontrivial (Fin G.n)] in
lemma ScaleState.certificateActivity_nonneg (s : ScaleState G j) (a b : Fin G.n) :
    0 ≤ s.certificateActivity a b := by
  unfold ScaleState.certificateActivity GraphBridge.rawActivity
  split_ifs
  · simpa only [one_mul] using mul_nonneg (s.positive a).le (s.positive b).le
  · simp

omit [Nontrivial (Fin G.n)] in
lemma ScaleState.certificateActivity_le (s : ScaleState G j) (a b : Fin G.n) :
    s.certificateActivity a b ≤ s.activity a b := by
  unfold ScaleState.certificateActivity ScaleState.activity raw GraphBridge.rawActivity
  split_ifs
  · rfl
  · simp only [zero_mul]
    exact mul_nonneg (mul_nonneg (pow_pos (cooling_pos G.n) j).le (s.positive a).le) (s.positive b).le

omit [Nontrivial (Fin G.n)] in
lemma ScaleState.certificateActivity_partition (s : ScaleState G j) :
    Switching.partition s.certificateActivity ∅ = (Z G : ℝ) * ∏ i, s.scale i := by
  change Switching.partition (fun a b => GraphBridge.rawActivity G 0 a b * s.scale a * s.scale b) ∅ = _
  rw [partition_vertex_scaling, GraphBridge.unpadded_partition]
  simp

theorem ScaleState.certificate_zero (s : ScaleState G j) (he : Even G.n)
    (hZ : Z G = 0) (D : ℕ) (a : SourceMarked s.activity K)
    (ha : 0 < sourceLaw s.activity K D a) :
    observableD s.activity s.certificateActivity K a = 0 := by
  apply observableD_zero_of_partition_zero (by simpa using he) s.activity s.certificateActivity
    s.activity_pos s.certificateActivity_nonneg s.certificateActivity_le
    (s.partition_pos he) K D
  · rw [s.certificateActivity_partition, hZ]
    simp
  · exact ha

open Finset Switching Transport Enlargement StageAnalysis
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
noncomputable local instance (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) :
    DecidableEq (SourceLabel w K) := Classical.decEq _
noncomputable local instance (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) :
    Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

theorem ScaleState.certificate_mean_lower (p : Parameters G) (s : ScaleState G p.K)
    (hs : s.Balanced p.hn) (hZ : 0 < Z G) :
    (1:ℝ)/4 ≤ ∑ a : SourceMarked s.activity p.K,
      sourceLaw s.activity p.K p.D a * observableD s.activity s.certificateActivity p.K a := by
  have hm : (∑ a : SourceMarked s.activity p.K,
      sourceLaw s.activity p.K p.D a * observableD s.activity s.certificateActivity p.K a) =
      sourceC s.activity p.K * partition s.certificateActivity ∅ / sourceBagZ s.activity p.K p.D := by
    convert observableD_mean_even (by simpa using p.even) s.activity s.certificateActivity
      s.activity_pos p.K p.D using 1
    exact Variation.sum_instances _ _ _
  rw [hm]
  have hB := (sourceBagZ_bounds (by simpa using p.hn) s.activity s.activity_pos
    (s.partition_pos p.even) hs.1 hs.2 p.K (s.cap le_rfl)).2
  have hp := (final_padding G p.epsilon p.epsilon_pos p.K p.schedule hZ).2
  have hsmall : partition (raw G p.K) ∅ ≤ 2 * (Z G : ℝ) := by
    have hz : (0:ℝ) ≤ Z G := Nat.cast_nonneg _
    have he := p.epsilon_real_lt_one
    nlinarith
  have hprod : 0 < ∏ i, s.scale i := prod_pos fun i _ => s.positive i
  have hact : partition s.activity ∅ ≤ 2 * partition s.certificateActivity ∅ := by
    rw [s.certificateActivity_partition]
    change partition (fun a b => raw G p.K a b * s.scale a * s.scale b) ∅ ≤ _
    rw [partition_vertex_scaling]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hsmall hprod.le
  have hc := sourceC_pos s.activity p.K
  have hb0 := sourceBagZ_pos s.activity s.activity_pos (s.partition_pos p.even) p.K p.D
  apply (le_div_iff₀ hb0).mpr
  change sourceBagZ s.activity p.K (sourceD (V:=Fin G.n) p.K) ≤ _ at hB
  have hmul := mul_le_mul_of_nonneg_left hact hc.le
  change (1:ℝ)/4 * sourceBagZ s.activity p.K (sourceD (V:=Fin G.n) p.K) ≤ _
  nlinarith

end MatchingFPRAS.Trial

namespace MatchingFPRAS.Variation
open Finset
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

lemma mean_le_positive_event (p X : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hX : ∀ x, 0 ≤ X x ∧ X x ≤ 1) :
    (∑ x, p x * X x) ≤ event p (fun x => 0 < X x) := by
  apply sum_le_sum
  intro x _
  change p x * X x ≤ if 0 < X x then p x else 0
  by_cases hx : 0 < X x
  · simp only [hx, ite_true]
    exact mul_le_of_le_one_right (hp x) (hX x).2
  · have hz : X x = 0 := le_antisymm (le_of_not_gt hx) (hX x).1
    simp [hz]

end MatchingFPRAS.Variation

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagPM (bags w K)) := Fintype.ofFinite _

theorem fixedSampler_support (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ)
    (bits : Fin (totalBitsPolynomial (Fintype.card (SourceVertex V K)) D K m ⌈η⁻¹⌉₊) → Bool) :
    0 < sourceLaw (fun x y => (w x y : ℝ)) K D
      (fixedSampler w hw K D m hD hN h hq M η bits) := by
  simp only [fixedSampler, padSampler, bitSampler, Function.comp_apply, markedSampler]
  exact source_draw_support w hw K D _ hD _ _

end MatchingFPRAS.RationalSource

end OAI
