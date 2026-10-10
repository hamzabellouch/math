import Mathlib
import OAI.Algebra.GroupRing.StageExpectation

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TwoSideFullStage
open scoped Classical BigOperators
open RepeatedBlocks BlockAlignment ComparedBlocks ChainStageLabels WordEstimate
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {A B E VA VB TA TB : Type} [Fintype A] [Fintype B] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : A ⊕ B → ℕ) (j : ℕ)

abbrev CA := {a : A // j < m (.inl a)}
abbrev CB := {b : B // j < m (.inr b)}
abbrev lenA : CA m j → ℕ := fun a => len (.inl a.val)
abbrev lenB : CB m j → ℕ := fun b => len (.inr b.val)

def restrictA (F : StagePosition len m j → Letter) : Position (lenA len m j) → Letter :=
  fun x => F ⟨⟨.inl x.1.val,x.1.property⟩,x.2⟩
def restrictB (F : StagePosition len m j → Letter) : Position (lenB len m j) → Letter :=
  fun x => F ⟨⟨.inr x.1.val,x.1.property⟩,x.2⟩

def indexA (i : Underlying s (lenA len m j)) : Underlying s len := ⟨.inl i.1.val,i.2⟩
def indexB (i : Underlying s (lenB len m j)) : Underlying s len := ⟨.inr i.1.val,i.2⟩

include hs in
theorem binsA (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (F : StagePosition len m j → Letter)
    (hF : F ∈ fullWords s len m j cmp d) :
    ∀ i, word s (lenA len m j) (StageExpectation.readWord (lenA len m j)
      (restrictA len m j F)) i ∈ binWords (height s (lenA len m j) i) (d (indexA s len m j i)) := by
  obtain ⟨w,_,_,hb,rfl⟩ := (Finset.mem_filter.mp hF).2
  intro i
  have he : word s (lenA len m j) (StageExpectation.readWord (lenA len m j)
      (restrictA len m j (fun x => w x.1.val x.2.val))) i =
      word s len w (indexA s len m j i) := by
    funext k
    dsimp only [word,StageExpectation.readWord]
    rw [dite_eq_left (StageExpectation.word_position s hs (lenA len m j) i k)]
    rfl
  rw [he]
  exact hb (indexA s len m j i)

include hs in
theorem binsB (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (F : StagePosition len m j → Letter)
    (hF : F ∈ fullWords s len m j cmp d) :
    ∀ i, word s (lenB len m j) (StageExpectation.readWord (lenB len m j)
      (restrictB len m j F)) i ∈ binWords (height s (lenB len m j) i) (d (indexB s len m j i)) := by
  obtain ⟨w,_,_,hb,rfl⟩ := (Finset.mem_filter.mp hF).2
  intro i
  have he : word s (lenB len m j) (StageExpectation.readWord (lenB len m j)
      (restrictB len m j (fun x => w x.1.val x.2.val))) i =
      word s len w (indexB s len m j i) := by
    funext k
    dsimp only [word,StageExpectation.readWord]
    rw [dite_eq_left (StageExpectation.word_position s hs (lenB len m j) i k)]
    rfl
  rw [he]
  exact hb (indexB s len m j i)

def joinBlock : Underlying s (lenA len m j) ⊕ Underlying s (lenB len m j) →
    Underlying s (StageExpectation.activeLen len m j)
  | .inl i => ⟨⟨.inl i.1.val,i.1.property⟩,i.2⟩
  | .inr i => ⟨⟨.inr i.1.val,i.1.property⟩,i.2⟩

omit [Fintype A] [Fintype B] in
theorem joinBlock_bijective : Function.Bijective (joinBlock s len m j) := by
  constructor
  · intro x y he
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        rcases x with ⟨⟨a,ha⟩,ix⟩
        rcases y with ⟨⟨b,hb⟩,iy⟩
        have hab : a=b := Sum.inl.inj (congrArg (fun z => z.1.val) he)
        subst b
        have hii : ix=iy := Fin.ext (congrArg (fun z => z.2.val) he)
        subst iy
        rfl
      | inr y => have h := congrArg (fun z => z.1.val) he; cases h
    | inr x =>
      cases y with
      | inl y => have h := congrArg (fun z => z.1.val) he; cases h
      | inr y =>
        rcases x with ⟨⟨a,ha⟩,ix⟩
        rcases y with ⟨⟨b,hb⟩,iy⟩
        have hab : a=b := Sum.inr.inj (congrArg (fun z => z.1.val) he)
        subst b
        have hii : ix=iy := Fin.ext (congrArg (fun z => z.2.val) he)
        subst iy
        rfl
  · rintro ⟨⟨c,hc⟩,b⟩
    cases c with
    | inl a => exact ⟨.inl ⟨⟨a,hc⟩,b⟩,rfl⟩
    | inr b' => exact ⟨.inr ⟨⟨b',hc⟩,b⟩,rfl⟩

def blockEquiv := Equiv.ofBijective (joinBlock s len m j) (joinBlock_bijective s len m j)

theorem bin_sum (d : Underlying s len → ℤ) :
    (∑ i, (d (indexA s len m j i) : ℝ)) + (∑ i, (d (indexB s len m j i) : ℝ)) =
      ∑ i ∈ activeBlocks s len m j, (d i : ℝ) := by
  rw [← StageExpectation.active_bin_sum s len m j d]
  calc
    _ = ∑ i : Underlying s (lenA len m j) ⊕ Underlying s (lenB len m j),
        (d (StageExpectation.activeIndex s len m j (joinBlock s len m j i)) : ℝ) := by
      rw [Fintype.sum_sum_type]
      rfl
    _ = _ := Fintype.sum_equiv (blockEquiv s len m j) _ _ (fun _ => rfl)

variable (firstA lastA : CA m j → VA) (firstB lastB : CB m j → VB)
  (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter)
  (pinA : VA → Option TA) (pinB : VB → Option TB)

def sideA : TwoSideStage.Side where
  C := CA m j; V := VA; TV := TA
  fC := inferInstance; fV := inferInstance; fTV := inferInstance
  len := lenA len m j
  first := firstA; last := lastA; outgoing := outA; pin := pinA

def sideB : TwoSideStage.Side where
  C := CB m j; V := VB; TV := TB
  fC := inferInstance; fV := inferInstance; fTV := inferInstance
  len := lenB len m j
  first := firstB; last := lastB; outgoing := outB; pin := pinB

local notation "SA" => sideA len m j firstA lastA outA pinA
local notation "SB" => sideB len m j firstB lastB outB pinB

theorem exponential_fusion (u v k x y z : ℝ) (hz : x+y=z) :
    Real.exp (u+v)*(k*Real.exp (-x-y)) = k*Real.exp (u-z+v) := by
  rw [← hz]
  simp only [sub_eq_add_neg,Real.exp_add,Real.exp_neg]
  ring

include hs in
/-- The joint matching expectation applied to the actual fullWords projection,
including cross-side comparisons. All entropy and bin costs are computed on
that one global pattern. -/
theorem mean_bound (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (err : ℕ)
    (hlarge : ∀ i, 3002 ≤ height s len i)
    (hscale : ∀ i, s+1200 ≤ 2*(height s len i : ℝ))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1,x.2.val) ≠ ((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (n p : ℝ) (N D R : ℕ) (hA : TwoSideStage.Conditions SA n p N D R)
    (hB : TwoSideStage.Conditions SB n p N D R) :
    TwoSideMean.mean (((SA).samples N) ×ˢ ((SB).samples N))
      (TwoSideStage.count SA SB (fullWords s len m j cmp d)
        (restrictA len m j) (restrictB len m j)) ≤
      ((SA).cost n p R * (SB).cost n p R) *
        Real.exp ((∑ c : StageLabels.activeComponents
          (ActualStageLabels.L s hs len m cmp err).graph.connectedComponentMk (activeBlocks s len m j),
          ActualStageLabels.cost s hs len m cmp err d c.val) -
          (∑ i ∈ activeBlocks s len m j, (d i : ℝ)) +
          (2*(err : ℝ)*Fintype.card (Underlying s len)+(s+1)*Fintype.card (A ⊕ B))*
            Real.log (Fintype.card Letter)) := by
  have h := TwoSideStage.mean_bound s hs SA SB (fullWords s len m j cmp d)
    (restrictA len m j) (restrictB len m j) n p N D R hA hB
    (fun i => d (indexA s len m j i)) (fun i => d (indexB s len m j i))
    (binsA s hs len m j cmp d) (binsB s hs len m j cmp d)
  have hc := full_stage_count s hs len m j cmp d err hlarge hscale hreduced
  have hn : 0 ≤ n := (Nat.cast_nonneg (Fintype.card TA)).trans hA.vertices
  have hp := hA.nonneg
  have hcost : 0 ≤ (SA).cost n p R * (SB).cost n p R := by unfold TwoSideStage.Side.cost; positivity
  have h' := h.trans (mul_le_mul_of_nonneg_right hc
    (mul_nonneg hcost (Real.exp_pos _).le))
  exact h'.trans_eq (exponential_fusion _ _ _ _ _ _ (bin_sum s len m j d))

end TorsionFreeZeroDivisors.TwoSideFullStage

namespace TorsionFreeZeroDivisors.MatchingGraphs
open PortSubdivision BallCount GirthSwitch
variable {V D T : Type*} [Fintype V] [Fintype D] [DecidableEq D]

/-- Nonemptiness of the exact typed matching family conditioned on girth.
The numerical hypothesis is an explicit finite-size bound, not a new standing
hypothesis for the main existential theorem. -/
theorem exists_typed_large_girth (origin : D → V) (label : D → T) (bar : T → T)
    (Γ₀ : PortGraph V D) (ho : Γ₀.origin = origin)
    (hlabel : ∀ f, label (Γ₀.reverse f) = bar (label f))
    (d N : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // origin e = v} ≤ d)
    (hbig : ∀ x, 4*d^(2*N+1) < Nat.card {e : D // label e = label x}) :
    ∃ Γ : PortGraph V D, Γ.origin = origin ∧
      (∀ f, label (Γ.reverse f) = bar (label f)) ∧
      (N : ℕ∞) ≤ Γ.subdivision.egirth := by
  classical
  let P : SimpleGraph (V ⊕ D) → Prop := fun G =>
    ∃ Γ : PortGraph V D, Γ.origin = origin ∧
      (∀ f, label (Γ.reverse f) = bar (label f)) ∧ G = Γ.subdivision
  have hne : ∃ G, P G := ⟨Γ₀.subdivision,Γ₀,ho,hlabel,rfl⟩
  have hsw : ∀ G, P G → ∀ a (p : G.Walk a a), p.IsCycle →
      ∃ x y u z, s(x,y) ∈ p.edges ∧ G.Adj u z ∧
        (∀ a ∈ ({x,y} : Set (V ⊕ D)), ∀ b ∈ ({u,z} : Set (V ⊕ D)),
          ∀ p : G.Walk a b, 2*N < p.length) ∧
        P (addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y) := by
    rintro G ⟨Γ,hΓo,hΓl,rfl⟩ a p hp
    obtain ⟨x,hx⟩ := Γ.cycle_has_middle p hp
    have hd' : ∀ v, Nat.card {e : D // Γ.origin e = v} ≤ d := by rw [hΓo]; exact hd
    obtain ⟨e,hel,hfar⟩ := exists_far_port Γ label d (2*N) h2 hd' x (hbig x)
    have hxe : x ≠ e := by
      intro h
      have hf := hfar (.inr x) (by simp) (.inr e) (by simp)
      subst e
      have hh := hf SimpleGraph.Walk.nil
      simp at hh
    have hxr : x ≠ Γ.reverse e := by
      intro h
      have hf := hfar (.inr x) (by simp) (.inr (Γ.reverse e)) (by simp)
      rw [h] at hf
      have hh := hf SimpleGraph.Walk.nil
      simp at hh
    refine ⟨.inr x,.inr (Γ.reverse x),.inr e,.inr (Γ.reverse e),hx,rfl,hfar,?_⟩
    refine ⟨Γ.switch x e,hΓo,Γ.switch_preserves_labels label bar hΓl x e hel.symm,?_⟩
    exact (subdivision_switch Γ x e hxe hxr).symm
  obtain ⟨G,⟨Γ,hΓo,hΓl,hG⟩,hg⟩ := exists_large_girth N P hne hsw
  exact ⟨Γ,hΓo,hΓl,hG ▸ hg⟩

end TorsionFreeZeroDivisors.MatchingGraphs

namespace TorsionFreeZeroDivisors.TypedGraphs
open TorsionFreeZeroDivisors.Types PortSubdivision ConditionedMatchings MatchingGraphs
variable {V : Type*} (outgoing : V → Finset Letter)

/-- The source's outgoing half-edges, preserving their basepoints and letters. -/
abbrev Dart := {e : V × Letter // e.2 ∈ outgoing e.1}
def origin (e : Dart outgoing) : V := e.val.1
def label (e : Dart outgoing) : Letter := e.val.2

def reverse (M : MatchingTuple outgoing) (e : Dart outgoing) : Dart outgoing :=
  ⟨(next outgoing M e.val.1 e.val.2,inverse e.val.2),
    next_reverse_mem outgoing M e.val.1 e.val.2 e.property⟩

theorem reverse_involutive (M : MatchingTuple outgoing) :
    Function.Involutive (reverse outgoing M) := by
  intro e
  apply Subtype.ext
  exact Prod.ext (next_reverse_next outgoing M e.val.1 e.val.2 e.property)
    (inverse_inverse e.val.2)

def matching (M : MatchingTuple outgoing) : Matching (label outgoing) inverse :=
  ⟨(reverse_involutive outgoing M).toPerm (reverse outgoing M),
    reverse_involutive outgoing M,by
      intro e he
      exact inverse_ne e.val.2 (congrArg (label outgoing) he),fun _ => rfl⟩

/-- An origin fibre is exactly the prescribed outgoing type. -/
def originFiber (v : V) : {e : Dart outgoing // origin outgoing e = v} ≃
    {t : Letter // t ∈ outgoing v} where
  toFun e := ⟨e.val.val.2,by
    have h := e.val.property
    simpa only [← e.property,origin,label] using h⟩
  invFun t := ⟨⟨(v,t.val),t.property⟩,rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext e.property.symm rfl
  right_inv _ := rfl

/-- A letter fibre is exactly its empirical carrier set on this side. -/
def labelFiber (t : Letter) : {e : Dart outgoing // label outgoing e = t} ≃
    {v : V // t ∈ outgoing v} where
  toFun e := ⟨e.val.val.1,by
    have h := e.val.property
    simpa only [← e.property,origin,label] using h⟩
  invFun v := ⟨⟨(v.val,t),v.property⟩,rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl e.property.symm
  right_inv _ := rfl

theorem origin_card (v : V) :
    Nat.card {e : Dart outgoing // origin outgoing e = v} = (outgoing v).card := by
  rw [Nat.card_congr (originFiber outgoing v), Nat.card_eq_fintype_card]
  exact Fintype.card_coe _

theorem label_card [Fintype V] (t : Letter) :
    Nat.card {e : Dart outgoing // label outgoing e = t} =
      Fintype.card {v : V // t ∈ outgoing v} := by
  rw [Nat.card_congr (labelFiber outgoing t),Nat.card_eq_fintype_card]

/-- No label can leave its basepoint twice: this is literally the immersion
into the rose, not a simplicity assumption on the graph. -/
theorem origin_label_injective : Function.Injective
    (fun e : Dart outgoing => (origin outgoing e,label outgoing e)) := by
  intro e f h
  exact Subtype.ext h

theorem exists_conditioned [Fintype V] (M : MatchingTuple outgoing) (N : ℕ)
    (hd : ∀ v, (outgoing v).card ≤ 132)
    (hsize : ∀ t, 4*132^(2*N+1) < Fintype.card {v : V // t ∈ outgoing v}) :
    (Matching.conditioned (label := label outgoing) (bar := inverse)
      (origin outgoing) N ∅).Nonempty := by
  classical
  let r := matching outgoing M
  obtain ⟨Γ,hΓo,hΓl,hg⟩ := exists_typed_large_girth
    (origin outgoing) (label outgoing) inverse (r.graph (origin outgoing)) rfl
    (fun e => r.label_reverse e) 132 N (by norm_num)
    (fun v => by rw [origin_card]; exact hd v)
    (fun e => by rw [label_card]; exact hsize _)
  let r' : Matching (label outgoing) inverse :=
    ⟨Γ.reverse_reverse.toPerm Γ.reverse,Γ.reverse_reverse,Γ.reverse_ne,hΓl⟩
  refine ⟨r',Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩⟩
  · intro a b h
    exact False.elim (Finset.notMem_empty _ h)
  · have he : r'.graph (origin outgoing) = Γ := by
      cases Γ
      simp_all only [Matching.graph]
      rfl
    rw [he]
    exact hg

/-- The actual prescribed A-side graph space has nonzero cardinality. -/
theorem conditionedA_nonempty (rep N : ℕ) (hsize : 4*132^(2*N+1) < 4260354*rep) :
    (Matching.conditioned (label := label (@outgoingA rep)) (bar := inverse)
      (origin (@outgoingA rep)) N ∅).Nonempty := by
  classical
  exact exists_conditioned _ (Classical.choice (matchingA_nonempty rep)) N
    (fun v => (degreeA_bounds v).2)
    (fun t => by rw [letter_frequencyA]; exact hsize)

theorem conditionedB_nonempty (rep N : ℕ) (hsize : 4*132^(2*N+1) < 4260354*rep) :
    (Matching.conditioned (label := label (@outgoingB rep)) (bar := inverse)
      (origin (@outgoingB rep)) N ∅).Nonempty := by
  classical
  exact exists_conditioned _ (Classical.choice (matchingB_nonempty rep)) N
    (fun v => (degreeB_bounds v).2)
    (fun t => by rw [letter_frequencyB]; exact hsize)

end TorsionFreeZeroDivisors.TypedGraphs

namespace TorsionFreeZeroDivisors.GirthAsymptotics
open Filter
open scoped Topology

/-- The source logarithmic girth, including its specified constant c=1/100. -/
def L (n : ℕ) : ℕ := ⌊Real.log n / 100⌋₊
/-- Exclusion cost for the faithful threefold port subdivision. -/
def exclusion (n : ℕ) : ℕ := 4 * 132 ^ (6 * L n + 1)

theorem log132_lt : Real.log 132 < 8 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
  have h : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_lt_pow_left₀ h (by norm_num : (0 : ℝ) ≤ 2) (by decide : 8 ≠ 0)
  have he : Real.exp (8 : ℝ) = Real.exp 1 ^ 8 := by
    simp [← Real.exp_nat_mul]
  rw [he]
  norm_num at hp ⊢
  linarith

theorem exclusion_bound (n : ℕ) (hn : 1 ≤ n) :
    (exclusion n : ℝ) ≤ 4 * Real.exp 8 * (n : ℝ) ^ (1/2 : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hl : 0 ≤ Real.log n := Real.log_nonneg hn'
  have hf : (L n : ℝ) ≤ Real.log n / 100 := Nat.floor_le (by positivity)
  have he : ((6 * L n + 1 : ℕ) : ℝ) * Real.log 132 ≤ Real.log n / 2 + 8 := by
    push_cast
    have hmul := mul_le_mul_of_nonneg_left (le_of_lt log132_lt)
      (show 0 ≤ 6 * (L n : ℝ) + 1 by positivity)
    nlinarith
  rw [exclusion, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat]
  have hpow : (132 : ℝ) ^ (6 * L n + 1) =
      Real.exp (((6 * L n + 1 : ℕ) : ℝ) * Real.log 132) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 132)]
  rw [hpow,Real.rpow_def_of_pos hn0]
  calc
    4 * Real.exp (↑(6 * L n + 1) * Real.log 132) ≤
        4 * Real.exp (Real.log n / 2 + 8) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num)
    _ = 4 * Real.exp 8 * Real.exp (Real.log n * (1/2)) := by
      rw [Real.exp_add]
      rw [div_eq_mul_inv]
      ring_nf

theorem exclusion_ratio : Tendsto (fun n : ℕ => (exclusion n : ℝ) / n) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1/2 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop
  have ht' := ht.const_mul (4 * Real.exp 8)
  simp only [mul_zero] at ht'
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => by positivity)) _ ht'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    (exclusion n : ℝ) / n ≤ (4 * Real.exp 8 * (n : ℝ) ^ (1/2 : ℝ)) / n :=
      div_le_div_of_nonneg_right (exclusion_bound n hn) (le_of_lt hn0)
    _ = 4 * Real.exp 8 * (n : ℝ) ^ (-(1/2 : ℝ)) := by
      rw [show -(1/2 : ℝ) = 1/2-1 by norm_num,Real.rpow_sub hn0,Real.rpow_one]
      ring

theorem L_tendsto : Tendsto L atTop atTop := by
  have hl : Tendsto (fun n : ℕ => Real.log (n : ℝ) / 100) atTop atTop := by
    simpa only [div_eq_mul_inv, Function.comp_apply] using
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).atTop_mul_const
        (by norm_num : (0 : ℝ) < (100 : ℝ)⁻¹)
  exact tendsto_nat_floor_atTop.comp hl

theorem eventual_small (p : ℝ) (hp : 0 < p) :
    ∀ᶠ n : ℕ in atTop, (exclusion n : ℝ) < p * n := by
  filter_upwards [exclusion_ratio.eventually_lt_const hp,eventually_ge_atTop 1] with n h hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact (div_lt_iff₀ hn0).mp h

end TorsionFreeZeroDivisors.GirthAsymptotics

end

end OAI
