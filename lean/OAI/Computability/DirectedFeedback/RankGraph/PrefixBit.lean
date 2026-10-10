import Mathlib
import OAI.Computability.DirectedFeedback.RankGraph.RoundBoolean

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
omit [Fintype U] [Fintype X] [NeZero M] [NeZero T] [Nonempty X] in
theorem vertices_takePrefix {t : ℕ} (ht : t ≤ T) (a : PrefixData U X M T) :
    vertices (takePrefix ht a) = takePrefix ht (vertices a) := rfl

variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (deleted : OutputVertex (M := M) G ψLaw → Bool)
variable (ord : OutputVertex (M := M) G ψLaw → ℕ)
variable (hord : ∀ {a b}, deleted a = false → deleted b = false →
  OutputArc G ψLaw hYX fiber a b → ord a < ord b)
variable (hrank : ∀ r, deleted (.inl r) = false)

def prefixBit (d : Full U X M T N) (t : ℕ) : Set (Fin t → X) → Bool :=
  if h : t ≤ T then referenceBit (rankOrder G ψLaw ord) d.1.val rankLength_ge
    (.inl ⟨⟨t,by omega⟩,takePrefix h (vertices d.2)⟩) else fun _ => false

include hord hrank in
theorem prefixBit_properties (d : Full U X M T N) {t : ℕ} (ht : t ≤ T) :
    prefixBit G ψLaw ord d t ∅ = false ∧ prefixBit G ψLaw ord d t Set.univ = true := by
  simp only [prefixBit, dite_eq_left ht]
  exact ⟨reference_empty rankLength_ge d.1.property
    (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _,
    reference_univ rankLength_ge d.1.property
    (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _⟩

def prefixTransition (d : Full U X M T N) (t : ℕ) : Fin (cellCount t) :=
  if h : t ≤ T then transition (prefixBit G ψLaw ord d t) (prefixCell t (sets d.2))
    (prefixBit_properties G ψLaw hYX fiber deleted ord hord hrank d h).1
    (prefixBit_properties G ψLaw hYX fiber deleted ord hord hrank d h).2
  else 0

theorem prefixBit_lift (d : Full U X M T N) (t : ℕ) (ht : t < T)
    (A : Set (Fin t → X)) :
    prefixBit G ψLaw ord d (t+1) (Fin.init ⁻¹' A) = prefixBit G ψLaw ord d t A := by
  simp only [prefixBit, dite_eq_left (show t+1 ≤ T by omega), dite_eq_left (show t ≤ T by omega), referenceBit]
  exact (compare_prefix_big (ord := rankOrder G ψLaw ord) (ψ := d.1.val)
    t ht (takePrefix (by omega) (vertices d.2)) A _ _ _).symm

theorem full_membership (fallback : X) (d : Full U X M T N)
    (hgood : Good (rankOrder G ψLaw ord) d.1.val rankLength_ge (fullWildcard (V := V) (Y := Y) d).tuple)
    (a : Fin T → X)
    (ha : cell d.2 a = prefixTransition G ψLaw hYX fiber deleted ord hord hrank d T)
    (j : Fin T) :
    (d.2 j).2.2 (a j) = bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback
      (d.1, ⟨j,takePrefix (Nat.le_of_lt j.isLt) d.2⟩) (d.2 j).1 (d.2 j).2.2 := by
  let g := prefixBit G ψLaw ord d
  let r := prefixTransition G ψLaw hYX fiber deleted ord hord hrank d
  have hg (t : ℕ) (ht : t ≤ T) : Monotone (g t) := by
    simp only [g, prefixBit, dite_eq_left ht]
    exact good_monotone rankLength_ge d.1.property
      (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank) _
      (good_take_prefix _ _ rankLength_ge T le_rfl (vertices d.2) hgood t ht)
  have hr (t : ℕ) (ht : t ≤ T) : Transition (g t) (prefixCell t (sets d.2)) (r t) := by
    simp only [r, prefixTransition, dite_eq_left ht]
    exact transition_spec _ _ _ _
  have hh := full_transition_membership g (sets d.2) r T hg
    (prefixBit_lift G ψLaw ord d) hr a ha j
  have hgood' : Good (rankOrder G ψLaw ord) d.1.val rankLength_ge
      (.inl ⟨⟨j.val+1,by have := j.isLt; omega⟩,
        Fin.snoc (vertices (takePrefix (Nat.le_of_lt j.isLt) d.2)) (d.2 j).1⟩) := by
    convert good_take_prefix (rankOrder G ψLaw ord) d.1.val rankLength_ge T le_rfl
      (vertices d.2) hgood (j.val+1) (by have := j.isLt; omega) using 1
    congr 2
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp [vertices, takePrefix]
    · simp [vertices, takePrefix]
  have hvertices : takePrefix (by have := j.isLt; omega : j.val+1 ≤ T) (vertices d.2) =
      Fin.snoc (vertices (takePrefix (Nat.le_of_lt j.isLt) d.2)) (d.2 j).1 := by
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp [vertices, takePrefix]
    · simp [vertices, takePrefix]
  simp only [vertices_takePrefix] at hvertices
  have hgood'' := hgood'
  simp only [vertices_takePrefix] at hgood''
  have hb (b : Bool) : decide (b = true) = b := by cases b <;> rfl
  simp only [g, r, conditionedValue, stepFunction, prefixBit,
    dite_eq_left (Nat.le_of_lt j.isLt), dite_eq_left (show j.val+1 ≤ T by have := j.isLt; omega),
    prefixTransition, sets, dite_eq_left j.isLt, Set.mem_ofPred_eq,
    hb, bigFunction, conditionedBig, normalizedCondition, ↓reduceIte,
    bigStepBit, cell_takePrefix, vertices_takePrefix, hgood''] at hh ⊢
  rw [hvertices] at hh
  exact hh

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (deleted : OutputVertex (M := M) G ψLaw → Bool)
variable (ord : OutputVertex (M := M) G ψLaw → ℕ)
variable (hord : ∀ {a b}, deleted a = false → deleted b = false →
  OutputArc G ψLaw hYX fiber a b → ord a < ord b)
variable (hrank : ∀ r, deleted (.inl r) = false)

def favorable (d : Full U X M T N) : Bool := decide (
  0 < (fullLaw G ψLaw).weight d ∧ fullDeleted G ψLaw deleted d = false ∧
  Good (rankOrder G ψLaw ord) d.1.val rankLength_ge (fullWildcard (V := V) (Y := Y) d).tuple)

def prefixValue (fallback : X) (ψ : Emb (rankLength X T) N) (t : ℕ)
    (a : PrefixData U X M t) (u : U) (b : X → Bool) : ℝ :=
  if ht : t < T then
    if bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback (ψ,⟨⟨t,ht⟩,a⟩) u b
    then 1 else 0
  else 0

theorem favorable_count (fallback : X) (d : Full U X M T N)
    (hd : favorable G ψLaw deleted ord d = true) (i : Fin M) :
    bias i * T / (2*M) ≤ count i (prefixValue G ψLaw hYX fiber deleted ord hord hrank fallback)
      d.1 d.2 := by
  obtain ⟨hpos,hkeep,hgood⟩ := of_decide_eq_true hd
  have hk : deleted (.inr (.inl (.inl ⟨d,hpos⟩))) = false := by
    simpa only [fullDeleted, extend, dite_eq_left hpos] using hkeep
  obtain ⟨x,hx,hstar⟩ := full_unstarred G ψLaw hYX fiber deleted ord hord hrank ⟨d,hpos⟩ hk hgood
  have hm (j : Fin T) := full_membership G ψLaw hYX fiber deleted ord hord hrank fallback d hgood x
    (by simpa only [prefixTransition, prefixBit, dite_eq_left le_rfl, takePrefix_self, fullWildcard, cell] using hx) j
  have he : count i (prefixValue G ψLaw hYX fiber deleted ord hord hrank fallback) d.1 d.2 =
      (fullCount d.2 i x : ℝ) := by
    simp only [count, fullCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, prefixValue]
    apply Finset.sum_congr rfl
    intro j _
    simp only [dite_eq_left j.isLt]
    rw [← hm j]
    by_cases hi : (d.2 j).2.1 = i <;> cases (d.2 j).2.2 (x j) <;> simp [hi]
  rw [he]
  exact not_lt.mp (fun h => hstar ⟨i,h⟩)

theorem favorable_probability (D H ρ : ℝ) (hH : 0 < H)
    (hcost : H * (fullLaw G ψLaw).probability (fullDeleted G ψLaw deleted) ≤ D)
    (hbad : (fullLaw (M := M) G ψLaw).probability (fun d => decide (¬
      Good (rankOrder G ψLaw ord) d.1.val rankLength_ge
        (fullWildcard (V := V) (Y := Y) d).tuple)) ≤ ρ)
    (hnum : ρ + D/H ≤ 1/2) :
    1/2 ≤ (fullLaw G ψLaw).probability (favorable G ψLaw deleted ord) := by
  have he := expectation_mono_support (fullLaw (M := M) G ψLaw)
    (f := fun _ => (1:ℝ))
    (g := fun d => (if favorable G ψLaw deleted ord d then 1 else 0) +
      (if fullDeleted G ψLaw deleted d then 1 else 0) +
      (if decide (¬Good (rankOrder G ψLaw ord) d.1.val rankLength_ge
        (fullWildcard (V := V) (Y := Y) d).tuple) then 1 else 0)) (by
      intro d hp
      by_cases hg : Good (rankOrder G ψLaw ord) d.1.val rankLength_ge
        (fullWildcard (V := V) (Y := Y) d).tuple
      <;> cases hk : fullDeleted G ψLaw deleted d <;> simp [favorable,hp,hg,hk])
  simp only [expectation_add, ← probability_eq_expect, expectation_const] at he
  have hc : (fullLaw G ψLaw).probability (fullDeleted G ψLaw deleted) ≤ D/H :=
    (le_div_iff₀ hH).mpr (by simpa [mul_comm] using hcost)
  linarith

theorem full_acceptance (fallback : X)
    (hprob : 1/2 ≤ (fullLaw G ψLaw).probability (favorable G ψLaw deleted ord)) (i : Fin M) :
    bias i / 4 ≤ (common (M := M) G ψLaw).expectation (fun d =>
      (bigMarginal G).expectation (fun u => (subsetLaw i).probability
        (bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback d u))) := by
  have hh := acceptance_lower_bound ψLaw (bigMarginal G) subsetLaw i T
    (prefixValue G ψLaw hYX fiber deleted ord hord hrank fallback) (bias i) (bias_pos i).le
    (favorable G ψLaw deleted ord)
    (by intro ψ t a u b; unfold prefixValue; split_ifs <;> norm_num)
    hprob (fun d hd => by
      simpa only [Fintype.card_fin] using
        (favorable_count G ψLaw hYX fiber deleted ord hord hrank fallback d hd i))
  apply hh.trans_eq
  apply expectation_congr
  intro d
  change (bigMarginal G).expectation (fun u =>
    (subsetLaw i).expectation (prefixValue G ψLaw hYX fiber deleted ord hord hrank fallback
      d.1 d.2.1.val d.2.2 u)) = _
  apply expectation_congr
  intro u
  rw [probability_eq_expect]
  apply expectation_congr
  intro b
  simp only [prefixValue, dite_eq_left d.2.1.isLt]

end DirectedFeedback.Construction

noncomputable section
open scoped BigOperators
namespace DirectedFeedback.Ranks

def Homogeneous {C : Type*} (r : ℕ) (color : Finset ℕ → C) (s : Finset ℕ) : Prop :=
  ∃ c, ∀ t ⊆ s, t.card = r → color t = c

theorem end_homogeneous {C : Type*} [Fintype C] [Nonempty C] (r : ℕ)
    (R : ℕ → ℕ) (hR : ∀ k, ∀ (s : Finset ℕ), R k ≤ s.card →
      ∀ color : Finset ℕ → C, ∃ h ⊆ s, h.card = k ∧ Homogeneous r color h) :
    ∀ k, ∃ N, ∀ (s : Finset ℕ), N ≤ s.card → ∀ color : Finset ℕ → C,
      ∃ h ⊆ s, h.card = k ∧ ∃ tag : ℕ → C,
        ∀ t ⊆ h, t.card = r + 1 → ∀ a ∈ t,
          (∀ b ∈ t, a ≤ b) → color t = tag a := by
  classical
  intro k
  induction k with
  | zero =>
    refine ⟨0, ?_⟩
    intro s _ color
    refine ⟨∅, Finset.empty_subset _, rfl, (fun _ => color ∅), ?_⟩
    intro t ht hcard a ha _
    have : t = ∅ := Finset.subset_empty.mp ht
    simp [this] at ha
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨R N + 1, ?_⟩
    intro s hs color
    have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
    let v := s.min' hsne
    have hv : v ∈ s := Finset.min'_mem _ _
    have hrest : R N ≤ (s.erase v).card := by
      rw [Finset.card_erase_of_mem hv]
      omega
    obtain ⟨B, hBs, hBcard, c, hc⟩ := hR N (s.erase v) hrest (fun t => color (insert v t))
    obtain ⟨H, hHB, hHcard, tag, htag⟩ := hN B hBcard.ge color
    have hvH : v ∉ H := fun h => (Finset.mem_erase.mp (hBs (hHB h))).1 rfl
    have hvmin : ∀ a ∈ B, v < a := by
      intro a ha
      have hsa := Finset.mem_erase.mp (hBs ha)
      exact lt_of_le_of_ne (Finset.min'_le _ _ hsa.2) hsa.1.symm
    refine ⟨insert v H, Finset.insert_subset hv (hHB.trans (hBs.trans (Finset.erase_subset _ _))),
      by simp [hvH, hHcard], (fun a => if a = v then c else tag a), ?_⟩
    intro t ht hcard a ha hamin
    by_cases hvt : v ∈ t
    · have hat : a = v := by
        apply Nat.le_antisymm (hamin v hvt)
        rcases Finset.mem_insert.mp (ht ha) with hav | haH
        · exact hav ▸ le_rfl
        · exact (hvmin a (hHB haH)).le
      subst a
      have het : t.erase v ⊆ B := by
        intro a ha
        rcases Finset.mem_insert.mp (ht (Finset.mem_erase.mp ha).2) with hav | haH
        · exact False.elim ((Finset.mem_erase.mp ha).1 hav)
        · exact hHB haH
      have hecard : (t.erase v).card = r := by
        rw [Finset.card_erase_of_mem hvt, hcard]
        omega
      have h := hc (t.erase v) het hecard
      simpa [Finset.insert_erase hvt] using h
    · have htH : t ⊆ H := by
        intro b hb
        rcases Finset.mem_insert.mp (ht hb) with hbv | hbH
        · exact False.elim (hvt (hbv ▸ hb))
        · exact hbH
      have hav : a ≠ v := fun he => hvt (he ▸ ha)
      simp only [ite_eq_right hav]
      exact htag t htH hcard a ha hamin

theorem finite_ramsey {C : Type*} [Fintype C] [Nonempty C] :
    ∀ r k : ℕ, ∃ N ≥ k, ∀ (s : Finset ℕ), N ≤ s.card →
      ∀ color : Finset ℕ → C, ∃ h ⊆ s, h.card = k ∧ Homogeneous r color h := by
  classical
  intro r
  induction r with
  | zero =>
    intro k
    refine ⟨k, le_rfl, ?_⟩
    intro s hs color
    obtain ⟨h, hhs, hh⟩ := Finset.exists_subset_card_eq hs
    refine ⟨h, hhs, hh, color ∅, ?_⟩
    intro t _ ht
    rw [Finset.card_eq_zero.mp ht]
  | succ r ih =>
    choose R hRk hR using ih
    intro k
    obtain ⟨N, hN⟩ := end_homogeneous r R hR (Fintype.card C * k)
    refine ⟨max N k, le_max_right _ _, ?_⟩
    intro s hs color
    obtain ⟨H, hHs, hHcard, tag, htag⟩ := hN s ((le_max_left _ _).trans hs) color
    obtain ⟨c, _, hc⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := H) (t := (Finset.univ : Finset C)) (f := tag)
      (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty
      (by simpa using hHcard.ge : Fintype.card C * k ≤ H.card)
    obtain ⟨h, hsub, hcard⟩ := Finset.exists_subset_card_eq hc
    refine ⟨h, hsub.trans (Finset.filter_subset _ _ |>.trans hHs), hcard, c, ?_⟩
    intro t ht htcard
    have htne : t.Nonempty := Finset.card_pos.mp (by omega)
    let a := t.min' htne
    have ha : a ∈ t := Finset.min'_mem _ _
    have ha' := Finset.mem_filter.mp (hsub (ht ha))
    rw [htag t (ht.trans (hsub.trans (Finset.filter_subset _ _))) htcard a ha
      (fun b hb => Finset.min'_le _ _ hb), ha'.2]

end DirectedFeedback.Ranks

noncomputable section
open scoped BigOperators
namespace DirectedFeedback.Ranks

variable {I J : Type*} [Fintype I] [Fintype J]

def payoff (a : I → J → ℝ) (x : I → ℝ) (y : J → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * y j * a i j

theorem payoff_left (a : I → J → ℝ) (x x' : I → ℝ) (y : J → ℝ) (r s : ℝ) :
    payoff a (r • x + s • x') y = r * payoff a x y + s * payoff a x' y := by
  simp only [payoff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem payoff_right (a : I → J → ℝ) (x : I → ℝ) (y y' : J → ℝ) (r s : ℝ) :
    payoff a x (r • y + s • y') = r * payoff a x y + s * payoff a x y' := by
  simp only [payoff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

def probabilitySimplex (Index : Type*) [Fintype Index] : Set (Index → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

theorem single_mem_probabilitySimplex {Index : Type*} [Fintype Index] [DecidableEq Index]
    (index : Index) : Pi.single index 1 ∈ probabilitySimplex Index :=
  ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ => le_rfl⟩, by simp⟩

theorem convex_probabilitySimplex (Index : Type*) [Fintype Index] :
    Convex ℝ (probabilitySimplex Index) := by
  intro left hleft right hright weightLeft weightRight hweightLeft hweightRight hsum
  refine ⟨fun index => ?_, ?_⟩
  · exact add_nonneg (mul_nonneg hweightLeft (hleft.1 index))
      (mul_nonneg hweightRight (hright.1 index))
  · simp_rw [Pi.add_apply, Pi.smul_apply]
    rwa [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum,
      hleft.2, hright.2, smul_eq_mul, smul_eq_mul, mul_one, mul_one]

theorem isCompact_probabilitySimplex (Index : Type*) [Fintype Index] :
    IsCompact (probabilitySimplex Index) := by
  have hform : probabilitySimplex Index =
      (⋂ index : Index, {weights : Index → ℝ | 0 ≤ weights index}) ∩
        {weights | ∑ index, weights index = 1} := by
    ext weights
    simp only [probabilitySimplex, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  apply IsCompact.of_isClosed_subset (s := Set.Icc (0 : Index → ℝ) 1) isCompact_Icc
  · rw [hform]
    exact (isClosed_iInter fun index =>
      isClosed_le continuous_const (continuous_apply index)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  · intro weights hweights
    refine ⟨hweights.1, fun index => ?_⟩
    change weights index ≤ 1
    rw [← hweights.2]
    exact Finset.single_le_sum (fun other _ => hweights.1 other) (Finset.mem_univ index)

theorem finite_minimax [Nonempty I] [Nonempty J] (a : I → J → ℝ) (δ : ℝ)
    (hresponse : ∀ y ∈ probabilitySimplex J, ∃ i, (∑ j, y j * a i j) ≤ δ) :
    ∃ x ∈ probabilitySimplex I, ∀ j, (∑ i, x i * a i j) ≤ δ := by
  classical
  have hI : (probabilitySimplex I).Nonempty := ⟨Pi.single (Classical.arbitrary I) 1,
    single_mem_probabilitySimplex _⟩
  have hJ : (probabilitySimplex J).Nonempty := ⟨Pi.single (Classical.arbitrary J) 1,
    single_mem_probabilitySimplex _⟩
  have hleft (y : J → ℝ) : Continuous (fun x : I → ℝ => payoff a x y) := by
    unfold payoff
    fun_prop
  have hright (x : I → ℝ) : Continuous (fun y : J → ℝ => payoff a x y) := by
    unfold payoff
    fun_prop
  have hcLeft (y : J → ℝ) : ConvexOn ℝ (probabilitySimplex I) (fun x => payoff a x y) := by
    refine ⟨convex_probabilitySimplex _, ?_⟩
    intro x _ x' _ r s _ _ _
    exact (payoff_left a x x' y r s).le
  have hcRight (x : I → ℝ) : ConcaveOn ℝ (probabilitySimplex J) (fun y => payoff a x y) := by
    refine ⟨convex_probabilitySimplex _, ?_⟩
    intro y _ y' _ r s _ _ _
    exact (payoff_right a x y y' r s).ge
  obtain ⟨x, hx, y, hy, hxy⟩ := Sion.exists_isSaddlePointOn hI (convex_probabilitySimplex _)
    (isCompact_probabilitySimplex _) (fun y _ => (hleft y).continuousOn.lowerSemicontinuousOn)
    (fun y _ => (hcLeft y).quasiconvexOn) (convex_probabilitySimplex _) hJ
    (isCompact_probabilitySimplex _) (fun x _ => (hright x).continuousOn.upperSemicontinuousOn)
    (fun x _ => (hcRight x).quasiconcaveOn)
  obtain ⟨i, hi⟩ := hresponse y hy
  refine ⟨x, hx, ?_⟩
  intro j
  have hsaddle := hxy (Pi.single i 1) (single_mem_probabilitySimplex _)
    (Pi.single j 1) (single_mem_probabilitySimplex _)
  have hpureLeft : payoff a (Pi.single i 1) y = ∑ j, y j * a i j := by
    simp [payoff, Pi.single_apply, ite_mul]
  have hpureRight : payoff a x (Pi.single j 1) = ∑ i, x i * a i j := by
    simp [payoff, Pi.single_apply, mul_ite, ite_mul]
  rw [hpureLeft, hpureRight] at hsaddle
  exact hsaddle.trans hi

theorem rational_simplex_approximation [Nonempty I] (x : I → ℝ)
    (hx : x ∈ probabilitySimplex I) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : I → ℚ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧
      (∑ i, |(q i : ℝ) - x i|) < ε := by
  classical
  let n : ℝ := Fintype.card I
  have hn : 0 < n := by
    change 0 < (Fintype.card I : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card I)
  let d := ε / (2 * n)
  have hd : 0 < d := by dsimp [d]; positivity
  have hex (i : I) : ∃ q : ℚ, 0 ≤ q ∧ (q : ℝ) ≤ x i ∧ x i - q < d := by
    by_cases hxi : x i = 0
    · exact ⟨0, le_rfl, by simp [hxi], by simpa [hxi] using hd⟩
    have hp : 0 < x i := lt_of_le_of_ne (hx.1 i) (Ne.symm hxi)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (x i - d) < x i by
      exact max_lt hp (by linarith))
    refine ⟨q, ?_, hq2.le, ?_⟩
    · exact_mod_cast (le_max_left _ _).trans hq1.le
    · have hh := (le_max_right _ _).trans_lt hq1
      linarith
  choose q hqnonneg hqle hqerr using hex
  let deficit : ℚ := 1 - ∑ i, q i
  have hdef : 0 ≤ deficit := by
    have hsum : (∑ i, (q i : ℝ)) ≤ 1 := by
      rw [← hx.2]
      exact Finset.sum_le_sum (fun i _ => hqle i)
    dsimp [deficit]
    exact_mod_cast (sub_nonneg.mpr hsum)
  have herr : (deficit : ℝ) < ε / 2 := by
    have hh := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hqerr i)
    have hdid : (∑ _i : I, d) = ε / 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change n * (ε / (2 * n)) = ε / 2
      field_simp
    rw [Finset.sum_sub_distrib, hx.2, hdid] at hh
    simpa [deficit] using hh
  let i₀ : I := Classical.arbitrary I
  let q' : I → ℚ := fun i => q i + if i = i₀ then deficit else 0
  refine ⟨q', (fun i => add_nonneg (hqnonneg i) (by split_ifs <;> positivity)), ?_, ?_⟩
  · simp [q', Finset.sum_add_distrib, deficit]
  · calc
      (∑ i, |(q' i : ℝ) - x i|) ≤
          ∑ i, ((x i - (q i : ℝ)) + if i = i₀ then (deficit : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro i _
        dsimp [q']
        push_cast
        split_ifs with hi
        · have ht := abs_add_le ((q i : ℝ) - x i) (deficit : ℝ)
          rw [abs_of_nonpos (sub_nonpos.mpr (hqle i)),
            abs_of_nonneg (show (0 : ℝ) ≤ (deficit : ℝ) by exact_mod_cast hdef)] at ht
          calc
            |(q i : ℝ) + (deficit : ℝ) - x i| =
                |((q i : ℝ) - x i) + (deficit : ℝ)| := by congr 1; ring
            _ ≤ -((q i : ℝ) - x i) + (deficit : ℝ) := ht
            _ = _ := by ring
        · rw [Rat.cast_zero, add_zero, add_zero, abs_of_nonpos (sub_nonpos.mpr (hqle i))]
          linarith
      _ = 2 * deficit := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hx.2]
        simp [deficit]
        ring
      _ < ε := by linarith

end DirectedFeedback.Ranks

noncomputable section
open scoped BigOperators
namespace DirectedFeedback.Ranks

abbrev Triple (n : ℕ) := {s : Finset (Fin n) // s.card = 3}
abbrev Increasing (L N : ℕ) := {f : Fin L → Fin N // StrictMono f}

theorem triple_nonempty {L : ℕ} (hL : 3 ≤ L) : Nonempty (Triple L) := by
  classical
  refine ⟨⟨Finset.univ.image (Fin.castLE hL), ?_⟩⟩
  rw [Finset.card_image_of_injective _ (Fin.castLE_injective hL)]
  simp

def toFinite (N : ℕ) (s : Finset ℕ) : Finset (Fin N) :=
  s.preimage Fin.val Fin.val_injective.injOn

@[simp] theorem toFinite_image {N : ℕ} (s : Finset (Fin N)) :
    toFinite N (s.image Fin.val) = s := by
  classical
  ext x
  simp [toFinite, Fin.val_inj]

abbrev RankTest (L N : ℕ) := (Triple L × Triple L) × Finset (Finset (Fin N))

def rankPayoff {L N : ℕ} (ψ : Increasing L N) (t : RankTest L N) : ℝ :=
  (if t.1.1.val.image ψ.val ∈ t.2 then 1 else 0) -
  (if t.1.2.val.image ψ.val ∈ t.2 then 1 else 0)

theorem rankPayoff_abs {L N : ℕ} (ψ : Increasing L N) (t : RankTest L N) :
    |rankPayoff ψ t| ≤ 1 := by
  unfold rankPayoff
  split_ifs <;> norm_num

theorem bucket_close (b : ℕ) (hb : 0 < b) (x y : ℝ) (_hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ⌊(b : ℝ) * x⌋₊ = ⌊(b : ℝ) * y⌋₊) : x - y ≤ 1 / b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 := Nat.lt_floor_add_one ((b : ℝ) * x)
  have h2 := Nat.floor_le (mul_nonneg hb'.le hy)
  rw [h] at h1
  apply (le_div_iff₀ hb').mpr
  nlinarith

theorem rank_spreading (L : ℕ) (hL : 3 ≤ L) (η : ℝ) (hη : 0 < η) :
    ∃ N ≥ L, ∃ μ : Increasing L N → ℚ,
      (∀ ψ, 0 ≤ μ ψ) ∧ (∑ ψ, μ ψ = 1) ∧
      ∀ I I' : Triple L, ∀ A : Finset (Finset (Fin N)),
        |(∑ ψ, (μ ψ : ℝ) * if I.val.image ψ.val ∈ A then 1 else 0) -
          (∑ ψ, (μ ψ : ℝ) * if I'.val.image ψ.val ∈ A then 1 else 0)| ≤ η := by
  classical
  let : Nonempty (Triple L) := triple_nonempty hL
  let P := Triple L × Triple L
  let c : ℝ := Fintype.card P
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card P)
  obtain ⟨b₀, hb₀⟩ := exists_nat_one_div_lt (show 0 < η / (4 * c) by positivity)
  let b := b₀ + 1
  have hb : 0 < b := Nat.succ_pos _
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hcb : c * (1 / (b : ℝ)) < η / 4 := by
    have hh := mul_lt_mul_of_pos_left hb₀ hc
    have heq : c * (η / (4 * c)) = η / 4 := by field_simp
    simpa [b, heq] using hh
  obtain ⟨N, hNL, hN⟩ := finite_ramsey (C := P → Fin (b + 1)) 3 L
  let : Nonempty (Increasing L N) := ⟨⟨Fin.castLE hNL, fun _ _ h => h⟩⟩
  have hresponse : ∀ τ ∈ probabilitySimplex (RankTest L N), ∃ ψ : Increasing L N,
      (∑ t, τ t * rankPayoff ψ t) ≤ η / 4 := by
    intro τ hτ
    let q (p : P) (Z : Finset (Fin N)) : ℝ :=
      ∑ A : Finset (Finset (Fin N)), τ (p, A) * if Z ∈ A then 1 else 0
    have hq0 (p : P) (Z : Finset (Fin N)) : 0 ≤ q p Z := by
      apply Finset.sum_nonneg
      intro A _
      split_ifs <;> simp [hτ.1 (p, A)]
    have hq1 (p : P) (Z : Finset (Fin N)) : q p Z ≤ 1 := by
      calc
        q p Z ≤ ∑ A : Finset (Finset (Fin N)), τ (p, A) := by
          apply Finset.sum_le_sum
          intro A _
          split_ifs <;> simp [hτ.1 (p, A)]
        _ ≤ ∑ p' : P, ∑ A : Finset (Finset (Fin N)), τ (p', A) := by
          exact Finset.single_le_sum (fun p' _ => Finset.sum_nonneg (fun A _ => hτ.1 (p', A)))
            (Finset.mem_univ p)
        _ = 1 := by
          have hh := hτ.2
          rw [Fintype.sum_prod_type] at hh
          exact hh
    let color (s : Finset ℕ) (p : P) : Fin (b + 1) :=
      ⟨⌊(b : ℝ) * q p (toFinite N s)⌋₊, by
        have hh := Nat.floor_mono (mul_le_mul_of_nonneg_left (hq1 p (toFinite N s)) hb'.le)
        simp only [mul_one, Nat.floor_natCast] at hh
        omega⟩
    obtain ⟨H, hHN, hHcard, tag, htag⟩ := hN (Finset.range N) (by simp) color
    let ψ₀ : Fin L → Fin N := fun i =>
      ⟨H.orderEmbOfFin hHcard i, Finset.mem_range.mp (hHN (H.orderEmbOfFin_mem hHcard i))⟩
    have hψ : StrictMono ψ₀ := fun i j hij => (H.orderEmbOfFin hHcard).strictMono hij
    let ψ : Increasing L N := ⟨ψ₀, hψ⟩
    have hmono (I : Triple L) : color ((I.val.image ψ.val).image Fin.val) = tag := by
      apply htag
      · intro a ha
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
        exact H.orderEmbOfFin_mem hHcard i
      · rw [Finset.card_image_of_injective _ Fin.val_injective,
          Finset.card_image_of_injective _ hψ.injective]
        exact I.property
    have hclose (p : P) : q p (p.1.val.image ψ.val) - q p (p.2.val.image ψ.val) ≤ 1 / b := by
      apply bucket_close b hb _ _ (hq0 _ _) (hq0 _ _)
      have heq := congrArg (fun f => (f p).val) ((hmono p.1).trans (hmono p.2).symm)
      simpa only [color, toFinite_image] using heq
    refine ⟨ψ, ?_⟩
    calc
      (∑ t, τ t * rankPayoff ψ t) =
          ∑ p : P, (q p (p.1.val.image ψ.val) - q p (p.2.val.image ψ.val)) := by
        rw [Fintype.sum_prod_type]
        simp only [rankPayoff, mul_sub, Finset.sum_sub_distrib, q]
        rfl
      _ ≤ ∑ _p : P, (1 / (b : ℝ)) := Finset.sum_le_sum (fun p _ => hclose p)
      _ = c * (1 / (b : ℝ)) := by simp [c]
      _ ≤ η / 4 := hcb.le
  obtain ⟨x, hx, hxbound⟩ := finite_minimax rankPayoff (η / 4) hresponse
  obtain ⟨μ, hμ0, hμ1, hμerr⟩ := rational_simplex_approximation x hx (η / 2) (by positivity)
  have hμbound (t : RankTest L N) : (∑ ψ, (μ ψ : ℝ) * rankPayoff ψ t) < η := by
    have hle : (∑ ψ, (μ ψ : ℝ) * rankPayoff ψ t) ≤
        (∑ ψ, x ψ * rankPayoff ψ t) + ∑ ψ, |(μ ψ : ℝ) - x ψ| := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro ψ _
      have hh : ((μ ψ : ℝ) - x ψ) * rankPayoff ψ t ≤ |(μ ψ : ℝ) - x ψ| := by
        calc
          _ ≤ |((μ ψ : ℝ) - x ψ) * rankPayoff ψ t| := le_abs_self _
          _ = |(μ ψ : ℝ) - x ψ| * |rankPayoff ψ t| := abs_mul _ _
          _ ≤ |(μ ψ : ℝ) - x ψ| * 1 :=
            mul_le_mul_of_nonneg_left (rankPayoff_abs ψ t) (abs_nonneg _)
          _ = _ := mul_one _
      linarith
    have hh := hxbound t
    linarith
  refine ⟨N, hNL, μ, hμ0, hμ1, ?_⟩
  intro I I' A
  have h1 := hμbound ((I, I'), A)
  have h2 := hμbound ((I', I), A)
  simp only [rankPayoff, mul_sub, Finset.sum_sub_distrib] at h1 h2
  exact abs_le.mpr ⟨by linarith, h1.le⟩

end DirectedFeedback.Ranks
open scoped Classical
namespace DirectedFeedback.Ranks
open DirectedFeedback.SourceProbability
open DirectedFeedback.SourceProbability.FiniteDistribution

def Spreads {L N : ℕ} (μ : FiniteDistribution (Increasing L N)) (η : ℝ) : Prop :=
  ∀ I I' : Triple L, ∀ A : Finset (Finset (Fin N)),
    |μ.probability (fun ψ => decide (I.val.image ψ.val ∈ A)) -
      μ.probability (fun ψ => decide (I'.val.image ψ.val ∈ A))| ≤ η

theorem exists_spreading_law (L : ℕ) (hL : 3 ≤ L) (η : ℝ) (hη : 0 < η) :
    ∃ N ≥ L, ∃ μ : FiniteDistribution (Increasing L N), Spreads μ η ∧
      ∀ ψ, ∃ q : ℚ, μ.weight ψ = q := by
  obtain ⟨N, hNL, q, hq0, hq1, hq⟩ := rank_spreading L hL η hη
  let μ : FiniteDistribution (Increasing L N) :=
    ⟨fun ψ => q ψ, fun ψ => by exact_mod_cast hq0 ψ, by exact_mod_cast hq1⟩
  refine ⟨N, hNL, μ, ?_, fun ψ => ⟨q ψ, rfl⟩⟩
  intro I I' A
  convert hq I I' A using 1
  simp only [probability, μ, decide_eq_true_eq, mul_ite, mul_one, mul_zero]

theorem triple_data_processing {L N : ℕ} {η : ℝ}
    (μ : FiniteDistribution (Increasing L N)) (hs : Spreads μ η)
    (f g : Fin 3 → Fin L) (hf : StrictMono f) (hg : StrictMono g)
    (K : (Fin 3 → Fin N) → Bool) :
    |μ.probability (fun ψ => K (ψ.val ∘ f)) -
      μ.probability (fun ψ => K (ψ.val ∘ g))| ≤ η := by
  classical
  let I (f : Fin 3 → Fin L) (hf : StrictMono f) : Triple L :=
    ⟨Finset.univ.image f, by rw [Finset.card_image_of_injective _ hf.injective]; simp⟩
  let event (s : Finset (Fin N)) : Bool :=
    if h : s.card = 3 then K (s.orderEmbOfFin h) else false
  let A : Finset (Finset (Fin N)) := Finset.univ.filter (fun s => event s = true)
  have hevent (f : Fin 3 → Fin L) (hf : StrictMono f) (ψ : Increasing L N) :
      decide ((I f hf).val.image ψ.val ∈ A) = K (ψ.val ∘ f) := by
    have hmono := ψ.property.comp hf
    have hc : ((I f hf).val.image ψ.val).card = 3 := by
      rw [Finset.card_image_of_injective _ ψ.property.injective]
      exact (I f hf).property
    have heq := Finset.orderEmbOfFin_unique hc (f := ψ.val ∘ f)
      (fun j => by simp [I]) hmono
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    have hh : event ((I f hf).val.image ψ.val) = K (ψ.val ∘ f) := by
      dsimp [event]
      rw [dite_eq_left hc, ← heq]
    simp [hh]
  simpa only [hevent] using hs (I f hf) (I g hg) A

def tripleVector {L : ℕ} (a c h : Fin L) : Fin 3 → Fin L := ![a, c, h]

theorem tripleVector_strict {L : ℕ} {a c h : Fin L} (hac : a < c) (hch : c < h) :
    StrictMono (tripleVector a c h) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [tripleVector]
  exact hac.trans hch

end DirectedFeedback.Ranks

namespace DirectedFeedback.RankGraph
open DirectedFeedback.SourceProbability
open DirectedFeedback.SourceProbability.FiniteDistribution
open DirectedFeedback.Ranks
variable {U V X Y : Type} {T N L : ℕ}

theorem comparison_expectations {η : ℝ}
    (μ : FiniteDistribution (Increasing L N)) (hs : Spreads μ η)
    (ord : Rank U V X Y T N → ℕ) (d : Tuple U V T)
    (E : Set (Domain U V X Y T d)) (a c h a' c' h' : Fin L)
    (hac : a < c) (hch : c < h) (hac' : a' < c') (hch' : c' < h') :
    |μ.probability (fun ψ => compareBit ord ψ.val d E a c h) -
      μ.probability (fun ψ => compareBit ord ψ.val d E a' c' h')| ≤ η := by
  classical
  exact triple_data_processing μ hs _ _ (tripleVector_strict hac hch)
    (tripleVector_strict hac' hch')
    (fun r => decide (ord (vertex d (fun lambda => if lambda ∈ E then r 0 else r 2)) <
      ord (marker (r 1))))

theorem ordered_disagreement {I : Type*} [Fintype I]
    (μ : FiniteDistribution I) (p q : I → Bool)
    (hpq : (∀ i, p i ≤ q i) ∨ (∀ i, q i ≤ p i)) {η : ℝ}
    (hc : |μ.probability p - μ.probability q| ≤ η) :
    μ.probability (fun i => decide (p i ≠ q i)) ≤ η := by
  rcases hpq with h | h
  · rw [indicator_difference μ p q (fun i => (Bool.le_iff_imp.mp (h i)))]
    exact (le_abs_self _).trans (by rwa [abs_sub_comm])
  · have he := indicator_difference μ q p (fun i => (Bool.le_iff_imp.mp (h i)))
    have hh : (fun i => decide (p i ≠ q i)) = (fun i => decide (q i ≠ p i)) := by
      funext i; simp [ne_comm]
    rw [hh, he]
    exact (le_abs_self _).trans hc

theorem compare_marker_mono (ord : Rank U V X Y T N → ℕ)
    (hord : ∀ {a b}, Arc a b → ord a < ord b)
    (ψ : Increasing L N) (d : Tuple U V T) (E : Set (Domain U V X Y T d))
    (a h : Fin L) {c c' : Fin L} (hc : c ≤ c') :
    compareBit ord ψ.val d E a c h ≤ compareBit ord ψ.val d E a c' h := by
  rcases hc.eq_or_lt with rfl | hc
  · exact le_rfl
  rw [Bool.le_iff_imp]
  simp only [compareBit, decide_eq_true_eq]
  exact fun hh => hh.trans (hord (marker_arc (ψ.property hc)))

theorem comparison_disagreement (hL : 30 ≤ L) {η : ℝ}
    (μ : FiniteDistribution (Increasing L N)) (hs : Spreads μ η)
    (ord : Rank U V X Y T N → ℕ)
    (hord : ∀ {a b}, Arc a b → ord a < ord b)
    (d : Tuple U V T) (E : Set (Domain U V X Y T d))
    (a c h : Fin L) (hu : usable a c h) :
    μ.probability (fun ψ => decide (compareBit ord ψ.val d E a c h ≠
      referenceBit ord ψ.val hL d E)) ≤ 3 * η := by
  have hua := hu.1
  have hac := hu.2.1
  have huc := hu.2.2.1
  have hucL := hu.2.2.2.1
  have huh := hu.2.2.2.2
  let z : Fin L := ⟨0, by omega⟩
  let lo : Fin L := ⟨1, by omega⟩
  let ref : Fin L := ⟨14, by omega⟩
  let hi : Fin L := ⟨L - 2, by omega⟩
  let cp : Fin L := ⟨c.val + 1, by omega⟩
  let A0 (ψ : Increasing L N) := compareBit ord ψ.val d E lo ref hi
  let A1 (ψ : Increasing L N) := compareBit ord ψ.val d E lo c hi
  let A2 (ψ : Increasing L N) := compareBit ord ψ.val d E z c cp
  let A3 (ψ : Increasing L N) := compareBit ord ψ.val d E a c h
  have h01 : μ.probability (fun ψ => decide (A0 ψ ≠ A1 ψ)) ≤ η := by
    apply ordered_disagreement
    · rcases le_total ref c with hc | hc
      · exact Or.inl (fun ψ => compare_marker_mono ord hord ψ d E lo hi hc)
      · exact Or.inr (fun ψ => compare_marker_mono ord hord ψ d E lo hi hc)
    · exact comparison_expectations μ hs ord d E lo ref hi lo c hi
        (by simp [Fin.lt_def, lo, ref]) (by simp [Fin.lt_def, ref, hi]; omega)
        (by simp [Fin.lt_def, lo]; omega) (by simp [Fin.lt_def, hi]; omega)
  have h12 : μ.probability (fun ψ => decide (A1 ψ ≠ A2 ψ)) ≤ η := by
    apply ordered_disagreement
    · apply Or.inl
      intro ψ
      apply compareBit_mono_of_arc hord
      exact twoLevel_arc ψ.property d (Set.Subset.refl _) (by simp [Fin.lt_def, z, lo])
        (by simp [Fin.lt_def, z, hi]; omega) (by simp [Fin.lt_def, cp, hi]; omega)
    · exact comparison_expectations μ hs ord d E lo c hi z c cp
        (by simp [Fin.lt_def, lo]; omega) (by simp [Fin.lt_def, hi]; omega)
        (by simp [Fin.lt_def, z]; omega) (by simp [Fin.lt_def, cp])
  have h23 : μ.probability (fun ψ => decide (A2 ψ ≠ A3 ψ)) ≤ η := by
    apply ordered_disagreement
    · apply Or.inr
      intro ψ
      apply compareBit_mono_of_arc hord
      exact twoLevel_arc ψ.property d (Set.Subset.refl _) (by simp [Fin.lt_def, z]; omega)
        (by simp [Fin.lt_def, z]; omega) (by simp [Fin.lt_def, cp]; omega)
    · exact comparison_expectations μ hs ord d E z c cp a c h
        (by simp [Fin.lt_def, z]; omega) (by simp [Fin.lt_def, cp]) hac (by omega)
  have hh := probability_disagree_triangle μ A0 A1 A3
  have hh' := probability_disagree_triangle μ A1 A2 A3
  have he : μ.probability (fun ψ => decide (A0 ψ ≠ A3 ψ)) ≤ 3 * η := by linarith
  calc
    _ = μ.probability (fun ψ => decide (A0 ψ ≠ A3 ψ)) := by
      apply congrArg (μ.probability)
      funext ψ
      change decide (A3 ψ ≠ A0 ψ) = decide (A0 ψ ≠ A3 ψ)
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      exact ne_comm
    _ ≤ _ := he

theorem goodness_probability [Fintype X] [Fintype Y]
    (hL : 30 ≤ L) {η : ℝ} (hη : 0 ≤ η)
    (μ : FiniteDistribution (Increasing L N)) (hs : Spreads μ η)
    (ord : Rank U V X Y T N → ℕ)
    (hord : ∀ {a b}, Arc a b → ord a < ord b) (d : Tuple U V T) :
    μ.probability (fun ψ => decide (¬Good ord ψ.val hL d)) ≤
      3 * η * (L : ℝ)^3 * 2^(Fintype.card (Domain U V X Y T d)) := by
  classical
  let J := Set (Domain U V X Y T d) × Fin L × Fin L × Fin L
  let bad (j : J) (ψ : Increasing L N) : Bool :=
    decide (usable j.2.1 j.2.2.1 j.2.2.2 ∧
      compareBit ord ψ.val d j.1 j.2.1 j.2.2.1 j.2.2.2 ≠ referenceBit ord ψ.val hL d j.1)
  have hb (j : J) : μ.probability (bad j) ≤ 3 * η := by
    by_cases hu : usable j.2.1 j.2.2.1 j.2.2.2
    · simpa only [bad, hu, true_and] using comparison_disagreement hL μ hs ord hord d j.1
        j.2.1 j.2.2.1 j.2.2.2 hu
    · simp only [bad, hu, false_and, decide_false, probability_false]
      positivity
  calc
    _ ≤ μ.probability (fun ψ => decide (∃ j : J, bad j ψ = true)) := by
      apply probability_mono
      intro ψ hp
      have hn : ¬Good ord ψ.val hL d := of_decide_eq_true hp
      unfold Good at hn
      push Not at hn
      obtain ⟨E, a, c, h, hu, he⟩ := hn
      apply decide_eq_true
      refine ⟨(E, a, c, h), ?_⟩
      simpa only [bad, decide_eq_true_eq] using And.intro hu he
    _ ≤ ∑ j : J, μ.probability (bad j) := probability_exists_le_sum μ bad
    _ ≤ ∑ _j : J, 3 * η := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp [J, Fintype.card_set, Nat.cast_mul, Nat.cast_pow]; ring

end DirectedFeedback.RankGraph

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.RankGraph
open DirectedFeedback.SourceProbability FiniteDistribution
open Ranks
variable {U V X Y : Type} [Fintype X] [Fintype Y] [Nonempty X]
variable {T N L : ℕ}

theorem domain_card_bound (hYX : Fintype.card Y ≤ Fintype.card X) (d : Tuple U V T) :
    Fintype.card (Domain U V X Y T d) ≤ (Fintype.card X)^T := by
  have hm : 1 ≤ Fintype.card X := Fintype.card_pos
  rcases d with ⟨t,s⟩ | ⟨t,s,v⟩
  · change Fintype.card (Fin t.val → X) ≤ _
    rw [Fintype.card_fun, Fintype.card_fin]
    exact Nat.pow_le_pow_right hm (by have := t.isLt; omega)
  · change Fintype.card ((Fin t.val → X) × Y) ≤ _
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    calc
      _ ≤ (Fintype.card X)^t.val * Fintype.card X := Nat.mul_le_mul_left _ hYX
      _ = (Fintype.card X)^(t.val+1) := (pow_succ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hm t.isLt

theorem goodness_bound (hYX : Fintype.card Y ≤ Fintype.card X)
    (hL : 30 ≤ L) {η ρ : ℝ} (hη : 0 ≤ η)
    (haccuracy : 3*η*(L:ℝ)^3*2^((Fintype.card X)^T) ≤ ρ)
    (μ : FiniteDistribution (Increasing L N)) (hs : Spreads μ η)
    (ord : Rank U V X Y T N → ℕ)
    (hord : ∀ {a b}, Arc a b → ord a < ord b) (d : Tuple U V T) :
    μ.probability (fun ψ => decide (¬Good ord ψ.val hL d)) ≤ ρ := by
  apply (goodness_probability hL hη μ hs ord hord d).trans
  apply le_trans _ haccuracy
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (domain_card_bound hYX d)

theorem sampled_goodness {Ω : Type*} [Fintype Ω]
    (hYX : Fintype.card Y ≤ Fintype.card X) (hL : 30 ≤ L) {η ρ : ℝ} (hη : 0 ≤ η)
    (haccuracy : 3*η*(L:ℝ)^3*2^((Fintype.card X)^T) ≤ ρ)
    (μ : FiniteDistribution (Increasing L N)) (hs : Spreads μ η)
    (ν : FiniteDistribution Ω) (tuple : Ω → Tuple U V T)
    (ord : Rank U V X Y T N → ℕ)
    (hord : ∀ {a b}, Arc a b → ord a < ord b) :
    (μ.product ν).probability (fun a => decide (¬Good ord a.1.val hL (tuple a.2))) ≤ ρ := by
  rw [probability_eq_expect, expectation_product, expectation_comm]
  simp_rw [← probability_eq_expect]
  calc
    _ ≤ ν.expectation (fun _ => ρ) := expectation_mono _ (fun a =>
      goodness_bound hYX hL hη haccuracy μ hs ord hord (tuple a))
    _ = _ := expectation_const _ _

end DirectedFeedback.RankGraph

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Ranks
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (deleted : OutputVertex (M := M) G ψLaw → Bool)
variable (ord : OutputVertex (M := M) G ψLaw → ℕ)
variable (hord : ∀ {a b}, deleted a = false → deleted b = false →
  OutputArc G ψLaw hYX fiber a b → ord a < ord b)
variable (hrank : ∀ r, deleted (.inl r) = false)
variable {η ρ : ℝ} (hη : 0 ≤ η)
variable (haccuracy : 3*η*(rankLength X T : ℝ)^3*2^((Fintype.card X)^T) ≤ ρ)
variable (hs : Spreads ψLaw η)

include hord hrank hη haccuracy hs in
theorem full_badness :
    (fullLaw (M := M) G ψLaw).probability (fun d => decide (¬
      Good (rankOrder G ψLaw ord) d.1.val rankLength_ge
        (fullWildcard (V := V) (Y := Y) d).tuple)) ≤ ρ := by
  exact sampled_goodness hYX rankLength_ge hη haccuracy ψLaw hs
    ((atomLaw (bigMarginal G) subsetLaw).iid T)
    (fun a => Sum.inl ⟨⟨T,by omega⟩,vertices a⟩)
    (rankOrder G ψLaw ord) (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank)

end DirectedFeedback.Construction
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
