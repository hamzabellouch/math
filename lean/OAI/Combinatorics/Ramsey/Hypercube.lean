import Mathlib

namespace OAI

/-! Finite Ramsey bounds, cross-edge colorings, and counterexample sequences for a proposed linear hypercube Ramsey bound. -/

namespace HypercubeRamsey

abbrev CubeVertex (n : ℕ) := Fin n → Bool

def cube (n : ℕ) : SimpleGraph (CubeVertex n) where
  Adj x y := hammingDist x y = 1
  symm := ⟨fun x y h => (hammingDist_comm y x).trans h⟩
  loopless := ⟨by intro x; simp⟩

def RamseyProperty {V : Type*} (H : SimpleGraph V) (M : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin M), Nonempty (H.Copy G) ∨ Nonempty (H.Copy Gᶜ)

noncomputable def ramseyNumber {V : Type*} [Fintype V] (H : SimpleGraph V) : ℕ :=
  sInf {M : ℕ | 0 < M ∧ RamseyProperty H M}

open Finset

theorem finite_clique_ramsey (m n : ℕ) :
    ∀ {V : Type*} (G : SimpleGraph V) (s : Finset V),
      2 ^ (m + n) ≤ s.card →
      (∃ t : Finset V, t ⊆ s ∧ t.card = m ∧ G.IsClique (t : Set V)) ∨
      (∃ t : Finset V, t ⊆ s ∧ t.card = n ∧ Gᶜ.IsClique (t : Set V)) := by
  classical
  induction m generalizing n with
  | zero =>
      intro V G s _
      exact Or.inl ⟨∅, empty_subset _, rfl, by simp⟩
  | succ m ihm =>
      induction n with
      | zero =>
          intro V G s _
          exact Or.inr ⟨∅, empty_subset _, rfl, by simp⟩
      | succ n ihn =>
          intro V G s hs
          obtain ⟨v, hv⟩ := card_pos.mp (lt_of_lt_of_le (by positivity) hs)
          let a := (s.erase v).filter (G.Adj v)
          let b := (s.erase v).filter (fun w => ¬ G.Adj v w)
          have ha : a ⊆ s := (filter_subset _ _).trans (erase_subset _ _)
          have hb : b ⊆ s := (filter_subset _ _).trans (erase_subset _ _)
          have hv_a : v ∉ a := by simp [a]
          have hv_b : v ∉ b := by simp [b]
          have hpart : a.card + b.card = s.card - 1 := by
            simpa [a, b, card_erase_of_mem hv] using
              (card_filter_add_card_filter_not (s := s.erase v) (G.Adj v))
          have hp : 2 ^ (m + 1 + (n + 1)) = 2 * 2 ^ (m + n + 1) := by
            rw [show m + 1 + (n + 1) = (m + n + 1) + 1 by omega, pow_succ]
            omega
          have hex : 2 ^ (m + n + 1) ≤ a.card ∨ 2 ^ (m + n + 1) ≤ b.card := by
            rw [hp] at hs
            omega
          rcases hex with h | h
          · rcases ihm (n + 1) G a (by simpa [Nat.add_assoc] using h) with
              ⟨t, ht, hcard, hclique⟩ | ⟨t, ht, hcard, hclique⟩
            · refine Or.inl ⟨insert v t, insert_subset hv (ht.trans ha), ?_, ?_⟩
              · rw [card_insert_of_notMem (fun hvt => hv_a (ht hvt)), hcard]
              · rw [coe_insert]
                exact hclique.insert fun w hw _ => (mem_filter.mp (ht hw)).2
            · exact Or.inr ⟨t, ht.trans ha, hcard, hclique⟩
          · rcases ihn G b (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h) with
              ⟨t, ht, hcard, hclique⟩ | ⟨t, ht, hcard, hclique⟩
            · exact Or.inl ⟨t, ht.trans hb, hcard, hclique⟩
            · refine Or.inr ⟨insert v t, insert_subset hv (ht.trans hb), ?_, ?_⟩
              · rw [card_insert_of_notMem (fun hvt => hv_b (ht hvt)), hcard]
              · rw [coe_insert]
                exact hclique.insert fun w hw hne => ⟨hne, (mem_filter.mp (ht hw)).2⟩

theorem copy_of_clique {V W : Type*} [Fintype V] (H : SimpleGraph V)
    (G : SimpleGraph W) {s : Finset W} (hcard : s.card = Fintype.card V)
    (hc : G.IsClique (s : Set W)) : Nonempty (H.Copy G) := by
  classical
  let e : V ≃ s := Fintype.equivOfCardEq (by simpa using hcard.symm)
  exact ⟨{
    toHom := {
      toFun := fun v => (e v).val
      map_rel' := fun {v w} hvw => hc (e v).property (e w).property
        (fun heq => hvw.ne (e.injective (Subtype.ext heq))) }
    injective' := fun _ _ heq => e.injective (Subtype.ext heq) }⟩

theorem ramseyProperty_exp_bound {V : Type*} [Fintype V] (H : SimpleGraph V) :
    RamseyProperty H (2 ^ (Fintype.card V + Fintype.card V)) := by
  intro G
  rcases finite_clique_ramsey (Fintype.card V) (Fintype.card V) G univ
      (by simp) with ⟨t, _, ht, hc⟩ | ⟨t, _, ht, hc⟩
  · exact Or.inl (copy_of_clique H G ht hc)
  · exact Or.inr (copy_of_clique H Gᶜ ht hc)

theorem ramsey_set_nonempty {V : Type*} [Fintype V] (H : SimpleGraph V) :
    {M : ℕ | 0 < M ∧ RamseyProperty H M}.Nonempty :=
  ⟨2 ^ (Fintype.card V + Fintype.card V), by positivity, ramseyProperty_exp_bound H⟩

theorem ramseyNumber_spec {V : Type*} [Fintype V] (H : SimpleGraph V) :
    0 < ramseyNumber H ∧ RamseyProperty H (ramseyNumber H) :=
  csInf_mem (ramsey_set_nonempty H)

theorem ramseyNumber_le {V : Type*} [Fintype V] (H : SimpleGraph V)
    {M : ℕ} (hM : 0 < M) (h : RamseyProperty H M) : ramseyNumber H ≤ M :=
  csInf_le' ⟨hM, h⟩

theorem ramseyNumber_exp_bound {V : Type*} [Fintype V] (H : SimpleGraph V) :
    ramseyNumber H ≤ 2 ^ (Fintype.card V + Fintype.card V) :=
  ramseyNumber_le H (by positivity) (ramseyProperty_exp_bound H)

theorem ramseyNumber_mono {V W : Type*} [Fintype V] [Fintype W]
    {H : SimpleGraph V} {K : SimpleGraph W} (f : H.Copy K) :
    ramseyNumber H ≤ ramseyNumber K := by
  apply ramseyNumber_le H (ramseyNumber_spec K).1
  intro G
  rcases (ramseyNumber_spec K).2 G with hr | hb
  · obtain ⟨g⟩ := hr
    exact Or.inl ⟨g.comp f⟩
  · obtain ⟨g⟩ := hb
    exact Or.inr ⟨g.comp f⟩

theorem card_le_ramseyNumber {V : Type*} [Fintype V] (H : SimpleGraph V) :
    Fintype.card V ≤ ramseyNumber H := by
  rcases (ramseyNumber_spec H).2 ⊥ with hr | hb
  · obtain ⟨f⟩ := hr
    simpa using Fintype.card_le_of_injective f f.injective
  · obtain ⟨f⟩ := hb
    simpa using Fintype.card_le_of_injective f f.injective

theorem coloring_below_ramsey {V : Type*} [Fintype V] (H : SimpleGraph V)
    {M : ℕ} (hpos : 0 < M) (hM : M < ramseyNumber H) :
    ∃ G : SimpleGraph (Fin M), ¬ Nonempty (H.Copy G) ∧ ¬ Nonempty (H.Copy Gᶜ) := by
  have hnot : ¬ RamseyProperty H M := fun h =>
    Nat.not_le_of_lt hM (ramseyNumber_le H hpos h)
  simpa only [RamseyProperty, not_forall, not_or] using hnot

@[simp] theorem card_cubeVertex (n : ℕ) : Fintype.card (CubeVertex n) = 2 ^ n := by
  simp [CubeVertex]

theorem elementary_cube_bounds (n : ℕ) :
    2 ^ n ≤ ramseyNumber (cube n) ∧
    ramseyNumber (cube n) ≤ 2 ^ (2 ^ n + 2 ^ n) := by
  constructor
  · simpa using card_le_ramseyNumber (cube n)
  · simpa using ramseyNumber_exp_bound (cube n)

@[simp] theorem ramseyNumber_cube_zero : ramseyNumber (cube 0) = 1 := by
  have hl : 1 ≤ ramseyNumber (cube 0) := (ramseyNumber_spec _).1
  refine le_antisymm (ramseyNumber_le _ (by decide) ?_) hl
  intro G
  refine Or.inl ⟨{
    toHom := { toFun := fun _ => (0 : Fin 1), map_rel' := ?_ }
    injective' := fun _ _ _ => Subsingleton.elim _ _ }⟩
  intro u v huv
  exact False.elim (huv.ne (Subsingleton.elim u v))

def crossGraph {L R : Type*} (E : L → R → Prop) : SimpleGraph (L ⊕ R) where
  Adj u v := match u, v with
    | .inl x, .inr y => E x y
    | .inr y, .inl x => E x y
    | _, _ => False
  symm := ⟨by intro u v; cases u <;> cases v <;> exact id⟩
  loopless := ⟨by intro u; cases u <;> exact not_false⟩

def redCrossCopy {L R W : Type*} (e : L ⊕ R ↪ W) (G : SimpleGraph W) :
    (crossGraph (fun x y => G.Adj (e (.inl x)) (e (.inr y)))).Copy G where
  toHom := {
    toFun := e
    map_rel' := by
      intro u v huv
      cases u with
      | inl x =>
          cases v with
          | inl y => exact False.elim huv
          | inr y => exact huv
      | inr y =>
          cases v with
          | inl x => exact (show G.Adj (e (.inl x)) (e (.inr y)) from huv).symm
          | inr x => exact False.elim huv }
  injective' := e.injective

def blueCrossCopy {L R W : Type*} (e : L ⊕ R ↪ W) (G : SimpleGraph W) :
    (crossGraph (fun x y => ¬ G.Adj (e (.inl x)) (e (.inr y)))).Copy Gᶜ where
  toHom := {
    toFun := e
    map_rel' := by
      intro u v huv
      refine ⟨e.injective.ne huv.ne, ?_⟩
      cases u with
      | inl x =>
          cases v with
          | inl y => exact False.elim huv
          | inr y => exact huv
      | inr y =>
          cases v with
          | inl x => exact fun h => huv h.symm
          | inr x => exact False.elim huv }
  injective' := e.injective

def splitEmbedding (N : ℕ) : Fin N ⊕ Fin N ↪ Fin (2 * N) :=
  finSumFinEquiv.toEmbedding.trans (finCongr (by omega)).toEmbedding

theorem cross_coloring_below_ramsey {V : Type*} [Fintype V] (H : SimpleGraph V)
    {N : ℕ} (hpos : 0 < N) (hN : 2 * N < ramseyNumber H) :
    ∃ E : Fin N → Fin N → Prop,
      ¬ Nonempty (H.Copy (crossGraph E)) ∧
      ¬ Nonempty (H.Copy (crossGraph (fun x y => ¬ E x y))) := by
  obtain ⟨G, hr, hb⟩ := coloring_below_ramsey H (by omega) hN
  refine ⟨fun x y => G.Adj (splitEmbedding N (.inl x)) (splitEmbedding N (.inr y)),
    ?_, ?_⟩
  · rintro ⟨f⟩
    exact hr ⟨(redCrossCopy (splitEmbedding N) G).comp f⟩
  · rintro ⟨f⟩
    exact hb ⟨(blueCrossCopy (splitEmbedding N) G).comp f⟩

theorem large_cube_of_not_linear
    (hnot : ¬ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (ramseyNumber (cube n) : ℝ) ≤ C * (2 : ℝ) ^ n)
    (b k : ℕ) :
    ∃ n : ℕ, k ≤ n ∧ b * 2 ^ n < ramseyNumber (cube n) := by
  classical
  have hunbounded : ∀ a : ℕ, ∃ n : ℕ, a * 2 ^ n < ramseyNumber (cube n) := by
    intro a
    by_contra ha
    push Not at ha
    apply hnot
    refine ⟨(a : ℝ) + 1, by positivity, ?_⟩
    intro n
    calc
      (ramseyNumber (cube n) : ℝ) ≤ (a : ℝ) * (2 : ℝ) ^ n := by
        exact_mod_cast ha n
      _ ≤ ((a : ℝ) + 1) * (2 : ℝ) ^ n := by
        gcongr
        linarith
  let S := ∑ i ∈ range k, ramseyNumber (cube i)
  obtain ⟨n, hn⟩ := hunbounded (b + S + 1)
  refine ⟨n, ?_, lt_of_le_of_lt (Nat.mul_le_mul_right (2 ^ n) (by omega)) hn⟩
  by_contra hnk
  have hs : ramseyNumber (cube n) ≤ S :=
    single_le_sum (s := range k) (f := fun i => ramseyNumber (cube i)) (a := n)
      (fun _ _ => Nat.zero_le _) (mem_range.mpr (by omega))
  have hm : b + S + 1 ≤ (b + S + 1) * 2 ^ n :=
    Nat.le_mul_of_pos_right _ (by positivity)
  omega

theorem counterexample_sequence_of_not_linear
    (hnot : ¬ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (ramseyNumber (cube n) : ℝ) ≤ C * (2 : ℝ) ^ n) :
    ∃ (d N : ℕ → ℕ) (E : ∀ k, Fin (N k) → Fin (N k) → Prop),
      Filter.Tendsto d Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun k => (N k : ℝ) / (2 : ℝ) ^ (d k))
        Filter.atTop Filter.atTop ∧
      (∀ k, 0 < N k) ∧
      (∀ k, N k ≤ d k * 2 ^ (d k)) ∧
      (∀ k, ¬ Nonempty ((cube (d k)).Copy (crossGraph (E k))) ∧
        ¬ Nonempty ((cube (d k)).Copy (crossGraph (fun x y => ¬ E k x y)))) := by
  classical
  have hex : ∀ k : ℕ, ∃ n : ℕ, k + 1 ≤ n ∧
      2 * (k + 1) * 2 ^ n < ramseyNumber (cube n) :=
    fun k => large_cube_of_not_linear hnot (2 * (k + 1)) (k + 1)
  choose d hd hbound using hex
  let N : ℕ → ℕ := fun k => (k + 1) * 2 ^ (d k)
  have hpos : ∀ k, 0 < N k := by
    intro k
    dsimp [N]
    positivity
  have hbad : ∀ k, ∃ E : Fin (N k) → Fin (N k) → Prop,
      ¬ Nonempty ((cube (d k)).Copy (crossGraph E)) ∧
      ¬ Nonempty ((cube (d k)).Copy (crossGraph (fun x y => ¬ E x y))) := by
    intro k
    apply cross_coloring_below_ramsey _ (hpos k)
    simpa only [N, Nat.mul_assoc] using hbound k
  choose E hred hblue using hbad
  refine ⟨d, N, E, ?_, ?_, hpos, ?_, fun k => ⟨hred k, hblue k⟩⟩
  · exact Filter.tendsto_atTop_mono
      (fun k => (Nat.le_succ k).trans (hd k)) Filter.tendsto_id
  · have hratio : ∀ k, (N k : ℝ) / (2 : ℝ) ^ (d k) = (k : ℝ) + 1 := by
      intro k
      simp [N]
    have hlim : Filter.Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ))
        Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
    simpa only [hratio, Nat.cast_add, Nat.cast_one] using hlim
  · intro k
    exact Nat.mul_le_mul_right _ (hd k)

end HypercubeRamsey

end OAI
