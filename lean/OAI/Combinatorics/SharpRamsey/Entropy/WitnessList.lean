import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.NewEvents

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ResidualCertificate
variable {V : Type*} [Fintype V] [DecidableEq V]
section WitnessMatching
variable {E N D : Type*} [DecidableEq E] [DecidableEq N] [DecidableEq D]
theorem exists_witness_list (s : Finset E) (neighbor : E → N) (direction : E → D)
    (K h : ℕ) (hn : ∀ n, (s.filter (fun e => neighbor e = n)).card ≤ K)
    (hd : ∀ d, (s.filter (fun e => direction e = d)).card ≤ K)
    (hh : h ≤ s.card / (2 * K)) :
    ∃ t ⊆ s, t.card = h ∧ Set.InjOn neighbor (t : Set E) ∧ Set.InjOn direction (t : Set E) := by
  obtain ⟨u, hu, hun, hud, hcard⟩ := exists_distinct_witnesses s neighbor direction K hn hd
  have hle : h ≤ u.card := hh.trans (Nat.div_le_of_le_mul hcard)
  obtain ⟨t, htu, htc⟩ := Finset.exists_subset_card_eq hle
  exact ⟨t, htu.trans hu, htc, hun.mono htu, hud.mono htu⟩

theorem exists_residual_roots [Fintype N] (batchSet : N → Finset E)
    (neighbor : N → E → N) (direction : N → E → D) (K h : ℕ)
    (hh : 0 < h)
    (hsize : ∀ v, h ≤ (batchSet v).card / (2 * K))
    (hn : ∀ v n, ((batchSet v).filter (fun e => neighbor v e = n)).card ≤ K)
    (hd : ∀ v d, ((batchSet v).filter (fun e => direction v e = d)).card ≤ K)
    (herr : (Fintype.card N : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2) :
    ∃ roots : Finset N, 10 * roots.card ≤ Fintype.card N ∧
      ∀ v, ∃ b₁ ∈ batchSet v, ∃ b₂ ∈ batchSet v,
        neighbor v b₁ ∈ roots ∧ neighbor v b₂ ∈ roots ∧
        neighbor v b₁ ≠ neighbor v b₂ ∧ direction v b₁ ≠ direction v b₂ := by
  classical
  have hex (v : N) := exists_witness_list (batchSet v) (neighbor v) (direction v)
    K h (hn v) (hd v) (hsize v)
  choose lists hsub hcard hin hn_dir using hex
  let W : N → Finset N := fun v => (lists v).image (neighbor v)
  have hW (v : N) : (W v).card = h := by
    change ((lists v).image (neighbor v)).card = h
    rw [Finset.card_image_of_injOn (hin v), hcard v]
  obtain ⟨roots, hr, hall⟩ := exists_small_root_set W hh hW herr
  refine ⟨roots, hr, ?_⟩
  intro v
  have htwo : 1 < (W v ∩ roots).card := by have := hall v; omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
  obtain ⟨b₁, hb₁, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp ha).1
  obtain ⟨b₂, hb₂, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hb).1
  refine ⟨b₁, hsub v hb₁, b₂, hsub v hb₂, (Finset.mem_inter.mp ha).2,
    (Finset.mem_inter.mp hb).2, hab, ?_⟩
  intro heq
  have := hn_dir v hb₁ hb₂ heq
  exact hab (congrArg (neighbor v) this)

end WitnessMatching

section SharedHitGeometry

open scoped Classical

variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

noncomputable def sharedBatches (s : V → Finset D) (hit : B → D → Prop) (v u : V) : Finset B :=
  Finset.univ.filter (fun r => ∃ d ∈ s v ∩ s u, hit r d)

noncomputable def touchedBatches (s : V → Finset D) (hit : B → D → Prop) (v : V) : Finset B :=
  Finset.univ.filter (fun r => ∃ u, u ≠ v ∧ r ∈ sharedBatches s hit v u)

omit [Fintype D] in

theorem roots_from_shared_hits (s : V → Finset D) (hit : B → D → Prop)
    (K h : ℕ) (hh : 0 < h)
    (hsize : ∀ v, h ≤ (touchedBatches s hit v).card / (2 * K))
    (hpair : ∀ v u, v ≠ u → (sharedBatches s hit v u).card ≤ K)
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2) :
    ∃ roots : Finset V, 10 * roots.card ≤ Fintype.card V ∧
      ∀ v, ∃ u ∈ roots, ∃ w ∈ roots, u ≠ w ∧ u ≠ v ∧ w ≠ v ∧
        ∃ d₁ ∈ s v ∩ s u, ∃ d₂ ∈ s v ∩ s w,
          d₁ ≠ d₂ ∧ (∃ r, hit r d₁) ∧ (∃ r, hit r d₂) := by
  classical
  have hwit (v : V) (r : touchedBatches s hit v) :
      ∃ z : V × D, z.1 ≠ v ∧ z.2 ∈ s v ∩ s z.1 ∧ hit r.val z.2 := by
    obtain ⟨u, hu, hs⟩ := (Finset.mem_filter.mp r.property).2
    obtain ⟨d, hd, hr⟩ := (Finset.mem_filter.mp hs).2
    exact ⟨(u, d), hu, hd, hr⟩
  choose wit hwit using hwit
  let neighbor (v : V) (r : B) : V :=
    if hr : r ∈ touchedBatches s hit v then (wit v ⟨r, hr⟩).1 else v
  let direction (v : V) (r : B) : Option D :=
    if hr : r ∈ touchedBatches s hit v then some (wit v ⟨r, hr⟩).2 else none
  have hvalid (v : V) (r : B) (hr : r ∈ touchedBatches s hit v) :
      ∃ d, direction v r = some d ∧ neighbor v r ≠ v ∧
        d ∈ s v ∩ s (neighbor v r) ∧ hit r d := by
    refine ⟨(wit v ⟨r, hr⟩).2, ?_⟩
    simp only [neighbor, direction, dite_eq_left hr]
    exact ⟨trivial, hwit v ⟨r, hr⟩⟩
  have hn (v u : V) :
      ((touchedBatches s hit v).filter (fun r => neighbor v r = u)).card ≤ K := by
    by_cases hu : v = u
    · have he : (touchedBatches s hit v).filter (fun r => neighbor v r = u) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro r hr
        obtain ⟨hr, he⟩ := Finset.mem_filter.mp hr
        obtain ⟨d, _, hd, _⟩ := hvalid v r hr
        exact hd (he.trans hu.symm)
      simp [he]
    · apply (Finset.card_le_card (show
          (touchedBatches s hit v).filter (fun r => neighbor v r = u) ⊆
            sharedBatches s hit v u from ?_)).trans (hpair v u hu)
      intro r hr
      obtain ⟨hr, he⟩ := Finset.mem_filter.mp hr
      obtain ⟨d, _, _, hd, hp⟩ := hvalid v r hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, he ▸ hd, hp⟩
  have hd (v : V) (d : Option D) :
      ((touchedBatches s hit v).filter (fun r => direction v r = d)).card ≤ K := by
    let T := (touchedBatches s hit v).filter (fun r => direction v r = d)
    by_cases he : T.Nonempty
    · obtain ⟨r₀, hr₀⟩ := he
      obtain ⟨hm₀, hd₀⟩ := Finset.mem_filter.mp hr₀
      obtain ⟨a, ha, hu, has, hp⟩ := hvalid v r₀ hm₀
      apply (Finset.card_le_card (show T ⊆ sharedBatches s hit v (neighbor v r₀) from ?_)).trans
        (hpair v (neighbor v r₀) hu.symm)
      intro r hr
      obtain ⟨hm, hd⟩ := Finset.mem_filter.mp hr
      obtain ⟨b, hb, _, hbs, hhit⟩ := hvalid v r hm
      have heq : b = a := Option.some.inj (hb.symm.trans (hd.trans (hd₀.symm.trans ha)))
      subst b
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a,
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hbs).1, (Finset.mem_inter.mp has).2⟩, hhit⟩
    · have hem : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      change T.card ≤ K
      simp [hem]
  obtain ⟨roots, hr, hroots⟩ := exists_residual_roots (touchedBatches s hit)
    neighbor direction K h hh hsize hn hd herr
  refine ⟨roots, hr, ?_⟩
  intro v
  obtain ⟨r₁, hr₁, r₂, hr₂, hu, hw, huv, hdir⟩ := hroots v
  obtain ⟨a, ha, hne₁, hmem₁, hhit₁⟩ := hvalid v r₁ hr₁
  obtain ⟨b, hb, hne₂, hmem₂, hhit₂⟩ := hvalid v r₂ hr₂
  refine ⟨neighbor v r₁, hu, neighbor v r₂, hw, huv, hne₁, hne₂,
    a, hmem₁, b, hmem₂, ?_, ⟨r₁, hhit₁⟩, ⟨r₂, hhit₂⟩⟩
  intro heq
  exact hdir (ha.trans (congrArg some heq) |>.trans hb.symm)

noncomputable def encodedDirections (s : V → Finset D) (E : Finset V) : Finset D :=
  E.biUnion s

noncomputable def touchedToEncoded (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (v : V) : Finset D :=
  (s v ∩ encodedDirections s E).filter (fun d => ∃ r, hit r d)

noncomputable def batchesOn (hit : B → D → Prop) (T : Finset D) : Finset B :=
  T.biUnion (fun d => Finset.univ.filter (fun r => hit r d))

noncomputable def survivingDirections (s : V → Finset D) (E : Finset V)
    (v : {v // v ∉ E}) : Finset D := s v.val \ encodedDirections s E

omit [Fintype D] [DecidableEq D] in
lemma mem_batchesOn (hit : B → D → Prop) (T : Finset D) (r : B) :
    r ∈ batchesOn hit T ↔ ∃ d ∈ T, hit r d := by
  simp [batchesOn]

omit [Fintype D] in

lemma surviving_touches (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (v : {v // v ∉ E}) :
    touchedBatches s hit v.val \ batchesOn hit (touchedToEncoded s hit E v.val) ⊆
      touchedBatches (survivingDirections s E) hit v := by
  classical
  intro r hr
  obtain ⟨hr, hnot⟩ := Finset.mem_sdiff.mp hr
  obtain ⟨u, huv, hu⟩ := (Finset.mem_filter.mp hr).2
  obtain ⟨d, hd, hh⟩ := (Finset.mem_filter.mp hu).2
  have hde : d ∉ encodedDirections s E := by
    intro he
    apply hnot
    rw [mem_batchesOn]
    exact ⟨d, Finset.mem_filter.mpr
      ⟨Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hd).1, he⟩, ⟨r, hh⟩⟩, hh⟩
  have hue : u ∉ E := by
    intro hu
    exact hde (Finset.mem_biUnion.mpr ⟨u, hu, (Finset.mem_inter.mp hd).2⟩)
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨u, hue⟩, ?_, ?_⟩
  · intro he
    exact huv (congrArg Subtype.val he)
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, ?_, hh⟩
    exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hd).1, hde⟩,
      Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hd).2, hde⟩⟩

omit [Fintype D] [DecidableEq D] in
lemma batchesOn_card_le (hit : B → D → Prop) (T : Finset D) (J : ℕ)
    (hJ : ∀ d ∈ T, (Finset.univ.filter (fun r => hit r d)).card ≤ J) :
    (batchesOn hit T).card ≤ T.card * J := by
  classical
  apply (Finset.card_biUnion_le).trans
  calc
    ∑ d ∈ T, (Finset.univ.filter (fun r => hit r d)).card ≤ ∑ _d ∈ T, J :=
      Finset.sum_le_sum hJ
    _ = _ := by simp
omit [Fintype D] in

lemma surviving_touches_card (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (v : {v // v ∉ E}) (J N : ℕ)
    (hbad : N ≤ (touchedBatches s hit v.val).card)
    (hloss : (batchesOn hit (touchedToEncoded s hit E v.val)).card ≤ J) :
    N - J ≤ (touchedBatches (survivingDirections s E) hit v).card := by
  have hs := Finset.card_le_card (surviving_touches s hit E v)
  have hd := Finset.card_sdiff_add_card_inter
    (touchedBatches s hit v.val) (batchesOn hit (touchedToEncoded s hit E v.val))
  have hi := Finset.card_le_card (Finset.inter_subset_right
    (s₁ := touchedBatches s hit v.val)
    (s₂ := batchesOn hit (touchedToEncoded s hit E v.val)))
  omega

omit [Fintype V] [DecidableEq V] in
omit [Fintype D] in

lemma terminal_high_loss (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (v : V) (J : ℕ)
    (hanchor : (touchedToEncoded s hit E v).card ≤ 1)
    (htrunc : ∀ d, (Finset.univ.filter (fun r => hit r d)).card ≤ J) :
    (batchesOn hit (touchedToEncoded s hit E v)).card ≤ J := by
  exact (batchesOn_card_le hit _ J (fun d _ => htrunc d)).trans
    (by simpa using Nat.mul_le_mul_right J hanchor)

omit [Fintype V] [DecidableEq V] [Fintype D] in
lemma terminal_low_loss (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (v : V) (hanchor : touchedToEncoded s hit E v = ∅) :
    (batchesOn hit (touchedToEncoded s hit E v)).card = 0 := by
  simp [hanchor, batchesOn]

omit [Fintype D] in

theorem terminal_state_roots (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (K J h : ℕ) (hh : 0 < h)
    (hsize : h ≤ (Fintype.card B / 2 - J) / (2 * K))
    (hbad : ∀ v ∉ E, Fintype.card B / 2 ≤ (touchedBatches s hit v).card)
    (hloss : ∀ v ∉ E, (batchesOn hit (touchedToEncoded s hit E v)).card ≤ J)
    (hpair : ∀ (v u : {v // v ∉ E}), v ≠ u →
      (sharedBatches (survivingDirections s E) hit v u).card < K)
    (herr : (Fintype.card {v // v ∉ E} : ℝ) * h *
      (19 / 20 : ℝ) ^ (h - 1) < 1 / 2) :
    ∃ roots : Finset {v // v ∉ E}, 10 * roots.card ≤ Fintype.card {v // v ∉ E} ∧
      ∀ v, ∃ u ∈ roots, ∃ w ∈ roots, u ≠ w ∧ u ≠ v ∧ w ≠ v ∧
        ∃ d₁ ∈ survivingDirections s E v ∩ survivingDirections s E u,
        ∃ d₂ ∈ survivingDirections s E v ∩ survivingDirections s E w,
          d₁ ≠ d₂ ∧ (∃ r, hit r d₁) ∧ (∃ r, hit r d₂) := by
  classical
  apply roots_from_shared_hits (survivingDirections s E) hit K h hh
  · intro v
    apply hsize.trans
    apply Nat.div_le_div_right
    exact surviving_touches_card s hit E v J _ (hbad v.val v.property)
      (hloss v.val v.property)
  · intro v u hvu
    exact (hpair v u hvu).le
  · exact herr

noncomputable def outsideDirections (s : V → Finset D) (E : Finset V) (v : V) : Finset D :=
  s v \ encodedDirections s E

inductive EncodingStep (s : V → Finset D) (hit : B → D → Prop)
    (anchorNumber K : ℕ) : Finset V → Finset V → Prop
  | anchor (E : Finset V) (v : V) (hv : v ∉ E)
      (ha : anchorNumber ≤ (touchedToEncoded s hit E v).card) :
      EncodingStep s hit anchorNumber K E (insert v E)
  | pair (E : Finset V) (v u : V) (hv : v ∉ E) (hu : u ∉ E) (hne : v ≠ u)
      (hp : K ≤ (sharedBatches (outsideDirections s E) hit v u).card) :
      EncodingStep s hit anchorNumber K E (insert v (insert u E))

omit [Fintype V] [Fintype D] [DecidableEq B] in
lemma encodingStep_strict (s : V → Finset D) (hit : B → D → Prop)
    (a K : ℕ) {E F : Finset V} (h : EncodingStep s hit a K E F) : E ⊂ F := by
  cases h with
  | anchor v hv ha => exact Finset.ssubset_insert hv
  | pair v u hv hu hne hp =>
    exact (Finset.ssubset_insert hu).trans_subset (Finset.subset_insert _ _)
omit [Fintype V] [Fintype D] [DecidableEq B] in

lemma encoding_reachable_subset (s : V → Finset D) (hit : B → D → Prop)
    (a K : ℕ) {E F : Finset V} (h : Relation.ReflTransGen (EncodingStep s hit a K) E F) :
    E ⊆ F := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | @tail F G h hFG ih => exact ih.trans (encodingStep_strict s hit a K hFG).subset

omit [Fintype D] [DecidableEq B] in

theorem exists_terminal_encoding (s : V → Finset D) (hit : B → D → Prop)
    (a K : ℕ) (E : Finset V) :
    ∃ F, Relation.ReflTransGen (EncodingStep s hit a K) E F ∧
      (∀ v ∉ F, (touchedToEncoded s hit F v).card < a) ∧
      ∀ v ∉ F, ∀ u ∉ F, v ≠ u →
        (sharedBatches (outsideDirections s F) hit v u).card < K := by
  classical
  let reachable : Finset (Finset V) := Finset.univ.filter
    (fun F => Relation.ReflTransGen (EncodingStep s hit a K) E F)
  have hE : E ∈ reachable := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩
  obtain ⟨F, hF, hmax⟩ := reachable.exists_max_image Finset.card ⟨E, hE⟩
  have hreach := (Finset.mem_filter.mp hF).2
  have hterminal (G : Finset V) : ¬EncodingStep s hit a K F G := by
    intro hs
    have hG : G ∈ reachable := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hreach.tail hs⟩
    exact (Nat.not_lt_of_ge (hmax G hG)) (Finset.card_lt_card (encodingStep_strict s hit a K hs))
  refine ⟨F, hreach, ?_, ?_⟩
  · intro v hv
    by_contra ha
    exact hterminal _ (.anchor F v hv (Nat.not_lt.mp ha))
  · intro v hv u hu hne
    by_contra hp
    exact hterminal _ (.pair F v u hv hu hne (Nat.not_lt.mp hp))

omit [Fintype D] in

theorem high_case_certificate_geometry (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (K J h : ℕ) (hh : 0 < h)
    (hsize : h ≤ (Fintype.card B / 2 - J) / (2 * K))
    (hbad : ∀ v ∉ E, Fintype.card B / 2 ≤ (touchedBatches s hit v).card)
    (htrunc : ∀ d, (Finset.univ.filter (fun r => hit r d)).card ≤ J)
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2) :
    ∃ F, Relation.ReflTransGen (EncodingStep s hit 2 K) E F ∧
      ∃ roots : Finset {v // v ∉ F}, 10 * roots.card ≤ Fintype.card {v // v ∉ F} ∧
        ∀ v, ∃ u ∈ roots, ∃ w ∈ roots, u ≠ w ∧ u ≠ v ∧ w ≠ v ∧
          ∃ d₁ ∈ survivingDirections s F v ∩ survivingDirections s F u,
          ∃ d₂ ∈ survivingDirections s F v ∩ survivingDirections s F w,
            d₁ ≠ d₂ ∧ (∃ r, hit r d₁) ∧ (∃ r, hit r d₂) := by
  classical
  obtain ⟨F, hF, ha, hp⟩ := exists_terminal_encoding s hit 2 K E
  refine ⟨F, hF, ?_⟩
  apply terminal_state_roots s hit F K J h hh hsize
  · intro v hv
    exact hbad v (fun he => hv (encoding_reachable_subset s hit 2 K hF he))
  · intro v hv
    exact terminal_high_loss s hit F v J (by have := ha v hv; omega) htrunc
  · intro v u hvu
    have hne : v.val ≠ u.val := fun he => hvu (Subtype.ext he)
    exact hp v.val v.property u.val u.property hne
  · apply lt_of_le_of_lt _ herr
    have hc : (Fintype.card {v // v ∉ F} : ℝ) ≤ Fintype.card V := by
      exact_mod_cast Fintype.card_subtype_le (fun v => v ∉ F)
    gcongr

omit [Fintype D] in

theorem low_case_certificate_geometry (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (K h : ℕ) (hh : 0 < h)
    (hsize : h ≤ (Fintype.card B / 2) / (2 * K))
    (hbad : ∀ v ∉ E, Fintype.card B / 2 ≤ (touchedBatches s hit v).card)
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2) :
    ∃ F, Relation.ReflTransGen (EncodingStep s hit 1 K) E F ∧
      ∃ roots : Finset {v // v ∉ F}, 10 * roots.card ≤ Fintype.card {v // v ∉ F} ∧
        ∀ v, ∃ u ∈ roots, ∃ w ∈ roots, u ≠ w ∧ u ≠ v ∧ w ≠ v ∧
          ∃ d₁ ∈ survivingDirections s F v ∩ survivingDirections s F u,
          ∃ d₂ ∈ survivingDirections s F v ∩ survivingDirections s F w,
            d₁ ≠ d₂ ∧ (∃ r, hit r d₁) ∧ (∃ r, hit r d₂) := by
  classical
  obtain ⟨F, hF, ha, hp⟩ := exists_terminal_encoding s hit 1 K E
  refine ⟨F, hF, ?_⟩
  apply terminal_state_roots s hit F K 0 h hh (by simpa using hsize)
  · intro v hv
    exact hbad v (fun he => hv (encoding_reachable_subset s hit 1 K hF he))
  · intro v hv
    have hem : touchedToEncoded s hit F v = ∅ := Finset.card_eq_zero.mp (by
      have := ha v hv
      omega)
    exact (terminal_low_loss s hit F v hem).le
  · intro v u hvu
    have hne : v.val ≠ u.val := fun he => hvu (Subtype.ext he)
    exact hp v.val v.property u.val u.property hne
  · apply lt_of_le_of_lt _ herr
    have hc : (Fintype.card {v // v ∉ F} : ℝ) ≤ Fintype.card V := by
      exact_mod_cast Fintype.card_subtype_le (fun v => v ∉ F)
    gcongr

def paidDirections (C : Finset (B × D)) : Finset D := C.image Prod.snd

def Realized (hit : B → D → Prop) (C : Finset (B × D)) : Prop :=
  ∀ p ∈ C, hit p.1 p.2

def DictionaryInvariant (s : V → Finset D) (E : Finset V) (C : Finset (B × D)) : Prop :=
  paidDirections C ⊆ encodedDirections s E

omit [Fintype V] [DecidableEq V] [Fintype D] in
lemma encodedDirections_mono (s : V → Finset D) {E F : Finset V} (h : E ⊆ F) :
    encodedDirections s E ⊆ encodedDirections s F := by
  intro d hd
  obtain ⟨v, hv, hdv⟩ := Finset.mem_biUnion.mp hd
  exact Finset.mem_biUnion.mpr ⟨v, h hv, hdv⟩

omit [Fintype D] [Fintype B] in
lemma paidDirections_union (C C' : Finset (B × D)) :
    paidDirections (C ∪ C') = paidDirections C ∪ paidDirections C' := by
  simp only [paidDirections, Finset.image_union]

omit [Fintype D] [Fintype B] in
lemma realized_union (hit : B → D → Prop) {C C' : Finset (B × D)}
    (h : Realized hit C) (h' : Realized hit C') : Realized hit (C ∪ C') := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact h p hp
  · exact h' p hp

noncomputable def anchorEvents (C : Finset (B × D)) (A : Finset D) (r : A → B) :
    Finset (B × D) :=
  (A.attach.filter (fun d => d.val ∉ paidDirections C)).image (fun d => (r d, d.val))

omit [Fintype D] [Fintype B] in
lemma anchorEvents_fresh (C : Finset (B × D)) (A : Finset D) (r : A → B) :
    Disjoint C (anchorEvents C A r) := by
  apply Finset.disjoint_left.mpr
  intro p hp he
  obtain ⟨d, hd, hdp⟩ := Finset.mem_image.mp he
  have hdC : d.val ∉ paidDirections C := (Finset.mem_filter.mp hd).2
  apply hdC
  exact Finset.mem_image.mpr ⟨p, hp, (congrArg Prod.snd hdp).symm⟩

omit [Fintype D] [Fintype B] in
lemma anchorEvents_card (C : Finset (B × D)) (A : Finset D) (r : A → B) :
    (anchorEvents C A r).card ≤ A.card :=
  (Finset.card_image_le).trans ((Finset.card_filter_le _ _).trans_eq Finset.card_attach)

omit [Fintype D] [Fintype B] in
lemma anchorEvents_directions (C : Finset (B × D)) (A : Finset D) (r : A → B) :
    paidDirections (anchorEvents C A r) ⊆ A := by
  intro d hd
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
  exact a.property

end SharedHitGeometry
end SharpRamseyFive.ResidualCertificate
end

end OAI
