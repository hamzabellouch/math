import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.PatchNotMem

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
namespace SharpRamseyFive.ComponentPartition
open scoped BigOperators
open Classical
variable {V C : Type} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
omit [DecidableEq V] [Fintype C] in
lemma singles_iff_unique (r : V → C) (v : V) :
    v ∈ singles r ↔ ∀ w, r w = r v → w = v := by
  rw [mem_singles]
  constructor
  · intro hc
    obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hc
    have hvw : v = w := by simpa only [hw, Finset.mem_singleton] using self_mem_fiber r v
    intro u hu
    have huw : u = w := by simpa only [hw, Finset.mem_singleton] using (mem_fiber r (r v) u).mpr hu
    exact huw.trans hvw.symm
  · intro hu
    have he : fiber r (r v) = {v} := by
      ext w
      simp only [mem_fiber, Finset.mem_singleton]
      exact ⟨hu w, fun h => h ▸ rfl⟩
    rw [he,Finset.card_singleton]

lemma large_card_sum (r : V → C) :
    ∑ c ∈ largeLabels r, (fiber r c).card = Fintype.card V - (singles r).card := by
  rw [← Finset.card_biUnion (fun c _ d _ hne => fiber_disjoint r hne), large_union,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]

variable (G : SimpleGraph V)
noncomputable def componentMap : V → V := fun v => (G.connectedComponentMk v).out

omit [Fintype V] [DecidableEq V] in
lemma componentMap_eq_iff (v w : V) : componentMap G v = componentMap G w ↔
    G.connectedComponentMk v = G.connectedComponentMk w := by
  constructor
  · intro h
    have hh := congrArg G.connectedComponentMk h
    have he (c : G.ConnectedComponent) : G.connectedComponentMk c.out = c := c.out_eq
    simpa only [componentMap, he] using hh
  · intro h
    exact congrArg (fun c : G.ConnectedComponent => c.out) h

omit [Fintype V] [DecidableEq V] in
lemma componentMap_idempotent (v : V) : componentMap G (componentMap G v) = componentMap G v := by
  have he (c : G.ConnectedComponent) : G.connectedComponentMk c.out = c := c.out_eq
  simp only [componentMap, he]

end SharpRamseyFive.ComponentPartition
namespace SharpRamseyFive.ComponentEnumeration
open Classical
open scoped BigOperators
open CertificateEnumeration
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H]

omit [Fintype V] in
lemma boundary_of_walk (G : SimpleGraph V) (E : Finset V) {u v : V}
    (p : G.Walk u v) (hu : u ∈ E) (hv : v ∉ E) :
    ∃ a ∈ E, ∃ b ∉ E, G.Adj a b := by
  induction p with
  | nil => exact False.elim (hv hu)
  | @cons a b c hab p ih =>
    by_cases hb : b ∈ E
    · exact ih hb hv
    · exact ⟨a, hu, b, hb, hab⟩

lemma connected_boundary (G : SimpleGraph V) (hG : G.Connected)
    (E : Finset V) (hE : E.Nonempty) (hne : E ≠ Finset.univ) :
    ∃ a ∈ E, ∃ b ∉ E, G.Adj a b := by
  classical
  obtain ⟨u, hu⟩ := hE
  have : ∃ v, v ∉ E := by
    by_contra h
    apply hne
    ext v
    simp only [Finset.mem_univ, iff_true]
    exact Classical.not_not.mp (fun hv => h ⟨v, hv⟩)
  obtain ⟨v, hv⟩ := this
  obtain ⟨p⟩ := hG u v
  exact boundary_of_walk G E p hu hv

variable (R : H → H → Prop)
noncomputable def relationGraph (hsym : Std.Symm R) (f : V → H) : SimpleGraph V where
  Adj u v := u ≠ v ∧ R (f u) (f v)
  symm := ⟨fun _ _ h => ⟨h.1.symm, hsym.symm _ _ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

abbrev Extension (s : V → H) := (u : V) × V × {h : H // R (s u) h}
noncomputable def extend (s : V → H) (a : Extension R s) : V → H :=
  Function.update s a.2.1 a.2.2.1

omit [DecidableEq V] in
lemma extension_card (Δ : ℕ)
    (hΔ : ∀ h, Fintype.card {h' : H // R h h'} ≤ Δ) (s : V → H) :
    Fintype.card (Extension R s) ≤ Fintype.card V ^ 2 * Δ := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod]
  calc
    _ ≤ ∑ u : V, Fintype.card V * Δ := by
      apply Finset.sum_le_sum
      intro u _
      exact Nat.mul_le_mul_left _ (hΔ (s u))
    _ = _ := by simp; ring

lemma dword_card_le {S : Type} (C : S → Type) (step : (s : S) → C s → S)
    [∀ s, Fintype (C s)] (M : ℕ) (hM : ∀ s, Fintype.card (C s) ≤ M)
    (n : ℕ) (s : S) : Fintype.card (DWord C step n s) ≤ M ^ n := by
  induction n generalizing s with
  | zero =>
    change Fintype.card PUnit ≤ 1
    exact le_of_eq Fintype.card_unique
  | succ n ih =>
    change Fintype.card ((a : C s) × DWord C step n (step s a)) ≤ M ^ (n + 1)
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ a : C s, M ^ n := Finset.sum_le_sum (fun a _ => ih (step s a))
      _ = Fintype.card (C s) * M ^ n := by simp
      _ ≤ M * M ^ n := Nat.mul_le_mul_right _ (hM s)
      _ = _ := (pow_succ' M n).symm

omit [Fintype H] in

theorem connected_extension_cover (hsym : Std.Symm R) (f s : V → H)
    (hf : (relationGraph R hsym f).Connected) (E : Finset V) (hE : E.Nonempty)
    (hcoh : ∀ u ∈ E, s u = f u) :
    ∃ w : DWord (Extension R) (extend R) (Fintype.card V - E.card) s,
      dFinish (Extension R) (extend R) s w = f := by
  classical
  generalize hm : Fintype.card V - E.card = m
  induction m generalizing s E with
  | zero =>
    have hEu : E = Finset.univ := by
      apply Finset.eq_univ_of_card
      have := Finset.card_le_univ E
      omega
    have hsf : s = f := by
      funext u
      exact hcoh u (by simp [hEu])
    subst s
    exact ⟨PUnit.unit, rfl⟩
  | succ n ih =>
    have hne : E ≠ Finset.univ := by
      intro h
      simp [h] at hm
    obtain ⟨u, hu, v, hv, huv⟩ := connected_boundary _ hf E hE hne
    let a : Extension R s := ⟨u, v, f v, by
      rw [hcoh u hu]
      exact huv.2⟩
    have hcoh' : ∀ z ∈ insert v E, extend R s a z = f z := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · simp [extend, a]
      · have hzv : z ≠ v := by intro h; subst z; exact hv hz
        simpa [extend, a, hzv] using hcoh z hz
    have hn : Fintype.card V - (insert v E).card = n := by
      rw [Finset.card_insert_of_notMem hv]
      omega
    obtain ⟨w, hw⟩ := ih (extend R s a) (insert v E) (by simp) hcoh' hn
    exact ⟨⟨a, w⟩, hw⟩

abbrev RelatedPair := (h : H) × {h' : H // R h h'}
abbrev Seed := V × V × RelatedPair R
noncomputable def seedStart (z : Seed (V := V) R) : V → H :=
  Function.update (fun _ => z.2.2.1) z.2.1 z.2.2.2.1

theorem connected_tuple_count (hsym : Std.Symm R) (hV : 2 ≤ Fintype.card V)
    (Δ : ℕ) (hΔ : ∀ h, Fintype.card {h' : H // R h h'} ≤ Δ) :
    Fintype.card {f : V → H // (relationGraph R hsym f).Connected} ≤
      Fintype.card V ^ 2 * Fintype.card (RelatedPair R) *
      (Fintype.card V ^ 2 * Δ) ^ (Fintype.card V - 2) := by
  classical
  let Code := (z : Seed (V := V) R) ×
    DWord (Extension R) (extend R) (Fintype.card V - 2) (seedStart R z)
  let decode : Code → V → H := fun c =>
    dFinish (Extension R) (extend R) (seedStart R c.1) c.2
  have hcover (f : {f : V → H // (relationGraph R hsym f).Connected}) :
      ∃ c : Code, decode c = f.1 := by
    have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    let u : V := Classical.choice inferInstance
    have hne : ({u} : Finset V) ≠ Finset.univ := by
      intro h
      have hh := congrArg Finset.card h
      simp at hh
      omega
    obtain ⟨a, ha, v, hv, huv⟩ := connected_boundary _ f.2 {u} (by simp) hne
    have hau : a = u := by simpa using ha
    subst a
    have hvu : v ≠ u := by simpa using hv
    let z : Seed (V := V) R := ⟨u, v, f.1 u, f.1 v, huv.2⟩
    have hcoh : ∀ x ∈ ({u, v} : Finset V), seedStart R z x = f.1 x := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp [seedStart, z, hvu.symm]
      · simp [seedStart, z]
    have hcov := connected_extension_cover R hsym f.1 (seedStart R z)
      f.2 {u,v} (by simp) hcoh
    have hcard : ({u,v} : Finset V).card = 2 := by simp [hvu.symm]
    rw [hcard] at hcov
    obtain ⟨w, hw⟩ := hcov
    exact ⟨⟨z, w⟩, hw⟩
  let enc : {f : V → H // (relationGraph R hsym f).Connected} → Code :=
    fun f => Classical.choose (hcover f)
  have henc : Function.Injective enc := by
    intro f g hfg
    apply Subtype.ext
    calc
      f.1 = decode (enc f) := (Classical.choose_spec (hcover f)).symm
      _ = decode (enc g) := congrArg decode hfg
      _ = g.1 := Classical.choose_spec (hcover g)
  calc
    _ ≤ Fintype.card Code := Fintype.card_le_of_injective enc henc
    _ = ∑ z : Seed (V := V) R, Fintype.card
        (DWord (Extension R) (extend R) (Fintype.card V - 2) (seedStart R z)) :=
      Fintype.card_sigma
    _ ≤ ∑ _z : Seed (V := V) R,
        (Fintype.card V ^ 2 * Δ) ^ (Fintype.card V - 2) := by
      apply Finset.sum_le_sum
      intro z _
      exact dword_card_le (Extension R) (extend R) _ (extension_card R Δ hΔ) _ _
    _ = _ := by simp [Seed, Fintype.card_prod, pow_two, mul_assoc]

end SharpRamseyFive.ComponentEnumeration

namespace SharpRamseyFive.ComponentPartition
open scoped BigOperators
open Classical
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
variable {V H C : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [Fintype C] [DecidableEq C]

omit [Fintype H] [DecidableEq H] in
lemma connected_fiber (R : H → H → Prop) (hsym : Std.Symm R) (f : V → H)
    (c : V) (hc : (fiber (componentMap (relationGraph R hsym f)) c).Nonempty) :
    (relationGraph R hsym (fun v : fiber (componentMap (relationGraph R hsym f)) c => f v)).Connected := by
  let G := relationGraph R hsym f
  let r := componentMap G
  obtain ⟨w,hw⟩ := hc
  have hw : r w = c := (mem_fiber _ _ _).mp hw
  let S := G.connectedComponentMk w
  let e : fiber r c ≃ S :=
    { toFun := fun v => ⟨v, (S.mem_supp_iff v).mpr
        ((componentMap_eq_iff G v w).mp ((mem_fiber r c v).mp v.property |>.trans hw.symm))⟩
      invFun := fun v => ⟨v, (mem_fiber r c v).mpr
        (((componentMap_eq_iff G v w).mpr ((S.mem_supp_iff v).mp v.property)).trans hw)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let φ : relationGraph R hsym (fun v : fiber r c => f v) ≃g S.toSimpleGraph :=
    { toEquiv := e
      map_rel_iff' := by
        intro x y
        change (x.val ≠ y.val ∧ R (f x) (f y)) ↔ (x ≠ y ∧ R (f x) (f y))
        simp only [ne_eq, Subtype.val_inj] }
  exact φ.connected_iff.mpr S.connected_toSimpleGraph

noncomputable def connectedWeight (R : H → H → Prop) (hsym : Std.Symm R)
    (r : V → C) (c : C) (x : fiber r c → H) : ℝ :=
  if (relationGraph R hsym x).Connected then 1 else 0

omit [Fintype H] [DecidableEq H] [Fintype C] in
lemma connectedWeight_nonneg (R : H → H → Prop) (hsym : Std.Symm R)
    (r : V → C) (c : C) (x : fiber r c → H) : 0 ≤ connectedWeight R hsym r c x := by
  unfold connectedWeight
  split_ifs <;> norm_num

omit [DecidableEq H] in
lemma connectedWeight_sum_le (R : H → H → Prop) (hsym : Std.Symm R)
    (r : V → C) (c : C) (hc : c ∈ largeLabels r)
    (Δ : ℕ) (hΔ : ∀ h, Fintype.card {h' : H // R h h'} ≤ Δ) :
    (∑ x : fiber r c → H, connectedWeight R hsym r c x) ≤
      ((fiber r c).card : ℝ) ^ 2 * Fintype.card (RelatedPair R) *
        (((fiber r c).card : ℝ) ^ 2 * Δ) ^ ((fiber r c).card - 2) := by
  have hc : 2 ≤ Fintype.card (fiber r c) := by simpa only [Fintype.card_coe] using (mem_largeLabels r c).mp hc
  have h := connected_tuple_count (V := fiber r c) R hsym hc Δ hΔ
  have he : (∑ x : fiber r c → H, connectedWeight R hsym r c x) =
      (Fintype.card {x : fiber r c → H // (relationGraph R hsym x).Connected} : ℝ) := by
    simp only [connectedWeight, Fintype.card_subtype, Finset.sum_boole]
  rw [he]
  simpa only [Fintype.card_coe, Nat.cast_mul, Nat.cast_pow] using (Nat.cast_le (α := ℝ)).mpr h

end SharpRamseyFive.ComponentPartition

namespace SharpRamseyFive.ComponentPartition
open scoped BigOperators
open Classical
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
variable {V H C : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [Fintype C] [DecidableEq C]

lemma univ_sub_large (r : V → C) :
    Finset.univ \ (largeLabels r).biUnion (fiber r) = singles r := by
  rw [large_union]
  simp

lemma partition_block_bound (R : H → H → Prop) (hsym : Std.Symm R)
    (r : V → C) (b A : ℝ) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (Δ : ℕ) (hΔ : ∀ h, Fintype.card {h' : H // R h h'} ≤ Δ)
    (hnum : ∀ c ∈ largeLabels r,
      b * (((fiber r c).card : ℝ) ^ 2 * Fintype.card (RelatedPair R) *
        (((fiber r c).card : ℝ) ^ 2 * Δ) ^ ((fiber r c).card - 2))
          ≤ A ^ (fiber r c).card)
    (F : (V → H) → ℝ)
    (hres : ∀ g, completionSum (singles r) g F ≤ A ^ (singles r).card)
    (g : V → H) :
    completionSum Finset.univ g
      (fun f => (∏ c ∈ largeLabels r,
        b * connectedWeight R hsym r c (fun v => f v)) * F f) ≤ A ^ Fintype.card V := by
  have ht := disjoint_blocks_exposure Finset.univ (largeLabels r) (fiber r)
    (fun c x => b * connectedWeight R hsym r c x) (fun c => A ^ (fiber r c).card)
    (fun c x => mul_nonneg hb (connectedWeight_nonneg R hsym r c x))
    (fun c => pow_nonneg hA _) (fun _ _ => Finset.subset_univ _)
    (fun _ _ _ _ hne => fiber_disjoint r hne)
    (fun c hc => by
      rw [← Finset.mul_sum]
      exact (mul_le_mul_of_nonneg_left (connectedWeight_sum_le R hsym r c hc Δ hΔ) hb).trans (hnum c hc))
    F (A ^ (singles r).card) (pow_nonneg hA _)
    (fun g => by simpa only [univ_sub_large] using hres g) g
  apply ht.trans_eq
  rw [Finset.prod_pow_eq_pow_sum, large_card_sum, ← pow_add]
  rw [Nat.sub_add_cancel (Finset.card_le_univ _)]

theorem graph_partition_sum (R : H → H → Prop) (hsym : Std.Symm R)
    (b A : ℝ) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (Δ : ℕ) (hΔ : ∀ h, Fintype.card {h' : H // R h h'} ≤ Δ)
    (hnum : ∀ m : ℕ, 2 ≤ m → m ≤ Fintype.card V →
      b * ((m : ℝ) ^ 2 * Fintype.card (RelatedPair R) * ((m : ℝ) ^ 2 * Δ) ^ (m - 2)) ≤ A ^ m)
    (F : Finset V → (V → H) → ℝ) (hF : ∀ E f, 0 ≤ F E f)
    (hres : ∀ (r : V → V) g,
      completionSum (singles r) g (F (singles r)) ≤ A ^ (singles r).card) :
    (∑ f : V → H, b ^ (largeLabels (componentMap (relationGraph R hsym f))).card *
      F (singles (componentMap (relationGraph R hsym f))) f) ≤
      (Fintype.card V : ℝ) ^ Fintype.card V * A ^ Fintype.card V := by
  let W (r : V → V) (f : V → H) : ℝ :=
    (∏ c ∈ largeLabels r, b * connectedWeight R hsym r c (fun v => f v)) * F (singles r) f
  have hW (r : V → V) (f : V → H) : 0 ≤ W r f :=
    mul_nonneg (Finset.prod_nonneg (fun c _ => mul_nonneg hb (connectedWeight_nonneg R hsym r c _))) (hF _ f)
  have hw (f : V → H) : W (componentMap (relationGraph R hsym f)) f =
      b ^ (largeLabels (componentMap (relationGraph R hsym f))).card *
        F (singles (componentMap (relationGraph R hsym f))) f := by
    dsimp only [W]
    congr 1
    calc
      _ = ∏ _c ∈ largeLabels (componentMap (relationGraph R hsym f)), b := by
        apply Finset.prod_congr rfl
        intro c hc
        have hfc : (fiber (componentMap (relationGraph R hsym f)) c).Nonempty :=
          Finset.card_pos.mp (by have := (mem_largeLabels _ c).mp hc; omega)
        simp only [connectedWeight, ite_eq_left (connected_fiber R hsym f c hfc), mul_one]
      _ = _ := Finset.prod_const _
  calc
    _ = ∑ f : V → H, W (componentMap (relationGraph R hsym f)) f := by simp only [hw]
    _ ≤ ∑ f : V → H, ∑ r : V → V, W r f := by
      apply Finset.sum_le_sum
      intro f _
      exact Finset.single_le_sum (fun r _ => hW r f) (Finset.mem_univ _)
    _ = ∑ r : V → V, ∑ f : V → H, W r f := Finset.sum_comm
    _ ≤ ∑ _r : V → V, A ^ Fintype.card V := by
      apply Finset.sum_le_sum
      intro r _
      classical
      by_cases hn : Nonempty (V → H)
      · let g : V → H := hn.some
        have hh := partition_block_bound R hsym r b A hb hA Δ hΔ
          (fun c hc => hnum _ ((mem_largeLabels _ _).mp hc) (Finset.card_le_univ _))
          (F (singles r)) (hres r) g
        simpa [completionSum, Agrees, W] using hh
      · have : IsEmpty (V → H) := not_nonempty_iff.mp hn
        simp only [Finset.univ_eq_empty, Finset.sum_empty]
        exact pow_nonneg hA _
    _ = _ := by simp [Nat.cast_pow]

end SharpRamseyFive.ComponentPartition

namespace SharpRamseyFive.AmbientEnumeration
open scoped BigOperators NNReal
open Classical
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.AmbientDesignations SharpRamseyFive.ComponentPartition
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
open SharpRamseyFive.SingletonEnumeration SharpRamseyFive.SelectionBridge
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

noncomputable def overlapRelation (weight : D → ℝ≥0) (lines : H → Finset D) (t : ℝ)
    (h k : H) : Prop := t < mass weight (lines h ∩ lines k)

omit [Fintype D] [Fintype H] [DecidableEq H] in
lemma overlapRelation_symm (weight : D → ℝ≥0) (lines : H → Finset D) (t : ℝ) :
    Std.Symm (overlapRelation weight lines t) := by
  constructor
  intro h k hh
  simpa only [overlapRelation, Finset.inter_comm] using hh

omit [Fintype V] [DecidableEq V] in
omit [Fintype D] [Fintype H] [DecidableEq H] in
lemma relation_graph_eq (weight : D → ℝ≥0) (lines : H → Finset D) (t : ℝ) (f : V → H) :
    relationGraph (overlapRelation weight lines t) (overlapRelation_symm weight lines t) f =
      strongGraph weight (lines ∘ f) t := by
  rfl
omit [Fintype D] in

lemma simple_image (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ) :
    (simpleSet weight s t).image (vertex weight s t) = singles (componentMap (strongGraph weight s t)) := by
  ext v
  rw [singles_iff_unique]
  simp only [Finset.mem_image, simpleSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c,hc,rfl⟩ w hw
    exact hc w (((componentMap_eq_iff _ _ _).mp hw).trans (vertex_color weight s t c))
  · intro hv
    let c := (strongGraph weight s t).connectedComponentMk v
    have he : vertex weight s t c = v := hv _ ((componentMap_eq_iff _ _ _).mpr (vertex_color weight s t c))
    exact ⟨c, fun w hw => (hv w ((componentMap_eq_iff _ _ _).mpr hw)).trans he.symm, he⟩
omit [Fintype D] in

lemma simple_card (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ) :
    (simpleSet weight s t).card = (singles (componentMap (strongGraph weight s t))).card := by
  rw [← simple_image, Finset.card_image_of_injective _ (vertex_injective weight s t)]
omit [Fintype D] in

lemma large_image (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ) :
    (Finset.univ \ simpleSet weight s t).image (vertex weight s t) =
      largeLabels (componentMap (strongGraph weight s t)) := by
  let G := strongGraph weight s t
  let r := componentMap G
  ext v
  simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_univ, true_and, mem_largeLabels]
  constructor
  · rintro ⟨c,hc,rfl⟩
    have hpos : 0 < (fiber r (vertex weight s t c)).card := by
      apply Finset.card_pos.mpr
      refine ⟨vertex weight s t c, ?_⟩
      rw [mem_fiber]
      exact congrArg (vertex weight s t) (vertex_color weight s t c)
    have hne : (fiber r (vertex weight s t c)).card ≠ 1 := by
      intro he
      apply hc
      simp only [simpleSet, Finset.mem_filter, Finset.mem_univ, true_and]
      intro w hw
      have hr : r (vertex weight s t c) = vertex weight s t c := by
        exact congrArg (vertex weight s t) (vertex_color weight s t c)
      have hs : vertex weight s t c ∈ singles r := by
        rw [mem_singles, hr]; exact he
      exact (singles_iff_unique r (vertex weight s t c)).mp hs w
        ((componentMap_eq_iff G _ _).mpr (hw.trans (vertex_color weight s t c).symm))
    change 2 ≤ (fiber r (vertex weight s t c)).card
    omega
  · intro hv
    change 2 ≤ (fiber r v).card at hv
    have hpos : 0 < (fiber r v).card := by omega
    obtain ⟨w,hw⟩ := Finset.card_pos.mp hpos
    let c := G.connectedComponentMk w
    have he : vertex weight s t c = v := (mem_fiber r v w).mp hw
    refine ⟨c, ?_, he⟩
    intro hc
    have hs : vertex weight s t c ∈ singles r := by
      rw [← simple_image]
      exact Finset.mem_image.mpr ⟨c,hc,rfl⟩
    have hcard := (mem_singles r (vertex weight s t c)).mp hs
    have hr : r (vertex weight s t c) = vertex weight s t c := by
      exact congrArg (vertex weight s t) (vertex_color weight s t c)
    rw [hr,he] at hcard
    omega

end SharpRamseyFive.AmbientEnumeration
end

end OAI
