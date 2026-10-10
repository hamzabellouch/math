import OAI.ModelTheory.Categoricity.EndpointDiagrams

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace TuplePatterns

open Tuples

variable {I : Type u} [LinearOrder I]

def sorted (s : Finset I) {n : ℕ} (hs : s.card = n + 1) : Tuple I :=
  ⟨n, (s.orderEmbOfFin hs).toEmbedding⟩

def support (t : Tuple I) : Finset I := Finset.univ.map t.2

omit [LinearOrder I] in
@[simp] theorem support_card (t : Tuple I) : (support t).card = t.1 + 1 := by
  simp only [support, Finset.card_map, Finset.card_univ, Fintype.card_fin]

@[simp] theorem support_sorted (s : Finset I) {n : ℕ} (hs : s.card = n + 1) :
    support (sorted s hs) = s := Finset.map_orderEmbOfFin_univ s hs

omit [LinearOrder I] in
theorem sub_support (t : Tuple I) {m : ℕ} (e : Fin (m + 1) ↪o Fin (t.1 + 1)) :
    support (sub t e) ⊆ support t := by
  change Finset.univ.map (e.toEmbedding.trans t.2) ⊆ Finset.univ.map t.2
  rw [← Finset.map_map]
  exact Finset.map_subset_map.mpr (Finset.subset_univ _)

theorem sub_sorted (s : Finset I) {n m : ℕ} (hs : s.card = n + 1)
    (e : Fin (m + 1) ↪o Fin (n + 1)) :
    sub (sorted s hs) e = sorted (support (sub (sorted s hs) e)) (support_card _) := by
  apply congrArg (Sigma.mk m)
  apply Function.Embedding.ext
  have h := Finset.orderEmbOfFin_unique' (support_card (sub (sorted s hs) e))
    (f := e.trans (s.orderEmbOfFin hs)) (fun x => Finset.mem_map.2 ⟨x, Finset.mem_univ _, rfl⟩)
  exact congrFun (congrArg (fun f : Fin (m + 1) ↪o I => (f : Fin (m + 1) → I)) h)

variable {C : Type u}

def setColor (c : Tuple I → C) (p0 : C) (s : Finset I) : C :=
  if h : s.card ≠ 0 then
    c (sorted s (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h)).symm)
  else p0

theorem setColor_sorted (c : Tuple I → C) (p0 : C) (s : Finset I) {n : ℕ}
    (hs : s.card = n + 1) : setColor c p0 s = c (sorted s hs) := by
  have hn : s.card ≠ 0 := by omega
  rw [setColor, dite_eq_left hn]
  have he : s.card - 1 = n := by omega
  subst n
  rfl

theorem sub_color (c : Tuple I → C) (p0 : C) (p : ℕ → C) (s : Finset I)
    {n : ℕ} (hs : s.card = n + 1)
    (hp : ∀ j ≤ n + 1, ∀ r ⊆ s, r.card = j → setColor c p0 r = p j)
    {m : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1)) :
    c (sub (sorted s hs) e) = p (m + 1) := by
  have hm : m + 1 ≤ n + 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
  have hsub : support (sub (sorted s hs) e) ⊆ s := by
    simpa only [support_sorted] using sub_support (sorted s hs) e
  rw [sub_sorted]
  rw [← setColor_sorted c p0]
  exact hp (m + 1) hm _ hsub (support_card _)

end TuplePatterns

namespace TailBound

open Tuples Diagrams Colors Tests ThresholdArithmetic

variable {I B : Type u} (hCH : CH.{u})

theorem profile_cardinal (hB : #B ≤ (ℵ_ 1 : Cardinal.{u})) : #(B → Palette.{u}) ≤ ξ.{u} := by
  rw [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.lift_id, palette_cardinal, ← Cardinal.two_power_aleph0]
  apply (Cardinal.power_le_power_left (by simpa only [Cardinal.two_power_aleph0] using Cardinal.continuum_ne_zero) hB).trans_eq
  rw [← Cardinal.power_mul, Cardinal.mul_eq_right (Cardinal.aleph0_le_aleph 1)
    (Cardinal.aleph0_le_aleph 1) Cardinal.aleph0_ne_zero]
  rfl

theorem index_lt (hB : #B ≤ (ℵ_ 1 : Cardinal.{u})) (hunc : ¬ Countable B)
    (c : Tuple I → B → Palette.{u})
    (hbad : ∀ t, {b | ¬ Test hCH (fun t => c t b) t}.Countable) :
    #I < tailThreshold.{u} := by
  classical
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  by_contra! hI
  let p0 : B → Palette.{u} := fun _ => ⟨color (fun _ => false)⟩
  obtain ⟨p, hp⟩ := FinitePatterns.exists_patterns tailThreshold ξ
    (fun _ => TuplePatterns.setColor c p0) strongLimit palette_infinite palette_lt
    palette_lt_cofinality (profile_cardinal hB) hI
  choose A hcard hA using (fun n => hp (n + 1))
  let t : ℕ → Tuple I := fun n => TuplePatterns.sorted (A n) (hcard n)
  have hcount : (⋃ n, {b | ¬ Test hCH (fun t => c t b) (t n)}).Countable :=
    Set.countable_iUnion (fun n => hbad (t n))
  obtain ⟨b, hb⟩ : ∃ b : B, b ∉ ⋃ n, {b | ¬ Test hCH (fun t => c t b) (t n)} := by
    by_contra! hn
    apply hunc
    apply Set.countable_univ_iff.1
    exact hcount.mono (fun b _ => hn b)
  have hb' : ∀ n, Test hCH (fun t => c t b) (t n) := by
    intro n
    exact not_not.mp (fun hn => hb (Set.mem_iUnion.2 ⟨n, hn⟩))
  apply Tests.no_pattern hCH (fun n => p (n + 1) b)
  intro n
  have httest := hb' n
  change Passes hCH (n := n) (fun m e => c (sub (t n) e) b) at httest
  obtain ⟨d, hd⟩ := httest
  refine ⟨d, ?_⟩
  intro m e
  refine ⟨(hd m e).1, ?_⟩
  rw [(hd m e).2]
  exact congrFun (TuplePatterns.sub_color c p0 p (A n) (hcard n) (hA n) e) b

end TailBound

namespace BaseOrders

variable {B : Type u} [LinearOrder B]

theorem initial_bound (h : ∀ b : B, (Set.Iic b).Countable) :
    #B ≤ (ℵ_ 1 : Cardinal.{u}) := by
  classical
  by_cases hsmall : #B ≤ ℵ₀
  · exact hsmall.trans (Cardinal.aleph0_le_aleph 1)
  have hone : (ℵ_ 1 : Cardinal.{u}) ≤ #B := by
    rw [show (ℵ_ (1 : Ordinal) : Cardinal.{u}) = succ ℵ₀ by
      rw [← Cardinal.aleph_zero, Cardinal.succ_aleph]; simp]
    exact Order.succ_le_of_lt (lt_of_not_ge hsmall)
  obtain ⟨e⟩ : Nonempty ((ω_ 1 : Ordinal.{u}).ToType ↪ B) := by
    apply (Cardinal.le_def _ _).1
    simpa only [Cardinal.mk_toType, Ordinal.card_omega] using hone
  have hcof : ∀ b : B, ∃ i, b ≤ e i := by
    intro b
    by_contra! hb
    have he : Function.Injective (fun i => (⟨e i, (hb i).le⟩ : Set.Iic b)) :=
      fun i j hij => e.injective (congrArg Subtype.val hij)
    have := (h b).to_subtype
    have hc := (Cardinal.mk_le_of_injective he).trans (Cardinal.mk_le_aleph0 (α := Set.Iic b))
    rw [Cardinal.mk_toType, Ordinal.card_omega] at hc
    exact (Cardinal.aleph0_lt_aleph.2 (by norm_num : (0 : Ordinal) < 1)).not_ge hc
  choose ix hix using hcof
  let f : B → Σ i : (ω_ 1 : Ordinal.{u}).ToType, Set.Iic (e i) :=
    fun b => ⟨ix b, b, hix b⟩
  have hf : Function.Injective f := by
    intro b c heq
    exact congrArg (fun x : Σ i, Set.Iic (e i) => x.2.val) heq
  apply (Cardinal.mk_le_of_injective hf).trans
  rw [Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun i => #(Set.Iic (e i))) ≤ Cardinal.sum (fun _ : (ω_ 1 : Ordinal.{u}).ToType =>
        (ℵ₀ : Cardinal.{u})) := by
      apply Cardinal.sum_le_sum
      intro i
      have := (h (e i)).to_subtype
      exact Cardinal.mk_le_aleph0
    _ = ℵ_ 1 := by
      rw [Cardinal.sum_const, Cardinal.mk_toType, Ordinal.card_omega, Cardinal.lift_id, Cardinal.lift_id,
        Cardinal.mul_eq_left (Cardinal.aleph0_le_aleph 1) (Cardinal.aleph0_le_aleph 1)
          Cardinal.aleph0_ne_zero]

theorem cardinal_le [Nonempty B] (h : ∀ a b : B, (Set.Icc a b).Countable) :
    #B ≤ (ℵ_ 1 : Cardinal.{u}) := by
  classical
  let p : B := Classical.arbitrary B
  have hup : #(Set.Ici p) ≤ (ℵ_ 1 : Cardinal.{u}) := by
    apply initial_bound
    intro b
    have hinj : Function.Injective (fun x : Set.Iic b =>
        (⟨x.val.val, x.val.property, x.property⟩ : Set.Icc p b.val)) :=
      fun x y heq => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : Set.Icc p b.val => z.val) heq
    have := (h p b).to_subtype
    have : Countable (Set.Iic b) := hinj.countable
    exact Set.to_countable _
  have hdn : #(Set.Iic p) ≤ (ℵ_ 1 : Cardinal.{u}) := by
    apply @initial_bound (OrderDual (Set.Iic p)) _
    intro b
    have hinj : Function.Injective (fun x : Set.Iic b =>
        (⟨x.val.val, x.property, x.val.property⟩ : Set.Icc b.val p)) :=
      fun x y heq => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : Set.Icc b.val p => z.val) heq
    have := (h b.val p).to_subtype
    have : Countable (Set.Iic b) := hinj.countable
    exact Set.to_countable _
  let f : B → Set.Ici p ⊕ Set.Iic p := fun b =>
    if hb : p ≤ b then Sum.inl ⟨b, hb⟩ else Sum.inr ⟨b, (le_of_not_ge hb)⟩
  have hf : Function.Injective f := by
    intro b c heq
    have hv := congrArg (Sum.elim Subtype.val Subtype.val) heq
    simpa [f, apply_dite] using hv
  apply (Cardinal.mk_le_of_injective hf).trans
  simpa only [Cardinal.mk_sum, Cardinal.lift_id,
    Cardinal.add_eq_self (Cardinal.aleph0_le_aleph 1)] using add_le_add hup hdn

end BaseOrders

end CHObstruction

end

end OAI
