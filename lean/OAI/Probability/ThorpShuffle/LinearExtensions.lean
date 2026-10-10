import OAI.Probability.ThorpShuffle.Classification

namespace OAI

universe uA uα uI uB

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

variable (A : Type uA) [Fintype A] [PartialOrder A]

def Extensions := {e : A ≃ Fin (Fintype.card A) // StrictMono e}

instance : Fintype (Extensions A) := inferInstanceAs (Fintype {e : A ≃ Fin (Fintype.card A) // StrictMono e})

omit [PartialOrder A] in

lemma labelByKey (k : A → ℕ) (hk : Function.Injective k) :
    ∃ e : A ≃ Fin (Fintype.card A), ∀ x y, e x < e y ↔ k x < k y := by
  let e : A ≃ Set.range k := Equiv.ofInjective k hk
  let : Fintype (Set.range k) := Fintype.ofEquiv A e
  let o := (Fintype.orderIsoFinOfCardEq (Set.range k) (Fintype.card_congr e.symm)).symm
  exact ⟨e.trans o.toEquiv, fun x y => o.lt_iff_lt⟩

omit [PartialOrder A] in

lemma labelByRank (r : A → ℕ) :
    ∃ e : A ≃ Fin (Fintype.card A), ∀ x y, r x < r y → e x < e y := by
  let b := Fintype.equivFin A
  let k (x : A) := r x * (Fintype.card A + 1) + (b x).val
  have hk : Function.Injective k := by
    intro x y h
    have hx := (b x).isLt
    have hy := (b y).isLt
    have hr : r x = r y := by
      change r x * (Fintype.card A + 1) + (b x).val = r y * (Fintype.card A + 1) + (b y).val at h
      nlinarith
    apply b.injective
    apply Fin.ext
    change r x * (Fintype.card A + 1) + (b x).val = r y * (Fintype.card A + 1) + (b y).val at h
    rw [hr] at h
    omega
  obtain ⟨e, he⟩ := labelByKey A k hk
  refine ⟨e, fun x y hxy => (he x y).mpr ?_⟩
  dsimp [k]
  have hx := (b x).isLt
  nlinarith

lemma extensions_nonempty : Nonempty (Extensions A) := by
  let h : A ≃ LinearExtension A := Equiv.refl A
  let : Fintype (LinearExtension A) := Fintype.ofEquiv A h
  let e := (Fintype.orderIsoFinOfCardEq (LinearExtension A) (Fintype.card_congr h.symm)).symm
  refine ⟨⟨h.trans e.toEquiv, ?_⟩⟩
  exact e.strictMono.comp
    (toLinearExtension.monotone.strictMono_of_injective fun _ _ hh => hh)

lemma fiberPerm_le_extensions (r : A → ℕ) (hr : StrictMono r) :
    Fintype.card (Thorp.Specht.fiberGroup r) ≤ Fintype.card (Extensions A) := by
  obtain ⟨e, he⟩ := labelByRank A r
  let F (g : Thorp.Specht.fiberGroup r) : Extensions A := ⟨g.val.trans e, by
    intro x y hxy
    apply he
    rw [g.property x, g.property y]
    exact hr hxy⟩
  apply Fintype.card_le_of_injective F
  intro g h hgh
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply e.injective
  exact congrArg (fun z : Extensions A => z.val x) hgh

end Thorp.Young

namespace Thorp.Specht
open scoped Classical
variable {α : Type uα} [Fintype α]

lemma tabloid_card_mul (r : α → ℕ) :
    Fintype.card (Tabloid r) * Fintype.card (fiberGroup r) = (Fintype.card α).factorial := by
  let G := Equiv.Perm α
  let b := baseTabloid r
  let e : MulAction.orbit G b ≃ Tabloid r := {
    toFun := Subtype.val
    invFun := fun f => ⟨f, by
      obtain ⟨g, hg⟩ := f.property
      refine ⟨g⁻¹, ?_⟩
      apply Subtype.ext
      funext x
      change r ((g⁻¹ : Equiv.Perm α)⁻¹ x) = f.val x
      rw [inv_inv]
      exact (congrFun hg x).symm⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let u : MulAction.stabilizer G b ≃ fiberGroup r := {
    toFun := fun g => ⟨g.val, (stabilizes_tabloid_iff r g.val b).mp g.property⟩
    invFun := fun g => ⟨g.val, (stabilizes_tabloid_iff r g.val b).mpr g.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [← Fintype.card_congr e, ← Fintype.card_congr u,
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group, Fintype.card_perm]

lemma tabloid_card_le (r : α → ℕ) (m : ℕ) (hr : ∀ x, r x < m) :
    Fintype.card (Tabloid r) ≤ m ^ Fintype.card α := by
  have hb (f : Tabloid r) (x : α) : f.val x < m := by
    obtain ⟨g, hg⟩ := f.property
    rw [hg]
    exact hr (g x)
  let F (f : Tabloid r) : α → Fin m := fun x => ⟨f.val x, hb f x⟩
  have hi : Function.Injective F := by
    intro f h hfh
    apply Subtype.ext
    funext x
    exact congrArg Fin.val (congrFun hfh x)
  have hh := Fintype.card_le_of_injective F hi
  simpa only [Fintype.card_fun, Fintype.card_fin] using hh

end Thorp.Specht

namespace Thorp.Young
open scoped Classical
variable (A : Type uA) [Fintype A] [PartialOrder A]

theorem rank_extension_bound (r : A → ℕ) (hr : StrictMono r) (m : ℕ) (hm : ∀ x, r x < m) :
    (Fintype.card A).factorial ≤ m ^ Fintype.card A * Fintype.card (Extensions A) := by
  rw [← Thorp.Specht.tabloid_card_mul r]
  exact Nat.mul_le_mul (Thorp.Specht.tabloid_card_le r m hm) (fiberPerm_le_extensions A r hr)

end Thorp.Young

namespace Thorp.Specht
open scoped Classical
variable {n : ℕ} (D : YoungDiagram) (t : Fin n ≃ Thorp.Young.Cells D)

lemma labels_card_le_degree {I : Type uI} [Fintype I]
    (l : I → Thorp.Young.Cells D ≃ Fin n) (hl : ∀ i, StrictMono (l i))
    (hi : Function.Injective l) : Fintype.card I ≤ Module.finrank ℂ (module D t).toSubmodule := by
  let F (i : I) : StandardPerm D t := ⟨t.trans (l i), by
    intro x y hxy
    change l i (t (t.symm x)) < l i (t (t.symm y))
    simpa only [Equiv.apply_symm_apply] using hl i hxy⟩
  have hF : Function.Injective F := by
    intro i j hij
    apply hi
    apply Equiv.ext
    intro x
    have hh := congrArg (fun g : StandardPerm D t => g.val (t.symm x)) hij
    simpa only [F, Equiv.trans_apply, Equiv.apply_symm_apply] using hh
  exact (Fintype.card_le_of_injective F hF).trans (standardPerm_card_le_degree D t)

lemma extensions_card_le_degree :
    Fintype.card (Thorp.Young.Extensions (Thorp.Young.Cells D)) ≤
      Module.finrank ℂ (module D t).toSubmodule := by
  have hc : Fintype.card (Thorp.Young.Cells D) = n := (Fintype.card_congr t.symm).trans (Fintype.card_fin n)
  let c := finCongr hc
  apply labels_card_le_degree D t (fun e => e.val.trans c)
  · intro e x y hxy
    exact e.property hxy
  · intro e f hef
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply c.injective
    exact congrArg (fun z : Thorp.Young.Cells D ≃ Fin n => z x) hef

end Thorp.Specht

namespace Thorp.Young
open scoped Classical

def transposeCells (D : YoungDiagram) : Cells D ≃o Cells D.transpose where
  toFun x := ⟨x.val.swap, by
    change x.val.swap ∈ D.transpose
    rw [YoungDiagram.mem_transpose, Prod.swap_swap]
    exact x.property⟩
  invFun x := ⟨x.val.swap, (YoungDiagram.mem_transpose.mp x.property)⟩
  left_inv x := by apply Subtype.ext; exact Prod.swap_swap x.val
  right_inv x := by apply Subtype.ext; exact Prod.swap_swap x.val
  map_rel_iff' := by intro x y; exact and_comm

lemma extensions_card_orderIso {A : Type uA} {B : Type uB} [Fintype A] [Fintype B] [PartialOrder A] [PartialOrder B]
    (e : A ≃o B) : Fintype.card (Extensions A) = Fintype.card (Extensions B) := by
  let c := finCongr (Fintype.card_congr e.toEquiv)
  let F : Extensions A ≃ Extensions B := {
    toFun := fun l => ⟨(e.symm.toEquiv.trans l.val).trans c, fun _ _ h => l.property (e.symm.strictMono h)⟩
    invFun := fun l => ⟨(e.toEquiv.trans l.val).trans c.symm, fun _ _ h => l.property (e.strictMono h)⟩
    left_inv := by intro l; apply Subtype.ext; ext x; simp [c]
    right_inv := by intro l; apply Subtype.ext; ext x; simp [c] }
  exact Fintype.card_congr F

lemma rank_strictMono (D : YoungDiagram) : StrictMono (fun x : Cells D => x.val.1 + x.val.2) := by
  intro x y hxy
  have hle := hxy.le
  have hn : x.val ≠ y.val := fun h => hxy.ne (Subtype.ext h)
  have he : x.val.1 ≠ y.val.1 ∨ x.val.2 ≠ y.val.2 := by
    by_contra hh
    push Not at hh
    exact hn (Prod.ext hh.1 hh.2)
  change x.val.1 + x.val.2 < y.val.1 + y.val.2
  rcases he with he | he <;> have := hle.1 <;> have := hle.2 <;> omega

def longest (D : YoungDiagram) : ℕ := max (D.rowLen 0) (D.colLen 0)

lemma coord_lt_longest (D : YoungDiagram) (x : Cells D) :
    x.val.1 < longest D ∧ x.val.2 < longest D := by
  constructor
  · exact (YoungDiagram.mem_iff_lt_colLen.mp (D.up_left_mem le_rfl (Nat.zero_le _) x.property)).trans_le (le_max_right _ _)
  · exact (YoungDiagram.mem_iff_lt_rowLen.mp (D.up_left_mem (Nat.zero_le _) le_rfl x.property)).trans_le (le_max_left _ _)

theorem factorial_le_rank_degree {n : ℕ} (D : YoungDiagram) (t : Fin n ≃ Cells D) :
    n.factorial ≤ (2 * longest D) ^ n * Module.finrank ℂ (Thorp.Specht.module D t).toSubmodule := by
  have hh := rank_extension_bound (Cells D) (fun x => x.val.1 + x.val.2) (rank_strictMono D)
    (2 * longest D) (fun x => by have := coord_lt_longest D x; omega)
  have hc : Fintype.card (Cells D) = n := (Fintype.card_congr t.symm).trans (Fintype.card_fin n)
  rw [hc] at hh
  exact hh.trans (Nat.mul_le_mul_left _ (Thorp.Specht.extensions_card_le_degree D t))

end Thorp.Young

end

end OAI
