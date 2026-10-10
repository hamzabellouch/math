import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

open FreeGroup

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def freeWordBall (m : ℕ) : Finset (FreeGroup α) := by
  classical
  exact (Finset.range (m + 1)).biUnion fun k =>
    Finset.univ.image (fun f : Fin k → α × Bool => FreeGroup.mk (List.ofFn f))

lemma mem_freeWordBall (g : FreeGroup α) (m : ℕ) :
    g ∈ freeWordBall m ↔ FreeGroup.norm g ≤ m := by
  classical
  constructor
  · intro hg
    obtain ⟨k, hk, hg'⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hg'
    exact FreeGroup.norm_mk_le.trans (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  · intro hg
    apply Finset.mem_biUnion.mpr
    refine ⟨g.toWord.length, Finset.mem_range.mpr (Nat.lt_succ_of_le hg), ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨fun i => g.toWord.get i, Finset.mem_univ _, ?_⟩
    simpa using (FreeGroup.mk_toWord (x := g))

lemma one_mem_freeWordBall (m : ℕ) : (1 : FreeGroup α) ∈ freeWordBall m := by
  rw [mem_freeWordBall]
  simp

lemma exists_freeBallTranslation (m : ℕ) (a : α) :
    ∃ σ : Equiv.Perm (freeWordBall (α := α) m),
      ∀ (x : freeWordBall (α := α) m), FreeGroup.of a * x.val ∈ freeWordBall m →
        (σ x).val = FreeGroup.of a * x.val := by
  classical
  let D := {x : freeWordBall (α := α) m // FreeGroup.of a * x.val ∈ freeWordBall m}
  let f : D → freeWordBall (α := α) m := fun x => x.val
  let g : D → freeWordBall (α := α) m := fun x => ⟨FreeGroup.of a * x.val.val, x.property⟩
  have hf : Function.Injective f := Subtype.val_injective
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact mul_left_cancel (congrArg Subtype.val h)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨σ, fun x hx => ?_⟩
  exact congrArg Subtype.val (hσ ⟨x, hx⟩)

noncomputable def freeBallTranslation (m : ℕ) (a : α) :
    Equiv.Perm (freeWordBall (α := α) m) :=
  (exists_freeBallTranslation m a).choose

lemma freeBallTranslation_apply (m : ℕ) (a : α) (x : freeWordBall (α := α) m)
    (hx : FreeGroup.of a * x.val ∈ freeWordBall m) :
    (freeBallTranslation m a x).val = FreeGroup.of a * x.val :=
  (exists_freeBallTranslation m a).choose_spec x hx

lemma freeBallTranslation_inv_apply (m : ℕ) (a : α) (x : freeWordBall (α := α) m)
    (hx : (FreeGroup.of a)⁻¹ * x.val ∈ freeWordBall m) :
    ((freeBallTranslation m a)⁻¹ x).val = (FreeGroup.of a)⁻¹ * x.val := by
  let y : freeWordBall (α := α) m := ⟨(FreeGroup.of a)⁻¹ * x.val, hx⟩
  have hy : freeBallTranslation m a y = x := by
    apply Subtype.ext
    rw [freeBallTranslation_apply]
    · simp [y]
    · simp [y, x.property]
  have hiy := congrArg (freeBallTranslation m a).symm hy
  simp only [Equiv.symm_apply_apply] at hiy
  exact congrArg Subtype.val hiy.symm

noncomputable def freeFiniteQuotient (m : ℕ) :
    FreeGroup α →* Equiv.Perm (freeWordBall (α := α) m) :=
  FreeGroup.lift (freeBallTranslation m)

lemma freeFiniteQuotient_of (m : ℕ) (a : α) :
    freeFiniteQuotient m (FreeGroup.of a) = freeBallTranslation m a := by
  simp [freeFiniteQuotient]

omit [Fintype α] [DecidableEq α] in
lemma free_mk_cons_pos (a : α) (w : List (α × Bool)) :
    FreeGroup.mk ((a, true) :: w) = FreeGroup.of a * FreeGroup.mk w := rfl

omit [Fintype α] [DecidableEq α] in
lemma free_mk_cons_neg (a : α) (w : List (α × Bool)) :
    FreeGroup.mk ((a, false) :: w) = (FreeGroup.of a)⁻¹ * FreeGroup.mk w := rfl

lemma freeFiniteQuotient_word_apply (m : ℕ) (w : List (α × Bool)) (hw : w.length ≤ m) :
    (freeFiniteQuotient m (FreeGroup.mk w) ⟨1, one_mem_freeWordBall m⟩).val =
      FreeGroup.mk w := by
  induction w with
  | nil => simp [← FreeGroup.one_eq_mk]
  | cons x w ih =>
    have hw' : w.length ≤ m := (Nat.le_succ w.length).trans hw
    have ih' := ih hw'
    have hmem : FreeGroup.mk (x :: w) ∈ freeWordBall (α := α) m :=
      (mem_freeWordBall _ _).mpr (FreeGroup.norm_mk_le.trans hw)
    rcases x with ⟨a, b⟩
    cases b
    · rw [free_mk_cons_neg] at hmem ⊢
      simp only [_root_.map_mul, _root_.map_inv, freeFiniteQuotient_of, Equiv.Perm.coe_mul,
        Function.comp_apply]
      rw [freeBallTranslation_inv_apply, ih']
      simpa only [ih'] using hmem
    · rw [free_mk_cons_pos] at hmem ⊢
      simp only [_root_.map_mul, freeFiniteQuotient_of, Equiv.Perm.coe_mul, Function.comp_apply]
      rw [freeBallTranslation_apply, ih']
      simpa only [ih'] using hmem

lemma freeFiniteQuotient_apply_base (m : ℕ) (g : FreeGroup α) (hg : g ∈ freeWordBall m) :
    (freeFiniteQuotient m g ⟨1, one_mem_freeWordBall m⟩).val = g := by
  have hw := freeFiniteQuotient_word_apply m g.toWord ((mem_freeWordBall g m).mp hg)
  simpa only [FreeGroup.mk_toWord] using hw

lemma freeFiniteQuotient_injOn_ball (m : ℕ) :
    Set.InjOn (freeFiniteQuotient (α := α) m) (↑(freeWordBall (α := α) m) : Set (FreeGroup α)) := by
  intro x hx y hy h
  have he := congrArg (fun σ : Equiv.Perm (freeWordBall (α := α) m) =>
    (σ ⟨1, one_mem_freeWordBall m⟩).val) h
  simpa only [freeFiniteQuotient_apply_base m x hx,
    freeFiniteQuotient_apply_base m y hy] using he

lemma freeFiniteQuotient_injOn_finset (S : Finset (FreeGroup α)) :
    ∃ m : ℕ, Set.InjOn (freeFiniteQuotient (α := α) m) (↑S : Set (FreeGroup α)) := by
  refine ⟨S.sup FreeGroup.norm, fun x hx y hy h => ?_⟩
  apply freeFiniteQuotient_injOn_ball _ ?_ ?_ h
  · exact (mem_freeWordBall _ _).mpr (Finset.le_sup hx)
  · exact (mem_freeWordBall _ _).mpr (Finset.le_sup hy)

lemma eventually_freeFiniteQuotient_eq_iff (s t : FreeGroup α) :
    ∀ᶠ m in Filter.atTop, freeFiniteQuotient m s = freeFiniteQuotient m t ↔ s = t := by
  filter_upwards [Filter.eventually_ge_atTop (max (FreeGroup.norm s) (FreeGroup.norm t))] with m hm
  constructor
  · intro h
    exact freeFiniteQuotient_injOn_ball m
      ((mem_freeWordBall _ _).mpr ((le_max_left _ _).trans hm))
      ((mem_freeWordBall _ _).mpr ((le_max_right _ _).trans hm)) h
  · rintro rfl
    rfl

lemma tendsto_freeFiniteQuotient_diagonal (s t : FreeGroup α) :
    Filter.Tendsto (fun m => if freeFiniteQuotient m s = freeFiniteQuotient m t then (1 : ℂ) else 0)
      Filter.atTop (nhds (if s = t then (1 : ℂ) else 0)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_freeFiniteQuotient_eq_iff s t] with m hm
  simp only [hm]

end WeakPureInfiniteness
end

end OAI
