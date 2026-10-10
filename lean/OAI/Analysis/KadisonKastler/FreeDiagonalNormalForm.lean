import OAI.Analysis.KadisonKastler.FreeDiagonalWords

namespace OAI

/-! # Algebraic normal form for the finite diagonal generators -/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B] {r d : ℕ}
  (e : Fin r → Fin d → B)

def reducedDiagonalSpan : Submodule ℂ B :=
  Submodule.span ℂ {x | ∃ w, ReducedDiagonalWord w ∧ x = diagonalWord e w}

theorem diagonalWord_mem_reducedDiagonalSpan {w : List (Fin r × Fin d)}
    (hw : ReducedDiagonalWord w) : diagonalWord e w ∈ reducedDiagonalSpan e :=
  Submodule.subset_span ⟨w, hw, rfl⟩

theorem one_mem_reducedDiagonalSpan : (1 : B) ∈ reducedDiagonalSpan e :=
  diagonalWord_mem_reducedDiagonalSpan e List.IsChain.nil

theorem ReducedDiagonalWord.replace_label {i : Fin r} {a b : Fin d}
    {w : List (Fin r × Fin d)} (hw : ReducedDiagonalWord ((i, a) :: w)) :
    ReducedDiagonalWord ((i, b) :: w) :=
  List.IsChain.imp_head (x := (i, a)) (y := (i, b)) (fun h => h) hw

theorem diagonalCentered_mul_word_mem
    (hp : ∀ i a, IsStarProjection (e i a))
    (ho : ∀ i a b, a ≠ b → e i a * e i b = 0)
    (i : Fin r) (a : Fin d) {w : List (Fin r × Fin d)}
    (hw : ReducedDiagonalWord w) :
    diagonalCentered e i a * diagonalWord e w ∈ reducedDiagonalSpan e := by
  cases w with
  | nil =>
    simpa using diagonalWord_mem_reducedDiagonalSpan e (List.IsChain.singleton (i, a))
  | cons b w =>
    rcases b with ⟨j, b⟩
    by_cases h : i = j
    · subst j
      have ha := diagonalWord_mem_reducedDiagonalSpan e (hw.replace_label (b := a))
      have hb := diagonalWord_mem_reducedDiagonalSpan e hw
      have ht := diagonalWord_mem_reducedDiagonalSpan e hw.tail
      rw [diagonalWord_cons, ← mul_assoc, diagonalCentered_mul e hp ho]
      simp only [add_mul, sub_mul, smul_mul_assoc, one_mul]
      exact (reducedDiagonalSpan e).add_mem
        ((reducedDiagonalSpan e).sub_mem ((reducedDiagonalSpan e).smul_mem _ ha)
          ((reducedDiagonalSpan e).smul_mem _ hb))
        ((reducedDiagonalSpan e).smul_mem _ ht)
    · have hnew : ReducedDiagonalWord ((i, a) :: (j, b) :: w) := by
        exact List.isChain_cons.mpr ⟨by simpa using h, hw⟩
      exact diagonalWord_mem_reducedDiagonalSpan e hnew

theorem diagonalCentered_mul_mem_reducedDiagonalSpan
    (hp : ∀ i a, IsStarProjection (e i a))
    (ho : ∀ i a b, a ≠ b → e i a * e i b = 0)
    (i : Fin r) (a : Fin d) {x : B} (hx : x ∈ reducedDiagonalSpan e) :
    diagonalCentered e i a * x ∈ reducedDiagonalSpan e := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact diagonalCentered_mul_word_mem e hp ho i a hw
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [mul_add] using (reducedDiagonalSpan e).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [mul_smul_comm] using (reducedDiagonalSpan e).smul_mem c ih

theorem diagonalWord_mul_mem_reducedDiagonalSpan
    (hp : ∀ i a, IsStarProjection (e i a))
    (ho : ∀ i a b, a ≠ b → e i a * e i b = 0)
    (w : List (Fin r × Fin d)) {x : B} (hx : x ∈ reducedDiagonalSpan e) :
    diagonalWord e w * x ∈ reducedDiagonalSpan e := by
  induction w with
  | nil => simpa using hx
  | cons a w ih =>
    rw [diagonalWord_cons, mul_assoc]
    exact diagonalCentered_mul_mem_reducedDiagonalSpan e hp ho a.1 a.2 ih

theorem mul_mem_reducedDiagonalSpan
    (hp : ∀ i a, IsStarProjection (e i a))
    (ho : ∀ i a b, a ≠ b → e i a * e i b = 0)
    {x y : B} (hx : x ∈ reducedDiagonalSpan e) (hy : y ∈ reducedDiagonalSpan e) :
    x * y ∈ reducedDiagonalSpan e := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, _, rfl⟩ := hx
    exact diagonalWord_mul_mem_reducedDiagonalSpan e hp ho w hy
  | zero => simp
  | add x z hx hz ihx ihz =>
    simpa only [add_mul] using (reducedDiagonalSpan e).add_mem ihx ihz
  | smul c x hx ih =>
    simpa only [smul_mul_assoc] using (reducedDiagonalSpan e).smul_mem c ih

theorem star_mem_reducedDiagonalSpan
    (hp : ∀ i a, IsStarProjection (e i a))
    {x : B} (hx : x ∈ reducedDiagonalSpan e) : star x ∈ reducedDiagonalSpan e := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [star_diagonalWord e hp]
    exact diagonalWord_mem_reducedDiagonalSpan e hw.reverse
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [star_add] using (reducedDiagonalSpan e).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [star_smul] using (reducedDiagonalSpan e).smul_mem (star c) ih

def reducedDiagonalAlgebra
    (hp : ∀ i a, IsStarProjection (e i a))
    (ho : ∀ i a b, a ≠ b → e i a * e i b = 0) : StarSubalgebra ℂ B where
  carrier := reducedDiagonalSpan e
  zero_mem' := (reducedDiagonalSpan e).zero_mem
  add_mem' := (reducedDiagonalSpan e).add_mem
  one_mem' := one_mem_reducedDiagonalSpan e
  mul_mem' := mul_mem_reducedDiagonalSpan e hp ho
  algebraMap_mem' c := by
    change algebraMap ℂ B c ∈ reducedDiagonalSpan e
    rw [Algebra.algebraMap_eq_smul_one]
    exact (reducedDiagonalSpan e).smul_mem c (one_mem_reducedDiagonalSpan e)
  star_mem' := star_mem_reducedDiagonalSpan e hp

theorem reducedDiagonalAlgebra_eq_adjoin
    (hp : ∀ i a, IsStarProjection (e i a))
    (ho : ∀ i a b, a ≠ b → e i a * e i b = 0) :
    reducedDiagonalAlgebra e hp ho =
      StarAlgebra.adjoin ℂ (Set.range (fun ia : Fin r × Fin d => e ia.1 ia.2)) := by
  let S := StarAlgebra.adjoin ℂ (Set.range (fun ia : Fin r × Fin d => e ia.1 ia.2))
  have hletter (i : Fin r) (a : Fin d) : diagonalCentered e i a ∈ S :=
    S.sub_mem (StarAlgebra.subset_adjoin ℂ _ ⟨(i, a), rfl⟩) (S.smul_mem S.one_mem _)
  have hword (w : List (Fin r × Fin d)) : diagonalWord e w ∈ S := by
    induction w with
    | nil => exact S.one_mem
    | cons a w ih => exact S.mul_mem (hletter a.1 a.2) ih
  apply le_antisymm
  · change reducedDiagonalSpan e ≤ S.toSubalgebra.toSubmodule
    apply Submodule.span_le.mpr
    rintro x ⟨w, _, rfl⟩
    exact hword w
  · apply StarAlgebra.adjoin_le
    rintro x ⟨⟨i, a⟩, rfl⟩
    have hc := diagonalWord_mem_reducedDiagonalSpan e (List.IsChain.singleton (i, a))
    have ht := (reducedDiagonalSpan e).smul_mem (Fintype.card (Fin d) : ℂ)⁻¹
      (one_mem_reducedDiagonalSpan e)
    change e i a ∈ reducedDiagonalSpan e
    simpa [diagonalWord, diagonalCentered] using (reducedDiagonalSpan e).add_mem hc ht

theorem generatedDiagonal_eq_reducedClosure
    (hp : ∀ i a, IsStarProjection (e i a))
    (ho : ∀ i a b, a ≠ b → e i a * e i b = 0) :
    generatedDiagonal e = (reducedDiagonalAlgebra e hp ho).topologicalClosure := by
  rw [reducedDiagonalAlgebra_eq_adjoin]
  rfl

end

end KadisonKastler

end OAI
