import Mathlib
import OAI.Combinatorics.BalancedRyser.Incidence.Affine

namespace OAI

namespace Balanced.TupleAlignment

variable {F : Type*} [Field F]

def lineEvalEquiv (d e : Direction F) (hne : d ≠ e) : Point F ≃ F × F where
  toFun p := (lineEval d p, lineEval e p)
  invFun a := lineIntersection (d, a.1) (e, a.2)
  left_inv p := by
    rcases p with ⟨x,y⟩
    cases d with
    | none =>
      cases e with
      | none => exact (hne rfl).elim
      | some b => simp [lineEval, lineIntersection]
    | some a =>
      cases e with
      | none => simp [lineEval, lineIntersection]
      | some b =>
        have hab : a - b ≠ 0 := sub_ne_zero.mpr (by simpa using hne)
        apply Prod.ext <;> simp only [lineEval, lineIntersection]
        · field_simp
          ring
        · field_simp
          ring
  right_inv p := by
    rcases p with ⟨x,y⟩
    cases d with
    | none =>
      cases e with
      | none => exact (hne rfl).elim
      | some b => simp [lineEval, lineIntersection]
    | some a =>
      cases e with
      | none => simp [lineEval, lineIntersection]
      | some b =>
        have hab : a - b ≠ 0 := sub_ne_zero.mpr (by simpa using hne)
        apply Prod.ext <;> simp only [lineEval, lineIntersection]
        · ring
        · field_simp
          ring

@[simp] theorem lineEvalEquiv_apply (d e : Direction F) (hne : d ≠ e) (p : Point F) :
    lineEvalEquiv d e hne p = (lineEval d p, lineEval e p) := rfl

@[simp] theorem lineEvalEquiv_symm_apply (d e : Direction F) (hne : d ≠ e) (a : F × F) :
    (lineEvalEquiv d e hne).symm a = lineIntersection (d,a.1) (e,a.2) := rfl

def offsetPairsEquiv (σ : Fin 4 → Bool) :
    (Fin 4 → Bool → F) ≃ (Fin 4 → F × F) where
  toFun o i := (o i (σ i), o (i + 1) (!(σ (i + 1))))
  invFun p i b := if b = σ i then (p i).1 else (p (i - 1)).2
  left_inv o := by
    funext i b
    cases h : σ i <;> cases b <;> simp [h]
  right_inv p := by
    funext i
    apply Prod.ext <;> simp

def tuplePositionEquiv (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool) :
    (Fin 4 → Bool → F) ≃ (Fin 4 → Point F) :=
  (offsetPairsEquiv σ).trans
    (Equiv.piCongrRight fun i => (lineEvalEquiv (d i) (d (i + 1)) (hd i)).symm)

@[simp] theorem tuplePositionEquiv_apply (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (o : Fin 4 → Bool → F) (i : Fin 4) :
    tuplePositionEquiv d hd σ o i =
      lineIntersection (d i, o i (σ i))
        (d (i + 1), o (i + 1) (!(σ (i + 1)))) := rfl

def linePointEquiv (g : Direction F) (c : F) :
    {p : Point F // OnLine p (g, c)} ≃ F where
  toFun p := match g with | none => p.1.2 | some _ => p.1.1
  invFun t := ⟨match g with | none => (c,t) | some m => (t,m*t+c), by
    cases g <;> simp [OnLine, lineEval]⟩
  left_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨x,y⟩,h⟩
    cases g with
    | none =>
      have hx : x = c := h
      simp [hx]
    | some m =>
      have hy : y - m*x = c := h
      apply Prod.ext
      · rfl
      · dsimp
        linear_combination -hy
  right_inv t := by cases g <;> rfl

def alignedOffsetsEquiv (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) :
    {o : Fin 4 → Bool → F // ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)} ≃
      (Fin 4 → F) :=
  (Equiv.subtypeEquivOfSubtype (tuplePositionEquiv d hd σ)).trans
    (Equiv.subtypePiEquivPi.trans
      (Equiv.piCongrRight fun _ => linePointEquiv g c))

theorem aligned_injective_iff (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F)
    (o : {o : Fin 4 → Bool → F //
      ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)}) :
    Function.Injective (tuplePositionEquiv d hd σ o.1) ↔
      Function.Injective (alignedOffsetsEquiv d hd σ g c o) := by
  constructor
  · intro h i j hij
    apply h
    have hsub :
        (⟨tuplePositionEquiv d hd σ o.1 i, o.2 i⟩ : {p // OnLine p (g,c)}) =
        ⟨tuplePositionEquiv d hd σ o.1 j, o.2 j⟩ :=
      (linePointEquiv g c).injective hij
    exact congrArg Subtype.val hsub
  · intro h i j hij
    apply h
    exact congrArg (linePointEquiv g c) (Subtype.ext hij)

def alignedDistinctOffsetsEquiv (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) :
    {o : {o : Fin 4 → Bool → F //
      ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)} //
      Function.Injective (tuplePositionEquiv d hd σ o.1)} ≃ (Fin 4 ↪ F) :=
  ((alignedOffsetsEquiv d hd σ g c).subtypeEquiv
    (aligned_injective_iff d hd σ g c)).trans
      (Equiv.subtypeInjectiveEquivEmbedding (Fin 4) F)

def sameLineOffsetsEquiv (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) :
    {o : Fin 4 → Bool → F //
      ∃ c, ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)} ≃
    Σ c : F, {o : Fin 4 → Bool → F //
      ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)} where
  toFun o := ⟨lineEval g (tuplePositionEquiv d hd σ o.1 0), o.1, by
    rcases o.2 with ⟨c,h⟩
    intro i
    exact (h i).trans (h 0).symm⟩
  invFun s := ⟨s.2.1, s.1, s.2.2⟩
  left_inv o := by apply Subtype.ext; rfl
  right_inv s := by
    rcases s with ⟨c, o, ho⟩
    have h0 : lineEval g (tuplePositionEquiv d hd σ o 0) = c := ho 0
    cases h0
    rfl

def successfulOffsetsEquiv (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) :
    {o : Fin 4 → Bool → F //
      (∃ c, ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)) ∧
      Function.Injective (tuplePositionEquiv d hd σ o)} ≃
    Σ c : F, {o : {o : Fin 4 → Bool → F //
      ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)} //
      Function.Injective (tuplePositionEquiv d hd σ o.1)} where
  toFun o := ⟨lineEval g (tuplePositionEquiv d hd σ o.1 0),
    ⟨o.1, by
      rcases o.2.1 with ⟨c,h⟩
      intro i
      exact (h i).trans (h 0).symm⟩, o.2.2⟩
  invFun s := ⟨s.2.1.1, ⟨s.1,s.2.1.2⟩, s.2.2⟩
  left_inv o := by apply Subtype.ext; rfl
  right_inv s := by
    rcases s with ⟨c, ⟨o,ho⟩,hi⟩
    have h0 : lineEval g (tuplePositionEquiv d hd σ o 0) = c := ho 0
    cases h0
    rfl

theorem uniform_map_equiv {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  classical
  ext b
  rw [PMF.map_apply, ← e.symm.tsum_eq]
  simp [Fintype.card_congr e]

section Finite
variable [Fintype F] [DecidableEq F]

theorem card_alignedOffsets (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) :
    Fintype.card {o : Fin 4 → Bool → F //
      ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)} = (Fintype.card F)^4 := by
  rw [Fintype.card_congr (alignedOffsetsEquiv d hd σ g c)]
  simp

theorem card_alignedDistinctOffsets (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) :
    Fintype.card {o : {o : Fin 4 → Bool → F //
      ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)} //
      Function.Injective (tuplePositionEquiv d hd σ o.1)} =
      (Fintype.card F).descFactorial 4 := by
  rw [Fintype.card_congr (alignedDistinctOffsetsEquiv d hd σ g c)]
  simp

theorem card_sameLineOffsets (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) :
    Fintype.card {o : Fin 4 → Bool → F //
      ∃ c, ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)} =
      (Fintype.card F)^5 := by
  rw [Fintype.card_congr (sameLineOffsetsEquiv d hd σ g)]
  simp only [Fintype.card_sigma, card_alignedOffsets, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

theorem card_successfulOffsets (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) :
    Fintype.card {o : Fin 4 → Bool → F //
      (∃ c, ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)) ∧
      Function.Injective (tuplePositionEquiv d hd σ o)} =
      Fintype.card F * (Fintype.card F).descFactorial 4 := by
  rw [Fintype.card_congr (successfulOffsetsEquiv d hd σ g)]
  simp only [Fintype.card_sigma, card_alignedDistinctOffsets, Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem alignedOffsets_probability (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) :
    (Fintype.card {o : Fin 4 → Bool → F //
      ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)} : ℝ) /
      Fintype.card (Fin 4 → Bool → F) = (Fintype.card F : ℝ)⁻¹^4 := by
  rw [card_alignedOffsets]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

omit [DecidableEq F] in
theorem tuplePosition_uniform (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool) :
    (PMF.uniformOfFintype (Fin 4 → Bool → F)).map
      (tuplePositionEquiv d hd σ) = PMF.uniformOfFintype (Fin 4 → Point F) :=
  uniform_map_equiv (tuplePositionEquiv d hd σ)

theorem alignedOffsets_outer_probability (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) :
    ((PMF.uniformOfFintype (Fin 4 → Bool → F)).toOuterMeasure
      {o | ∀ i, OnLine (tuplePositionEquiv d hd σ o i) (g,c)}).toReal =
      (Fintype.card F : ℝ)⁻¹^4 := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  convert alignedOffsets_probability d hd σ g c using 2
  congr 1

end Finite

end Balanced.TupleAlignment

end OAI
