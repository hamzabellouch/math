import OAI.Combinatorics.BalancedRyser.Local.TupleAlignment
import OAI.Combinatorics.BalancedRyser.Probability.FiniteUniformConditioning

namespace OAI

namespace Balanced.TupleAlignment

variable {F : Type*} [Field F]

abbrev ChildOffsets (a : Bool → F) :=
  {o : Fin 4 → Bool → F // o 0 = a}

def childFreshEquiv (a : Bool → F) : ChildOffsets a ≃ (Fin 3 → Bool → F) where
  toFun o i := o.1 i.succ
  invFun f := ⟨Fin.cases a f, rfl⟩
  left_inv o := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact o.2.symm
    · rfl
  right_inv f := rfl

@[simp] theorem tuplePositionEquiv_symm_apply
    (d : Fin 4 → Direction F) (hd : ∀ i, d i ≠ d (i + 1))
    (σ : Fin 4 → Bool) (p : Fin 4 → Point F) (i : Fin 4) (b : Bool) :
    (tuplePositionEquiv d hd σ).symm p i b =
      if b = σ i then lineEval (d i) (p i) else lineEval (d i) (p (i - 1)) := by
  simp [tuplePositionEquiv, offsetPairsEquiv, lineEvalEquiv]

@[simp] theorem lineEvalEquiv_symm_fst (d e : Direction F) (hne : d ≠ e) (a : F × F) :
    lineEval d ((lineEvalEquiv d e hne).symm a) = a.1 :=
  congrArg Prod.fst ((lineEvalEquiv d e hne).apply_symm_apply a)

@[simp] theorem lineEvalEquiv_symm_snd (d e : Direction F) (hne : d ≠ e) (a : F × F) :
    lineEval e ((lineEvalEquiv d e hne).symm a) = a.2 :=
  congrArg Prod.snd ((lineEvalEquiv d e hne).apply_symm_apply a)

def childAlignedPositions (d₀ g : Direction F) (hg : d₀ ≠ g)
    (σ₀ : Bool) (c : F) (a : Bool → F) (x : F × F) : Fin 4 → Point F :=
  ![(lineEvalEquiv d₀ g hg).symm (a σ₀, c),
    ((linePointEquiv g c).symm x.1).1,
    ((linePointEquiv g c).symm x.2).1,
    (lineEvalEquiv d₀ g hg).symm (a (!σ₀), c)]

theorem childAlignedPositions_onLine (d₀ g : Direction F) (hg : d₀ ≠ g)
    (σ₀ : Bool) (c : F) (a : Bool → F) (x : F × F) (i : Fin 4) :
    OnLine (childAlignedPositions d₀ g hg σ₀ c a x i) (g,c) := by
  fin_cases i
  · exact lineEvalEquiv_symm_snd d₀ g hg (a σ₀,c)
  · exact ((linePointEquiv g c).symm x.1).2
  · exact ((linePointEquiv g c).symm x.2).2
  · exact lineEvalEquiv_symm_snd d₀ g hg (a (!σ₀),c)

abbrev AlignedChildOffsets (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) (a : Bool → F) :=
  {o : ChildOffsets a // ∀ i,
    OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)}

def alignedChildFromPair (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : d 0 ≠ g) (c : F) (a : Bool → F) (x : F × F) :
    AlignedChildOffsets d hd σ g c a := by
  let p := childAlignedPositions (d 0) g hg (σ 0) c a x
  refine ⟨⟨(tuplePositionEquiv d hd σ).symm p, ?_⟩, ?_⟩
  · funext b
    rw [tuplePositionEquiv_symm_apply]
    by_cases hb : b = σ 0
    · rw [ite_eq_left hb]
      change lineEval (d 0) ((lineEvalEquiv (d 0) g hg).symm (a (σ 0), c)) = a b
      rw [lineEvalEquiv_symm_fst, hb]
    · rw [ite_eq_right hb]
      change lineEval (d 0) ((lineEvalEquiv (d 0) g hg).symm (a (!(σ 0)), c)) = a b
      rw [lineEvalEquiv_symm_fst]
      cases b <;> cases hσ : σ 0 <;> simp_all
  · intro i
    change OnLine ((tuplePositionEquiv d hd σ)
      ((tuplePositionEquiv d hd σ).symm p) i) (g,c)
    rw [Equiv.apply_symm_apply]
    exact childAlignedPositions_onLine (d 0) g hg (σ 0) c a x i

@[simp] theorem alignedChildFromPair_positions (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : d 0 ≠ g) (c : F) (a : Bool → F) (x : F × F) :
    tuplePositionEquiv d hd σ (alignedChildFromPair d hd σ g hg c a x).1.1 =
      childAlignedPositions (d 0) g hg (σ 0) c a x := by
  exact (tuplePositionEquiv d hd σ).apply_symm_apply _

@[simp] theorem tuplePosition_lineEval_left (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (o : Fin 4 → Bool → F) (i : Fin 4) :
    lineEval (d i) (tuplePositionEquiv d hd σ o i) = o i (σ i) :=
  lineEvalEquiv_symm_fst (d i) (d (i + 1)) (hd i) _

@[simp] theorem tuplePosition_lineEval_right (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (o : Fin 4 → Bool → F) (i : Fin 4) :
    lineEval (d (i + 1)) (tuplePositionEquiv d hd σ o i) =
      o (i + 1) (!(σ (i + 1))) :=
  lineEvalEquiv_symm_snd (d i) (d (i + 1)) (hd i) _

def alignedChildToPair (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) (a : Bool → F)
    (o : AlignedChildOffsets d hd σ g c a) : F × F :=
  ((linePointEquiv g c) ⟨tuplePositionEquiv d hd σ o.1.1 1, o.2 1⟩,
   (linePointEquiv g c) ⟨tuplePositionEquiv d hd σ o.1.1 2, o.2 2⟩)

def alignedChildOffsetsEquiv (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : d 0 ≠ g) (c : F) (a : Bool → F) :
    AlignedChildOffsets d hd σ g c a ≃ F × F where
  toFun := alignedChildToPair d hd σ g c a
  invFun := alignedChildFromPair d hd σ g hg c a
  left_inv o := by
    apply Subtype.ext
    apply Subtype.ext
    apply (tuplePositionEquiv d hd σ).injective
    rw [alignedChildFromPair_positions]
    funext i
    fin_cases i
    · change (lineEvalEquiv (d 0) g hg).symm (a (σ 0), c) = _
      apply (lineEvalEquiv (d 0) g hg).injective
      rw [Equiv.apply_symm_apply]
      apply Prod.ext
      · change a (σ 0) = lineEval (d 0) (tuplePositionEquiv d hd σ o.1.1 0)
        rw [tuplePosition_lineEval_left, o.1.2]
      · exact (o.2 0).symm
    · exact congrArg Subtype.val ((linePointEquiv g c).symm_apply_apply
        ⟨tuplePositionEquiv d hd σ o.1.1 1, o.2 1⟩)
    · exact congrArg Subtype.val ((linePointEquiv g c).symm_apply_apply
        ⟨tuplePositionEquiv d hd σ o.1.1 2, o.2 2⟩)
    · change (lineEvalEquiv (d 0) g hg).symm (a (!(σ 0)), c) = _
      apply (lineEvalEquiv (d 0) g hg).injective
      rw [Equiv.apply_symm_apply]
      apply Prod.ext
      · change a (!(σ 0)) = lineEval (d 0) (tuplePositionEquiv d hd σ o.1.1 3)
        have h := tuplePosition_lineEval_right d hd σ o.1.1 3
        simpa only [show (3 : Fin 4) + 1 = 0 from rfl, o.1.2] using h.symm
      · exact (o.2 3).symm
  right_inv x := by
    simp only [alignedChildToPair, alignedChildFromPair_positions]
    change ((linePointEquiv g c) ((linePointEquiv g c).symm x.1),
      (linePointEquiv g c) ((linePointEquiv g c).symm x.2)) = x
    simp only [Equiv.apply_symm_apply, Prod.mk.eta]

abbrev ChildOffsetsAt (j : Fin 4) (a : Bool → F) :=
  {o : Fin 4 → Bool → F // o j = a}

def childRotationEquiv (j : Fin 4) (a : Bool → F) :
    ChildOffsetsAt j a ≃ ChildOffsets a where
  toFun o := ⟨fun i => o.1 (i + j), by simpa using o.2⟩
  invFun o := ⟨fun i => o.1 (i - j), by simpa using o.2⟩
  left_inv o := by
    apply Subtype.ext
    funext i
    simp
  right_inv o := by
    apply Subtype.ext
    funext i
    simp

omit [Field F] in
theorem rotated_adjacent (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (j : Fin 4) :
    ∀ i, d (i + j) ≠ d (i + 1 + j) := by
  intro i
  simpa only [add_assoc, add_comm, add_left_comm] using hd (i + j)

theorem tuplePosition_rotation (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (o : Fin 4 → Bool → F) (j i : Fin 4) :
    tuplePositionEquiv (fun k => d (k + j)) (rotated_adjacent d hd j)
      (fun k => σ (k + j)) (fun k => o (k + j)) i =
      tuplePositionEquiv d hd σ o (i + j) := by
  simp only [tuplePositionEquiv_apply, add_assoc, add_comm]

abbrev AlignedChildOffsetsAt (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) (j : Fin 4) (a : Bool → F) :=
  {o : ChildOffsetsAt j a // ∀ i,
    OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)}

def alignedChildRotationEquiv (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (c : F) (j : Fin 4) (a : Bool → F) :
    AlignedChildOffsetsAt d hd σ g c j a ≃
      AlignedChildOffsets (fun i => d (i + j)) (rotated_adjacent d hd j)
        (fun i => σ (i + j)) g c a :=
  Equiv.subtypeEquiv (childRotationEquiv j a) (fun o => by
    constructor
    · intro ho i
      change OnLine (tuplePositionEquiv (fun k => d (k + j))
        (rotated_adjacent d hd j) (fun k => σ (k + j))
        (fun k => o.1 (k + j)) i) (g,c)
      rw [tuplePosition_rotation]
      exact ho (i + j)
    · intro ho i
      have h := ho (i - j)
      change OnLine (tuplePositionEquiv (fun k => d (k + j))
        (rotated_adjacent d hd j) (fun k => σ (k + j))
        (fun k => o.1 (k + j)) (i - j)) (g,c) at h
      rw [tuplePosition_rotation] at h
      simpa only [sub_add_cancel] using h)

def alignedChildOffsetsAtEquiv (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (j : Fin 4) (hg : d j ≠ g) (c : F) (a : Bool → F) :
    AlignedChildOffsetsAt d hd σ g c j a ≃ F × F :=
  (alignedChildRotationEquiv d hd σ g c j a).trans
    (alignedChildOffsetsEquiv (fun i => d (i + j)) (rotated_adjacent d hd j)
      (fun i => σ (i + j)) g (by simpa using hg) c a)

instance (a : Bool → F) : Nonempty (ChildOffsets a) :=
  ⟨(childFreshEquiv a).symm (fun _ _ => 0)⟩

instance (j : Fin 4) (a : Bool → F) : Nonempty (ChildOffsetsAt j a) :=
  ⟨(childRotationEquiv j a).symm ((childFreshEquiv a).symm (fun _ _ => 0))⟩

section Finite
variable [Fintype F] [DecidableEq F]

omit [Field F] in
theorem card_childOffsets (a : Bool → F) :
    Fintype.card (ChildOffsets a) = Fintype.card F ^ 6 := by
  rw [Fintype.card_congr (childFreshEquiv a)]
  simp [← pow_mul]

theorem card_alignedChildOffsets (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : d 0 ≠ g) (c : F) (a : Bool → F) :
    Fintype.card (AlignedChildOffsets d hd σ g c a) = Fintype.card F ^ 2 := by
  rw [Fintype.card_congr (alignedChildOffsetsEquiv d hd σ g hg c a)]
  simp [pow_two]

theorem alignedChildOffsets_probability (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : d 0 ≠ g) (c : F) (a : Bool → F) :
    (Fintype.card (AlignedChildOffsets d hd σ g c a) : ℝ) /
      Fintype.card (ChildOffsets a) = (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  rw [card_alignedChildOffsets d hd σ g hg, card_childOffsets]
  simp only [Nat.cast_pow]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem alignedChildOffsets_pmf_probability (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (hg : d 0 ≠ g) (c : F) (a : Bool → F) :
    ((PMF.uniformOfFintype (ChildOffsets a)).toOuterMeasure
      {o | ∀ i, OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  exact alignedChildOffsets_probability d hd σ g hg c a

omit [Field F] in
theorem card_childOffsetsAt (j : Fin 4) (a : Bool → F) :
    Fintype.card (ChildOffsetsAt j a) = Fintype.card F ^ 6 := by
  rw [Fintype.card_congr (childRotationEquiv j a), card_childOffsets]

theorem card_alignedChildOffsetsAt (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (j : Fin 4) (hg : d j ≠ g) (c : F) (a : Bool → F) :
    Fintype.card (AlignedChildOffsetsAt d hd σ g c j a) = Fintype.card F ^ 2 := by
  rw [Fintype.card_congr (alignedChildOffsetsAtEquiv d hd σ g j hg c a)]
  simp [pow_two]

theorem alignedChildOffsetsAt_pmf_probability (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (j : Fin 4) (hg : d j ≠ g) (c : F) (a : Bool → F) :
    ((PMF.uniformOfFintype (ChildOffsetsAt j a)).toOuterMeasure
      {o | ∀ i, OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)}).toReal =
      (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  change ((Fintype.card (AlignedChildOffsetsAt d hd σ g c j a) : ENNReal) /
    (Fintype.card (ChildOffsetsAt j a) : ENNReal)).toReal = _
  rw [card_alignedChildOffsetsAt d hd σ g j hg, card_childOffsetsAt]
  simp only [Nat.cast_pow, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem alignedChildOffsetsAt_supported (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (j : Fin 4) (hg : d j ≠ g) (c : F) (a : Bool → F) :
    ∃ o ∈ {o : ChildOffsetsAt j a |
      ∀ i, OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)},
      o ∈ (PMF.uniformOfFintype (ChildOffsetsAt j a)).support := by
  let o := (alignedChildOffsetsAtEquiv d hd σ g j hg c a).symm (0,0)
  exact ⟨o.1, o.2, PMF.mem_support_uniformOfFintype _⟩

theorem alignedChildOffsetsAt_conditional_law (d : Fin 4 → Direction F)
    (hd : ∀ i, d i ≠ d (i + 1)) (σ : Fin 4 → Bool)
    (g : Direction F) (j : Fin 4) (hg : d j ≠ g) (c : F) (a : Bool → F) :
    (PMF.uniformOfFintype (ChildOffsetsAt j a)).filter
      {o | ∀ i, OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)}
      (alignedChildOffsetsAt_supported d hd σ g j hg c a) =
    (PMF.uniformOfFintype (F × F)).map
      (fun x => ((alignedChildOffsetsAtEquiv d hd σ g j hg c a).symm x).1) := by
  let : Nonempty (AlignedChildOffsetsAt d hd σ g c j a) :=
    ⟨(alignedChildOffsetsAtEquiv d hd σ g j hg c a).symm (0,0)⟩
  let : Nonempty ({o : ChildOffsetsAt j a |
      ∀ i, OnLine (tuplePositionEquiv d hd σ o.1 i) (g,c)} : Set (ChildOffsetsAt j a)) :=
    ⟨(alignedChildOffsetsAtEquiv d hd σ g j hg c a).symm (0,0)⟩
  rw [Balanced.uniform_filter_eq_subtype_map]
  change (PMF.uniformOfFintype (AlignedChildOffsetsAt d hd σ g c j a)).map Subtype.val = _
  have h := uniform_map_equiv (alignedChildOffsetsAtEquiv d hd σ g j hg c a).symm
  rw [← h, PMF.map_comp]
  rfl

end Finite
end Balanced.TupleAlignment

end OAI
