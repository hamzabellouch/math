import OAI.Combinatorics.SquareDifference.TupleEnergy

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference

noncomputable def tupleAddressReflect (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) : Equiv.Perm (TupleAddress S) :=
  Function.Involutive.toPerm
    (fun u a => (if a.1 = b then Equiv.swap α β else 1) * u a)
    (by
      intro u
      funext a
      by_cases ha : a.1 = b <;> simp [ha, ← mul_assoc])

lemma tupleProjection_reflect_all (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (v : TupleVertex) :
    tupleProjection S (reflect b α β v) = tupleAddressReflect S b α β (tupleProjection S v) := by
  funext a
  by_cases ha : a.1 = b <;> simp [tupleProjection, reflect, tupleAddressReflect, ha]

noncomputable def tupleEntryReflect (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) : Equiv.Perm (TupleListEntry S) :=
  Equiv.prodCongr (tupleAddressReflect S b α β) (Equiv.refl _)

lemma tupleListEdges_reflect (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (e : TupleListEntry S × TupleListEntry S) :
    (tupleEntryReflect S b α β e.1, tupleEntryReflect S b α β e.2) ∈ tupleListEdges S ↔
      e ∈ tupleListEdges S := by
  classical
  unfold tupleListEdges
  split_ifs with hs
  · simp only [mem_filter, mem_univ, true_and]
    exact addressEdge_left_translate tupleCycle (tupleT + 1)
      (fun a : {a : Fin tupleBlocks // a ∉ S} => if a.1 = b then Equiv.swap α β else 1)
      e.1.1 e.2.1
  · simp

lemma tupleValidity_reflect {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (Y : TupleListEntry S → ZMod p) :
    tupleValidity S (Y ∘ tupleEntryReflect S b α β) = tupleValidity S Y := by
  classical
  apply prod_equiv (Equiv.prodCongr (tupleEntryReflect S b α β) (tupleEntryReflect S b α β))
  · intro e
    exact (tupleListEdges_reflect S b α β e).symm
  · intro e _
    rfl

lemma tupleWeight_reflect (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (α β : Fin tupleH) (j : TupleVertex → TupleListIndex S) :
    tupleWeight S (j ∘ reflect b α β) = tupleWeight S j := by
  classical
  have heq : Matrix.submatrix (interaction (h := tupleH) S tupleDelta)
      (reflectEquiv b α β) (reflectEquiv b α β) = interaction S tupleDelta := by
    ext x y
    change interaction S tupleDelta (reflect b α β x) (reflect b α β y) = _
    exact interaction_reflect S tupleDelta b α β x y
  have hh := indexWeight_equiv (reflectEquiv b α β) (interaction S tupleDelta) j
  have hleft : indexWeight (Matrix.submatrix (interaction S tupleDelta)
      (reflectEquiv b α β) (reflectEquiv b α β)) (j ∘ reflect b α β) =
      indexWeight (interaction S tupleDelta) (j ∘ reflect b α β) := congrArg (fun H => indexWeight H (j ∘ reflect b α β)) heq
  exact hleft.symm.trans hh

lemma tupleOutput_reflect {p : ℕ} (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (α β : Fin tupleH) (Y : TupleListEntry S → ZMod p) (j : TupleVertex → TupleListIndex S) :
    tupleOutput S (Y ∘ tupleEntryReflect S b α β) (j ∘ reflect b α β) =
      tupleOutput S Y j ∘ reflect b α β := by
  funext v
  simp only [tupleOutput, Function.comp_def, tupleProjection_reflect_all,
    tupleEntryReflect, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]

lemma tupleComponent_reflect {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (G : (TupleVertex → ZMod p) → ℝ) :
    tupleComponent S (fun z => G (z ∘ reflect b α β)) = tupleComponent S G := by
  classical
  symm
  unfold tupleComponent
  rw [expect_precompose (tupleEntryReflect S b α β)
    (fun Y => 𝔼 j : TupleVertex → TupleListIndex S,
      tupleValidity S Y * tupleWeight S j * G (tupleOutput S Y j))]
  apply expect_congr rfl
  intro Y _
  rw [expect_precompose (reflectEquiv b α β)
    (fun j => tupleValidity S (Y ∘ tupleEntryReflect S b α β) *
      tupleWeight S j * G (tupleOutput S (Y ∘ tupleEntryReflect S b α β) j))]
  apply expect_congr rfl
  intro j _
  change tupleValidity S (Y ∘ tupleEntryReflect S b α β) *
      tupleWeight S (j ∘ reflect b α β) *
      G (tupleOutput S (Y ∘ tupleEntryReflect S b α β) (j ∘ reflect b α β)) = _
  rw [tupleValidity_reflect, tupleWeight_reflect, tupleOutput_reflect]

lemma tupleCutForm_symmetric {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH)
    (F G : (CutHalf b α β → ZMod p) → ℝ) :
    tupleComponent S (fun z => F (fun x => z x.1) * G (fun x => z (reflect b α β x.1))) =
      tupleComponent S (fun z => G (fun x => z x.1) * F (fun x => z (reflect b α β x.1))) := by
  rw [← tupleComponent_reflect (p := p) S b α β
    (fun z => G (fun x => z x.1) * F (fun x => z (reflect b α β x.1)))]
  apply congrArg (fun H : (TupleVertex → ZMod p) → ℝ => tupleComponent S H)
  funext z
  change F (fun x => z x.1) * G (fun x => z (reflect b α β x.1)) =
    G (fun x => z (reflect b α β x.1)) *
      F (fun x => z (reflect b α β (reflect b α β x.1)))
  have hz : (fun x : CutHalf b α β => z (reflect b α β (reflect b α β x.1))) =
      fun x : CutHalf b α β => z x.1 := funext fun x => congrArg z (reflect_involutive b α β x.1)
  rw [hz, mul_comm]

def symbolPotential {h : ℕ} (w : Equiv.Perm (Fin h)) : ℤ :=
  ∑ i : Fin h, (i.val : ℤ) * ((w.symm i).val : ℤ)

lemma symbolPotential_swap {h : ℕ} (w : Equiv.Perm (Fin h))
    {α β : Fin h} (hne : α ≠ β) :
    symbolPotential (Equiv.swap α β * w) - symbolPotential w =
      ((β.val : ℤ) - α.val) * (((w.symm α).val : ℤ) - (w.symm β).val) := by
  unfold symbolPotential
  rw [← sum_sub_distrib]
  calc
    _ = ∑ i : Fin h, (
      (if i = α then (α.val : ℤ) * ((w.symm β).val : ℤ) - (α.val : ℤ) * (w.symm α).val else 0) +
      (if i = β then (β.val : ℤ) * ((w.symm α).val : ℤ) - (β.val : ℤ) * (w.symm β).val else 0)) := by
      apply sum_congr rfl
      intro i _
      by_cases hi : i = α
      · subst i
        simp [Equiv.Perm.mul_def, hne]
      · by_cases hj : i = β
        · subst i
          simp [Equiv.Perm.mul_def, hne.symm]
        · simp [Equiv.Perm.mul_def, Equiv.swap_apply_of_ne_of_ne hi hj, hi, hj]
    _ = _ := by
      simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
      ring

def wordPotential {B : Type*} [Fintype B] {h : ℕ} (v : WordVertex B h) : ℤ :=
  ∑ b : B, symbolPotential (v b)

lemma wordPotential_reflect {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hne : α ≠ β) (v : WordVertex B h) :
    wordPotential (reflect b α β v) - wordPotential v =
      ((β.val : ℤ) - α.val) * (((v b).symm α).val - ((v b).symm β).val) := by
  unfold wordPotential
  rw [← sum_sub_distrib, sum_eq_single b]
  · simpa [reflect] using symbolPotential_swap (v b) hne
  · intro c _ hcb
    simp [reflect, hcb]
  · simp

def foldWord {B : Type*} [DecidableEq B] {h : ℕ} (b : B) (α β : Fin h)
    (v : WordVertex B h) : WordVertex B h :=
  if cutPlus b α β v then v else reflect b α β v

lemma foldWord_potential_le {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hab : α < β) (v : WordVertex B h) :
    wordPotential v ≤ wordPotential (foldWord b α β v) := by
  unfold foldWord
  split_ifs with hv
  · exact le_rfl
  · have hgap := wordPotential_reflect b hab.ne v
    have h₁ : 0 ≤ (β.val : ℤ) - α.val := sub_nonneg.mpr (by exact_mod_cast hab.le)
    have h₂ : 0 ≤ (((v b).symm α).val : ℤ) - ((v b).symm β).val := by
      have hh : (v b).symm β ≤ (v b).symm α := le_of_not_gt hv
      exact sub_nonneg.mpr (by exact_mod_cast hh)
    have := mul_nonneg h₁ h₂
    omega

lemma foldWord_potential_lt {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hab : α < β) (v : WordVertex B h)
    (hv : ¬ cutPlus b α β v) :
    wordPotential v < wordPotential (foldWord b α β v) := by
  rw [foldWord, ite_eq_right hv]
  have hgap := wordPotential_reflect b hab.ne v
  have h₁ : 0 < (β.val : ℤ) - α.val := sub_pos.mpr (by exact_mod_cast hab)
  have h₂ : 0 < (((v b).symm α).val : ℤ) - ((v b).symm β).val := by
    have hh : (v b).symm β < (v b).symm α :=
      lt_of_le_of_ne (le_of_not_gt hv) (by intro hh; exact hab.ne ((v b).symm.injective hh.symm))
    exact sub_pos.mpr (by exact_mod_cast hh)
  have := mul_pos h₁ h₂
  omega

lemma exists_unsorted_cut {B : Type*} [DecidableEq B] {h : ℕ}
    (v : WordVertex B h) (hv : v ≠ fun _ => 1) :
    ∃ b : B, ∃ α β : Fin h, α < β ∧ ¬ cutPlus b α β v := by
  by_contra! hn
  apply hv
  funext b
  have hm : Monotone ((v b).symm) := by
    intro α β hab
    rcases hab.eq_or_lt with rfl | hab
    · exact le_rfl
    · exact (hn b α β hab).le
  have heq : (v b).symm = 1 := (Equiv.Perm.monotone_iff _).mp hm
  exact inv_eq_one.mp heq

abbrev WordCut (B : Type*) (h : ℕ) := B × PositionPair h

def foldMap {B : Type*} [DecidableEq B] {h : ℕ} (cs : List (WordCut B h)) :
    WordVertex B h → WordVertex B h :=
  cs.foldr (fun c f => foldWord c.1 c.2.1.1 c.2.1.2 ∘ f) id

lemma exists_constant_fold {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ} :
    ∃ cs : List (WordCut B h), ∀ v : WordVertex B h, foldMap cs v = fun _ => 1 := by
  classical
  let R : Finset (WordVertex B h → WordVertex B h) :=
    univ.filter fun f => ∃ cs : List (WordCut B h), foldMap cs = f
  have hR : R.Nonempty := ⟨id, mem_filter.mpr ⟨mem_univ _, ⟨[], rfl⟩⟩⟩
  obtain ⟨f, hf, hmax⟩ := R.exists_max_image (fun f => ∑ v, wordPotential (f v)) hR
  obtain ⟨cs, rfl⟩ := (mem_filter.mp hf).2
  refine ⟨cs, fun v => ?_⟩
  by_contra hv
  obtain ⟨b, α, β, hab, hv⟩ := exists_unsorted_cut (foldMap cs v) hv
  let c : WordCut B h := (b, ⟨(α, β), hab⟩)
  have hmem : foldMap (c :: cs) ∈ R :=
    mem_filter.mpr ⟨mem_univ _, ⟨c :: cs, rfl⟩⟩
  have hlt : (∑ w : WordVertex B h, wordPotential (foldMap cs w)) <
      ∑ w : WordVertex B h, wordPotential (foldMap (c :: cs) w) := by
    apply sum_lt_sum
    · intro w _
      exact foldWord_potential_le b hab (foldMap cs w)
    · exact ⟨v, mem_univ _, foldWord_potential_lt b hab (foldMap cs v) hv⟩
  exact (not_lt_of_ge (hmax _ hmem)) hlt

lemma max_fold_preserved {V A : Type*} [Fintype V] [Fintype A]
    (Λ : (V → A) → ℝ) {M : ℝ} (_hM : 0 ≤ M)
    (hbound : ∀ a, |Λ a| ≤ M) (φ ψ : V → V)
    (hfold : ∀ a, |Λ a| ^ 2 ≤ Λ (a ∘ φ) * Λ (a ∘ ψ))
    (hpos : ∀ a, 0 ≤ Λ (a ∘ φ) ∧ 0 ≤ Λ (a ∘ ψ))
    (a : V → A) (ha : |Λ a| = M) : |Λ (a ∘ φ)| = M := by
  have hx := (hpos a).1
  have hy := (hpos a).2
  have hxy := hfold a
  have hxb := hbound (a ∘ φ)
  have hyb := hbound (a ∘ ψ)
  rw [ha] at hxy
  rw [abs_of_nonneg hx] at hxb ⊢
  rw [abs_of_nonneg hy] at hyb
  nlinarith [mul_le_mul_of_nonneg_left hyb hx,
    mul_le_mul_of_nonneg_left hxb hx, sq_nonneg (M - Λ (a ∘ φ))]

lemma word_folding_maximum {B A : Type*} [Fintype B] [DecidableEq B]
    [Fintype A] [Nonempty A] {h : ℕ}
    (Λ : (WordVertex B h → A) → ℝ)
    (hfold : ∀ b α β, α ≠ β → ∀ a,
      |Λ a| ^ 2 ≤ Λ (a ∘ foldWord b α β) * Λ (a ∘ foldWord b β α))
    (hpos : ∀ b α β, α ≠ β → ∀ a, 0 ≤ Λ (a ∘ foldWord b α β)) :
    ∃ i : A, ∀ a : WordVertex B h → A, |Λ a| ≤ |Λ (fun _ => i)| := by
  classical
  obtain ⟨a, _, hmax⟩ := univ.exists_max_image (fun a : WordVertex B h → A => |Λ a|)
    univ_nonempty
  have hbnd : ∀ a', |Λ a'| ≤ |Λ a| := fun a' => hmax a' (mem_univ _)
  have hpres (b : B) (α β : Fin h) (hne : α ≠ β) (a' : WordVertex B h → A)
      (ha' : |Λ a'| = |Λ a|) : |Λ (a' ∘ foldWord b α β)| = |Λ a| :=
    max_fold_preserved Λ (abs_nonneg _) hbnd _ _ (hfold b α β hne)
      (fun a' => ⟨hpos b α β hne a', hpos b β α hne.symm a'⟩) a' ha'
  have hseq (cs : List (WordCut B h)) (a' : WordVertex B h → A)
      (ha' : |Λ a'| = |Λ a|) : |Λ (a' ∘ foldMap cs)| = |Λ a| := by
    induction cs generalizing a' with
    | nil => exact ha'
    | cons c cs ih =>
      exact ih (a' ∘ foldWord c.1 c.2.1.1 c.2.1.2)
        (hpres c.1 c.2.1.1 c.2.1.2 c.2.2.ne a' ha')
  obtain ⟨cs, hcs⟩ := exists_constant_fold (B := B) (h := h)
  have heq : a ∘ foldMap cs = fun _ => a (fun _ => 1) := funext fun v => congrArg a (hcs v)
  refine ⟨a (fun _ => 1), fun a' => ?_⟩
  have hs := hseq cs a rfl
  rw [heq] at hs
  exact (hbnd a').trans_eq hs.symm

noncomputable def graphValidity {I : Type*} {p : ℕ} [Fact p.Prime]
    (E : Finset (I × I)) (z : I → ZMod p) : ℝ :=
  ∏ e ∈ E, squareIndicator (z e.2 - z e.1)

lemma graphValidity_all {I : Type*} [Fintype I] [DecidableEq I]
    {p : ℕ} [Fact p.Prime] (E : Finset (I × I)) (z : I → ZMod p) :
    graphValidity E z = ∏ i, ∏ j, if (i,j) ∈ E then squareIndicator (z j - z i) else 1 := by
  classical
  rw [graphValidity, ← Fintype.prod_ite_mem]
  rw [← univ_product_univ, prod_product]

noncomputable def cutInternalEdges {I : Type*} [Fintype I]
    (E : Finset ((I ⊕ I) × (I ⊕ I))) : Finset (I × I) := by
  classical
  exact univ.filter fun e => (Sum.inl e.1, Sum.inl e.2) ∈ E

noncomputable def cutCrossEdges {I : Type*} [Fintype I]
    (E : Finset ((I ⊕ I) × (I ⊕ I))) : Finset (I × I) := by
  classical
  exact univ.filter fun e => (Sum.inl e.1, Sum.inr e.2) ∈ E ∨
    (Sum.inr e.2, Sum.inl e.1) ∈ E

noncomputable def cutCrossDirection {I : Type*}
    (E : Finset ((I ⊕ I) × (I ⊕ I))) (i j : I) : Bool := by
  classical
  exact decide ((Sum.inl i, Sum.inr j) ∈ E)

lemma cutCrossEdges_factor {I : Type*} [Fintype I] [DecidableEq I]
    {p : ℕ} [Fact p.Prime] (E : Finset ((I ⊕ I) × (I ⊕ I)))
    (hnoopp : ∀ e ∈ E, (e.2,e.1) ∉ E) (x y : I → ZMod p) :
    listKernel (cutCrossEdges E) (cutCrossDirection E) x y =
      (∏ i, ∏ j, if (Sum.inl i, Sum.inr j) ∈ E then squareIndicator (y j - x i) else 1) *
      (∏ j, ∏ i, if (Sum.inr j, Sum.inl i) ∈ E then squareIndicator (x i - y j) else 1) := by
  classical
  rw [listKernel, ← Fintype.prod_ite_mem, ← univ_product_univ, prod_product]
  rw [prod_comm (f := fun j i => if (Sum.inr j, Sum.inl i) ∈ E then
    squareIndicator (x i - y j) else 1)]
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro j _
  by_cases hpm : (Sum.inl i, Sum.inr j) ∈ E
  · have hmp := hnoopp _ hpm
    simp [cutCrossEdges, cutCrossDirection, hpm, hmp]
  · by_cases hmp : (Sum.inr j, Sum.inl i) ∈ E <;>
      simp [cutCrossEdges, cutCrossDirection, hpm, hmp]

lemma graphValidity_cut {I : Type*} [Fintype I] [DecidableEq I]
    {p : ℕ} [Fact p.Prime] (E : Finset ((I ⊕ I) × (I ⊕ I)))
    (hnoopp : ∀ e ∈ E, (e.2,e.1) ∉ E)
    (href : ∀ i j, (Sum.inr i, Sum.inr j) ∈ E ↔ (Sum.inl i, Sum.inl j) ∈ E)
    (x y : I → ZMod p) :
    graphValidity E (Sum.elim x y) =
      graphValidity (cutInternalEdges E) x * graphValidity (cutInternalEdges E) y *
        listKernel (cutCrossEdges E) (cutCrossDirection E) x y := by
  classical
  rw [graphValidity_all, Fintype.prod_sum_type]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, prod_mul_distrib]
  rw [cutCrossEdges_factor E hnoopp, graphValidity_all, graphValidity_all]
  simp only [cutInternalEdges, mem_filter, mem_univ, true_and, href]
  ring

lemma graphValidity_nonneg {I : Type*} {p : ℕ} [Fact p.Prime]
    (E : Finset (I × I)) (z : I → ZMod p) : 0 ≤ graphValidity E z := by
  exact prod_nonneg fun e _ => squareIndicator_nonneg _

lemma graphValidity_sq {I : Type*} {p : ℕ} [Fact p.Prime]
    (E : Finset (I × I)) (z : I → ZMod p) : graphValidity E z ^ 2 = graphValidity E z := by
  classical
  unfold graphValidity
  rw [← prod_pow]
  apply prod_congr rfl
  intro e _
  unfold squareIndicator
  split_ifs <;> norm_num

lemma list_quadratic_lower {I : Type*} [Fintype I] [DecidableEq I]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (E : Finset (I × I))
    (dir : I → I → Bool) (f : (I → ZMod p) → ℝ) :
    -(32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8) *
      (𝔼 x : I → ZMod p, (f x)^2) ≤
      𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p, f x * listKernel E dir x y * f y := by
  have h := list_mixing hp E dir f f
  have hv : 0 ≤ 𝔼 x : I → ZMod p, (f x)^2 := expect_nonneg (fun _ _ => sq_nonneg _)
  have hs : Real.sqrt (𝔼 x : I → ZMod p, (f x)^2) *
      Real.sqrt (𝔼 x : I → ZMod p, (f x)^2) = 𝔼 x : I → ZMod p, (f x)^2 :=
    Real.mul_self_sqrt hv
  rw [mul_assoc, hs] at h
  have hex : (𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p,
      f x * (listKernel E dir x y - (1/2:ℝ)^E.card) * f y) =
      (𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p, f x * listKernel E dir x y * f y) -
        (1/2:ℝ)^E.card * (𝔼 x : I → ZMod p, f x)^2 := by
    simp only [sub_mul, mul_sub, expect_sub_distrib, ← expect_mul, ← mul_expect]
    ring
  rw [hex] at h
  have hc : 0 ≤ (1/2:ℝ)^E.card * (𝔼 x : I → ZMod p, f x)^2 := by positivity
  have hl := (abs_le.mp h).1
  nlinarith

open scoped Classical

noncomputable def graphPullback {I K : Type*} [Fintype I]
    (e : I ≃ K) (E : Finset (K × K)) : Finset (I × I) := by
  classical
  exact univ.filter fun ij => (e ij.1, e ij.2) ∈ E

lemma graphValidity_pullback {I K : Type*} [Fintype I] {p : ℕ} [Fact p.Prime]
    (e : I ≃ K) (E : Finset (K × K)) (z : K → ZMod p) :
    graphValidity (graphPullback e E) (z ∘ e) = graphValidity E z := by
  classical
  apply prod_equiv (Equiv.prodCongr e e)
  · intro ij
    simp only [graphPullback, mem_filter, mem_univ, true_and, Equiv.prodCongr_apply]
    rfl
  · intro ij _
    rfl

abbrev TupleHalfAddress (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks) (hb : b ∉ S)
    (α β : Fin tupleH) := CutHalf (⟨b, hb⟩ : {c : Fin tupleBlocks // c ∉ S}) α β

abbrev TupleHalfEntry (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks) (hb : b ∉ S)
    (α β : Fin tupleH) := TupleHalfAddress S b hb α β × TupleListIndex S

noncomputable instance tupleHalfEntryFintype (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) (α β : Fin tupleH) :
    Fintype (TupleHalfEntry S b hb α β) := by
  classical
  unfold TupleHalfEntry
  infer_instance

noncomputable def tupleEntryHalfEquiv (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    TupleHalfEntry S b hb α β ⊕ TupleHalfEntry S b hb α β ≃ TupleListEntry S :=
  (Equiv.sumProdDistrib _ _ _).symm.trans
    (Equiv.prodCongr (halfSumEquiv (⟨b, hb⟩ : {c : Fin tupleBlocks // c ∉ S}) hne) (Equiv.refl _))

lemma tupleEntryHalfEquiv_inl (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (a : TupleHalfEntry S b hb α β) :
    tupleEntryHalfEquiv S b hb hne (Sum.inl a) = (a.1.1, a.2) := rfl

lemma tupleEntryHalfEquiv_inr (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (a : TupleHalfEntry S b hb α β) :
    tupleEntryHalfEquiv S b hb hne (Sum.inr a) =
      tupleEntryReflect S b α β (a.1.1, a.2) := by
  apply Prod.ext
  · funext c
    change reflect (⟨b,hb⟩ : {c : Fin tupleBlocks // c ∉ S}) α β a.1.1 c =
      (if c.1 = b then Equiv.swap α β else 1) * a.1.1 c
    have he : c = ⟨b,hb⟩ ↔ c.1 = b := Subtype.ext_iff
    by_cases hc : c = ⟨b,hb⟩
    · subst c; simp [reflect]
    · have hc' : c.1 ≠ b := fun h => hc (he.mpr h)
      simp [reflect, hc, hc']
  · rfl

def tupleHalfProjection (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (hb : b ∉ S) (α β : Fin tupleH) (x : CutHalf b α β) : TupleHalfAddress S b hb α β :=
  ⟨tupleProjection S x.1, x.2⟩

noncomputable def tupleHalfWeight (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (j : CutHalf b α β → TupleListIndex S) : ℝ :=
  indexWeight (Matrix.submatrix (interaction S tupleDelta) Subtype.val Subtype.val) j

noncomputable def tupleUnmarkedGraph (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :=
  graphPullback (tupleEntryHalfEquiv S b hb hne) (tupleListEdges S)

lemma tupleUnmarkedGraph_noopp (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    ∀ e ∈ tupleUnmarkedGraph S b hb hne, (e.2,e.1) ∉ tupleUnmarkedGraph S b hb hne := by
  classical
  intro e he hh
  simp only [tupleUnmarkedGraph, graphPullback, mem_filter, mem_univ, true_and] at he hh
  exact tupleListEdges_no_opp S _ he hh

lemma tupleUnmarkedGraph_reflect (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (a c : TupleHalfEntry S b hb α β) :
    (Sum.inr a, Sum.inr c) ∈ tupleUnmarkedGraph S b hb hne ↔
      (Sum.inl a, Sum.inl c) ∈ tupleUnmarkedGraph S b hb hne := by
  classical
  simp only [tupleUnmarkedGraph, graphPullback, mem_filter, mem_univ, true_and,
    tupleEntryHalfEquiv_inl, tupleEntryHalfEquiv_inr]
  exact tupleListEdges_reflect S b α β ((a.1.1,a.2),(c.1.1,c.2))

lemma tupleOutput_half (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    {p : ℕ} (x y : TupleHalfEntry S b hb α β → ZMod p)
    (j k : CutHalf b α β → TupleListIndex S) :
    tupleOutput S ((Sum.elim x y) ∘ (tupleEntryHalfEquiv S b hb hne).symm)
      ((Sum.elim j k) ∘ (halfSumEquiv b hne).symm) ∘ (halfSumEquiv b hne) =
      Sum.elim (fun v => x (tupleHalfProjection S b hb α β v, j v))
        (fun v => y (tupleHalfProjection S b hb α β v, k v)) := by
  funext v
  rcases v with v | v
  · change (Sum.elim x y) ((tupleEntryHalfEquiv S b hb hne).symm
        (tupleProjection S v.1, (Sum.elim j k) ((halfSumEquiv b hne).symm ((halfSumEquiv b hne) (Sum.inl v))))) = _
    rw [Equiv.symm_apply_apply]
    change (Sum.elim x y) ((tupleEntryHalfEquiv S b hb hne).symm
      ((tupleEntryHalfEquiv S b hb hne) (Sum.inl (tupleHalfProjection S b hb α β v, j v)))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  · change (Sum.elim x y) ((tupleEntryHalfEquiv S b hb hne).symm
        (tupleProjection S (reflect b α β v.1),
          (Sum.elim j k) ((halfSumEquiv b hne).symm ((halfSumEquiv b hne) (Sum.inr v))))) = _
    rw [Equiv.symm_apply_apply]
    change (Sum.elim x y) ((tupleEntryHalfEquiv S b hb hne).symm
      (tupleProjection S (reflect b α β v.1), k v)) = _
    rw [tupleProjection_reflect_all]
    have he := tupleEntryHalfEquiv_inr S b hb hne (tupleHalfProjection S b hb α β v, k v)
    change _ = (tupleAddressReflect S b α β (tupleProjection S v.1), k v) at he
    rw [← he, Equiv.symm_apply_apply]
    rfl

lemma tupleHalfWeight_one_le (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (j : CutHalf b α β → TupleListIndex S) :
    1 ≤ tupleHalfWeight S b α β j :=
  one_le_indexWeight _ (fun _ _ => interaction_nonneg S tupleDelta_pos.le _ _) j

lemma tupleHalfWeight_le (S : Finset (Fin tupleBlocks)) (hS : S.card ≤ tupleT + 1)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (j : CutHalf b α β → TupleListIndex S) : tupleHalfWeight S b α β j ≤ tupleWeightBound := by
  let J := (Sum.elim j j) ∘ (halfSumEquiv b hne).symm
  have hW := tupleWeight_le S hS J
  have he := indexWeight_equiv (halfSumEquiv b hne) (interaction S tupleDelta) J
  have hj : J ∘ halfSumEquiv b hne = Sum.elim j j := by
    funext x
    exact congrArg (Sum.elim j j) ((halfSumEquiv b hne).symm_apply_apply x)
  rw [hj, unmarked_weight_factor S tupleDelta b hb hne] at he
  change tupleHalfWeight S b α β j * tupleHalfWeight S b α β j = tupleWeight S J at he
  rw [← he] at hW
  have h1 := tupleHalfWeight_one_le S b α β j
  nlinarith

end SquareDifference
end

end OAI
