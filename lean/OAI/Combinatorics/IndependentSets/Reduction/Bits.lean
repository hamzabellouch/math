import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.Heavy

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators Classical

def ofBits : {n : ℕ} → (Fin n → Bool) → Cube n
  | 0, _ => ()
  | _+1, x => (x 0, ofBits (fun i => x i.succ))

@[simp] lemma bit_ofBits {n : ℕ} (x : Fin n → Bool) : bit (ofBits x) = x := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [ofBits, bit, Fin.cases_succ, ih]

@[simp] lemma ofBits_bit {n : ℕ} (x : Cube n) : ofBits (bit x) = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    simp only [ofBits, bit, Fin.cases_zero, Fin.cases_succ, ih]

def bitEquiv (n : ℕ) : Cube n ≃ (Fin n → Bool) where
  toFun := bit
  invFun := ofBits
  left_inv := ofBits_bit
  right_inv := bit_ofBits

lemma bit_flip {n : ℕ} (i : Fin n) (x : Cube n) :
    bit (flip i x) = Function.update (bit x) i (!(bit x i)) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    funext j
    refine Fin.cases ?_ (fun k => ?_) i
    · refine Fin.cases ?_ (fun l => ?_) j <;> simp [flip, bit]
    · refine Fin.cases ?_ (fun l => ?_) j
      · simp [flip, bit, Function.update_of_ne (Fin.succ_ne_zero k).symm]
      · by_cases h : l = k
        · subst l; simpa [flip, bit] using congrFun (ih k x) k
        · simpa [flip, bit, h, Function.update_of_ne h, Function.update_of_ne (fun he => h (Fin.succ_inj.mp he))] using congrFun (ih k x) l

lemma expect_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : (𝔼 x, f (e x)) = 𝔼 y, f y := by
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ]
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma mean_bit {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    mean (fun x : Cube n => f (bit x)) = 𝔼 x, f x :=
  expect_equiv (bitEquiv n) f

noncomputable def bitInfluence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (i : ι) : ℝ :=
  𝔼 x, |(f x - f (Function.update x i (!(x i))))/2|

lemma influence_bit {n : ℕ} (f : (Fin n → Bool) → ℝ) (i : Fin n) :
    influence (fun x : Cube n => f (bit x)) i = bitInfluence f i := by
  simp only [influence, diff, bit_flip]
  exact mean_bit (fun x => |(f x - f (Function.update x i (!(x i))))/2|)

theorem bits_junta_uniform {L u : ℝ} (hL : 0 ≤ L) (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ n : ℕ, ∀ f : (Fin n → Bool) → ℝ,
      (∀ x, |f x| ≤ 1) → (∑ i, bitInfluence f i) ≤ L →
      ∃ S : Finset (Fin n), S.card ≤ J ∧ ∃ g : (Fin n → Bool) → ℝ,
        (∀ x, |g x| ≤ 1) ∧
        (∀ x y, (∀ i ∈ S, x i = y i) → g x = g y) ∧
        (𝔼 x, (f x - g x)^2) < u := by
  obtain ⟨J,hJ,h⟩ := boolean_junta_uniform hL hu
  refine ⟨J,hJ,?_⟩
  intro n f hf hI
  let f' : Cube n → ℝ := fun x => f (bit x)
  have hI' : (∑ i, influence f' i) ≤ L := by simpa only [f', influence_bit] using hI
  obtain ⟨S,hS,he⟩ := h n f' (fun x => hf _) hI'
  let g : (Fin n → Bool) → ℝ := fun x => truncate S f' (ofBits x)
  refine ⟨S,hS,g,?_,?_,?_⟩
  · intro x
    exact truncate_bounded S f' (fun x => hf _) _
  · intro x y hxy
    apply truncate_depends
    simpa only [bit_ofBits] using hxy
  · have heq : (𝔼 x, (f x-g x)^2) = mean (fun x : Cube n => (f' x-truncate S f' x)^2) := by
      rw [← mean_bit]
      simp only [f', g, ofBits_bit]
    rwa [heq]

def reindexBits {ι κ : Type*} (e : ι ≃ κ) : (κ → Bool) ≃ (ι → Bool) where
  toFun := fun x i => x (e i)
  invFun := fun x j => x (e.symm j)
  left_inv := by intro x; funext j; simp
  right_inv := by intro x; funext i; simp

lemma reindexBits_update {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (x : κ → Bool) (i : ι) :
    reindexBits e (Function.update x (e i) (!(x (e i)))) =
      Function.update (reindexBits e x) i (!(reindexBits e x i)) := by
  funext j
  by_cases h : j = i
  · subst j; simp [reindexBits]
  · simp [reindexBits, Function.update_of_ne h, Function.update_of_ne (e.injective.ne h)]

lemma bitInfluence_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (f : (ι → Bool) → ℝ) (i : ι) :
    bitInfluence (fun x => f (reindexBits e x)) (e i) = bitInfluence f i := by
  simp only [bitInfluence, reindexBits_update]
  exact expect_equiv (reindexBits e) (fun x => |(f x - f (Function.update x i (!(x i))))/2|)

theorem arbitrary_bits_junta_uniform {L u : ℝ} (hL : 0 ≤ L) (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    ∀ f : (ι → Bool) → ℝ, (∀ x, |f x| ≤ 1) → (∑ i, bitInfluence f i) ≤ L →
      ∃ S : Finset ι, S.card ≤ J ∧ ∃ g : (ι → Bool) → ℝ,
        (∀ x, |g x| ≤ 1) ∧
        (∀ x y, (∀ i ∈ S, x i = y i) → g x = g y) ∧
        (𝔼 x, (f x - g x)^2) < u := by
  obtain ⟨J,hJ,h⟩ := bits_junta_uniform hL hu
  refine ⟨J,hJ,?_⟩
  intro ι _ _ f hf hI
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let f' : (Fin (Fintype.card ι) → Bool) → ℝ := fun x => f (reindexBits e x)
  have hI' : (∑ i, bitInfluence f' i) ≤ L := by
    rw [← e.sum_comp (fun j => bitInfluence f' j)]
    simpa only [f', bitInfluence_reindex] using hI
  obtain ⟨S,hS,g,hg,hdep,he⟩ := h (Fintype.card ι) f' (fun x => hf _) hI'
  let T : Finset ι := S.map e.symm.toEmbedding
  let g' : (ι → Bool) → ℝ := fun x => g ((reindexBits e).symm x)
  refine ⟨T, by simpa [T] using hS, g', (fun x => hg _), ?_, ?_⟩
  · intro x y hxy
    apply hdep
    intro j hj
    exact hxy (e.symm j) (Finset.mem_map.mpr ⟨j,hj,rfl⟩)
  · have heq : (𝔼 x, (f x-g' x)^2) = 𝔼 x, (f' x-g x)^2 := by
      rw [← expect_equiv (reindexBits e)]
      simp only [g', Equiv.symm_apply_apply, f']
    rwa [heq]

end LargeIndependentSets.BooleanJunta

end OAI
