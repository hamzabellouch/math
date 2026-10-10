import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.RenameFraction

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality

variable {I : Type*} [Fintype I] [DecidableEq I]

def Cut (d e : I → ℕ) := ∀ i, {s : Finset (Fin (d i + e i)) // s.card = d i}

instance (d e : I → ℕ) : Fintype (Cut d e) := by unfold Cut; infer_instance
instance (d e : I → ℕ) : DecidableEq (Cut d e) := by unfold Cut; infer_instance

variable {d e : I → ℕ}

noncomputable def cutPerm (g : ∀ i, Equiv.Perm (Fin (d i + e i))) : Cut d e ≃ Cut d e :=
  Equiv.piCongrRight (fun i => (g i).finsetCongr.subtypeEquiv (fun s => by
    simp [Equiv.finsetCongr_apply]))

omit [Fintype I] [DecidableEq I] in
@[simp] lemma cutPerm_val (g : ∀ i, Equiv.Perm (Fin (d i + e i))) (A : Cut d e) (i : I) :
    (cutPerm g A i).val = (A i).val.map (g i).toEmbedding := rfl

omit [Fintype I] [DecidableEq I] in
@[simp] lemma mem_cutPerm (g : ∀ i, Equiv.Perm (Fin (d i + e i))) (A : Cut d e)
    (i : I) (a : Fin (d i + e i)) :
    g i a ∈ (cutPerm g A i).val ↔ a ∈ (A i).val := by
  simp

noncomputable def leftEnum (A : Cut d e) (i : I) : Fin (d i) ≃ (A i).val :=
  ((A i).val.orderIsoOfFin (A i).property).toEquiv

omit [Fintype I] [DecidableEq I] in
lemma right_card (A : Cut d e) (i : I) : (A i).valᶜ.card = e i := by
  rw [Finset.card_compl, Fintype.card_fin, (A i).property, Nat.add_sub_cancel_left]

noncomputable def rightEnum (A : Cut d e) (i : I) : Fin (e i) ≃ ↥((A i).valᶜ) :=
  ((A i).valᶜ.orderIsoOfFin (right_card A i)).toEquiv

noncomputable def leftInput (A : Cut d e) : (Σ i,Fin (d i)) → (Σ i,Fin (d i + e i)) :=
  fun a => ⟨a.1, leftEnum A a.1 a.2⟩

noncomputable def rightInput (A : Cut d e) : (Σ i,Fin (e i)) → (Σ i,Fin (d i + e i)) :=
  fun a => ⟨a.1, rightEnum A a.1 a.2⟩

noncomputable def leftImageEquiv (g : ∀ i, Equiv.Perm (Fin (d i + e i)))
    (A : Cut d e) (i : I) : (A i).val ≃ (cutPerm g A i).val :=
  (g i).subtypeEquiv (fun _ => (mem_cutPerm g A i _).symm)

noncomputable def rightImageEquiv (g : ∀ i, Equiv.Perm (Fin (d i + e i)))
    (A : Cut d e) (i : I) : ↥((A i).valᶜ) ≃ ↥((cutPerm g A i).valᶜ) :=
  (g i).subtypeEquiv (by intro a; simp only [Finset.mem_compl, mem_cutPerm])

noncomputable def leftReindex (g : ∀ i, Equiv.Perm (Fin (d i + e i)))
    (A : Cut d e) (i : I) : Equiv.Perm (Fin (d i)) :=
  (leftEnum A i).trans ((leftImageEquiv g A i).trans (leftEnum (cutPerm g A) i).symm)

noncomputable def rightReindex (g : ∀ i, Equiv.Perm (Fin (d i + e i)))
    (A : Cut d e) (i : I) : Equiv.Perm (Fin (e i)) :=
  (rightEnum A i).trans ((rightImageEquiv g A i).trans (rightEnum (cutPerm g A) i).symm)

omit [Fintype I] [DecidableEq I] in
lemma leftInput_reindex (g : ∀ i, Equiv.Perm (Fin (d i + e i))) (A : Cut d e) :
    leftInput (cutPerm g A) ∘ packAction (fun i => Fin (d i)) (leftReindex g A) =
      packAction (fun i => Fin (d i + e i)) g ∘ leftInput A := by
  funext ⟨i,a⟩
  change (⟨i, ↑(leftEnum (cutPerm g A) i (leftReindex g A i a))⟩ : Σi,Fin (d i + e i)) =
    ⟨i,g i ↑(leftEnum A i a)⟩
  simp only [leftReindex, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

omit [Fintype I] [DecidableEq I] in
lemma rightInput_reindex (g : ∀ i, Equiv.Perm (Fin (d i + e i))) (A : Cut d e) :
    rightInput (cutPerm g A) ∘ packAction (fun i => Fin (e i)) (rightReindex g A) =
      packAction (fun i => Fin (d i + e i)) g ∘ rightInput A := by
  funext ⟨i,a⟩
  change (⟨i, ↑(rightEnum (cutPerm g A) i (rightReindex g A i a))⟩ : Σi,Fin (d i + e i)) =
    ⟨i,g i ↑(rightEnum A i a)⟩
  simp only [rightReindex, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

def PackSymmetric (d : I → ℕ) (f : MvPolynomial (Σ i,Fin (d i)) ℚ) : Prop :=
  ∀ g : ∀i, Equiv.Perm (Fin (d i)), rename (packAction (fun i => Fin (d i)) g) f = f

omit [Fintype I] [DecidableEq I] in
lemma rename_leftInput (f : MvPolynomial (Σ i,Fin (d i)) ℚ) (hf : PackSymmetric d f)
    (g : ∀ i, Equiv.Perm (Fin (d i + e i))) (A : Cut d e) :
    rename (packAction (fun i => Fin (d i + e i)) g) (rename (leftInput A) f) =
      rename (leftInput (cutPerm g A)) f := by
  rw [MvPolynomial.rename_rename, ← leftInput_reindex, ← MvPolynomial.rename_rename, hf]

omit [Fintype I] [DecidableEq I] in
lemma rename_rightInput (f : MvPolynomial (Σ i,Fin (e i)) ℚ) (hf : PackSymmetric e f)
    (g : ∀ i, Equiv.Perm (Fin (d i + e i))) (A : Cut d e) :
    rename (packAction (fun i => Fin (d i + e i)) g) (rename (rightInput A) f) =
      rename (rightInput (cutPerm g A)) f := by
  rw [MvPolynomial.rename_rename, ← rightInput_reindex, ← MvPolynomial.rename_rename, hf]

omit [Fintype I] [DecidableEq I] in
@[simp] lemma cutPerm_compl (g : ∀ i, Equiv.Perm (Fin (d i + e i)))
    (A : Cut d e) (i : I) :
    (cutPerm g A i).valᶜ = (A i).valᶜ.map (g i).toEmbedding := by
  ext b
  obtain ⟨a,rfl⟩ := (g i).surjective b
  simp

local notation "P" => MvPolynomial (Σ i, Fin (d i + e i)) ℚ
local notation "K" => FractionRing (MvPolynomial (Σ i, Fin (d i + e i)) ℚ)

noncomputable def cutFactor (A : Cut d e) (i j : I) (k : ℕ) : P :=
  ∏ a ∈ (A i).val, ∏ b ∈ (A j).valᶜ, (diagonal ⟨i,a⟩ ⟨j,b⟩)^k

omit [Fintype I] [DecidableEq I] in
lemma rename_cutFactor (g : ∀ i, Equiv.Perm (Fin (d i + e i)))
    (A : Cut d e) (i j : I) (k : ℕ) :
    rename (packAction (fun i => Fin (d i + e i)) g) (cutFactor A i j k) =
      cutFactor (cutPerm g A) i j k := by
  simp only [cutFactor]
  rw [cutPerm_compl, cutPerm_val]
  simp only [map_prod, map_pow, diagonal, map_sub, rename_X,
    Finset.prod_map, Function.Embedding.coeFn_mk]
  rfl

noncomputable def cutDenominator (A : Cut d e) : P := ∏ i, cutFactor A i i 1

noncomputable def cutNumerator (a : I → I → ℕ) (A : Cut d e)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) : P :=
  rename (leftInput A) f * rename (rightInput A) g * ∏ i, ∏ j, cutFactor A i j (a i j)

omit [DecidableEq I] in
lemma rename_cutDenominator (g : ∀ i, Equiv.Perm (Fin (d i + e i))) (A : Cut d e) :
    rename (packAction (fun i => Fin (d i + e i)) g) (cutDenominator A) =
      cutDenominator (cutPerm g A) := by
  simp only [cutDenominator, map_prod, rename_cutFactor]

omit [DecidableEq I] in
lemma rename_cutNumerator (a : I → I → ℕ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (hf : PackSymmetric d f)
    (g : MvPolynomial (Σi,Fin (e i)) ℚ) (hg : PackSymmetric e g)
    (σ : ∀ i, Equiv.Perm (Fin (d i + e i))) (A : Cut d e) :
    rename (packAction (fun i => Fin (d i + e i)) σ) (cutNumerator a A f g) =
      cutNumerator a (cutPerm σ A) f g := by
  simp only [cutNumerator, map_mul, map_prod, rename_cutFactor,
    rename_leftInput f hf, rename_rightInput g hg]

lemma cutDenominator_dvd (A : Cut d e) :
    cutDenominator A ∣ naturalVandermonde (fun i => d i + e i) (fun _ => True) := by
  change (∏i,cutFactor A i i 1) ∣ _
  have he : ∀ i, cutFactor A i i 1 =
      ∏ ab ∈ ((A i).val ×ˢ (A i).valᶜ), diagonal (⟨i,ab.1⟩ : Σi,Fin (d i+e i)) ⟨i,ab.2⟩ := by
    intro i
    simp only [cutFactor, pow_one, Finset.prod_product]
  simp_rw [he]
  apply packed_pairs_product_dvd
  · intro i ab hab heq
    have hm := Finset.mem_product.mp hab
    exact (Finset.mem_compl.mp hm.2) (heq ▸ hm.1)
  · intro i ab hab hba
    have h1 := Finset.mem_product.mp hab
    have h2 := Finset.mem_product.mp hba
    exact (Finset.mem_compl.mp h1.2) h2.1
  · intro i ab hab
    apply diagonal_dvd_naturalVandermonde
    intro heq
    have hm := Finset.mem_product.mp hab
    exact (Finset.mem_compl.mp hm.2) (heq ▸ hm.1)

lemma cutDenominator_ne_zero (A : Cut d e) : cutDenominator A ≠ 0 :=
  ne_zero_of_dvd_ne_zero (naturalVandermonde_ne_zero _ (fun _ => True))
    (cutDenominator_dvd A)

noncomputable def rawShuffle (a : I → I → ℕ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) : K :=
  ∑ A : Cut d e, algebraMap P K (cutNumerator a A f g) /
    algebraMap P K (cutDenominator A)

lemma rawShuffle_symmetric (a : I → I → ℕ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (hf : PackSymmetric d f)
    (g : MvPolynomial (Σi,Fin (e i)) ℚ) (hg : PackSymmetric e g)
    (σ : ∀ i, Equiv.Perm (Fin (d i + e i))) :
    renameFraction (packAction (fun i => Fin (d i + e i)) σ) (rawShuffle a f g) =
      rawShuffle a f g := by
  simp only [rawShuffle, map_sum, map_div₀, renameFraction_algebraMap,
    rename_cutNumerator a f hf g hg, rename_cutDenominator]
  exact Equiv.sum_comp (cutPerm σ) (fun A : Cut d e =>
    algebraMap P K (cutNumerator a A f g) / algebraMap P K (cutDenominator A))

lemma rawShuffle_regular (a : I → I → ℕ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) :
    ∃ N : P, algebraMap P K (naturalVandermonde (fun i => d i + e i) (fun _ => True)) *
      rawShuffle a f g = algebraMap P K N := by
  have hterms (A : Cut d e) : ∃ N : P,
      algebraMap P K (naturalVandermonde (fun i => d i + e i) (fun _ => True)) *
        (algebraMap P K (cutNumerator a A f g) / algebraMap P K (cutDenominator A)) =
      algebraMap P K N := by
    obtain ⟨b,hb⟩ := cutDenominator_dvd A
    refine ⟨b * cutNumerator a A f g, ?_⟩
    have hne : algebraMap P K (cutDenominator A) ≠ 0 :=
      by
        intro hz
        apply cutDenominator_ne_zero A
        exact (IsFractionRing.injective P K) (by simpa using hz)
    rw [hb, map_mul, map_mul]
    field_simp
  choose N hN using hterms
  refine ⟨∑A,N A, ?_⟩
  simp only [rawShuffle, Finset.mul_sum, hN, map_sum]

theorem rawShuffle_polynomial (a : I → I → ℕ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (hf : PackSymmetric d f)
    (g : MvPolynomial (Σi,Fin (e i)) ℚ) (hg : PackSymmetric e g) :
    ∃ h : P, PackSymmetric (fun i => d i + e i) h ∧
      rawShuffle a f g = algebraMap P K h := by
  obtain ⟨h,hh⟩ := invariant_fraction_regular _ (rawShuffle a f g)
    (rawShuffle_symmetric a f hf g hg) (rawShuffle_regular a f g)
  refine ⟨h,?_,hh⟩
  intro σ
  apply IsFractionRing.injective P K
  rw [← renameFraction_algebraMap, ← hh, rawShuffle_symmetric a f hf g hg σ]

end ElementaryPositivity.RawShuffle

end

end OAI
