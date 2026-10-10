import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.RepresentationLimits

namespace OAI

/-! Random signs for bounded Hochschild cohomology. -/

noncomputable section

open scoped BigOperators
namespace PopaQuantization

def sign (b : Bool) : ℝ := if b then -1 else 1
@[simp] lemma sign_sq (b : Bool) : sign b * sign b=1 := by cases b <;> norm_num [sign]
@[simp] lemma sign_sum : ∑ b : Bool, sign b=0 := by norm_num [sign]

variable {n : ℕ}
def character (s : Finset (Fin n)) (a : Fin n → Bool) : ℝ :=
  ∏ i, if i∈s then sign (a i) else 1

lemma character_empty (a : Fin n → Bool) : character ∅ a=1 := by simp [character]
lemma character_singleton (i : Fin n) (a : Fin n → Bool) : character {i} a=sign (a i) := by
  simp [character]
lemma character_eq_prod (s : Finset (Fin n)) (a : Fin n → Bool) :
    character s a=∏ i∈s, sign (a i) := by
  classical
  calc
    character s a = ∏ i∈s, if i∈s then sign (a i) else 1 := by
      apply (Finset.prod_subset (Finset.subset_univ s) ?_).symm
      intro i _ hi
      exact ite_eq_right hi
    _ = _ := Finset.prod_congr rfl (fun i hi => ite_eq_left hi)
lemma character_pair (i j : Fin n) (hij : i ≠ j) (a : Fin n → Bool) :
    character {i,j} a=sign (a i)*sign (a j) := by
  classical
  rw [character_eq_prod,Finset.prod_pair hij]

lemma character_orthogonal (s t : Finset (Fin n)) :
    (∑ a : Fin n → Bool, character s a*character t a)=
      if s=t then (2:ℝ)^n else 0 := by
  classical
  have he : (∑ a : Fin n → Bool, character s a*character t a)=
      ∏ i : Fin n, (∑ b : Bool, (if i∈s then sign b else 1)*(if i∈t then sign b else 1)) := by
    simp only [character,← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i (b : Bool) =>
      (if i∈s then sign b else 1)*(if i∈t then sign b else 1))).symm
  rw [he]
  by_cases h : s=t
  · subst t
    simp only [ite_true]
    have hi (i : Fin n) : (∑ b : Bool, (if i∈s then sign b else 1)*(if i∈s then sign b else 1))=2 := by
      by_cases h : i∈s <;> norm_num [h,sign]
    simp only [hi,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := not_forall.mp (Finset.ext_iff.not.mp h)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hs : i∈s <;> by_cases ht : i∈t <;> simp_all [sign]

variable {E ι : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι]

lemma signed_norm_sq (l : ι → Finset (Fin n)) (v : ι → E) (a : Fin n → Bool) :
    ‖∑ i, character (l i) a • v i‖^2=
      ∑ i, ∑ j, (character (l i) a*character (l j) a)*inner ℝ (v i) (v j) := by
  rw [← real_inner_self_eq_norm_sq]
  rw [sum_inner]
  simp only [inner_sum,inner_smul_left,inner_smul_right,starRingEnd_apply,star_trivial]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma character_mean_square (l : ι → Finset (Fin n)) (hl : Function.Injective l) (v : ι → E) :
    (∑ a : Fin n → Bool, ‖∑ i, character (l i) a • v i‖^2)=
      (2:ℝ)^n*∑ i, ‖v i‖^2 := by
  classical
  simp_rw [signed_norm_sq]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n → Bool)))]
  simp_rw [← Finset.sum_mul,character_orthogonal,hl.eq_iff]
  simp [ite_mul,← Finset.mul_sum]
end PopaQuantization

open scoped BigOperators
namespace PopaQuantization

abbrev UpperPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

def pairLabel {n : ℕ} (p : Option (UpperPair n)) : Finset (Fin n) :=
  match p with
  | none => ∅
  | some p => {p.val.1,p.val.2}

lemma pairLabel_injective {n : ℕ} : Function.Injective (@pairLabel n) := by
  classical
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      have hh : b.val.1 ∈ pairLabel none := by rw [h]; simp [pairLabel]
      simp [pairLabel] at hh
  | some a =>
    cases b with
    | none => simp [pairLabel] at h
    | some b =>
      have hs := congrArg (fun s : Finset (Fin n) => (s : Set (Fin n))) h
      simp only [pairLabel,Finset.coe_pair,Set.pair_eq_pair_iff] at hs
      rcases hs with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact congrArg some (Subtype.ext (Prod.ext h1 h2))
      · have ha := a.property
        have hb := b.property
        omega

lemma sum_diagonal_upper {n : ℕ} {E : Type*} [AddCommMonoid E] (x : Fin n → Fin n → E) :
    (∑ i, ∑ j, x i j)=(∑ i, x i i)+∑ p : UpperPair n, (x p.val.1 p.val.2+x p.val.2 p.val.1) := by
  classical
  have hsub (f : Fin n → Fin n → E) :
      (∑ p : UpperPair n, f p.val.1 p.val.2)=
        ∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0 := by
    rw [← Fintype.sum_prod_type (f := fun p : Fin n × Fin n => if p.1 < p.2 then f p.1 p.2 else 0)]
    simpa [Finset.sum_filter] using (Finset.sum_subtype
      (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
      (by intro p; simp) (fun p => f p.1 p.2)).symm
  have he (i j : Fin n) : x i j=(if i=j then x i j else 0)+
      (if i < j then x i j else 0)+(if j < i then x i j else 0) := by
    rcases lt_trichotomy i j with h | h | h <;> simp [h,ne_of_lt,ne_of_gt,not_lt_of_ge,le_of_lt]
  calc
    (∑ i, ∑ j, x i j) = ∑ i, ∑ j,
        ((if i=j then x i j else 0)+(if i < j then x i j else 0)+(if j < i then x i j else 0)) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      exact he i j
    _ = (∑ i, x i i)+(∑ i, ∑ j, if i < j then x i j else 0)+
        (∑ i, ∑ j, if i < j then x j i else 0) := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j : Fin n => if j < i then x i j else 0)]
      simp
    _ = _ := by
      rw [Finset.sum_add_distrib, hsub (fun i j => x i j), hsub (fun i j => x j i)]
      abel

variable {n : ℕ} {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

def pairCoefficients (x : Fin n → Fin n → E) (p : Option (UpperPair n)) : E :=
  match p with
  | none => ∑ i, x i i
  | some p => x p.val.1 p.val.2+x p.val.2 p.val.1

lemma quadratic_expansion (x : Fin n → Fin n → E) (a : Fin n → Bool) :
    (∑ i, ∑ j, (sign (a i)*sign (a j)) • x i j)=
      ∑ p : Option (UpperPair n), character (pairLabel p) a • pairCoefficients x p := by
  classical
  rw [sum_diagonal_upper,Fintype.sum_option]
  simp only [pairLabel,pairCoefficients,character_empty,one_smul,sign_sq]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [character_pair _ _ (ne_of_lt p.property),smul_add]
  rw [mul_comm (sign (a p.val.2))]

theorem quadratic_mean_square_bound (x : Fin n → Fin n → E) :
    (∑ a : Fin n → Bool, ‖∑ i, ∑ j, (sign (a i)*sign (a j)) • x i j‖^2) ≤
      (2:ℝ)^n*(‖∑ i, x i i‖^2+2*∑ i, ∑ j, ‖x i j‖^2) := by
  classical
  simp_rw [quadratic_expansion]
  rw [character_mean_square _ pairLabel_injective,Fintype.sum_option]
  simp only [pairCoefficients]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_right
  have hpair (p : UpperPair n) : ‖x p.val.1 p.val.2+x p.val.2 p.val.1‖^2 ≤
      2*(‖x p.val.1 p.val.2‖^2+‖x p.val.2 p.val.1‖^2) := by
    have hh := norm_add_le (x p.val.1 p.val.2) (x p.val.2 p.val.1)
    nlinarith [norm_nonneg (x p.val.1 p.val.2+x p.val.2 p.val.1),
      norm_nonneg (x p.val.1 p.val.2),norm_nonneg (x p.val.2 p.val.1),
      sq_nonneg (‖x p.val.1 p.val.2‖-‖x p.val.2 p.val.1‖)]
  calc
    (∑ p : UpperPair n, ‖x p.val.1 p.val.2+x p.val.2 p.val.1‖^2) ≤
      ∑ p : UpperPair n, 2*(‖x p.val.1 p.val.2‖^2+‖x p.val.2 p.val.1‖^2) :=
        Finset.sum_le_sum (fun p _ => hpair p)
    _ = 2*∑ p : UpperPair n, (‖x p.val.1 p.val.2‖^2+‖x p.val.2 p.val.1‖^2) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      rw [sum_diagonal_upper (fun i j => ‖x i j‖^2)]
      have hh : 0 ≤ ∑ i : Fin n, ‖x i i‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      linarith
end PopaQuantization

end

end OAI
