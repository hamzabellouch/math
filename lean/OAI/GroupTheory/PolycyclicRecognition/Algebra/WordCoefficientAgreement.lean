import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordMinimumDegree

namespace OAI

/-! # Agreement of word coefficients below a fixed degree -/

noncomputable section
namespace PolycyclicRecognition

variable {n k : ℕ}

def WordCoefficientAgreement (p q : RationalWords n) (k : ℕ) : Prop :=
  ∀ w, w.length < k → p.coeff w = q.coeff w

theorem WordCoefficientAgreement.refl (p : RationalWords n) (k : ℕ) :
    WordCoefficientAgreement p p k := fun _ _ => rfl

theorem WordCoefficientAgreement.sub {p q r s : RationalWords n}
    (hp : WordCoefficientAgreement p q k) (hr : WordCoefficientAgreement r s k) :
    WordCoefficientAgreement (p - r) (q - s) k := by
  intro w hw
  simp only [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, hp w hw, hr w hw]

theorem WordCoefficientAgreement.mul {p q r s : RationalWords n}
    (hp : WordCoefficientAgreement p q k) (hr : WordCoefficientAgreement r s k) :
    WordCoefficientAgreement (p * r) (q * s) k := by
  intro w hw
  rw [word_coeff_mul, word_coeff_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hlen : (wordSplit w i).1.length + (wordSplit w i).2.length = w.length := by
    rw [← FreeMonoid.length_mul, wordSplit_mul]
  rw [hp _ (by omega), hr _ (by omega)]

theorem WordCoefficientAgreement.pow {p q : RationalWords n}
    (hp : WordCoefficientAgreement p q k) (a : ℕ) :
    WordCoefficientAgreement (p ^ a) (q ^ a) k := by
  induction a with
  | zero => exact .refl _ _
  | succ a ha => simpa only [pow_succ] using ha.mul hp

theorem wordCoefficientAgreement_list_prod
    (l : List (RationalWords n × RationalWords n))
    (h : ∀ p ∈ l, WordCoefficientAgreement p.1 p.2 k) :
    WordCoefficientAgreement (l.map Prod.fst).prod (l.map Prod.snd).prod k := by
  induction l with
  | nil => exact .refl _ _
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h p (List.mem_cons_self ..)).mul
      (ih (fun q hq => h q (List.mem_cons_of_mem _ hq)))

theorem wordCoefficientAgreement_ofFn_prod {a : ℕ}
    (p q : Fin a → RationalWords n)
    (h : ∀ i, WordCoefficientAgreement (p i) (q i) k) :
    WordCoefficientAgreement (List.ofFn p).prod (List.ofFn q).prod k := by
  have hh := wordCoefficientAgreement_list_prod (List.ofFn (fun i => (p i, q i))) (by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact h i)
  simpa only [List.map_ofFn, Function.comp_def] using hh

end PolycyclicRecognition

end

end OAI
