import OAI.Probability.FreeIsing.Posterior.FinitePosterior
import OAI.Probability.FreeIsing.Spins.Kernel

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FiniteSpinCoupling

variable {A B : Type*} [Fintype A] [Fintype B]

def energy (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin) (x : A × B) : ℝ :=
  EA x.1 + EB x.2 + beta * spinSign (a x.1) * spinSign (b x.2)

def partition (E : A → ℝ) : ℝ := ∑ x, Real.exp (E x)

def numerator (E : A → ℝ) (a : A → IsingSpin) : ℝ :=
  ∑ x, spinSign (a x) * Real.exp (E x)

def mean (E : A → ℝ) (a : A → IsingSpin) : ℝ :=
  FinitePosterior.mean E (fun _ => 0) (fun x => spinSign (a x)) 0

lemma mean_eq (E : A → ℝ) (a : A → IsingSpin) :
    mean E a = numerator E a / partition E := by
  simp [mean, numerator, partition, FinitePosterior.mean,
    FinitePosterior.partition, FinitePosterior.weight]

lemma partition_pos [Nonempty A] (E : A → ℝ) : 0 < partition E :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

omit [Fintype A] [Fintype B] in
lemma exp_interaction (beta : ℝ) (a b : IsingSpin) :
    Real.exp (beta * spinSign a * spinSign b) =
      Real.cosh beta + Real.sinh beta * spinSign a * spinSign b := by
  cases a <;> cases b <;>
    simp [spinSign, ← sub_eq_add_neg, Real.cosh_add_sinh, Real.cosh_sub_sinh]

omit [Fintype A] [Fintype B] in
lemma exp_energy (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin) (x : A × B) :
    Real.exp (energy beta EA EB a b x) =
      Real.cosh beta * Real.exp (EA x.1) * Real.exp (EB x.2) +
      Real.sinh beta * (spinSign (a x.1) * Real.exp (EA x.1)) *
        (spinSign (b x.2) * Real.exp (EB x.2)) := by
  rw [energy, Real.exp_add, Real.exp_add, exp_interaction]
  ring

theorem partition_energy (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin) :
    partition (energy beta EA EB a b) =
      Real.cosh beta * partition EA * partition EB +
      Real.sinh beta * numerator EA a * numerator EB b := by
  simp only [partition, Fintype.sum_prod_type, exp_energy,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, numerator]

theorem numerator_energy_fst (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin) :
    numerator (energy beta EA EB a b) (fun x => a x.1) =
      Real.cosh beta * numerator EA a * partition EB +
      Real.sinh beta * partition EA * numerator EB b := by
  have heq (x : A × B) :
      spinSign (a x.1) * Real.exp (energy beta EA EB a b x) =
        Real.cosh beta * (spinSign (a x.1) * Real.exp (EA x.1)) * Real.exp (EB x.2) +
        Real.sinh beta * Real.exp (EA x.1) *
          (spinSign (b x.2) * Real.exp (EB x.2)) := by
    rw [exp_energy]
    cases a x.1 <;> simp only [spinSign_neg, spinSign_pos] <;> ring
  simp only [numerator, Fintype.sum_prod_type, heq,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, partition]

theorem mean_energy_fst [Nonempty A] [Nonempty B]
    (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin) :
    mean (energy beta EA EB a b) (fun x => a x.1) =
      (mean EA a + Real.tanh beta * mean EB b) /
        (1 + Real.tanh beta * mean EA a * mean EB b) := by
  rw [mean_eq, numerator_energy_fst, partition_energy, mean_eq, mean_eq]
  rw [Real.tanh_eq_sinh_div_cosh]
  have hA := (partition_pos EA).ne'
  have hB := (partition_pos EB).ne'
  have hC := (Real.cosh_pos beta).ne'
  field_simp

theorem mean_equiv {S : Type*} [Fintype S] (e : S ≃ A)
    (E : A → ℝ) (a : A → IsingSpin) :
    mean (E ∘ e) (a ∘ e) = mean E a := by
  simp only [mean_eq, numerator, partition, Function.comp_apply]
  rw [e.sum_comp (fun x => spinSign (a x) * Real.exp (E x)),
    e.sum_comp (fun x => Real.exp (E x))]

theorem mean_energy_snd [Nonempty A] [Nonempty B]
    (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin) :
    mean (energy beta EA EB a b) (fun x => b x.2) =
      (mean EB b + Real.tanh beta * mean EA a) /
        (1 + Real.tanh beta * mean EA a * mean EB b) := by
  have he : energy beta EA EB a b =
      energy beta EB EA b a ∘ Equiv.prodComm A B := by
    funext x
    simp only [energy, Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    ring
  rw [he]
  change mean (energy beta EB EA b a ∘ Equiv.prodComm A B)
    ((fun x : B × A => b x.1) ∘ Equiv.prodComm A B) = _
  rw [mean_equiv, mean_energy_fst]
  congr 1; ring

theorem mean_of_energy_split {S : Type*} [Fintype S]
    [Nonempty A] [Nonempty B] (e : S ≃ A × B)
    (E : S → ℝ) (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin)
    (hE : ∀ x, E x = energy beta EA EB a b (e x)) :
    mean E (fun x => a (e x).1) =
      (mean EA a + Real.tanh beta * mean EB b) /
        (1 + Real.tanh beta * mean EA a * mean EB b) := by
  have he : E = energy beta EA EB a b ∘ e := funext hE
  rw [he]
  change mean (energy beta EA EB a b ∘ e) ((fun x : A × B => a x.1) ∘ e) = _
  rw [mean_equiv, mean_energy_fst]

end Problem367.FiniteSpinCoupling

end

end OAI
