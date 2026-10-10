import OAI.MathematicalPhysics.Heisenberg.SimultaneousPins

namespace OAI

section
noncomputable section
open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical

namespace Heisenberg.Pin
attribute [-instance] Subtype.instDecidableEq
open Heisenberg.Cycle Heisenberg.Return
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

lemma pinDensity_comparison (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω) (E : Set V) (T : Finset V) (ω : Ω) :
    pinDensity μ π E ω ≤ (2 : ℝ) ^ T.card * pinDensity μ π (E ∪ (T : Set V)) ω := by
  have hZ : pinPartition μ π (E ∪ (T : Set V)) ≤ pinPartition μ π E := by
    apply Finset.sum_le_sum
    intro o _
    exact mul_le_mul_of_nonneg_left (pin_weight_comparison (π o) E T).1 (hμ o)
  have hn : μ ω * (2 : ℝ) ^ missingCount (π ω) E ≤
      (2 : ℝ) ^ T.card * (μ ω * (2 : ℝ) ^ missingCount (π ω) (E ∪ (T : Set V))) := by
    calc
      _ ≤ μ ω * ((2 : ℝ) ^ T.card * (2 : ℝ) ^ missingCount (π ω) (E ∪ (T : Set V))) :=
        mul_le_mul_of_nonneg_left (pin_weight_comparison (π ω) E T).2 (hμ ω)
      _ = _ := by ring
  have hμω := hμ ω
  unfold pinDensity
  rw [← mul_div_assoc]
  exact div_le_div₀ (by positivity) hn (pinPartition_pos μ π hμ hpos _) hZ

def testPins (E : Set V) (T : Finset V) : Finset ↥(E ∪ (T : Set V)) :=
  T.subtype (fun i => i ∈ E ∪ (T : Set V))

omit [Fintype V] in
@[simp] lemma mem_testPins (E : Set V) (T : Finset V) (i : ↥(E ∪ (T : Set V))) :
    i ∈ testPins E T ↔ (i : V) ∈ T := Finset.mem_subtype

omit [Fintype V] in
@[simp] lemma card_testPins (E : Set V) (T : Finset V) :
    (testPins E T).card = T.card := by
  rw [testPins, Finset.card_subtype, Finset.filter_eq_self.mpr]
  intro i hi
  exact Or.inr hi

lemma testPins_event (π : Equiv.Perm V) (E : Set V) (T : Finset V)
    (hET : Disjoint E (T : Set V)) :
    (∀ i ∈ testPins E T, nextPermutation π (E ∪ (T : Set V)) i ∈ testPins E T) ↔
      ∀ i ∈ T, ¬ HasHit π E i := by
  refine Iff.trans ?_ (nextPoint_preserves_iff π E (T : Set V) hET)
  simp only [mem_testPins]
  constructor
  · intro h i hi
    exact h ⟨i, Or.inr hi⟩ hi
  · intro h i hi
    exact h i hi

def returnFraction (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (E : Set V) (T : Finset V) : ℝ :=
  (∑ i ∈ testPins E T, ∑ ω,
    if nextPermutation (π ω) (E ∪ (T : Set V)) i ∈ testPins E T
    then pinDensity μ π (E ∪ (T : Set V)) ω else 0) / T.card

lemma pinned_input_return_bound (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω) (hs : Stable (lawSymbol μ π))
    (P : Set V) (T : Finset P) (hT : T.Nonempty) :
    (∑ ω, if ∀ i ∈ T, nextPermutation (π ω) P i ∈ T then pinDensity μ π P ω else 0) ≤
      ((∑ i ∈ T, ∑ ω, if nextPermutation (π ω) P i ∈ T then pinDensity μ π P ω else 0)
        / T.card) ^ T.card := by
  have h := finite_input_return_bound (pinDensity μ π P)
    (fun ω => nextPermutation (π ω) P) (pinDensity_nonneg μ π hμ hpos P)
    (pinDensity_sum μ π hμ hpos P) (stable_pinDensity μ π hμ hpos hs P) T hT
  simpa only using h

theorem finite_simultaneous_pin_test (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω) (hs : Stable (lawSymbol μ π))
    (E : Set V) (T : Finset V) (hT : T.Nonempty) (hET : Disjoint E (T : Set V)) :
    (∑ ω, if ∀ i ∈ T, ¬ HasHit (π ω) E i then pinDensity μ π E ω else 0) ≤
      (2 * returnFraction μ π E T) ^ T.card := by
  have hTP : (testPins E T).Nonempty := by
    obtain ⟨i, hi⟩ := hT
    exact ⟨⟨i, Or.inr hi⟩, (mem_testPins E T _).mpr hi⟩
  have hb := pinned_input_return_bound μ π hμ hpos hs (E ∪ (T : Set V))
    (testPins E T) hTP
  simp only [testPins_event _ _ _ hET, card_testPins] at hb
  change (∑ ω, if ∀ i ∈ T, ¬ HasHit (π ω) E i then
    pinDensity μ π (E ∪ (T : Set V)) ω else 0) ≤ returnFraction μ π E T ^ T.card at hb
  calc
    _ ≤ ∑ ω, (2 : ℝ) ^ T.card * (if ∀ i ∈ T, ¬ HasHit (π ω) E i then
        pinDensity μ π (E ∪ (T : Set V)) ω else 0) := by
      apply Finset.sum_le_sum
      intro ω _
      split_ifs
      · exact pinDensity_comparison μ π hμ hpos E T ω
      · simp
    _ = (2 : ℝ) ^ T.card * (∑ ω, if ∀ i ∈ T, ¬ HasHit (π ω) E i then
        pinDensity μ π (E ∪ (T : Set V)) ω else 0) := (Finset.mul_sum ..).symm
    _ ≤ (2 : ℝ) ^ T.card * returnFraction μ π E T ^ T.card :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := (mul_pow ..).symm

end Heisenberg.Pin

namespace Heisenberg.FiniteExchange
open Pin
open scoped Classical

def Bits : ℕ → Type
  | 0 => PUnit
  | n+1 => Bool × Bits n
instance bitsFintype : (n : ℕ) → Fintype (Bits n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n+1 => @instFintypeProd Bool (Bits n) inferInstance (bitsFintype n)

def weight (p : ℕ → ℝ) : (n : ℕ) → Bits n → ℝ
  | 0, _ => 1
  | n+1, b => (if b.1 then p n else 1-p n) * weight p n b.2

def endpoint {V : Type*} [DecidableEq V] (a b : ℕ → V) (initial : Equiv.Perm V) :
    (n : ℕ) → Bits n → Equiv.Perm V
  | 0, _ => initial
  | n+1, c => (if c.1 then Equiv.swap (a n) (b n) else 1) * endpoint a b initial n c.2

lemma weight_nonneg (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (n : ℕ) (c : Bits n) : 0 ≤ weight p n c := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih =>
    apply mul_nonneg _ (ih c.2)
    rcases c with ⟨x,c⟩
    cases x <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact sub_nonneg.mpr (hp n).2
    · exact (hp n).1

lemma weight_sum (p : ℕ → ℝ) (n : ℕ) : ∑ c, weight p n c = 1 := by
  induction n with
  | zero =>
    change (∑ c : PUnit, (1 : ℝ)) = 1
    simp
  | succ n ih =>
    change (∑ c : Bool × Bits n, (if c.1 then p n else 1-p n) * weight p n c.2) = 1
    rw [Fintype.sum_prod_type,Fintype.sum_bool]
    simp only [ite_true,Bool.false_eq_true,ite_false,← Finset.mul_sum,ih,mul_one]
    ring

theorem endpoint_stable {V : Type*} [Fintype V] [DecidableEq V]
    (a b : ℕ → V) (initial : Equiv.Perm V) (p : ℕ → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (n : ℕ) :
    Stable (lawSymbol (weight p n) (endpoint a b initial n)) := by
  induction n with
  | zero =>
    have h : lawSymbol (weight p 0) (endpoint a b initial 0) = permutationSymbol initial := by
      change (∑ _ : PUnit, MvPolynomial.C ((1 : ℝ) : ℂ) * permutationSymbol initial) = _
      simp
    rw [h]
    exact stable_permutationSymbol initial
  | succ n ih =>
    exact stable_lawSymbol_bernoulli (weight p n) (endpoint a b initial n) ih
      (a n) (b n) (hp n).1 (hp n).2

end Heisenberg.FiniteExchange

namespace Heisenberg.FiniteExchange
open Pin Return
variable {V : Type*} [Fintype V]

theorem finite_history_pin_test
    (a b : ℕ → V) (initial : Equiv.Perm V) (p : ℕ → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (n : ℕ)
    (E : Set V) (T : Finset V) (hT : T.Nonempty) (hET : Disjoint E (T : Set V)) :
    (∑ c : Bits n, if ∀ i ∈ T, ¬ HasHit (endpoint a b initial n c) E i then
      pinDensity (weight p n) (endpoint a b initial n) E c else 0) ≤
      (2 * returnFraction (weight p n) (endpoint a b initial n) E T) ^ T.card := by
  exact finite_simultaneous_pin_test (weight p n) (endpoint a b initial n)
    (weight_nonneg p hp n) (by rw [weight_sum]; exact zero_lt_one)
    (endpoint_stable a b initial p hp n) E T hT hET

end Heisenberg.FiniteExchange

namespace Heisenberg.Exposure
variable {B : Type*}
end Heisenberg.Exposure
namespace Heisenberg.LayeredExchange
variable {T V : Type*}

end Heisenberg.LayeredExchange

namespace Heisenberg.Exposure
variable {A B : Type*} [Monoid A] [Monoid B]

end Heisenberg.Exposure
namespace Heisenberg.LayeredExchange
open Exposure
variable {T V : Type*}

end Heisenberg.LayeredExchange

namespace Heisenberg.Pin
open Exposure
variable {V Ω Ψ : Type*} [Fintype V] [Fintype Ω] [Fintype Ψ]

lemma lawSymbol_reparam (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (e : Ψ ≃ Ω) :
    lawSymbol (μ ∘ e) (π ∘ e) = lawSymbol μ π := by
  exact e.sum_comp (fun ω => MvPolynomial.C (μ ω : ℂ) * permutationSymbol (π ω))

lemma stable_array (n : ℕ) (a b : Fin n → V) (p : Fin n → ℝ)
    (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1) :
    Stable (lawSymbol (fun c : Fin n → Bool => ∏ i,if c i then p i else 1-p i)
      (fun c => orderedProduct n (fun i => if c i then Equiv.swap (a i) (b i) else 1))) := by
  classical
  induction n with
  | zero => simpa [lawSymbol,orderedProduct] using stable_permutationSymbol (1 : Equiv.Perm V)
  | succ n ih =>
    have ht := ih (fun i => a i.succ) (fun i => b i.succ) (fun i => p i.succ) (fun i => hp i.succ)
    have hh := stable_lawSymbol_bernoulli
      (fun c : Fin n → Bool => ∏ i,if c i then p i.succ else 1-p i.succ)
      (fun c => orderedProduct n (fun i => if c i then Equiv.swap (a i.succ) (b i.succ) else 1))
      ht (a 0) (b 0) (hp 0).1 (hp 0).2
    rw [←lawSymbol_reparam _ _ (splitArray n)] at hh
    convert hh using 1
    congr 1
    funext c
    exact Fin.prod_univ_succ _

end Heisenberg.Pin

namespace Heisenberg.LayeredExchange
attribute [-instance] instDecidableEqProd
open Exposure Pin Return
variable {V : Type*} [Fintype V]

theorem stable_wiring {n : ℕ} (s : Equiv.Perm (Fin n))
    (a b : Fin n → V) (p : Fin n → ℝ) (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1) :
    Stable (lawSymbol (fun c : Fin n → Bool => ∏ i,if c i then p i else 1-p i)
      (fun c => wiring s (fun i => if c i then Equiv.swap (a i) (b i) else 1))) := by
  classical
  have h := stable_array n (fun i => (i,a i)) (fun i => (i,b i)) p hp
  have hh := stable_rename_outputs h (Equiv.prodCongr s (Equiv.refl V))
  rw [←lawSymbol_deterministic_output] at hh
  convert hh using 1
  apply congrArg (lawSymbol _)
  funext c
  rw [wiring,fibers_ordered_product]
  congr 1
  congr 1
  funext i
  cases c i <;> simp only [Bool.false_eq_true,ite_false,ite_true,fibers_swap]
  · simp [fibers_one]
  · ext z <;> simp only [Equiv.swap_apply_def] <;> split_ifs <;> rfl

def layerWeight {n : ℕ} (p : Fin n → ℝ) (c : Fin n → Bool) : ℝ :=
  ∏ i,if c i then p i else 1-p i

def coinWiring {n : ℕ} (s : Equiv.Perm (Fin n)) (a b : Fin n → V)
    (c : Fin n → Bool) : Equiv.Perm (Fin n × V) :=
  wiring s (fun i => if c i then Equiv.swap (a i) (b i) else 1)

lemma layerWeight_nonneg {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1) :
    ∀ c,0 ≤ layerWeight p c := by
  intro c
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith [(hp i).1,(hp i).2]

lemma layerWeight_sum {n : ℕ} (p : Fin n → ℝ) : (∑ c,layerWeight p c)=1 := by
  unfold layerWeight
  rw [←Fintype.prod_sum (fun i (c : Bool) => if c then p i else 1-p i)]
  simp

lemma coinWiring_stable {n : ℕ} (s : Equiv.Perm (Fin n)) (a b : Fin n → V)
    (p : Fin n → ℝ) (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1) :
    Stable (lawSymbol (layerWeight p) (coinWiring s a b)) := stable_wiring s a b p hp

attribute [local irreducible] pinDensity returnFraction lawSymbol wiring fibers layerWeight coinWiring

theorem layer_pin_test {n : ℕ} (s : Equiv.Perm (Fin n))
    (a b : Fin n → V) (p : Fin n → ℝ) (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1)
    (E : Set (Fin n × V)) (T : Finset (Fin n × V)) (hT : T.Nonempty)
    (hET : Disjoint E (T : Set (Fin n × V))) :
    (∑ c,if ∀ i ∈ T,¬HasHit (coinWiring s a b c) E i then
      pinDensity (layerWeight p) (coinWiring s a b) E c else 0) ≤
      (2*returnFraction (layerWeight p) (coinWiring s a b) E T)^T.card := by
  exact finite_simultaneous_pin_test (layerWeight p) (coinWiring s a b)
    (layerWeight_nonneg p hp) (by rw [layerWeight_sum]; exact zero_lt_one)
    (coinWiring_stable s a b p hp) E T hT hET

end Heisenberg.LayeredExchange
end
end
end
end
end
end
end
end
end
end

end OAI
