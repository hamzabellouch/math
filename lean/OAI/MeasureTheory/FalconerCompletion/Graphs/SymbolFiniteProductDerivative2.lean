import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.InverseAngularTerms
import OAI.MeasureTheory.FalconerCompletion.Graphs.SymbolFiniteProductDerivative

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set
open scoped ContDiff
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem symbol_finite_product_derivativeND {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → V → ℂ) (c : ι → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (m : ℕ) (s : Set V) (hc : ∀ i ∈ S, 0 ≤ c i)
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i))
    (hb : ∀ i ∈ S, ∀ k ≤ m, ∀ x ∈ s, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ c i*D^k) :
    ∀ k ≤ m, ∀ x ∈ s, ‖iteratedFDeriv ℝ k (fun x => ∏ i ∈ S, f i x) x‖ ≤
      (∏ i ∈ S, c i)*((S.card:ℝ)*D)^k := by
  induction S using Finset.induction_on with
  | empty =>
    intro k hk x hx
    cases k with
    | zero => simp
    | succ k => simp [iteratedFDeriv_succ_const]
  | @insert a S ha ih =>
    have hcS : ∀ i ∈ S, 0 ≤ c i := fun i hi => hc i (Finset.mem_insert_of_mem hi)
    have hfS : ∀ i ∈ S, ContDiff ℝ ∞ (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hbS := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have ih := ih hcS hfS hbS
    intro k hk x hx
    simp only [Finset.prod_insert ha,Finset.card_insert_of_notMem ha,Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ ∑ j ∈ Finset.range (k+1), (k.choose j:ℝ)*‖iteratedFDeriv ℝ j (f a) x‖*
          ‖iteratedFDeriv ℝ (k-j) (fun x => ∏ i ∈ S, f i x) x‖ :=
        norm_iteratedFDeriv_mul_le (hf a (Finset.mem_insert_self _ _))
          (contDiff_prod fun i hi => hfS i hi) x (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))
      _ ≤ ∑ j ∈ Finset.range (k+1), (k.choose j:ℝ)*(c a*D^j)*
          ((∏ i ∈ S, c i)*((S.card:ℝ)*D)^(k-j)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hca := hc a (Finset.mem_insert_self _ _)
        gcongr
        · exact hb a (Finset.mem_insert_self _ _) j (hjk.trans hk) x hx
        · exact ih (k-j) ((Nat.sub_le _ _).trans hk) x hx
      _ = (c a*∏ i ∈ S,c i)*(D+(S.card:ℝ)*D)^k := by
        rw [add_pow,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by congr 2; ring

lemma symbol_finite_product_supportND {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → V → ℂ) {i : ι} (hi : i ∈ S) (k : ℕ) :
    tsupport (iteratedFDeriv ℝ k (fun x => ∏ j ∈ S, f j x)) ⊆ tsupport (f i) := by
  apply (tsupport_iteratedFDeriv_subset k).trans
  have he : (fun x => ∏ j ∈ S, f j x) = fun x => f i x*∏ j ∈ S.erase i, f j x := by
    funext x
    exact (Finset.mul_prod_erase S (fun j => f j x) hi).symm
  rw [he]
  exact tsupport_mul_subset_left

lemma symbol_budget_costND {ι : Type*} (S : Finset ι) (q : ι → ℕ)
    {C : ℝ} (hC : 1 ≤ C) {B : ℕ} (hB : ∑ i ∈ S, q i ≤ B) :
    (∏ i ∈ S, C^(q i)) ≤ C^B := by
  rw [Finset.prod_pow_eq_pow_sum]
  exact pow_le_pow_right₀ hC hB

theorem symbol_budget_productND {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → V → ℂ) (q : ι → ℕ) {C D P : ℝ}
    (hC : 1 ≤ C) (hD : 0 ≤ D) {B m : ℕ} (s : Set V)
    (hB : ∑ i ∈ S, q i ≤ B) (hcard : (S.card:ℝ) ≤ P)
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i))
    (hb : ∀ i ∈ S, ∀ k ≤ m, ∀ x ∈ s,
      ‖iteratedFDeriv ℝ k (f i) x‖ ≤ C^(q i)*(C*D)^k) :
    ∀ k ≤ m, ∀ x ∈ s,
      ‖iteratedFDeriv ℝ k (fun x => ∏ i ∈ S, f i x) x‖ ≤ C^(B+k)*(P*D)^k := by
  intro k hk x hx
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  calc
    _ ≤ (∏ i ∈ S,C^(q i))*((S.card:ℝ)*(C*D))^k :=
      symbol_finite_product_derivativeND S f (fun i => C^(q i)) (C*D) (mul_nonneg hC₀ hD)
        m s (fun _ _ => pow_nonneg hC₀ _) hf hb k hk x hx
    _ ≤ C^B*(P*(C*D))^k :=
      mul_le_mul (symbol_budget_costND S q hC hB)
        (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hcard (mul_nonneg hC₀ hD)) k)
        (by positivity) (pow_nonneg hC₀ _)
    _ = _ := by rw [pow_add]; ring

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set
open scoped ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

lemma normalizedAngularWordND_budget_bound (W : Finset (List (V →L[ℝ] V)))
    (m b : ℕ) (hb : ∀ L ∈ W, L.length ≤ b) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ L ∈ W, ∀ (f : SmoothFunctionND V) (A : ℝ), 1 ≤ A →
      (∀ w, ‖w‖=1 → ‖f.1 w‖ ≤ 1) →
      (∀ j ≤ m+b, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j f.1 w‖ ≤ C*A^j) →
      ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (normalizedAngularWordND A L f).1 w‖ ≤ D^L.length*(D*A)^j := by
  obtain ⟨D,hD,hDb⟩ := normalizedAngularWordND_finite_bound W m b hb C hC
  refine ⟨max 1 D,le_max_left _ _,?_⟩
  intro L hL f A hA hf0 hf j hj w hw
  by_cases hz : L.length+j=0
  · have hlen : L=[] := List.length_eq_zero_iff.mp (by omega)
    have hj0 : j=0 := by omega
    subst L; subst j
    simpa [normalizedAngularWordND,angularWordOperatorND] using hf0 w hw
  · have hpos : 1 ≤ L.length+j := by omega
    calc
      _ ≤ D*A^j := hDb L hL f A hA hf j hj w hw
      _ ≤ (max 1 D)^(L.length+j)*A^j := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hA) _)
        have hp : max 1 D ≤ (max 1 D)^(L.length+j) := by
          simpa only [pow_one] using (pow_le_pow_right₀ (le_max_left 1 D) hpos)
        exact (le_max_right _ _).trans hp
      _ = _ := by rw [pow_add,mul_pow]; ring

lemma normalizedAngularProductND_admissible {ι : Type*} [DecidableEq ι]
    (W : Finset (List (V →L[ℝ] V))) (m b B : ℕ)
    (hW : ∀ L ∈ W, L.length ≤ b) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (S : Finset ι) (f : ι → SmoothFunctionND V)
      (L : ι → List (V →L[ℝ] V)) (A : ι → ℝ) (M P : ℝ),
      (∀ i ∈ S, L i ∈ W) → (∑ i ∈ S, (L i).length ≤ B) →
      (∀ i ∈ S, 1 ≤ A i) → (∀ i ∈ S, A i ≤ M) → 0 ≤ M → (S.card:ℝ) ≤ P →
      (∀ i ∈ S, ∀ w, ‖w‖=1 → ‖(f i).1 w‖ ≤ 1) →
      (∀ i ∈ S, ∀ j ≤ m+b, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (f i).1 w‖ ≤ C*(A i)^j) →
      ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (smoothFinsetProductND S (fun i =>
          normalizedAngularWordND (A i) (L i) (f i))).1 w‖ ≤ D^(B+j)*(P*M)^j := by
  obtain ⟨D,hD,hDb⟩ := normalizedAngularWordND_budget_bound W m b hW C hC
  refine ⟨D,hD,?_⟩
  intro S f L A M P hL hB hA hM hM0 hP hf0 hf j hj w hw
  apply symbol_budget_productND S (fun i => (normalizedAngularWordND (A i) (L i) (f i)).1)
    (fun i => (L i).length) hD hM0 {w | ‖w‖=1} hB hP
    (fun _ _ => smoothFunctionND_contDiff _) ?_ j hj w hw
  intro i hi k hk z hz
  apply (hDb (L i) (hL i hi) (f i) (A i) (hA i hi) (hf0 i hi) (hf i hi) k hk z hz).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hD) _)
  exact pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans hD) (zero_le_one.trans (hA i hi)))
    (mul_le_mul_of_nonneg_left (hM i hi) (zero_le_one.trans hD)) _

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
