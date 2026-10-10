import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.Swap
import OAI.Combinatorics.RamseyFive.Entropy.HistoryCylinder

namespace OAI

section
namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]

noncomputable def piRectangle (E : ∀ i, Finset (α i)) : Finset (∀ i, α i) :=
  Finset.univ.filter (fun x => ∀ i, x i ∈ E i)

lemma eventMass_piRectangle (p : ∀ i, Law (α i)) (E : ∀ i, Finset (α i)) :
    eventMass (piLaw p) (piRectangle E) = ∏ i, eventMass (p i) (E i) := by
  simp only [eventMass, piRectangle, Finset.sum_filter, piLaw]
  calc
    _ = ∑ x : ∀ i, α i, ∏ i, if x i ∈ E i then p i (x i) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Fintype.prod_ite_zero]
    _ = _ := by
      rw [← Fintype.prod_sum (fun i a => if a ∈ E i then p i a else 0)]
      apply Finset.prod_congr rfl
      intro i hi
      rw [←Finset.sum_filter, Finset.filter_univ_mem]

lemma conditionOn_piRectangle (p : ∀ i, Law (α i)) (E : ∀ i, Finset (α i))
    (hE : ∀ i, 0 < eventMass (p i) (E i)) :
    conditionOn (piLaw p) (piRectangle E)
      (by rw [eventMass_piRectangle]; exact Finset.prod_pos (fun i _ => hE i)) =
        piLaw (fun i => conditionOn (p i) (E i) (hE i)) := by
  apply Law.ext
  funext x
  rw [conditionOn_apply, eventMass_piRectangle]
  simp only [piRectangle, Finset.mem_filter, Finset.mem_univ, true_and,
    piLaw, conditionOn]
  rw [Fintype.prod_ite_zero, Finset.prod_div_distrib]

lemma map_piLaw (p : ∀ i, Law (α i)) (f : ∀ i, α i → β i) :
    map (piLaw p) (fun x i => f i (x i)) = piLaw (fun i => map (p i) (f i)) := by
  apply Law.ext
  funext y
  simp only [map, piLaw]
  calc
    _ = ∑ x : ∀ i, α i, ∏ i, if f i (x i) = y i then p i (x i) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Fintype.prod_ite_zero]
      simp only [funext_iff]
    _ = _ := (Fintype.prod_sum (fun i a => if f i a = y i then p i a else 0)).symm

lemma uniformType_pi [∀ i, Nonempty (α i)] :
    uniformType (∀ i, α i) = piLaw (fun i => uniformType (α i)) := by
  apply Law.ext
  funext x
  simp only [uniformType, uniformOn, Finset.mem_univ, ite_true, Finset.card_univ,
    piLaw, Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.PermutationCylinder
open FiniteEntropy
open scoped Classical BigOperators
variable {ι α Ω H : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
  [Fintype Ω] [Fintype H]

theorem blocks_posterior (S : ι → Finset α) (e : ι → Equiv.Perm α) :
    conditionOn (piLaw (fun _ : ι => uniformType (Equiv.Perm α)))
      (piRectangle (fun i => cylinderSet (S i) (e i)))
      (by
        rw [eventMass_piRectangle]
        exact Finset.prod_pos
          (fun i _ => uniformType_event_pos _ (cylinderSet_nonempty (S i) (e i)))) =
    piLaw (fun i => uniformOn (cylinderSet (S i) (e i)) (cylinderSet_nonempty (S i) (e i))) := by
  rw [conditionOn_piRectangle _ _
    (fun i => uniformType_event_pos _ (cylinderSet_nonempty (S i) (e i)))]
  congr 1
  funext i
  exact conditionOn_uniformType _ (cylinderSet_nonempty (S i) (e i))

theorem blocks_fresh_law (S : ι → Finset α) (e : ι → Equiv.Perm α)
    (x y : ι → α) (hx : ∀ i, x i ∉ S i) (hy : ∀ i, y i ∉ (S i).map (e i).toEmbedding) :
    map (piLaw (fun i => conditionOn (uniformType (Equiv.Perm α))
      (cylinderSet (S i) (e i)) (uniformType_event_pos _ (cylinderSet_nonempty (S i) (e i)))))
      (fun r i => r i (x i)) y =
        ∏ i, (1 : ℝ) / (Fintype.card α - (S i).card : ℕ) := by
  rw [map_piLaw (fun i => conditionOn (uniformType (Equiv.Perm α))
    (cylinderSet (S i) (e i)) (uniformType_event_pos _ (cylinderSet_nonempty (S i) (e i))))
    (fun i (r : Equiv.Perm α) => r (x i))]
  change (∏ i, map (conditionOn (uniformType (Equiv.Perm α)) _ _) (fun p => p (x i)) (y i)) = _
  apply Finset.prod_congr rfl
  intro i hi
  exact posterior_draw (S i) (e i) (hx i) (hy i)

end SharpRamseyFive.PermutationCylinder

end

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {B A : Type} [Fintype B] [Fintype A]

lemma piLaw_update_balance (μ : B → Law A) (s : B → A) (b : B) (a : A) :
    piLaw μ s * μ b a = piLaw μ (Function.update s b a) * μ b (s b) := by
  classical
  have h₁ := Finset.mul_prod_erase Finset.univ (fun c => μ c (s c)) (Finset.mem_univ b)
  have h₂ := Finset.mul_prod_erase Finset.univ
    (fun c => μ c (Function.update s b a c)) (Finset.mem_univ b)
  have hprod : (∏ c ∈ Finset.univ.erase b, μ c (Function.update s b a c)) =
      ∏ c ∈ Finset.univ.erase b, μ c (s c) := by
    apply Finset.prod_congr rfl
    intro c hc
    rw [Function.update_of_ne (Finset.mem_erase.mp hc).1]
  simp only [Function.update_self, hprod] at h₂
  change (∏ c, μ c (s c)) * μ b a = (∏ c, μ c (Function.update s b a c)) * μ b (s b)
  rw [←h₁, ←h₂]
  ring

theorem independent_selected_identity (μ : B → Law A)
    (f : (B → A) → B → A → ℝ)
    (hown : ∀ s b a i, f (Function.update s b a) b i = f s b i) (b : B) :
    (∑ s, piLaw μ s * f s b (s b)) =
      ∑ s, piLaw μ s * (∑ a, μ b a * f s b a) := by
  classical
  have hh := Fintype.sum_equiv (RepresentativeAverage.swapAt (A := A) b)
    (fun z => piLaw μ z.1 * μ b z.2 * f z.1 b (z.1 b))
    (fun z => piLaw μ z.1 * μ b z.2 * f z.1 b z.2) (by
      intro z
      simp only [RepresentativeAverage.swapAt, Function.Involutive.toPerm, Equiv.coe_fn_mk]
      rw [hown]
      rw [←piLaw_update_balance]
      )
  simp only [Fintype.sum_prod_type] at hh
  calc
    _ = ∑ s, ∑ a, piLaw μ s * μ b a * f s b (s b) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [←Finset.sum_mul, ←Finset.mul_sum, (μ b).sum_one, mul_one]
    _ = ∑ s, ∑ a, piLaw μ s * μ b a * f s b a := hh
    _ = _ := by simp only [Finset.mul_sum, mul_assoc]

end
end SharpRamseyFive.FiniteEntropy

end OAI
