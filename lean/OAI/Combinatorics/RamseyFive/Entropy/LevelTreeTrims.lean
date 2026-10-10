import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.OriginalLevelLaw
import OAI.Combinatorics.RamseyFive.Geometry.TreeTrims

namespace OAI

section
namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
lemma relationMass_swap (R : α → β → Prop) (f : α → ℝ) (g : β → ℝ) :
    relationMass (fun b a => R a b) g f = relationMass R f g := by
  simp only [relationMass, Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> ring
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type} [Fintype I] [DecidableEq I]
  {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

theorem oriented_level_point_trim
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
    (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
    (p : I → Law (ℙ K V)) (q : I → Law (ℙ K (Dual K V)))
    (L : ℝ) (hL : 0≤L)
    (hμ : ∀ i a, (∑ s, μ i s * uniformWeight (X i s) a) ≤ L*p i a)
    (hν : ∀ i b, (∑ t, ν i t * uniformWeight (Y i t) b) ≤ L*q i b)
    (c δ τ P : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2)
    (tree : BinaryTree I) (j : Address tree) :
    (∑ z, originalLevelLaw μ ν z * eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω => ∃ C,
        orientedPivotContextAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree ω (Finset.univ,Finset.univ) j = some C ∧
        ((X (label tree j) (z.1 (label tree j)) ∩ C.1).card : ℝ) <
          (9/10:ℝ)*(X (label tree j) (z.1 (label tree j))).card))) ≤
      10 * pathBudget (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) * L^2 *
        relationMass Incident (p (label tree j)) (q i)) (fun _ => 0) tree j := by
  let C₀ : ℝ := 50*(Nat.card K:ℝ)/(9*(c*δ))
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  let ρ := fun (z : (∀ i, A i) × (∀ i, B i)) i => C₀ * relationMass Incident
    (uniformWeight (X (label tree j) (z.1 (label tree j)))) (uniformWeight (Y i (z.2 i)))
  have hpoint (z : (∀ i, A i) × (∀ i, B i)) := oriented_original_point_trim f r σ hσ hq hd hq3
    (fun i => X i (z.1 i)) (fun i => Y i (z.2 i)) (fun i => hX i _) (fun i => hY i _)
    c δ τ P hc hc9 hδ hτ (X (label tree j) (z.1 (label tree j))) tree j
  simp_rw [relationMass_swap] at hpoint
  calc
    _ ≤ ∑ z, originalLevelLaw μ ν z * (10*pathBudget (ρ z) (fun _ => 0) tree j) :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpoint z) ((originalLevelLaw μ ν).nonneg z)
    _ = 10 * pathBudget (fun i => ∑ z, originalLevelLaw μ ν z * ρ z i) (fun _ => 0) tree j := by
      have he := mean_pathBudget (originalLevelLaw μ ν) ρ (fun _ _ => 0) tree j
      simp only [mul_zero, Finset.sum_const_zero] at he
      rw [← he, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply pathBudget_mono
      · intro i
        have hs := originalLevelLaw_cross_domination μ ν (label tree j) i Incident
          (X (label tree j)) (Y i) (p (label tree j)) (q i) L hL (hμ _) (hν _)
        calc
          _ = C₀*(∑ z, originalLevelLaw μ ν z * relationMass Incident
              (uniformWeight (X (label tree j) (z.1 (label tree j)))) (uniformWeight (Y i (z.2 i)))) := by
            simp only [ρ, Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
          _ ≤ C₀*(L^2*relationMass Incident (p (label tree j)) (q i)) := mul_le_mul_of_nonneg_left hs hC₀
          _ = _ := by dsimp only [C₀]; ring
      · intro i; rfl

theorem oriented_level_dual_trim
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (μ : ∀ i, Law (A i)) (ν : ∀ i, Law (B i))
    (X : ∀ i, A i → Finset (ℙ K V)) (Y : ∀ i, B i → Finset (ℙ K (Dual K V)))
    (hX : ∀ i a, (X i a).Nonempty) (hY : ∀ i b, (Y i b).Nonempty)
    (p : I → Law (ℙ K V)) (q : I → Law (ℙ K (Dual K V)))
    (L : ℝ) (hL : 0≤L)
    (hμ : ∀ i a, (∑ s, μ i s * uniformWeight (X i s) a) ≤ L*p i a)
    (hν : ∀ i b, (∑ t, ν i t * uniformWeight (Y i t) b) ≤ L*q i b)
    (c δ τ P : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ≤c*δ^2)
    (tree : BinaryTree I) (j : Address tree) :
    (∑ z, originalLevelLaw μ ν z * eventMass (orientedPivotTreeLaw f r tree)
      (Finset.univ.filter (fun ω => ∃ C,
        orientedPivotContextAt f r σ hσ hq hd.le (fun i => X i (z.1 i)) (fun i => Y i (z.2 i))
          (fun i => hX i _) (fun i => hY i _) c δ τ P hδ tree ω (Finset.univ,Finset.univ) j = some C ∧
        ((Y (label tree j) (z.2 (label tree j)) ∩ C.2).card : ℝ) <
          (9/10:ℝ)*(Y (label tree j) (z.2 (label tree j))).card))) ≤
      10 * pathBudget (fun _ => 0) (fun i => (50*(Nat.card K:ℝ)/(9*(c*δ))) * L^2 *
        relationMass Incident (p i) (q (label tree j))) tree j := by
  let C₀ : ℝ := 50*(Nat.card K:ℝ)/(9*(c*δ))
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  let ρ := fun (z : (∀ i, A i) × (∀ i, B i)) i => C₀ * relationMass Incident
    (uniformWeight (X i (z.1 i))) (uniformWeight (Y (label tree j) (z.2 (label tree j))))
  have hpoint (z : (∀ i, A i) × (∀ i, B i)) := oriented_original_dual_trim f r σ hσ hq hd hq3
    (fun i => X i (z.1 i)) (fun i => Y i (z.2 i)) (fun i => hX i _) (fun i => hY i _)
    c δ τ P hc hc9 hδ hτ (Y (label tree j) (z.2 (label tree j))) tree j
  calc
    _ ≤ ∑ z, originalLevelLaw μ ν z * (10*pathBudget (fun _ => 0) (ρ z) tree j) :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpoint z) ((originalLevelLaw μ ν).nonneg z)
    _ = 10 * pathBudget (fun _ => 0) (fun i => ∑ z, originalLevelLaw μ ν z * ρ z i) tree j := by
      have he := mean_pathBudget (originalLevelLaw μ ν) (fun _ _ => 0) ρ tree j
      simp only [mul_zero, Finset.sum_const_zero] at he
      rw [← he, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply pathBudget_mono
      · intro i; rfl
      · intro i
        have hs := originalLevelLaw_cross_domination μ ν i (label tree j) Incident
          (X i) (Y (label tree j)) (p i) (q (label tree j)) L hL (hμ _) (hν _)
        calc
          _ = C₀*(∑ z, originalLevelLaw μ ν z * relationMass Incident
              (uniformWeight (X i (z.1 i))) (uniformWeight (Y (label tree j) (z.2 (label tree j))))) := by
            simp only [ρ, Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
          _ ≤ C₀*(L^2*relationMass Incident (p i) (q (label tree j))) := mul_le_mul_of_nonneg_left hs hC₀
          _ = _ := by dsimp only [C₀]; ring
end SharpRamseyFive.ProjectiveIncidence

end

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {A B Ω Ξ ι Θ : Type*} [Fintype A] [Fintype B] [Fintype Ω]
  [Fintype Ξ] [Fintype ι] [Fintype Θ]

lemma independent_event (p : Law Ω) (q : Law Ξ) (P : Ω → Ξ → Prop) :
    eventMass (adaptiveLaw p (fun _ => q))
      (Finset.univ.filter (fun z => P z.1 z.2)) =
        ∑ x, p x * eventMass q (Finset.univ.filter (P x)) := by
  simp only [eventMass, Finset.sum_filter, Fintype.sum_prod_type, adaptiveLaw,
    Finset.mul_sum, mul_ite, mul_zero]

lemma independent_endpoint_event (p : Law Ω) (q : Law Ξ) (endpoint : Ω → B)
    (good : B → Prop) (P : B → Ξ → Prop) :
    eventMass (adaptiveLaw p (fun _ => q))
      (Finset.univ.filter (fun z => good (endpoint z.1) ∧ P (endpoint z.1) z.2)) =
      ∑ b, (if good b then map p endpoint b else 0) *
        eventMass q (Finset.univ.filter (P b)) := by
  calc
    _ = ∑ x, p x * eventMass q (Finset.univ.filter
        (fun ξ => good (endpoint x) ∧ P (endpoint x) ξ)) := by
      simp only [eventMass, Finset.sum_filter, Fintype.sum_prod_type, adaptiveLaw,
        Finset.mul_sum, mul_ite, mul_zero]
    _ = ∑ x, p x * (if good (endpoint x) then
        eventMass q (Finset.univ.filter (P (endpoint x))) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hg : good (endpoint x) <;> simp [hg, eventMass]
    _ = ∑ b, map p endpoint b * (if good b then
        eventMass q (Finset.univ.filter (P b)) else 0) := (sum_map p endpoint (fun b => if good b then eventMass q (Finset.univ.filter (P b)) else 0)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      split_ifs <;> simp

lemma relationMass_mixture_left (R : A → B → Prop) (μ : Law ι)
    (f : ι → A → ℝ) (g : B → ℝ) :
    (∑ i, μ i * relationMass R (f i) g) =
      relationMass R (fun a => ∑ i, μ i * f i a) g := by
  simp only [relationMass, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem actual_target_average (R : A → B → Prop) (p : Law A)
    (g : B → ℝ) (hg : ∀ b, 0 ≤ g b) (μ : Law ι) (X : ι → Finset A)
    (prior : ι → Law Θ) (reject : ι → Θ → B → ℝ) (C L : ℝ)
    (hC : 0 ≤ C) (_hL : 0 ≤ L)
    (hX : ∀ a, (∑ i, μ i * uniformWeight (X i) a) ≤ L * p a)
    (hlocal : ∀ i θ b, reject i θ b ≤
      C * ((((Finset.univ.filter (fun a => R a b)) ∩ X i).card : ℝ) / (X i).card)) :
    (∑ i, μ i * (∑ θ, prior i θ * (∑ b, g b * reject i θ b))) ≤
      C * L * relationMass R p g := by
  have hpoint (i : ι) (θ : Θ) :
      (∑ b, g b * reject i θ b) ≤ C * relationMass R (uniformWeight (X i)) g := by
    rw [relationMass_by_target, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    rw [sum_uniformWeight]
    have h := mul_le_mul_of_nonneg_left (hlocal i θ b) (hg b)
    nlinarith only [h]
  calc
    _ ≤ ∑ i, μ i * (C * relationMass R (uniformWeight (X i)) g) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (μ.nonneg i)
      calc
        _ ≤ ∑ θ, prior i θ * (C * relationMass R (uniformWeight (X i)) g) :=
          Finset.sum_le_sum fun θ _ => mul_le_mul_of_nonneg_left (hpoint i θ) ((prior i).nonneg θ)
        _ = _ := by rw [← Finset.sum_mul, (prior i).sum_one, one_mul]
    _ = C * relationMass R (fun a => ∑ i, μ i * uniformWeight (X i) a) g := by
      rw [← relationMass_mixture_left, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ C * (L * relationMass R p g) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simp only [relationMass, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro z hz
      have h := mul_le_mul_of_nonneg_right (hX z.1) (hg z.2)
      nlinarith only [h]
    _ = _ := by ring

end SharpRamseyFive.FiniteEntropy

end OAI
