import OAI.NumberTheory.JointDickman.Arithmetic.RandomRootSieve
import OAI.NumberTheory.JointDickman.Amplification.RootSelection

namespace OAI

/-! # Interval sieve for individually weighted forms

Roots may coincide. The Euler factor is the exact residue average of all
local form weights, rather than a product that assumes distinct roots.
-/

namespace JointDickman

open Finset

/-- The product of the weights of all forms vanishing at a residue. -/
noncomputable def formRootWeight {k p : ℕ}
    (root : Fin k → ZMod p) (θ : Fin k → ℝ) (r : ZMod p) : ℝ :=
  ∏ i ∈ univ.filter (fun i => root i = r), θ i

/-- Independently weighting each form gives the precise local residue
factor, uniformly even when some roots coincide. -/
theorem form_interval_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ)
      (root : ∀ p : P, Fin k → ZMod p.val) (θ : P → Fin k → ℝ)
      (a b Z : ℕ), a ≤ b → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p i, 0 ≤ θ p i ∧ θ p i ≤ 1) →
      (∑ n ∈ Ico a b, ∏ p : P, formRootWeight (root p) (θ p) (n : ZMod p.val)) ≤
      C * ((b : ℝ) - a) *
        (∏ p : P, (∑ r ∈ range p.val,
          formRootWeight (root p) (θ p) (r : ZMod p.val)) / p.val) +
        2 * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  classical
  obtain ⟨C, hC, hbound⟩ := randomized_root_interval_sieve hFord hM hk
  refine ⟨C, hC, ?_⟩
  intro P root θ a b Z hab hZ hP hθ
  let I : Finset (Fin k) := univ
  let Ω := {S : Finset (Fin k) // S ∈ I.powerset}
  let μ (p : P) (S : Ω) := bernoulliSubsetMass I (fun i => 1 - θ p i) S.val
  let A (p : P) (S : Ω) := S.val.image (root p)
  have hμ (p : P) (S : Ω) : 0 ≤ μ p S :=
    bernoulliSubsetMass_nonneg (mem_powerset.mp S.property) (by
      intro i _
      constructor <;> linarith [(hθ p i).1, (hθ p i).2])
  have hμ1 (p : P) : ∑ S : Ω, μ p S = 1 := by
    rw [I.powerset.sum_coe_sort (fun S => bernoulliSubsetMass I (fun i => 1 - θ p i) S)]
    exact bernoulliSubsetMass_sum I _
  have hA (p : P) (S : Ω) : (A p S).card ≤ k := by
    calc
      _ ≤ S.val.card := card_image_le
      _ ≤ I.card := card_le_card (mem_powerset.mp S.property)
      _ = k := by simp [I]
  have hpoint (p : P) (n : ℕ) :
      (∑ S : Ω, μ p S * (if (n : ZMod p.val) ∈ A p S then 0 else 1)) =
        formRootWeight (root p) (θ p) (n : ZMod p.val) := by
    change (∑ S : Ω, bernoulliSubsetMass I (fun i => 1 - θ p i) S.val *
      (if (n : ZMod p.val) ∈ S.val.image (root p) then 0 else 1)) = _
    rw [I.powerset.sum_coe_sort (fun S => bernoulliSubsetMass I (fun i => 1 - θ p i) S *
      (if (n : ZMod p.val) ∈ S.image (root p) then 0 else 1))]
    exact bernoulli_root_survival I (root p) (θ p) n
  have hdensity (p : P) :
      (∑ S : Ω, μ p S * (1 - ((A p S).card : ℝ) / p.val)) =
        (∑ r ∈ range p.val, formRootWeight (root p) (θ p) (r : ZMod p.val)) / p.val := by
    let : NeZero p.val := ⟨(hP p.val p.property).1.ne_zero⟩
    have h := bernoulli_root_density (show 0 < Fintype.card (ZMod p.val) by
      rw [ZMod.card]; exact (hP p.val p.property).1.pos) I (root p) (θ p)
    simp only [ZMod.card] at h
    change (∑ S : Ω, bernoulliSubsetMass I (fun i => 1 - θ p i) S.val *
      (1 - ((S.val.image (root p)).card : ℝ) / p.val)) = _
    rw [I.powerset.sum_coe_sort (fun S => bernoulliSubsetMass I (fun i => 1 - θ p i) S *
      (1 - ((S.image (root p)).card : ℝ) / p.val)), h]
    congr 1
    have hp := residue_sum_eq_range (fun r : ZMod p.val =>
      (formRootWeight (root p) (θ p) r : ℂ))
    exact_mod_cast hp
  have h := hbound P (fun _ => Ω) μ A a b Z hab hZ hP hμ hμ1 hA
  simpa only [hpoint, hdensity] using h

end JointDickman

end OAI
