import OAI.NumberTheory.JointDickman.Arithmetic.RandomRectangleSieve
import OAI.NumberTheory.JointDickman.Amplification.UnionSelection
import OAI.NumberTheory.JointDickman.Arithmetic.SieveAffineLines

namespace OAI

/-! # Independently weighted forms in a rectangle -/

namespace JointDickman

open Finset

noncomputable def formSetWeight {k : ℕ} {α : Type*} [DecidableEq α]
    (F : Fin k → Finset α) (θ : Fin k → ℝ) (x : α) : ℝ :=
  ∏ i ∈ univ.filter (fun i => x ∈ F i), θ i

/-- The rectangular form-weight bound with exact residue averages. Each
zero set may be any set of at most `p` pairs, in particular a proper line. -/
theorem form_rectangle_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ)
      (F : ∀ p : P, Fin k → Finset (ZMod p.val × ZMod p.val))
      (θ : P → Fin k → ℝ) (a b c d Z : ℕ), a ≤ b → c ≤ d → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p i, (F p i).card ≤ p.val) → (∀ p i, 0 ≤ θ p i ∧ θ p i ≤ 1) →
      (∑ r ∈ Ico a b, ∑ s ∈ Ico c d, ∏ p : P,
        formSetWeight (F p) (θ p) ((r : ZMod p.val), (s : ZMod p.val))) ≤
      C * ((b : ℝ) - a) * ((d : ℝ) - c) *
        (∏ p : P, (∑ r ∈ range p.val, ∑ s ∈ range p.val,
          formSetWeight (F p) (θ p) ((r : ZMod p.val), (s : ZMod p.val))) / (p.val : ℝ) ^ 2) +
      2 * (((b : ℝ) - a) + ((d : ℝ) - c) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  classical
  obtain ⟨C, hC, hbound⟩ := randomized_pair_rectangle_sieve hFord hM hk
  refine ⟨C, hC, ?_⟩
  intro P F θ a b c d Z hab hcd hZ hP hF hθ
  let I : Finset (Fin k) := univ
  let Ω := {S : Finset (Fin k) // S ∈ I.powerset}
  let μ (p : P) (S : Ω) := bernoulliSubsetMass I (fun i => 1 - θ p i) S.val
  let A (p : P) (S : Ω) := S.val.biUnion (F p)
  have hμ (p : P) (S : Ω) : 0 ≤ μ p S :=
    bernoulliSubsetMass_nonneg (mem_powerset.mp S.property) (by
      intro i _
      constructor <;> linarith [(hθ p i).1, (hθ p i).2])
  have hμ1 (p : P) : ∑ S : Ω, μ p S = 1 := by
    rw [I.powerset.sum_coe_sort (fun S => bernoulliSubsetMass I (fun i => 1 - θ p i) S)]
    exact bernoulliSubsetMass_sum I _
  have hA (p : P) (S : Ω) : (A p S).card ≤ k * p.val := by
    calc
      _ ≤ ∑ i ∈ S.val, (F p i).card := card_biUnion_le
      _ ≤ ∑ _i ∈ S.val, p.val := sum_le_sum (fun i _ => hF p i)
      _ = S.val.card * p.val := by simp
      _ ≤ I.card * p.val := Nat.mul_le_mul_right _ (card_le_card (mem_powerset.mp S.property))
      _ = _ := by simp [I]
  have hpoint (p : P) (r s : ℕ) :
      (∑ S : Ω, μ p S * (if ((r : ZMod p.val), (s : ZMod p.val)) ∈ A p S then 0 else 1)) =
        formSetWeight (F p) (θ p) ((r : ZMod p.val), (s : ZMod p.val)) := by
    change (∑ S : Ω, bernoulliSubsetMass I (fun i => 1 - θ p i) S.val *
      (if ((r : ZMod p.val), (s : ZMod p.val)) ∈ S.val.biUnion (F p) then 0 else 1)) = _
    rw [I.powerset.sum_coe_sort (fun S => bernoulliSubsetMass I (fun i => 1 - θ p i) S *
      (if ((r : ZMod p.val), (s : ZMod p.val)) ∈ S.biUnion (F p) then 0 else 1))]
    exact bernoulli_union_survival I (F p) (θ p) _
  have hdensity (p : P) :
      (∑ S : Ω, μ p S * (1 - ((A p S).card : ℝ) / (p.val : ℝ) ^ 2)) =
        (∑ r ∈ range p.val, ∑ s ∈ range p.val,
          formSetWeight (F p) (θ p) ((r : ZMod p.val), (s : ZMod p.val))) / (p.val : ℝ) ^ 2 := by
    let : NeZero p.val := ⟨(hP p.val p.property).1.ne_zero⟩
    have h := bernoulli_union_density
      (show 0 < Fintype.card (ZMod p.val × ZMod p.val) by
        simp only [Fintype.card_prod, ZMod.card]
        exact Nat.mul_pos (hP p.val p.property).1.pos (hP p.val p.property).1.pos) I (F p) (θ p)
    simp only [Fintype.card_prod, ZMod.card, ← pow_two, Nat.cast_pow] at h
    change (∑ S : Ω, bernoulliSubsetMass I (fun i => 1 - θ p i) S.val *
      (1 - ((S.val.biUnion (F p)).card : ℝ) / (p.val : ℝ) ^ 2)) = _
    rw [I.powerset.sum_coe_sort (fun S => bernoulliSubsetMass I (fun i => 1 - θ p i) S *
      (1 - ((S.biUnion (F p)).card : ℝ) / (p.val : ℝ) ^ 2)), h]
    congr 1
    have hres (f : ZMod p.val → ℝ) : (∑ x, f x) = ∑ n ∈ range p.val, f n := by
      exact_mod_cast residue_sum_eq_range (fun x => (f x : ℂ))
    rw [Fintype.sum_prod_type]
    simp_rw [hres]
    rfl
  have h := hbound P (fun _ => Ω) μ A a b c d Z hab hcd hZ hP hμ hμ1 hA
  simpa only [hpoint, hdensity] using h

end JointDickman

end OAI
