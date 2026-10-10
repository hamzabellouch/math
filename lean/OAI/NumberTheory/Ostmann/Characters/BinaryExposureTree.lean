import OAI.NumberTheory.Ostmann.Characters.BinaryExposure

namespace OAI

noncomputable section
namespace Ostmann.Characters.BinaryExposure
attribute [local instance] Classical.propDecidable

def Budget : ℕ → Type
  | 0 => PUnit
  | k+1 => NNReal × (Budget k × Budget k)

def Budget.value : {k:ℕ} → Budget k → NNReal
  | 0,_ => 1
  | _k+1,b => b.1 * b.2.1.value * b.2.2.value

variable {G H:Type*} [Group G] [Fintype G]

def Controlled (c:ℕ→H→G→G→Prop) (left right:ℕ→H→G→G→H) :
    (k:ℕ) → H → G → Budget k → Prop
  | 0,_,_,_ => True
  | k+1,h,t,b =>
      (Nat.card {x:G // c k h t x}:ℝ) / Nat.card G ≤ b.1 ∧
      ∀ x:G, Controlled c left right k (left k h t x) x b.2.1 ∧
        Controlled c left right k (right k h t x) (x⁻¹*t) b.2.2

theorem probability_le_tree (c:ℕ→H→G→G→Prop)
    (left right:ℕ→H→G→G→H) (k:ℕ) (h:H) (t:G) (b:Budget k)
    (hc:Controlled c left right k h t b) :
    probability c left right k h t ≤ (b.value:ℝ) := by
  induction k generalizing h t with
  | zero => exact le_rfl
  | succ k ih =>
    change avg (fun x:G=>(if c k h t x then 1 else 0)*
      probability c left right k (left k h t x) x *
      probability c left right k (right k h t x) (x⁻¹*t)) ≤ _
    apply le_trans (avg_mono _ (fun x:G=>(if c k h t x then 1 else 0)*
      ((b.2.1.value:ℝ)*(b.2.2.value:ℝ))) ?_)
    · rw [avg_mul_const,avg_indicator]
      change _ ≤ (b.1:ℝ)*(b.2.1.value:ℝ)*(b.2.2.value:ℝ)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hc.1 (mul_nonneg b.2.1.value.property b.2.2.value.property)
    · intro x
      by_cases hx:c k h t x
      · simp only [hx,ite_true,one_mul]
        exact mul_le_mul (ih _ _ b.2.1 (hc.2 x).1)
          (ih _ _ b.2.2 (hc.2 x).2)
          (probability_nonneg c left right k _ _) b.2.1.value.property
      · simp only [hx,ite_false,zero_mul,le_refl]

theorem count_le_tree (c:ℕ→H→G→G→Prop)
    (left right:ℕ→H→G→G→H) (k:ℕ) (h:H) (t:G) (b:Budget k)
    (hc:Controlled c left right k h t b) :
    (Nat.card {z:BinaryHaar.Splits G k // admissible c left right k h t z}:ℝ)/
      Nat.card (BinaryHaar.Splits G k) ≤ (b.value:ℝ) := by
  rw [← probability_eq_count]
  exact probability_le_tree c left right k h t b hc

end Ostmann.Characters.BinaryExposure

end

end OAI
