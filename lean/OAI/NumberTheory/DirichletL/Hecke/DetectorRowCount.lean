import OAI.NumberTheory.DirichletL.Hecke.DetectorSimultaneous

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRowCount
open HeckeFamily HeckeDyadic

lemma card_of_energy {α : Type*} (rows : Finset α) (F : α→ℂ)
    (U p b C : ℝ) (hU : 0<U)
    (hspike : ∀ u∈rows, U^p≤‖F u‖^2)
    (henergy : ∑ u∈rows, ‖F u‖^2≤C*U^b) :
    (rows.card : ℝ)≤C*U^(b-p) := by
  have hs : (rows.card : ℝ)*U^p≤C*U^b := by
    calc
      _ = ∑ u∈rows, U^p := by simp
      _ ≤ ∑ u∈rows, ‖F u‖^2 := Finset.sum_le_sum hspike
      _ ≤ _ := henergy
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hU p)).mp
  calc
    _ ≤ C*U^b := hs
    _ = (C*U^(b-p))*U^p := by rw [mul_assoc,←Real.rpow_add hU]; congr 2; ring

theorem inverse_count {α : Type*} (rows : Finset α) (χ : α→Character)
    (W : ℝ→ℂ) (D : ℝ) (σ freq : α→ℝ) (P : α→ℂ)
    (U δ r q z εw εp εm C : ℝ) (hU : 0<U)
    (hM : ∀ u∈rows, U^(δ*r-εw)≤‖polynomial (χ u) true W D (σ u) (freq u)‖^2)
    (hP : ∀ u∈rows, U^(2*q*z-εp)≤‖P u‖^2)
    (henergy : ∑ u∈rows,
      ‖polynomial (χ u) true W D (σ u) (freq u)*P u‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ)≤C*U^(1-δ*r-2*q*z+εw+εp+εm) := by
  have hs (u : α) (hu : u∈rows) :
      U^((δ*r-εw)+(2*q*z-εp))≤‖polynomial (χ u) true W D (σ u) (freq u)*P u‖^2 := by
    rw [Real.rpow_add hU,norm_mul,mul_pow]
    exact mul_le_mul (hM u hu) (hP u hu) (Real.rpow_nonneg hU.le _) (sq_nonneg _)
  have hh := card_of_energy rows _ U _ (1+εm) C hU hs henergy
  convert hh using 1; congr 2; ring

theorem plain_count {α : Type*} (rows : Finset α) (χ : α→Character)
    (W : ℝ→ℂ) (N : ℝ) (σ freq : α→ℝ) (P : α→ℂ)
    (U δ m q z εw εp εm C : ℝ) (hU : 0<U)
    (hS : ∀ u∈rows, U^(δ*m-εw)≤‖polynomial (χ u) false W N (σ u) (freq u)‖^2)
    (hP : ∀ u∈rows, U^(2*q*z-εp)≤‖P u‖^2)
    (henergy : ∑ u∈rows,
      ‖polynomial (χ u) false W N (σ u) (freq u)*
        polynomial (χ u) false W N (σ u) (freq u)*P u‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ)≤C*U^(1-2*δ*m-2*q*z+2*εw+εp+εm) := by
  have hs (u : α) (hu : u∈rows) :
      U^((δ*m-εw)+(δ*m-εw)+(2*q*z-εp))≤
        ‖polynomial (χ u) false W N (σ u) (freq u)*
          polynomial (χ u) false W N (σ u) (freq u)*P u‖^2 := by
    rw [Real.rpow_add hU,Real.rpow_add hU,norm_mul,norm_mul,mul_pow,mul_pow]
    exact mul_le_mul (mul_le_mul (hS u hu) (hS u hu) (Real.rpow_nonneg hU.le _) (sq_nonneg _))
      (hP u hu) (Real.rpow_nonneg hU.le _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hh := card_of_energy rows _ U _ (1+εm) C hU hs henergy
  convert hh using 1; congr 2; ring

theorem classified_card_bound {α Label : Type*} [Fintype Label]
    (rows : Finset α) (presentation : α→Label) (left right : α→ℕ)
    (B : ℕ) (hleft : ∀ u∈rows, left u<B) (hright : ∀ u∈rows, right u<B)
    (K : ℝ)
    (hfiber : ∀ p : Label, ∀ j∈Finset.range B, ∀ k∈Finset.range B,
      ((rows.filter (fun u => presentation u=p ∧ left u=j ∧ right u=k)).card : ℝ)≤K) :
    (rows.card : ℝ)≤(Fintype.card Label : ℝ)*(B : ℝ)^2*K := by
  let labels : Finset (Label×ℕ×ℕ) := Finset.univ ×ˢ (Finset.range B ×ˢ Finset.range B)
  let label : α→Label×ℕ×ℕ := fun u => (presentation u,left u,right u)
  have hmaps : (rows : Set α).MapsTo label labels := by
    intro u hu
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (hleft u hu),Finset.mem_range.mpr (hright u hu)⟩⟩
  have he := Finset.card_eq_sum_card_fiberwise hmaps
  have he' : (rows.card : ℝ)=∑ l∈labels,
      ((rows.filter (fun u => label u=l)).card : ℝ) := by exact_mod_cast he
  rw [he']
  calc
    _ ≤ ∑ l∈labels, K := by
      apply Finset.sum_le_sum
      intro l hl
      rcases l with ⟨p,j,k⟩
      obtain ⟨hp,hjk⟩ := Finset.mem_product.mp hl
      obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
      have hh := hfiber p j hj k hk
      simpa only [label,Prod.mk.injEq] using hh
    _ = _ := by simp [labels,Finset.card_product,pow_two,mul_assoc]

end SevenEighths.HeckeDetectorRowCount

end

end OAI
