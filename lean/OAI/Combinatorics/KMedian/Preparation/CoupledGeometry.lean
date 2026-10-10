import Mathlib
import OAI.Combinatorics.KMedian.Preparation.PreparationStars
import OAI.Combinatorics.KMedian.Preparation.CoupledPreparation

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

abbrev Physical (I T : Type) := I ⊕ (T × I)

def physicalCount {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (z : L.Ω × (T → Finset I)) : Physical I T → ℕ :=
  Sum.elim (fun i => L.O z.1 (.inl i)) (L.C z.1 z.2)

noncomputable def physicalOpen {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (z : L.Ω × (T → Finset I)) (a : Physical I T) : ℝ := g*(physicalCount L z a:ℝ)

theorem physical_cap {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (hy1 : ∀ i, y i ≤ 1)
    (z : L.Ω × (T → Finset I)) (hz : 0 < (L.ν.joint L.κ).weight z) :
    ∀ a, 0 ≤ physicalOpen L z a ∧ physicalOpen L z a ≤ 1 := by
  obtain ⟨hω,hξ⟩ := L.ν.support_joint L.κ z hz
  intro a
  refine ⟨mul_nonneg hg (Nat.cast_nonneg _),?_⟩
  cases a with
  | inl i =>
    apply L.open_cap z.1 hω (.inl i)
    dsimp only [weight]
    split_ifs
    · exact hy1 i
    · norm_num
  | inr ti =>
    exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ((L.pieces z.1 z.2 hξ ti.1).2.1 ti.2)) hg).trans_eq hunit

theorem zero_deficit_total {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (t : T) (hc : c t=0) (hp : p t+c t=1) :
    ∀ ω, 0 < L.ν.weight ω → g*(L.K ω t:ℝ)=1 := by
  have hp' : p t=1 := by simpa only [hc,add_zero] using hp
  have he := L.total_deviation t
  simp only [hp',hc,mul_zero,Real.sqrt_zero,add_zero] at he
  have hz : L.ν.expect (fun ω => |g*(L.K ω t:ℝ)-1|)=0 :=
    le_antisymm he (L.ν.expect_nonneg (fun _ => abs_nonneg _))
  intro ω hω
  exact sub_eq_zero.mp (abs_eq_zero.mp
    (L.ν.nonneg_expect_zero_support _ (fun _ => abs_nonneg _) hz ω hω))

theorem physical_mass {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (z : L.Ω × (T → Finset I)) (hξ : 0 < (L.κ z.1).weight z.2) :
    (∑ a, physicalOpen L z a)=
      (∑ e, flag e*(g*(L.O z.1 e:ℝ)))+(∑ t, g*(L.K z.1 t:ℝ)) := by
  simp only [physicalOpen,physicalCount,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    flag,one_mul,zero_mul,sum_const_zero,add_zero,Fintype.sum_prod_type]
  congr 1
  apply sum_congr rfl
  intro t _
  rw [← mul_sum,← Nat.cast_sum,(L.pieces z.1 z.2 hξ t).1]

theorem bundle_ball_mass {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (hg : 0 ≤ g) (z : L.Ω × (T → Finset I)) (hξ : 0 < (L.κ z.1).weight z.2)
    (d : I → ℝ) (r : ℝ) (H : Finset T) (hH : ∀ t ∈ H, ∀ i ∈ P t, d i ≤ r) :
    (∑ t ∈ H, g*(L.K z.1 t:ℝ)) ≤
      ∑ a ∈ univ.filter (fun a : Physical I T => Sum.elim d (fun ti => d ti.2) a ≤ r),
        physicalOpen L z a := by
  classical
  let f := fun t => ∑ i, if d i ≤ r then g*(L.C z.1 z.2 (t,i):ℝ) else 0
  have hf : ∀ t, 0 ≤ f t := fun t => sum_nonneg (fun i _ => by
    split_ifs <;> [exact mul_nonneg hg (Nat.cast_nonneg _); exact le_rfl])
  have he : ∀ t ∈ H, f t=g*(L.K z.1 t:ℝ) := by
    intro t ht
    rw [← (L.pieces z.1 z.2 hξ t).1,Nat.cast_sum,mul_sum]
    apply sum_congr rfl
    intro i _
    by_cases hi : d i ≤ r
    · exact ite_eq_left hi
    · have hn : i ∉ P t := fun hiP => hi (hH t ht i hiP)
      simp only [ite_eq_right hi,(L.pieces z.1 z.2 hξ t).2.2 i hn,Nat.cast_zero,mul_zero]
  have hsum : (∑ t ∈ H, g*(L.K z.1 t:ℝ)) ≤ ∑ t, f t := by
    calc
      _ = ∑ t ∈ H, f t := sum_congr rfl (fun t ht => (he t ht).symm)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ H) (fun t _ _ => hf t)
  rw [sum_filter,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [Sum.elim_inl,Sum.elim_inr,physicalOpen,physicalCount]
  have hout : 0 ≤ ∑ i, if d i ≤ r then g*(L.O z.1 (.inl i):ℝ) else 0 :=
    sum_nonneg (fun i _ => by
      split_ifs <;> [exact mul_nonneg hg (Nat.cast_nonneg _); exact le_rfl])
  exact hsum.trans (le_add_of_nonneg_left hout)

end MetricKMedian.Preparation
end
end

end OAI
