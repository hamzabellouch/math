import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.UnselectedCard
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GapTemplate

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.ArithmeticSaving Finset Classical
noncomputable section

abbrev GoodGapTemplate (h ℓ L J t m : ℕ) := {d : GapTemplate ℓ L J t m // d.WellFormed h}

def gapTemplateBudget (ℓ L J t : ℕ) : ℕ :=
  (ℓ*J+1)*2^ℓ*(ℓ*J+1)^(ℓ*J)*(2*ℓ+1)^(L*t)*(ℓ*J+1)^(2*t)

def gapTemplateMass (S : PrimeSystem) (P : ℝ) (h ℓ L J t : ℕ) : ℝ :=
  ∑ m : Fin (ℓ*J+1), ∑ d : GoodGapTemplate h ℓ L J t m.val,
    ∑ v : Fin m.val → S.Index,
      (d.val.system h d.property).fiberWeight P 0 (fun a => (v a:ℕ))

lemma gapTemplate_card_uniform (ℓ L J t m : ℕ) (hm : m ≤ ℓ*J) :
    Fintype.card (GapTemplate ℓ L J t m) ≤
      2^ℓ*(ℓ*J+1)^(ℓ*J)*(2*ℓ+1)^(L*t)*(ℓ*J+1)^(2*t) := by
  rw [GapTemplate.card]
  gcongr
  omega

theorem gapTemplateMass_le (S : PrimeSystem) (P B : ℝ) (h ℓ L J t : ℕ)
    (hP : 0 < P) (hB : 0 ≤ B)
    (hS : ∀ p : S.Index, P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp B) :
    gapTemplateMass S P h ℓ L J t ≤ (gapTemplateBudget ℓ L J t:ℝ) *
      (max 1 (∑ p ∈ S.primes,(p:ℝ)⁻¹))^(ℓ*J)*((2+B)/P)^t := by
  let N := ℓ*J
  let H : ℝ := max 1 (∑ p ∈ S.primes,(p:ℝ)⁻¹)
  let δ : ℝ := (2+B)/P
  let C : ℕ := 2^ℓ*(N+1)^N*(2*ℓ+1)^(L*t)*(N+1)^(2*t)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hH : 1 ≤ H := le_max_left _ _
  have hrow (m : Fin (N+1)) (d : GoodGapTemplate h ℓ L J t m.val) :
      (∑ v : Fin m.val → S.Index,
        (d.val.system h d.property).fiberWeight P 0 (fun a => (v a:ℕ))) ≤ H^N*δ^t := by
    have hb := (d.val.system h d.property).fiber_sum_le S.primes P B 0 hP hB le_rfl
      (fun p hp => ⟨S.prime_mem p hp,(hS ⟨p,hp⟩).1,(hS ⟨p,hp⟩).2⟩)
    rw [zero_div,max_eq_right (show 0 ≤ (2+B)/P from hδ)] at hb
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hδ _)
    apply (pow_le_pow_left₀ (by positivity) (le_max_right (1:ℝ) _) _).trans
    apply pow_le_pow_right₀ hH
    rw [unselected_card,Fintype.card_fin]
    omega
  have hcodes (m : Fin (N+1)) :
      (∑ d : GoodGapTemplate h ℓ L J t m.val,
        ∑ v : Fin m.val → S.Index,
          (d.val.system h d.property).fiberWeight P 0 (fun a => (v a:ℕ))) ≤
        (C:ℝ)*(H^N*δ^t) := by
    calc
      _ ≤ ∑ _ : GoodGapTemplate h ℓ L J t m.val,H^N*δ^t := sum_le_sum (fun d _ => hrow m d)
      _ = (Fintype.card (GoodGapTemplate h ℓ L J t m.val):ℝ)*(H^N*δ^t) := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (pow_nonneg (zero_le_one.trans hH) _) (pow_nonneg hδ _))
        exact_mod_cast (Fintype.card_subtype_le _).trans
          (gapTemplate_card_uniform ℓ L J t m.val (Nat.lt_succ_iff.mp m.isLt))
  calc
    _ ≤ ∑ _ : Fin (N+1),(C:ℝ)*(H^N*δ^t) := sum_le_sum (fun m _ => hcodes m)
    _ = ((N+1:ℕ):ℝ)*(C:ℝ)*(H^N*δ^t) := by simp [mul_assoc]
    _ = _ := by
      dsimp only [gapTemplateBudget,C,N,H,δ]
      push_cast
      ring

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
