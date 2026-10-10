import OAI.NumberTheory.CubicMoment.Transform.MetaplecticLocalSeries
import OAI.NumberTheory.CubicMoment.Estimates.SupportedIdealCount

namespace OAI

/-! Finite versions of the absolute local Euler sum in the Voronoi
formula, including the actual squarefree and supported ideal exponents. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticPrimeWeight (p σ : ℝ) (e : Fin 2) (k : ℕ) : ℝ :=
  if e = 0 then
    if k = 0 then 1 else p*metaplecticLocalRatio p σ^k
  else p^(-σ)*metaplecticLocalRatio p σ^k

lemma metaplecticPrimeWeight_nonneg {p σ : ℝ} (hp : 0 ≤ p) (e : Fin 2) (k : ℕ) :
    0 ≤ metaplecticPrimeWeight p σ e k := by
  unfold metaplecticPrimeWeight metaplecticLocalRatio
  split_ifs <;> positivity

lemma metaplecticPrimeWeight_sum (p σ : ℝ) (k : ℕ) :
    (∑ e : Fin 2, metaplecticPrimeWeight p σ e k) = metaplecticLocalTerms p σ k := by
  simp only [Fin.sum_univ_two,metaplecticPrimeWeight,ite_true,show (1 : Fin 2) ≠ 0 by decide,ite_false]
  rfl

/-- The local summand is exactly the common-prime factor, times the
square-root coefficient growth, times the inverse norm power. -/
lemma metaplecticPrimeWeight_eq {p : ℝ} (hp : 0 < p) (σ : ℝ) (e : Fin 2) (k : ℕ) :
    metaplecticPrimeWeight p σ e k =
      (if e.val+k = 0 then 1 else p)*p^((k:ℝ)/2)*
        p^(-((e.val:ℝ)+3*k)*(1+σ)) := by
  have hq : metaplecticLocalRatio p σ^k = p^((k:ℝ)*(-5/2-3*σ)) := by
    rw [metaplecticLocalRatio,←Real.rpow_mul_natCast hp.le]
    congr 1
    ring
  have he : e = 0 ∨ e = 1 := by fin_cases e <;> simp
  rcases he with rfl | rfl
  · by_cases hk : k = 0
    · subst k
      simp [metaplecticPrimeWeight]
    · simp only [metaplecticPrimeWeight,ite_true,ite_eq_right hk,Fin.val_zero,
        zero_add,Nat.cast_zero]
      rw [hq,mul_assoc,←Real.rpow_add hp]
      congr 2
      ring
  · simp only [metaplecticPrimeWeight,show (1 : Fin 2) ≠ 0 by decide,ite_false,Fin.val_one,
      Nat.add_eq_zero_iff,Nat.one_ne_zero,false_and,Nat.cast_one]
    rw [hq]
    calc
      _ = p^(-σ+(k:ℝ)*(-5/2-3*σ)) := (Real.rpow_add hp _ _).symm
      _ = p^(1+(k:ℝ)/2+-((1:ℝ)+3*k)*(1+σ)) := by congr 1; ring
      _ = (p^(1:ℝ)*p^((k:ℝ)/2))*p^(-((1:ℝ)+3*k)*(1+σ)) := by
        rw [←Real.rpow_add hp,←Real.rpow_add hp]
      _ = _ := by rw [Real.rpow_one]

lemma metaplecticPrimeWeight_box {p σ : ℝ} (hp : 2 ≤ p) (hσ : 0 < σ) (M : ℕ) :
    (∑ z : Fin 2 × Fin M, metaplecticPrimeWeight p σ z.1 z.2.val) ≤
      metaplecticLocalEuler p σ := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [metaplecticPrimeWeight_sum]
  rw [Fin.sum_univ_eq_sum_range]
  exact sum_le_hasSum _ (fun k _ => by
    rw [←metaplecticPrimeWeight_sum]
    exact Finset.sum_nonneg (fun e _ => metaplecticPrimeWeight_nonneg (by linarith) e k))
    (metaplecticLocalTerms_hasSum hp hσ)

lemma metaplectic_local_code_bound {α β : Type*} [Fintype α] [Fintype β]
    (M : ℕ) (f : α → β → Fin 2 × Fin M) (hf : Function.Injective f)
    (p : β → ℝ) (hp : ∀ b, 2 ≤ p b) {σ : ℝ} (hσ : 0 < σ) :
    (∑ a : α, ∏ b : β, metaplecticPrimeWeight (p b) σ (f a b).1 (f a b).2.val) ≤
      ∏ b : β, metaplecticLocalEuler (p b) σ := by
  calc
    _ ≤ ∑ g : β → Fin 2 × Fin M, ∏ b : β,
        metaplecticPrimeWeight (p b) σ (g b).1 (g b).2.val := by
      apply Finset.sum_le_sum_of_injOn f (fun _ _ _ _ h => hf h) (Finset.subset_univ _)
      · intro a ha
        exact le_rfl
      · intro g hg hgn
        exact Finset.prod_nonneg (fun b _ =>
          metaplecticPrimeWeight_nonneg (by linarith [hp b]) _ _)
    _ = ∏ b : β, ∑ z : Fin 2 × Fin M, metaplecticPrimeWeight (p b) σ z.1 z.2.val :=
      (Fintype.prod_sum (fun (b : β) (z : Fin 2 × Fin M) =>
        metaplecticPrimeWeight (p b) σ z.1 z.2.val)).symm
    _ ≤ _ := Finset.prod_le_prod₀
      (fun b _ => Finset.sum_nonneg (fun z _ =>
        metaplecticPrimeWeight_nonneg (by linarith [hp b]) _ _))
      (fun b _ => metaplecticPrimeWeight_box (hp b) hσ M)

/-- The absolute supported-prime factor in terms of genuine ideal
exponents. The first ideal is squarefree; the second carries the cubes. -/
def metaplecticIdealLocalWeight (S : Finset EisensteinIdealPrime)
    (σ : ℝ) (μ ν : EisensteinIdealExponent) : ℝ :=
  ∏ p ∈ S,
    (if μ p+ν p = 0 then 1 else (normNat (idealPrimeRepresentative p):ℝ))*
      (normNat (idealPrimeRepresentative p):ℝ)^((ν p:ℝ)/2)*
      (normNat (idealPrimeRepresentative p):ℝ)^(-((μ p:ℝ)+3*ν p)*(1+σ))

/-- Arbitrary finite sets of supported pairs are bounded by the literal
Euler product; no norm cutoff or bound on prime-power exponents is used. -/
theorem metaplectic_ideal_local_sum {σ : ℝ} (hσ : 0 < σ)
    (S : Finset EisensteinIdealPrime)
    (T : Finset (EisensteinIdealExponent × EisensteinIdealExponent))
    (hT : ∀ a ∈ T, a.1.support ⊆ S ∧ a.2.support ⊆ S ∧ ∀ p, a.1 p ≤ 1) :
    (∑ a ∈ T, metaplecticIdealLocalWeight S σ a.1 a.2) ≤
      ∏ p ∈ S, metaplecticLocalEuler (normNat (idealPrimeRepresentative p)) σ := by
  let M := T.sup (fun a => S.sup a.2)+1
  let f : T → S → Fin 2 × Fin M := fun a p =>
    (⟨a.val.1 p,by have := (hT a a.property).2.2 p; omega⟩,
      ⟨a.val.2 p,by
        have h1 := Finset.le_sup (f := a.val.2) p.property
        have h2 := Finset.le_sup (f := fun a => S.sup a.2) a.property
        dsimp [M]
        omega⟩)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Prod.ext
    · ext p
      by_cases hp : p ∈ S
      · exact congrArg (fun g : S → Fin 2 × Fin M => (g ⟨p,hp⟩).1.val) hab
      · rw [Finsupp.notMem_support_iff.mp (fun h => hp ((hT a a.property).1 h)),
          Finsupp.notMem_support_iff.mp (fun h => hp ((hT b b.property).1 h))]
    · ext p
      by_cases hp : p ∈ S
      · exact congrArg (fun g : S → Fin 2 × Fin M => (g ⟨p,hp⟩).2.val) hab
      · rw [Finsupp.notMem_support_iff.mp (fun h => hp ((hT a a.property).2.1 h)),
          Finsupp.notMem_support_iff.mp (fun h => hp ((hT b b.property).2.1 h))]
  have hprime (p : S) : (2:ℝ) ≤ normNat (idealPrimeRepresentative p) := by
    exact_mod_cast idealPrimeRepresentative_normNat_ge_two p
  have hbound := metaplectic_local_code_bound M f hf
    (fun p : S => (normNat (idealPrimeRepresentative p):ℝ)) hprime hσ
  have he (a : T) : metaplecticIdealLocalWeight S σ a.val.1 a.val.2 =
      ∏ p : S, metaplecticPrimeWeight (normNat (idealPrimeRepresentative p)) σ
        (f a p).1 (f a p).2.val := by
    rw [metaplecticIdealLocalWeight,←Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro p hp
    exact (metaplecticPrimeWeight_eq (by have := hprime p; linarith) σ (f a p).1 (f a p).2.val).symm
  rw [←Finset.sum_coe_sort]
  simp_rw [he]
  exact hbound.trans_eq (Finset.prod_coe_sort S
    (fun p => metaplecticLocalEuler (normNat (idealPrimeRepresentative p)) σ))

/-- The local product has subpower growth in any ambient ideal. -/
theorem metaplectic_ideal_euler_small_power {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : EisensteinIdealExponent,
      (∏ p ∈ ρ.support, metaplecticLocalEuler (normNat (idealPrimeRepresentative p)) σ) ≤
        C*idealExponentNorm ρ^ε := by
  obtain ⟨C,hC,hdiv⟩ := ideal_divisor_product_small_power (show 0 < ε/2 by positivity)
  refine ⟨C^2,by positivity,?_⟩
  intro ρ
  have hprod : (∏ p ∈ ρ.support,
      metaplecticLocalEuler (normNat (idealPrimeRepresentative p)) σ) ≤
        (∏ p ∈ ρ.support, ((ρ p:ℝ)+1))^2 := by
    rw [←Finset.prod_pow]
    apply Finset.prod_le_prod₀
    · intro p hp
      apply metaplecticLocalEuler_nonneg _ hσ
      exact_mod_cast idealPrimeRepresentative_normNat_ge_two p
    · intro p hp
      have hn : (1:ℝ) ≤ ρ p := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
      have hb := metaplecticLocalEuler_le_three
        (p := (normNat (idealPrimeRepresentative p):ℝ))
        (by exact_mod_cast idealPrimeRepresentative_normNat_ge_two p) hσ
      nlinarith
  calc
    _ ≤ (∏ p ∈ ρ.support, ((ρ p:ℝ)+1))^2 := hprod
    _ ≤ (C*idealExponentNorm ρ^(ε/2))^2 :=
      pow_le_pow_left₀ (Finset.prod_nonneg (fun p _ => by positivity)) (hdiv ρ) _
    _ = C^2*idealExponentNorm ρ^ε := by
      have he : (idealExponentNorm ρ^(ε/2))^2 = idealExponentNorm ρ^ε := by
        rw [←Real.rpow_mul_natCast (idealExponentNorm_pos ρ).le]
        congr 1
        ring
      rw [mul_pow,he]

/-- The precise supported-prime sum needed for absolute convergence of
Voronoi is uniformly bounded by an arbitrary ambient norm power. -/
theorem metaplectic_ideal_local_small_power {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : EisensteinIdealExponent)
      (T : Finset (EisensteinIdealExponent × EisensteinIdealExponent)),
      (∀ a ∈ T, a.1.support ⊆ ρ.support ∧ a.2.support ⊆ ρ.support ∧ ∀ p, a.1 p ≤ 1) →
      (∑ a ∈ T, metaplecticIdealLocalWeight ρ.support σ a.1 a.2) ≤
        C*idealExponentNorm ρ^ε := by
  obtain ⟨C,hC,hEuler⟩ := metaplectic_ideal_euler_small_power hε hσ
  exact ⟨C,hC,fun ρ T hT => (metaplectic_ideal_local_sum hσ ρ.support T hT).trans (hEuler ρ)⟩

end CubicFirstMoment

end

end OAI
