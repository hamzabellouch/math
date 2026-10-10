import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleOrdinaryScales
import OAI.NumberTheory.CubicMoment.Estimates.PrimeBoxRange

namespace OAI

/-! Ordinary surviving boxes satisfy the actual bilinear range after
absorbing only fixed support ratios into half the grouping gap. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

theorem largePrimeTuplePiece_ordinary_range (i j : ℕ) {ξ δ : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {η : ℝ}, 0 < η → ∀ G : ℕ,
      ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (Ct : ℕ) (H : ℝ) {N : ℕ}
        (k : (Fin i ⊕ Fin j) → Fin N),
      ∀ q ∈ largePrimeTupleBox i j X,
        largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0 →
        ¬largePrimeTupleExceptional δ q →
        ∃ s : Finset (Fin i ⊕ Fin j),
          let B := largeTupleSubsetScale (fun a => (k a).val) s
          let A := largeTupleSubsetScale (fun a => (k a).val) (Finset.univ\s)
          X^(1/3+ε:ℝ) ≤ B ∧ B^2 ≤ 3*X ∧
            X/(2*2^(i+j)) ≤ A*B ∧ A*B ≤ 3*X ∧
            B^(1-η/16) ≤ A ∧ A ≤ B^2/(1+Real.log B)^G := by
  obtain ⟨ε,hε,hgroup⟩ := largePrimeTuplePiece_ordinary_group i j hξ hξz hδ
  refine ⟨ε/2,by positivity,?_⟩
  intro η hη G
  have hC : 0 < (1/2:ℝ)^(1/3+ε)/(2:ℝ)^(i+j) := by positivity
  filter_upwards [eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 200,
    eventually_rpow_le_const_mul (by linarith : (1/3+ε/2:ℝ) < 1/3+ε) hC,
    eventually_prime_box_range (by positivity : (0:ℝ) < ε/2) hη (i+j) G]
    with X hX hlog hgap hrange
  intro ℓ Ct H N k q hq hne hex
  have hXp : 0 < X := zero_lt_one.trans_le hX
  obtain ⟨s,hBlow,hBhi⟩ := hgroup ℓ Ct H X hX hlog k q hq hne hex
  let B := largeTupleSubsetScale (fun a => (k a).val) s
  let A := largeTupleSubsetScale (fun a => (k a).val) (Finset.univ\s)
  have hBp : 0 < B := largeTupleSubsetScale_pos _ _
  have hn := largePrimeTupleTerm_product_range hXp (mul_ne_zero_iff.mp hne).1
  change X/2 ≤ norm (largePrimeTupleProduct q) ∧ norm (largePrimeTupleProduct q) ≤ 3*X at hn
  have hlower : X^(1/3+ε/2:ℝ) ≤ B := by
    apply hgap.trans
    calc
      _ = (X/2)^(1/3+ε:ℝ)/(2:ℝ)^(i+j) := by
        rw [show X/2 = (1/2:ℝ)*X by ring,Real.mul_rpow (by norm_num) hXp.le]
        ring
      _ ≤ norm (largePrimeTupleProduct q)^(1/3+ε:ℝ)/(2:ℝ)^(i+j) :=
        div_le_div_of_nonneg_right
          (Real.rpow_le_rpow (by positivity) hn.1 (by linarith)) (by positivity)
      _ ≤ B := hBlow
  have hsq : B^2 ≤ 3*X := by
    have hh := pow_le_pow_left₀ hBp.le hBhi 2
    have he : (norm (largePrimeTupleProduct q)^(1/2:ℝ))^2 = norm (largePrimeTupleProduct q) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (norm_nonneg _)]
      norm_num
    exact (hh.trans_eq he).trans hn.2
  have hprod : A*B = largeTupleSubsetScale (fun a => (k a).val) Finset.univ := by
    dsimp only [A,B]
    rw [mul_comm,largeTupleSubsetScale_complement]
  have hprodRange := largePrimeTuplePiece_scale_product hXp k hne
  rw [←hprod] at hprodRange
  exact ⟨s,hlower,hsq,hprodRange.1,hprodRange.2,
    hrange A B hprodRange.1 hprodRange.2 hsq hlower⟩

end CubicFirstMoment

end

end OAI
