import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeGeometry

namespace OAI

/-! One surviving height window fixes independent prime groups for the
entire signed tail. Their choice therefore does not depend on frequency. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

def tailPrimeTupleTail (i j : ℕ) (ξ H T X : ℝ)
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ v ∈ Finset.range (heightWindowCount H T),
    tailPrimeTuplePiece i j 0 ξ H (T*(3/2:ℝ)^v) X k

lemma tailPrimeTupleTail_witness {i j : ℕ} {ξ H T X : ℝ}
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (hne : tailPrimeTupleTail i j ξ H T X k ≠ 0) :
    ∃ v ∈ Finset.range (heightWindowCount H T), ∃ q ∈ largePrimeTupleBox i j X,
      tailPrimeTupleTerm i j 0 ξ H (T*(3/2:ℝ)^v) X q*
        normTupleWeight k (largePrimeTupleNorm q) ≠ 0 := by
  have hv : ∃ v ∈ Finset.range (heightWindowCount H T),
      tailPrimeTuplePiece i j 0 ξ H (T*(3/2:ℝ)^v) X k ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Finset.sum_eq_zero h)
  obtain ⟨v,hv,hvn⟩ := hv
  obtain ⟨q,hq,hqn⟩ := tailPrimeTuplePiece_witness k hvn
  exact ⟨v,hv,q,hq,hqn⟩

lemma tailPrimeTuple_scale_product {i j N : ℕ} {ℓ : ℤ} {ξ H U X : ℝ}
    (hX : 0 < X) (k : (Fin i ⊕ Fin j) → Fin N)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hne : tailPrimeTupleTerm i j ℓ ξ H U X q*normTupleWeight k (largePrimeTupleNorm q) ≠ 0) :
    X/(2*2^(i+j)) ≤ largeTupleSubsetScale (fun a => (k a).val) Finset.univ ∧
      largeTupleSubsetScale (fun a => (k a).val) Finset.univ ≤ 3*X := by
  obtain ⟨ht,hw⟩ := mul_ne_zero_iff.mp hne
  obtain ⟨hlo,hhi⟩ := tailPrimeTupleTerm_product_range hX ht
  obtain ⟨hl,hu⟩ := largePrimeTuplePiece_subset_range k hw Finset.univ
  rw [largePrimeTupleNorm_prod] at hl hu
  simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin] at hu
  refine ⟨?_,hl.trans hhi⟩
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*2^(i+j))).mpr
  nlinarith

theorem eventually_tailPrimeTupleTail_groups (i j : ℕ) {κ ξ : ℝ}
    (hκ : 0 < κ) (hκsmall : κ < 1/12) (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∀ᶠ X : ℝ in atTop, ∀ H T : ℝ,
      ∀ k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (k a).val) →
      tailPrimeTupleTail i j ξ H T X k ≠ 0 →
      ∃ s : Finset (Fin i ⊕ Fin j),
        let B := largeTupleSubsetScale (fun a => (k a).val) s
        let A := largeTupleSubsetScale (fun a => (k a).val) (Finset.univ\s)
        X^(1/3-3*κ) ≤ B ∧ B^2 ≤ 3*X ∧ X/(2*2^(i+j)) ≤ A*B ∧ A*B ≤ 3*X ∧
        (∀ a, 1 ≤ largeTupleNormScale (fun a => (k a).val) a) ∧
        (∀ a, (2*B)^(ξ/2) < largeTupleNormScale (fun a => (k a).val) a) ∧
        ∀ H' T' : ℝ, tailPrimeTupleTail i j ξ H' T' X k =
          ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
            envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ X (fun a => (k a).val) s)
              (largeTupleOtherSupport ξ X (fun a => (k a).val) s)
              (largeTupleSelectedCoefficient ξ X (fun a => (k a).val) s)
              (largeTupleOtherCoefficient ξ X (fun a => (k a).val) s)
              primeProductEnvelope H' T' X := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_tailPrimeTuple_upper_grouping i j hκ hκsmall hξ hξz,
    eventually_tailPrimeTuple_coordinate_envelope (i := i) (j := j) hκ.le hκsmall hξz,
    tailPrimeTuplePiece_rough_scales i j hξ hξz] with X hX hgroup hcoord hrough
  intro H T k hhigh hne
  obtain ⟨v,_hv,q,hq,hqn⟩ := tailPrimeTupleTail_witness k hne
  obtain ⟨s,hB,hBsq⟩ := hgroup 0 H (T*(3/2:ℝ)^v) k hhigh q hq hqn
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hprod := tailPrimeTuple_scale_product hXp k hqn
  have hp : largeTupleSubsetScale (fun a => (k a).val) (Finset.univ\s)*
      largeTupleSubsetScale (fun a => (k a).val) s =
      largeTupleSubsetScale (fun a => (k a).val) Finset.univ := by
    rw [mul_comm,largeTupleSubsetScale_complement]
  have hr := hrough 0 H (T*(3/2:ℝ)^v) k q hq hqn
  have hB3 : largeTupleSubsetScale (fun a => (k a).val) s ≤ 3*X := by
    have hBp := largeTupleSubsetScale_pos (fun a => (k a).val) s
    nlinarith
  refine ⟨s,hB,hBsq,by simpa only [hp] using hprod.1,
    by simpa only [hp] using hprod.2,hr.1,
    hr.2 _ (largeTupleSubsetScale_pos _ _).le hB3,?_⟩
  intro H' T'
  unfold tailPrimeTupleTail
  simp_rw [tailPrimeTuplePiece_full i j 0 ξ H' _ X k
    (hcoord 0 H (T*(3/2:ℝ)^v) k hhigh q hq hqn),
    tailPrimeTupleIndependent_regroup i j 0 ξ H' _ X _ s]
  rw [←Finset.mul_sum,tailPrimeTupleRegrouped_tail]

end CubicFirstMoment

end

end OAI
