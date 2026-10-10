import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeTailGeometry
import OAI.NumberTheory.CubicMoment.Angular.AngularTailPrimeRegroup
import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeGeometry

namespace OAI

/-! One surviving height window fixes independent prime groups for the
entire signed tail. Their choice therefore does not depend on frequency. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)

def angular_tailPrimeTupleTail (i j : ℕ) (ξ H T X : ℝ)
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ v ∈ Finset.range (heightWindowCount H T),
    tailPrimeTuplePiece i j ℓ ξ H (T*(3/2:ℝ)^v) X k

lemma angular_tailPrimeTupleTail_witness {i j : ℕ} {ξ H T X : ℝ}
    (k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (hne : angular_tailPrimeTupleTail ℓ i j ξ H T X k ≠ 0) :
    ∃ v ∈ Finset.range (heightWindowCount H T), ∃ q ∈ largePrimeTupleBox i j X,
      tailPrimeTupleTerm i j ℓ ξ H (T*(3/2:ℝ)^v) X q*
        normTupleWeight k (largePrimeTupleNorm q) ≠ 0 := by
  have hv : ∃ v ∈ Finset.range (heightWindowCount H T),
      tailPrimeTuplePiece i j ℓ ξ H (T*(3/2:ℝ)^v) X k ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Finset.sum_eq_zero h)
  obtain ⟨v,hv,hvn⟩ := hv
  obtain ⟨q,hq,hqn⟩ := tailPrimeTuplePiece_witness k hvn
  exact ⟨v,hv,q,hq,hqn⟩

theorem angular_eventually_tailPrimeTupleTail_groups (i j : ℕ) {κ ξ : ℝ}
    (hκ : 0 < κ) (hκsmall : κ < 1/12) (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∀ᶠ X : ℝ in atTop, ∀ H T : ℝ,
      ∀ k : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (k a).val) →
      angular_tailPrimeTupleTail ℓ i j ξ H T X k ≠ 0 →
      ∃ s : Finset (Fin i ⊕ Fin j),
        let B := largeTupleSubsetScale (fun a => (k a).val) s
        let A := largeTupleSubsetScale (fun a => (k a).val) (Finset.univ\s)
        X^(1/3-3*κ) ≤ B ∧ B^2 ≤ 3*X ∧ X/(2*2^(i+j)) ≤ A*B ∧ A*B ≤ 3*X ∧
        (∀ a, 1 ≤ largeTupleNormScale (fun a => (k a).val) a) ∧
        (∀ a, (2*B)^(ξ/2) < largeTupleNormScale (fun a => (k a).val) a) ∧
        ∀ H' T' : ℝ, angular_tailPrimeTupleTail ℓ i j ξ H' T' X k =
          ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
            envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ X (fun a => (k a).val) s)
              (largeTupleOtherSupport ξ X (fun a => (k a).val) s)
              (fun b => theta ℓ b*largeTupleSelectedCoefficient ξ X (fun a => (k a).val) s b)
              (fun b => theta ℓ b*largeTupleOtherCoefficient ξ X (fun a => (k a).val) s b)
              primeProductEnvelope H' T' X := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_tailPrimeTuple_upper_grouping i j hκ hκsmall hξ hξz,
    eventually_tailPrimeTuple_coordinate_envelope (i := i) (j := j) hκ.le hκsmall hξz,
    tailPrimeTuplePiece_rough_scales i j hξ hξz] with X hX hgroup hcoord hrough
  intro H T k hhigh hne
  obtain ⟨v,_hv,q,hq,hqn⟩ := angular_tailPrimeTupleTail_witness ℓ k hne
  obtain ⟨s,hB,hBsq⟩ := hgroup ℓ H (T*(3/2:ℝ)^v) k hhigh q hq hqn
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hprod := tailPrimeTuple_scale_product hXp k hqn
  have hp : largeTupleSubsetScale (fun a => (k a).val) (Finset.univ\s)*
      largeTupleSubsetScale (fun a => (k a).val) s =
      largeTupleSubsetScale (fun a => (k a).val) Finset.univ := by
    rw [mul_comm,largeTupleSubsetScale_complement]
  have hr := hrough ℓ H (T*(3/2:ℝ)^v) k q hq hqn
  have hB3 : largeTupleSubsetScale (fun a => (k a).val) s ≤ 3*X := by
    have hBp := largeTupleSubsetScale_pos (fun a => (k a).val) s
    nlinarith
  refine ⟨s,hB,hBsq,by simpa only [hp] using hprod.1,
    by simpa only [hp] using hprod.2,hr.1,
    hr.2 _ (largeTupleSubsetScale_pos _ _).le hB3,?_⟩
  intro H' T'
  unfold angular_tailPrimeTupleTail
  simp_rw [tailPrimeTuplePiece_full i j ℓ ξ H' _ X k
    (hcoord ℓ H (T*(3/2:ℝ)^v) k hhigh q hq hqn),
    tailPrimeTupleIndependent_regroup i j ℓ ξ H' _ X _ s]
  rw [←Finset.mul_sum,angular_tailPrimeTupleRegrouped_tail ℓ]

end CubicFirstMoment

end

end OAI
