import OAI.NumberTheory.JointDickman.Arithmetic.PrimeDistanceComparison

namespace OAI

/-! # Nonprincipal distance survives fixed prime changes and large-prime labels -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem minimumDistance_tendsto_of_prime_agreement
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (P : Finset ℕ)
    (f : ℕ → ArithmeticFunction ℂ) (hf : ∀ n k, ‖f n k‖ ≤ 1)
    (X : ℕ → ℝ) (hX : Tendsto X atTop atTop)
    (heq : ∀ᶠ n in atTop, ∀ p : ℕ, p.Prime → p ∉ P →
      (p : ℝ) ≤ (X n)^c → f n p = χ (p : ZMod q)) :
    Tendsto (fun n => minimumDistance (f n) (X n)) atTop atTop := by
  have htail := (largePrimeSet_reciprocal_tendsto hM hc hc1).comp hX
  let K := -Real.log c+1+(∑ p ∈ P, 1/(p : ℝ))
  apply tendsto_atTop.mpr
  intro R
  have hbase := hX.eventually (hKMT q χ hχ (R+2*K))
  filter_upwards [heq,hX.eventually_ge_atTop 10,
    htail.eventually (eventually_le_nhds (by linarith : -Real.log c < -Real.log c+1)),
    hbase] with n heq h10 htail hlarge
  unfold minimumDistance
  apply le_csInf
  · exact ⟨primeDistanceSquared (f n) (X n) 0,
      ⟨0,Set.mem_Icc.mpr ⟨by linarith,by linarith⟩,rfl⟩⟩
  · rintro y ⟨t,ht,rfl⟩
    have ht' : |t| ≤ X n := abs_le.mpr ⟨by linarith [ht.1],ht.2⟩
    have hb := hlarge t ht'
    have hd := primeDistanceSquared_lower_of_agree (f n) (characterArithmetic χ)
      (hf n) (characterArithmetic_norm_le_one χ) P (X n) ((X n)^c) t
      (fun p hp hpP hpX => (heq p hp hpP hpX).trans (characterArithmetic_prime χ hp).symm)
    dsimp only [Function.comp_def,K] at hb htail
    linarith

end JointDickman

end OAI
