import OAI.NumberTheory.DirichletL.Descent.SecondEnergy

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open SevenEighths.InverseSecondFibers IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def tripleDivisorWeight (K : ℕ) (γ : OuterTriple) : ℝ :=
  ((idealDivisors γ.q0).card : ℝ)^(5+2*K) *
    ((idealDivisors γ.quotient).card : ℝ)^(2*K) *
    ((idealDivisors γ.residual).card : ℝ)^(2*K)

lemma tripleDivisorWeight_nonneg (K : ℕ) (γ : OuterTriple) :
    0 ≤ tripleDivisorWeight K γ := by unfold tripleDivisorWeight; positivity

theorem ideal_divisor_power_small (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal Eis, I ≠ 0 →
      ((idealDivisors I).card : ℝ)^j ≤ C*(Ideal.absNorm I : ℝ)^ε := by
  have hj : 0 < (j+1 : ℝ) := by positivity
  obtain ⟨C,hC,hb⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/(j+1)) (div_pos hε hj)
  refine ⟨C^(j+1), by positivity, ?_⟩
  intro I hI
  have hcard : (1 : ℝ) ≤ (idealDivisors I).card := by
    exact_mod_cast InverseInitialFibers.divisor_card_pos I hI
  calc
    _ ≤ ((idealDivisors I).card : ℝ)^(j+1) := pow_le_pow_right₀ hcard (by omega)
    _ ≤ (C*(Ideal.absNorm I : ℝ)^(ε/(j+1)))^(j+1) :=
      pow_le_pow_left₀ (by positivity) (hb I hI) _
    _ = C^(j+1)*(Ideal.absNorm I : ℝ)^ε := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast
      field_simp

theorem tripleDivisorWeight_small (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : OuterTriple,
      γ.q0 ≠ 0 → γ.quotient ≠ 0 → γ.residual ≠ 0 →
      tripleDivisorWeight K γ ≤
        C*((Ideal.absNorm γ.q0 : ℝ)*Ideal.absNorm γ.quotient*Ideal.absNorm γ.residual)^ε := by
  obtain ⟨Cq,hCq,hq⟩ := ideal_divisor_power_small (5+2*K) ε hε
  obtain ⟨Ct,hCt,ht⟩ := ideal_divisor_power_small (2*K) ε hε
  refine ⟨Cq*Ct*Ct, by positivity, ?_⟩
  intro γ hq0 ht0 hr0
  unfold tripleDivisorWeight
  calc
    _ ≤ (Cq*(Ideal.absNorm γ.q0 : ℝ)^ε) *
        (Ct*(Ideal.absNorm γ.quotient : ℝ)^ε) *
        (Ct*(Ideal.absNorm γ.residual : ℝ)^ε) := by
      gcongr
      · exact hq γ.q0 hq0
      · exact ht γ.quotient ht0
      · exact ht γ.residual hr0
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ (Ideal.absNorm γ.q0 : ℝ)*Ideal.absNorm γ.quotient)
        (by positivity), Real.mul_rpow (by positivity) (by positivity)]
      ring

theorem outerTriple_card (Γ : Finset OuterTriple) (B T R : ℝ)
    (hB : 1 ≤ B) (hT : 1 ≤ T) (hR : 1 ≤ R)
    (hzero : ∀ γ ∈ Γ, γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hnorm : ∀ γ ∈ Γ, (Ideal.absNorm γ.q0 : ℝ) ≤ B ∧
      (Ideal.absNorm γ.quotient : ℝ) ≤ T ∧ (Ideal.absNorm γ.residual : ℝ) ≤ R) :
    (Γ.card : ℝ) ≤ 128^3*B*T*R := by
  let f : OuterTriple → Ideal Eis × Ideal Eis × Ideal Eis := fun γ => (γ.q0,γ.quotient,γ.residual)
  have hf : Function.Injective f := by
    intro γ δ h
    exact OuterTriple.ext (congrArg Prod.fst h)
      (congrArg (fun z => z.2.1) h) (congrArg (fun z => z.2.2) h)
  have hc := DescentFiberCost.fixed_triple_count (Γ.image f) B T R hB hT hR
    (fun x hx => by obtain ⟨γ,hγ,rfl⟩ := Finset.mem_image.mp hx; exact hzero γ hγ)
    (fun x hx => by obtain ⟨γ,hγ,rfl⟩ := Finset.mem_image.mp hx; exact hnorm γ hγ)
  simpa only [Finset.card_image_of_injective _ hf] using hc

theorem triple_normalized_mass (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Γ : Finset OuterTriple) (B T R : ℝ),
      1 ≤ B → 1 ≤ T → 1 ≤ R →
      (∀ γ ∈ Γ, γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0) →
      (∀ γ ∈ Γ, (Ideal.absNorm γ.q0 : ℝ) ≤ B ∧
        (Ideal.absNorm γ.quotient : ℝ) ≤ T ∧ (Ideal.absNorm γ.residual : ℝ) ≤ R) →
      (B*T*R)⁻¹ * (∑ γ ∈ Γ, tripleDivisorWeight K γ) ≤ C*(B*T*R)^ε := by
  obtain ⟨C,hC,hb⟩ := tripleDivisorWeight_small K ε hε
  refine ⟨128^3*C, by positivity, ?_⟩
  intro Γ B T R hB hT hR hz hn
  have hpos : 0 < B*T*R := by positivity
  have hw : ∀ γ ∈ Γ, tripleDivisorWeight K γ ≤ C*(B*T*R)^ε := by
    intro γ hγ
    obtain ⟨hq,ht,hr⟩ := hz γ hγ
    apply (hb γ hq ht hr).trans
    gcongr
    · exact (hn γ hγ).1
    · exact (hn γ hγ).2.1
    · exact (hn γ hγ).2.2
  have hs : (∑ γ ∈ Γ, tripleDivisorWeight K γ) ≤
      (128^3*B*T*R)*(C*(B*T*R)^ε) := by
    calc
      _ ≤ ∑ _γ ∈ Γ, C*(B*T*R)^ε := Finset.sum_le_sum hw
      _ = (Γ.card : ℝ)*(C*(B*T*R)^ε) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (outerTriple_card Γ B T R hB hT hR hz hn) (by positivity)
  apply (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hpos.le)).trans_eq
  field_simp

end
end SevenEighths.InverseMoment

end OAI
