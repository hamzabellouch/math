import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPrefixSum

namespace OAI

/-! The first retained-block majorant is summable with arbitrary small
powers of its finite norm cutoff and its squarefree level. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_divisor_card_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r →
      ((metaplecticPrimaryDivisors r).card:ℝ) ≤ C*norm r^ε := by
  obtain ⟨C,hC,hb⟩ := primary_divisor_card_small_power hε
  refine ⟨C,hC,?_⟩
  intro r hr
  exact hb (primaryElementBall (norm r))
    (fun d hd => (mem_primaryElementBall.mp hd).1) r (primary_ne_zero hr)

theorem metaplectic_first_prefix_mass {ε ρ : ℝ} (hε : 0 < ε)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r →
      ∀ (P : Finset (MetaplecticDyadPrefix r)) (J : ℝ), 0 < J →
      (∀ p ∈ P, ∃ k : ℕ, p.2.2.2.2.val ∣ r^k) →
      (∀ p ∈ P, norm p.1 ≤ J ∧ norm p.2.2.2.2 ≤ J) →
      (∑ p ∈ P, norm p.1^(-1:ℝ)*ρ^p.2.1*norm p.2.2.2.2^(-(1/2):ℝ)) ≤
        C*J^ε*norm r^(2*ε) := by
  obtain ⟨A,hA,harm⟩ := primary_argument_harmonic hε
  obtain ⟨B,hB,hdiv⟩ := metaplectic_divisor_card_power hε
  obtain ⟨E,hE,hsup⟩ := primary_argument_supported_sum hε (by norm_num : (0:ℝ) < 1/2)
  let U : ℝ := Nat.card (Eisensteinˣ)
  let K : ℝ := A*(1-ρ)⁻¹*U*B*E
  have hden : 0 < 1-ρ := sub_pos.mpr hρ1
  have hK : 0 ≤ K := by dsimp [K,U]; positivity
  refine ⟨K+1,by positivity,?_⟩
  intro r hr P J hJ hsupport hsize
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hd := harm (P.image Prod.fst) J hJ (by
    intro d hd
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd
    exact (hsize p hp).1)
  have hh := hsup r hr (P.image (fun p => p.2.2.2.2)) J (by
    intro d hd
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd
    exact hsupport p hp) (by
    intro d hd
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd
    exact (hsize p hp).2)
  have hk : (∑ k ∈ P.image (fun p => p.2.1), ρ^k) ≤ (1-ρ)⁻¹ := by
    have hg := hasSum_geometric_of_lt_one hρ0 hρ1
    rw [←hg.tsum_eq]
    exact hg.summable.sum_le_tsum _ (fun k _ => pow_nonneg hρ0 k)
  have hhdiv := hdiv r hr
  have hp := metaplectic_prefix_product_bound P
    (fun d => norm d^(-1:ℝ)) (fun k => ρ^k) (fun d => norm d^(-(1/2):ℝ))
    (fun d => Real.rpow_nonneg (norm_nonneg d) _)
    (fun k => pow_nonneg hρ0 k) (fun d => Real.rpow_nonneg (norm_nonneg d) _)
  calc
    _ ≤ (∑ d ∈ P.image Prod.fst, norm d^(-1:ℝ))*
        (∑ k ∈ P.image (fun p => p.2.1), ρ^k)*U*
        ((metaplecticPrimaryDivisors r).card:ℝ)*
        (∑ h ∈ (P.image (fun p => p.2.2.2.2) : Finset PrimaryArgument),
          norm h^(-(1/2):ℝ)) := hp
    _ ≤ (A*J^ε)*(1-ρ)⁻¹*U*(B*norm r^ε)*(E*norm r^ε) := by
      gcongr
      exact Finset.sum_nonneg (fun h _ => Real.rpow_nonneg (norm_nonneg h) _)
    _ = K*J^ε*norm r^(2*ε) := by
      rw [show 2*ε = ε+ε by ring,Real.rpow_add hR]
      dsimp [K]
      ring
    _ ≤ (K+1)*J^ε*norm r^(2*ε) := by
      gcongr
      linarith

/-- The second scalar weight is smaller than the first one termwise; the
same arbitrary small-power estimate therefore suffices for the application. -/
theorem metaplectic_second_prefix_mass {ε ρ : ℝ} (hε : 0 < ε)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r →
      ∀ (P : Finset (MetaplecticDyadPrefix r)) (J : ℝ), 0 < J →
      (∀ p ∈ P, ∃ k : ℕ, p.2.2.2.2.val ∣ r^k) →
      (∀ p ∈ P, norm p.1 ≤ J ∧ norm p.2.2.2.2 ≤ J) →
      (∑ p ∈ P, norm p.1^(-(5/2):ℝ)*ρ^p.2.1*norm p.2.2.2.2^(-(3/2):ℝ)) ≤
        C*J^ε*norm r^(2*ε) := by
  obtain ⟨C,hC,hb⟩ := metaplectic_first_prefix_mass hε hρ0 hρ1
  refine ⟨C,hC,?_⟩
  intro r hr P J hJ hsupport hsize
  apply (Finset.sum_le_sum ?_).trans (hb r hr P J hJ hsupport hsize)
  intro p hp
  have hd := Real.rpow_le_rpow_of_exponent_le (one_le_norm (primary_ne_zero p.1.property))
    (by norm_num : (-(5/2):ℝ) ≤ -1)
  have hh := Real.rpow_le_rpow_of_exponent_le (one_le_norm (primary_ne_zero p.2.2.2.2.property))
    (by norm_num : (-(3/2):ℝ) ≤ -(1/2))
  exact mul_le_mul (mul_le_mul_of_nonneg_right hd (pow_nonneg hρ0 p.2.1)) hh
    (Real.rpow_nonneg (norm_nonneg p.2.2.2.2) _)
    (mul_nonneg (Real.rpow_nonneg (norm_nonneg p.1) _) (pow_nonneg hρ0 p.2.1))

end CubicFirstMoment

end

end OAI
