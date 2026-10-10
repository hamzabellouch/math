import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPrefixAmplitude
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPrefixMass

namespace OAI

/-! Summing both actual retained-block amplitudes over all supported
prefixes, with no coefficient or support-count estimate left as an assumption. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma two_positive_parts {A B s : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 ≤ s) :
    A+B*s ≤ (A+B)*(1+s) := by
  nlinarith [mul_nonneg hA hs]

theorem metaplectic_prefix_amplitude_sum {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : Eisenstein, primary r →
      ∀ (P : Finset (MetaplecticDyadPrefix r)) (J : ℝ), 0 < J →
      (∀ p ∈ P, ∃ k : ℕ, p.2.2.2.2.val ∣ r^k) →
      (∀ p ∈ P, norm p.1 ≤ J ∧ norm p.2.2.2.2 ≤ J) →
      ∀ C : ℝ, 0 ≤ C → ∀ I T : ℝ,
      (∑ p ∈ P, metaplecticPrefixAmplitude r C p/Real.sqrt (norm r)*
        (1+Real.sqrt (2*(I/metaplecticFreeScale p)/T))) ≤
          D*C*J^ε*norm r^(2*ε)*(1+Real.sqrt (2*I/(norm r*T))) := by
  obtain ⟨A,hA,ha⟩ := metaplectic_first_prefix_mass (ρ := (3:ℝ)^(-1/6:ℝ)) hε
    (Real.rpow_nonneg (by norm_num) (-1/6:ℝ))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num : (-1/6:ℝ) < 0))
  obtain ⟨B,hB,hb⟩ := metaplectic_second_prefix_mass (ρ := (3:ℝ)^(-2/3:ℝ)) hε
    (Real.rpow_nonneg (by norm_num) (-2/3:ℝ))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num : (-2/3:ℝ) < 0))
  refine ⟨Real.sqrt 3*A+3*B,by positivity,?_⟩
  intro r hr P J hJ hsupport hsize C hC I T
  have hR := norm_nonneg r
  let w1 := fun p : MetaplecticDyadPrefix r =>
    norm p.1^(-1:ℝ)*((3:ℝ)^(-1/6:ℝ))^p.2.1*norm p.2.2.2.2^(-(1/2):ℝ)
  let w2 := fun p : MetaplecticDyadPrefix r =>
    norm p.1^(-(5/2):ℝ)*((3:ℝ)^(-2/3:ℝ))^p.2.1*norm p.2.2.2.2^(-(3/2):ℝ)
  let s := Real.sqrt (2*I/(norm r*T))
  have h1 := ha r hr P J hJ hsupport hsize
  have h2 := hb r hr P J hJ hsupport hsize
  have hp (p : MetaplecticDyadPrefix r) :
      metaplecticPrefixAmplitude r C p/Real.sqrt (norm r)*
        (1+Real.sqrt (2*(I/metaplecticFreeScale p)/T)) ≤
          C*Real.sqrt 3*w1 p+C*3*s*w2 p := by
    have hf := metaplectic_prefix_first_amplitude hr hC p
    have hs := metaplectic_prefix_second_amplitude hr hC p I T
    calc
      _ = metaplecticPrefixAmplitude r C p/Real.sqrt (norm r)+
          metaplecticPrefixAmplitude r C p/Real.sqrt (norm r)*
            Real.sqrt (2*(I/metaplecticFreeScale p)/T) := by ring
      _ ≤ _ := add_le_add hf hs
      _ = _ := by dsimp [w1,w2,s]; ring
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hn : 0 ≤ C*J^ε*norm r^(2*ε) := by positivity
  calc
    _ ≤ ∑ p ∈ P, (C*Real.sqrt 3*w1 p+C*3*s*w2 p) := Finset.sum_le_sum (fun p _ => hp p)
    _ = C*Real.sqrt 3*(∑ p ∈ P, w1 p)+C*3*s*(∑ p ∈ P, w2 p) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
    _ ≤ C*Real.sqrt 3*(A*J^ε*norm r^(2*ε))+C*3*s*(B*J^ε*norm r^(2*ε)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
        (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = (C*J^ε*norm r^(2*ε))*(Real.sqrt 3*A+(3*B)*s) := by ring
    _ ≤ (C*J^ε*norm r^(2*ε))*((Real.sqrt 3*A+3*B)*(1+s)) :=
      mul_le_mul_of_nonneg_left (two_positive_parts (by positivity) (by positivity) hs0) hn
    _ = _ := by dsimp [s]; ring

end CubicFirstMoment

end

end OAI
