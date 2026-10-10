import OAI.NumberTheory.CubicMoment.Estimates.StructuredFrequencyPolynomial
import OAI.NumberTheory.CubicMoment.Estimates.EnlargedNoncubeMass

namespace OAI

/-! Nonexceptional frequency savings for the actual logarithmically varying
prime convolutions. Coefficient energy is proved, not supplied as an input. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma noncube_energy_absorption {C r j B D ν E A : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hj : 0 ≤ j) (hB : 0 < B) (hD : 0 ≤ D)
    (hE : E ≤ B^(1+ν/2)) (hA : A ≤ C*r*j*B*D*B^(-ν)*E) :
    A ≤ C*r*j*B^2*D*B^(-ν/2) := by
  have hm : 0 ≤ C*r*j*B*D*B^(-ν) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hr) hj) hB.le) hD)
      (Real.rpow_nonneg hB.le _)
  have hid : B^(-ν)*B^(1+ν/2) = B*B^(-ν/2) := by
    calc
      _ = B^(1-ν/2) := by rw [← Real.rpow_add hB]; congr 1; ring
      _ = B^(1:ℝ)*B^(-ν/2) := by rw [← Real.rpow_add hB]; congr 1; ring
      _ = _ := by rw [Real.rpow_one]
  calc
    A ≤ C*r*j*B*D*B^(-ν)*B^(1+ν/2) :=
      hA.trans (mul_le_mul_of_nonneg_left hE hm)
    _ = (C*r*j*B*D)*(B^(-ν)*B^(1+ν/2)) := by ring
    _ = _ := by rw [hid]; ring

theorem logarithmic_structured_noncube (hHuxley : HuxleyAdditiveLargeSieve)
    {κ δ R : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) (hR : 1 ≤ R) :
    ∃ η C ν : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < C ∧ 0 < ν ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ T₀ : ℝ, ∀ (r : γ) (X : ι → ℝ) (Z B p q : ℝ) (v e : Eisenstein) (u : ℝ)
      (Ram S T J H : Finset Eisenstein), T₀ ≤ L r →
      (∀ i, 0 < X i) → (∏ i, X i) = L r → R^(Fintype.card ι)*L r ≤ B →
      0 ≤ p → 0 ≤ q → p+2*q ≤ 1+η → κ ≤ p+2*q →
      δ ≤ |p-1|+|q| → δ ≤ |p-1/3|+|q-1/3| →
      (∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ B^p) →
      (∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ B^q) →
      H ⊆ coprimeResidualSupport Ram J (coprimePairs S T) →
      (∑ h ∈ H, ‖structuredPrimeSum h 1 v e u (W r) X Z‖^2) ≤
        C*(Ram.card:ℝ)*J.card*B^2*(B^p*(B^q)^2)^(1/3:ℝ)*B^(-ν) := by
  obtain ⟨η,C,ν,hη,hηhi,hC,hν,hraw⟩ := quantitative_enlarged_noncube_mass hHuxley hκ hδ
  refine ⟨η,C,ν/2,hη,hηhi,hC,by positivity,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨T₀,henergy⟩ := logarithmic_structured_coefficient_energy hW
    (show 0 ≤ R by linarith) (show 0 < ν/2 by positivity) hlo hhi
  refine ⟨T₀,?_⟩
  intro r X Z B p q v e u Ram S T J H hT₀ hX hprod hcover hp hq hsize hlarge hfirst hbalanced hS hT hH
  have hLpos : 0 < L r := zero_lt_one.trans_le (hL r)
  have hLB : L r ≤ B := le_trans (by
    calc
      L r = 1*L r := (one_mul _).symm
      _ ≤ R^(Fintype.card ι)*L r := mul_le_mul_of_nonneg_right (one_le_pow₀ hR) hLpos.le) hcover
  have hB : 1 ≤ B := (hL r).trans hLB
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  let A := structuredFrequencySupport (W r) X Z
  let β := structuredFrequencyCoefficient v e u (W r) X Z
  have hA : ∀ a ∈ A, primary a ∧ Squarefree a ∧ norm a ≤ B := by
    intro a ha
    have ha' := structuredFrequencySupport_bounds (W r) X hX
      (show 0 ≤ R by linarith) (hlo r) (hhi r) Z a ha
    have hn : norm a ≤ R^(Fintype.card ι)*L r := by
      simpa only [hprod] using ha'.2.2
    exact ⟨ha'.1,ha'.2.1,hn.trans hcover⟩
  have hE : (∑ a ∈ A, ‖β a‖^2) ≤ B^(1+ν/2) := by
    apply (structuredFrequencyCoefficient_energy_le v e u (W r) X Z).trans
    apply (henergy r X Z (hL r) hT₀ hX hprod).trans
    exact Real.rpow_le_rpow hLpos.le hLB (by positivity)
  have hm := hraw B p q hB hp hq hsize hlarge hfirst hbalanced
    A Ram S T J H hA hS hT hH β
  have heq : (∑ h ∈ H, ‖structuredPrimeSum h 1 v e u (W r) X Z‖^2) =
      ∑ h ∈ H, ‖∑ a ∈ A, β a*cubicSymbol a h‖^2 := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [structuredPrimeSum_eq_frequency]
  rw [heq]
  simpa only [neg_div] using noncube_energy_absorption hC.le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hBpos (Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hBpos.le _) (sq_nonneg _)) _)
    hE hm

end CubicFirstMoment

end

end OAI
