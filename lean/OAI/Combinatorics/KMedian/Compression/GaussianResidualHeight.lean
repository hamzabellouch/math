import Mathlib
import OAI.Combinatorics.KMedian.Compression.GaussianResidualCertificate
import OAI.Combinatorics.KMedian.Compression.RationalKernelHeightSupport

namespace OAI


                                              
section
namespace MetricKMedian.Gaussian
open Finset

 theorem rational_circuit_ratio (r n L : ℕ) (A : Fin r → Fin n → ℚ)
    (hnum : ∀ i j, |(A i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((A i j).den:ℤ) ≤ (2:ℤ)^L)
    (z : Fin n → ℚ) (hc : IsCircuit A z) (hk : ∀ i, ∑ j, A i j*z j=0)
    (w : Fin n) (hw : z w=1) :
    ∃ U : Fin n → ℤ, U w ≠ 0 ∧
      (∀ j, |U j| ≤ (2:ℤ)^(2*r*(r+L*(n+1)))) ∧
      ∀ j, z j=(U j:ℚ)/(U w:ℚ) := by
  let V : Fin r → Fin n → ℤ := fun i => RationalScaling.numerator (A i)
  let D : Fin r → ℚ := fun i => RationalScaling.denominator (A i)
  have hD : ∀ i, D i ≠ 0 := by
    intro i
    apply ne_of_gt
    dsimp only [D]
    exact_mod_cast RationalScaling.denominator_pos (A i)
  have hV : ∀ i j, (V i j:ℚ)=A i j*D i := fun i j => RationalScaling.numerator_cast (A i) j
  have hVb : ∀ i j, |V i j| ≤ (2:ℤ)^(L*(n+1)) := by
    intro i j
    simpa only [Fintype.card_fin] using RationalScaling.numerator_bound (A i) L (hnum i) (hden i) j
  have hki : ∀ v : Fin n → ℚ,
      (∀ i, ∑ j, (V i j:ℚ)*v j=0) ↔ (∀ i, ∑ j, A i j*v j=0) := by
    intro v
    simp only [hV]
    exact row_scaling_kernel_iff A D hD v
  have hcV : IsCircuit (fun i j => (V i j:ℚ)) z := by
    intro v hv hkv
    exact hc v hv ((hki v).mp hkv)
  exact circuit_integer_ratio V z (L*(n+1)) hVb ((hki z).mpr hk) hcV w hw

 theorem combination_height (R H L : ℕ) (q z : Fin R → ℚ) (U : Fin R → ℤ)
    (w : Fin R) (hw : U w ≠ 0) (hU : ∀ i, |U i| ≤ (2:ℤ)^H)
    (hz : ∀ i, z i=(U i:ℚ)/(U w:ℚ))
    (hnum : ∀ i, |(q i).num| ≤ (2:ℤ)^L)
    (hden : ∀ i, ((q i).den:ℤ) ≤ (2:ℤ)^L) :
    |(∑ i, q i*z i).num| ≤ (2:ℤ)^(R+H+L*(R+1)) ∧
      (((∑ i, q i*z i).den:ℕ):ℤ) ≤ (2:ℤ)^(R+H+L*(R+1)) := by
  let V := RationalScaling.numerator q
  let D := RationalScaling.denominator q
  let a : ℤ := ∑ i, V i*U i
  let b : ℤ := D*U w
  have hD : 0 < D := RationalScaling.denominator_pos q
  have hDc : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hwc : (U w:ℚ) ≠ 0 := by exact_mod_cast hw
  have hb : b ≠ 0 := mul_ne_zero hD.ne' hw
  have hV : ∀ i, |V i| ≤ (2:ℤ)^(L*(R+1)) := by
    intro i
    simpa only [Fintype.card_fin] using RationalScaling.numerator_bound q L hnum hden i
  have hDb : D ≤ (2:ℤ)^(L*R) := by
    simpa only [Fintype.card_fin] using RationalScaling.denominator_bound q L hden
  have he : (∑ i, q i*z i)=(a:ℚ)/(b:ℚ) := by
    have hq : ∀ i, q i=(V i:ℚ)/(D:ℚ) := by
      intro i
      apply (eq_div_iff hDc).mpr
      exact (RationalScaling.numerator_cast q i).symm
    simp only [a,b,Int.cast_mul,Int.cast_sum,hq,hz]
    rw [Finset.sum_div]
    apply sum_congr rfl
    intro i _
    ring
  have ha : |a| ≤ (2:ℤ)^(R+H+L*(R+1)) := by
    calc
      _ ≤ ∑ i : Fin R, |V i*U i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin R, (2:ℤ)^(L*(R+1))*(2:ℤ)^H :=
        sum_le_sum (fun i _ => by rw [abs_mul]; exact mul_le_mul (hV i) (hU i) (abs_nonneg _) (by positivity))
      _ = (R:ℤ)*(2:ℤ)^(L*(R+1)+H) := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,pow_add]
      _ ≤ (2:ℤ)^R*(2:ℤ)^(L*(R+1)+H) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (Nat.lt_two_pow_self (n:=R)).le
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hbH : |b| ≤ (2:ℤ)^(R+H+L*(R+1)) := by
    calc
      _ = D*|U w| := by simp only [b,abs_mul,abs_of_pos hD]
      _ ≤ (2:ℤ)^(L*R)*(2:ℤ)^H := mul_le_mul hDb (hU w) (abs_nonneg _) (by positivity)
      _ = (2:ℤ)^(L*R+H) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by nlinarith)
  rw [he]
  exact ratio_num_den_bound a b hb _ ha hbH

def residualHeight (R N L : ℕ) : ℕ := R+2*N*(N+L*(R+1))+L*(R+1)

namespace ResidualCertificate
variable {R N r n : ℕ} {A : Fin R → Fin N → ℚ} {B : Fin r → Fin n → ℚ}

 theorem entry_height (P : ResidualCertificate A B) (L : ℕ)
    (hnum : ∀ i j, |(A i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((A i j).den:ℤ) ≤ (2:ℤ)^L) (i : Fin r) (j : Fin n) :
    |(B i j).num| ≤ (2:ℤ)^(residualHeight R N L) ∧
      ((B i j).den:ℤ) ≤ (2:ℤ)^(residualHeight R N L) := by
  obtain ⟨U,hUw,hU,hz⟩ := rational_circuit_ratio P.pivotCols.card R L
    (fun c t => A t (P.pivotCols.orderEmbOfFin rfl c))
    (fun c t => hnum t _) (fun c t => hden t _)
    (P.coefficient i) (P.circuit i)
    (fun c => P.annihilates i _ (P.pivotCols.orderEmbOfFin_mem rfl c)) (P.row i) (P.normalized i)
  have hc : P.pivotCols.card ≤ N := (card_le_card (subset_univ P.pivotCols)).trans_eq (card_fin N)
  have hpow : 2*P.pivotCols.card*(P.pivotCols.card+L*(R+1)) ≤ 2*N*(N+L*(R+1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hc) (Nat.add_le_add_right hc _)
  have hUb : ∀ t, |U t| ≤ (2:ℤ)^(2*N*(N+L*(R+1))) := fun t =>
    (hU t).trans (pow_le_pow_right₀ (by norm_num) hpow)
  rw [P.represents]
  exact combination_height R (2*N*(N+L*(R+1))) L (fun t => A t (P.col j))
    (P.coefficient i) U (P.row i) hUw hUb hz (fun t => hnum t _) (fun t => hden t _)

end ResidualCertificate
end MetricKMedian.Gaussian
end

end OAI
