import OAI.NumberTheory.TotientAsymptotic.LocalNormalityLayer
import OAI.NumberTheory.TotientAsymptotic.NormalInternalDiscard

namespace OAI

/-! Summation of all local normality failures in the actual candidate grid. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def localNormalityFailures (x c : ℝ) (L H : ℕ) : Finset (Fin (m x-H) → ℕ) :=
  (Finset.univ : Finset (Fin (m x-H))).biUnion (fun i =>
    (Finset.univ.filter (fun j => i ≤ j)).biUnion (localAbnormalTuples x c L H i))

theorem local_normality_discard {c : ℝ} (hc : 0 < c) :
    ∀ L : ℕ,∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      (∑ p ∈ localNormalityFailures x c L H,reciprocalShiftWeight p) ≤
        polynomialGeometricTail 0 rho H*G x (m x-H) := by
  classical
  obtain ⟨A,C,D,hA,hC,hD,hlayer⟩ := local_normality_layer_mass hc
  intro L
  obtain ⟨J,hJ,hheight⟩ := localPrimeHeight_log_bound hA L
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    (hheight.and (local_normality_geometric_decay hC hD hJ.le))
  filter_upwards [hlayer L,eventually_ge_atTop K,eventually_ge_atTop 1] with H hH hHK hH1
  filter_upwards [hH,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hm hB
  let N := m x-H
  have hsum_i (i : Fin N) :
      (∑ p ∈ (Finset.univ.filter (fun j => i ≤ j)).biUnion (localAbnormalTuples x c L H i),
        reciprocalShiftWeight p) ≤ G x (m x-H)*rho^(m x-i.val) := by
    let h := m x-i.val
    let U := localPrimeHeight A L h
    let E := C*(2*U+2)^6*Real.exp (-(h:ℝ)^4/6)*(D*(2*U+2))^(N-i.val-1)
    have hHi : H ≤ h := by have := i.isLt; dsimp [N,h] at *; omega
    have hh1 : (1:ℝ) ≤ h := by exact_mod_cast (hH1.trans hHi)
    have hU : 2 ≤ U := localPrimeHeight_ge_two hA.le L h
    have hh0 : 0 ≤ E := by dsimp [E]; positivity
    have hkernel : (h:ℝ)^2*E ≤ rho^h := by
      have hh := (hK h (hHK.trans hHi)).2 U
        (le_trans (by norm_num) (localPrimeHeight_ge_two hA.le L h))
        ((hK h (hHK.trans hHi)).1) (N-i.val-1) (by dsimp [N,h]; omega)
      simpa only [E,mul_assoc] using hh
    have hcard : ((Finset.univ.filter (fun j : Fin N => i ≤ j)).card:ℝ) ≤ (h:ℝ)^2 := by
      have hcN : (Finset.univ.filter (fun j : Fin N => i ≤ j)).card ≤ N-i.val := by
        rw [show Finset.univ.filter (fun j : Fin N => i ≤ j)=Finset.Ici i by ext j; simp]
        simp
      have hh : ((N-i.val:ℕ):ℝ) ≤ h := by exact_mod_cast (show N-i.val ≤ h by dsimp [N,h]; omega)
      have hcR : ((Finset.univ.filter (fun j : Fin N => i ≤ j)).card:ℝ) ≤ ((N-i.val:ℕ):ℝ) := by exact_mod_cast hcN
      nlinarith only [hcR,hh,hh1]
    calc
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => i ≤ j),
          ∑ p ∈ localAbnormalTuples x c L H i j,reciprocalShiftWeight p :=
        by
          convert nonnegative_sum_biUnion_le _ _ _ reciprocalShiftWeight_nonneg using 1
          congr 1
          ext p
          simp
      _ ≤ ∑ _j ∈ Finset.univ.filter (fun j : Fin N => i ≤ j),G x (m x-H)*E := by
        apply Finset.sum_le_sum
        intro j hj
        have hh := hx i j (Finset.mem_filter.mp hj).2
        dsimp only at hh
        convert hh using 1
        dsimp [E,U,h,N]
        ring
      _ = G x (m x-H)*(((Finset.univ.filter (fun j : Fin N => i ≤ j)).card:ℝ)*E) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        ring
      _ ≤ G x (m x-H)*((h:ℝ)^2*E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hh0) (G_pos hB _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hkernel (G_pos hB _).le
  have hgeo : (∑ i : Fin N,rho^(m x-i.val)) ≤ polynomialGeometricTail 0 rho H := by
    change (∑ i : Fin N,(fun j : ℕ => rho^(m x-j)) i.val) ≤ _
    have he := Fin.sum_univ_eq_sum_range (fun j => rho^(m x-j)) N
    rw [he]
    apply le_trans _ (reverse_geometric_sum hm)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,by have := Finset.mem_range.mp hi; dsimp [N] at this; omega⟩
    · intro i _ _
      exact (pow_pos rho_pos _).le
  calc
    _ ≤ ∑ i : Fin N,∑ p ∈ (Finset.univ.filter (fun j => i ≤ j)).biUnion
        (localAbnormalTuples x c L H i),reciprocalShiftWeight p :=
      by
        convert nonnegative_sum_biUnion_le _ _ _ reciprocalShiftWeight_nonneg using 1
        congr 1
        ext p
        simp [localNormalityFailures,N]
    _ ≤ ∑ i : Fin N,G x (m x-H)*rho^(m x-i.val) := Finset.sum_le_sum (fun i _ => hsum_i i)
    _ = G x (m x-H)*(∑ i : Fin N,rho^(m x-i.val)) := (Finset.mul_sum _ _ _).symm
    _ ≤ G x (m x-H)*polynomialGeometricTail 0 rho H := mul_le_mul_of_nonneg_left hgeo (G_pos hB _).le
    _ = _ := mul_comm _ _

end TotientAsymptotic

end

end OAI
