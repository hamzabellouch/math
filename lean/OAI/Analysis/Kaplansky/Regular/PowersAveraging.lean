import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Regular.PowersAverageBound
import OAI.Analysis.Kaplansky.Regular.PowersPartition
import OAI.Analysis.Kaplansky.Regular.ReducedPolynomials

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal
section
attribute [local instance 2000] Classical.propDecidable Classical.decEq

lemma conjugateMap_polynomial_val (u : F2) (c : F2 →₀ ℂ) :
    (conjugateMap u (polynomial c)).val = ∑ f ∈ c.support, c f • left (u*f*u⁻¹) := by
  rw [conjugateMap_val,polynomial_apply]
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro f hf
  rw [←left_mul,←left_mul]

lemma polynomial_mask_zero (u : F2) (D : F2 → Prop) (c : F2 →₀ ℂ)
    (hD : ∀ f ∈ c.support, ∀ w, D w → ¬D (u*f*u⁻¹*w)) :
    mask D*(conjugateMap u (polynomial c)).val*mask D=0 := by
  rw [conjugateMap_polynomial_val]
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]
  apply Finset.sum_eq_zero
  intro f hf
  rw [mask_left_mask_zero D (u*f*u⁻¹) (hD f hf)]
  exact smul_zero (A := HilbertSum F2 ℂ →L[ℂ] HilbertSum F2 ℂ) (c f)

lemma polynomial_average_bound (c : F2 →₀ ℂ) (hc : c 1=0) (N : ℕ) :
    ∃ h : Fin N → F2, ‖averageConjugate h (polynomial c)‖ ≤
      (N:ℝ)⁻¹*(2*Real.sqrt N*‖polynomial c‖) := by
  obtain ⟨u,D,h,hD,hd⟩ := powers_partition c.support
    (fun f hf he => Finsupp.mem_support_iff.mp hf (he ▸ hc)) N
  refine ⟨fun i => h i*u,?_⟩
  exact average_conjugated_partition_bound D h hd u (polynomial c)
    (polynomial_mask_zero u D c hD)

end

lemma polynomial_average_small (c : F2 →₀ ℂ) (hc : c 1=0) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, 0<N ∧ ∃ h : Fin N → F2, ‖averageConjugate h (polynomial c)‖ < ε := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max 0 (2*‖polynomial c‖/ε))
  have hn0 : (0:ℝ)<n := lt_of_le_of_lt (le_max_left _ _) hn
  have hn1 : 2*‖polynomial c‖ < (n:ℝ)*ε :=
    (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_right _ _) hn)
  obtain ⟨h,hh⟩ := polynomial_average_bound c hc (n^2)
  refine ⟨n^2,pow_pos (Nat.cast_pos.mp hn0) 2,h,lt_of_le_of_lt hh ?_⟩
  rw [Nat.cast_pow,Real.sqrt_sq (le_of_lt hn0)]
  calc
    _ = 2*‖polynomial c‖/(n:ℝ) := by field_simp
    _ < ε := (div_lt_iff₀ hn0).mpr (by simpa [mul_comm] using hn1)

theorem powers_averaging (x : Algebra F2) (hx : coefficient x=0) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, 0<N ∧ ∃ h : Fin N → F2, ‖averageConjugate h x‖ < ε := by
  obtain ⟨c,hc,hxc⟩ := polynomial_dense_zero x hx (ε/2) (half_pos hε)
  obtain ⟨N,hN,h,hh⟩ := polynomial_average_small c hc (ε/2) (half_pos hε)
  refine ⟨N,hN,h,?_⟩
  exact lt_of_le_of_lt (average_approximation_bound hN h x (polynomial c))
    (by linarith)


end KaplanskyConsequences.Regular

end

end OAI
