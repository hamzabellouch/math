import OAI.NumberTheory.CubicGram.SieveImprovement
import OAI.NumberTheory.CubicMoment.Estimates.DispersionAlgebra

namespace OAI

/-! The proved cubic large sieve with an unrestricted inner coefficient
support. The cube decomposition is already in the baseline; here its
summed dyadic bound is transferred to a sharp norm cutoff. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma finiteCubicBound_le_dualDyadicNorm (P H : Finset Eisenstein)
    (hP : ∀ p ∈ P, primary p) {Z : ℝ} (hZ : 0 < Z)
    (hH : ∀ h ∈ H, h ≠ 0 ∧ norm h ≤ Z) :
    finiteCubicBound P H ≤ 256*dualDyadicNorm P (1/Z) 8 := by
  let J := H.image (fun h => Nat.log 2 (normNat h))
  have hz : 0 < 1/Z := by positivity
  have hs := summable_dualDyadicNorm P hP hz (by norm_num : 2 ≤ 8)
  apply (finiteCubicBound_le_iff _ _ (mul_nonneg (by norm_num)
    (dualDyadicNorm_nonneg P hz.le 8))).mpr
  intro v
  let E := ∑ p ∈ P, ‖v p‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hdyad (j : ℕ) (hj : j ∈ J) :
      finiteCubicBound P (frequencyDyad j) ≤
        256*(finiteCubicBound P (frequencyDyad j)/(1+(1/Z)*2^j)^8) := by
    obtain ⟨h,hh,hlog⟩ := Finset.mem_image.mp hj
    have hhj : h ∈ frequencyDyad j := mem_frequencyDyad.mpr ⟨(hH h hh).1,hlog⟩
    have hpow : (2:ℝ)^j ≤ Z := (frequencyDyad_norm hhj).1.trans (hH h hh).2
    have hsmall : (1/Z)*(2:ℝ)^j ≤ 1 := by
      rw [one_div,mul_comm,← div_eq_mul_inv]
      exact (div_le_one hZ).mpr hpow
    have hden : 0 < (1+(1/Z)*(2:ℝ)^j)^8 := by positivity
    have hdenle : (1+(1/Z)*(2:ℝ)^j)^8 ≤ 256 := by
      have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1+(1/Z)*(2:ℝ)^j)
        (show 1+(1/Z)*(2:ℝ)^j ≤ 2 by linarith) 8
      norm_num at h ⊢
      exact h
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hden).mpr
    exact (mul_le_mul_of_nonneg_left hdenle (finiteCubicBound_nonneg _ _)).trans_eq (mul_comm _ _)
  calc
    (∑ h ∈ H, ‖∑ p ∈ P, v p*cubicSymbol p h‖^2) =
        ∑ j ∈ J, ∑ h ∈ H with Nat.log 2 (normNat h) = j,
          ‖∑ p ∈ P, v p*cubicSymbol p h‖^2 :=
      (Finset.sum_fiberwise_of_maps_to (fun h hh => Finset.mem_image_of_mem _ hh) _).symm
    _ ≤ ∑ j ∈ J, finiteCubicBound P (frequencyDyad j)*E := by
      apply Finset.sum_le_sum
      intro j hj
      have hsub : H.filter (fun h => Nat.log 2 (normNat h) = j) ⊆ frequencyDyad j := by
        intro h hh
        exact mem_frequencyDyad.mpr ⟨(hH h (Finset.mem_filter.mp hh).1).1,
          (Finset.mem_filter.mp hh).2⟩
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans
        (finiteCubicBound_controls_mass P (frequencyDyad j) v)
    _ ≤ ∑ j ∈ J, (256*(finiteCubicBound P (frequencyDyad j)/(1+(1/Z)*2^j)^8))*E :=
      Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (hdyad j hj) hE)
    _ = (256*∑ j ∈ J, finiteCubicBound P (frequencyDyad j)/(1+(1/Z)*2^j)^8)*E := by
      simp only [Finset.mul_sum,Finset.sum_mul]
    _ ≤ (256*dualDyadicNorm P (1/Z) 8)*E := by
      apply mul_le_mul_of_nonneg_right _ hE
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact hs.sum_le_tsum J (fun j _ => div_nonneg (finiteCubicBound_nonneg _ _) (by positivity))

private lemma inverse_negative_rpow {Z : ℝ} (hZ : 0 < Z) (a : ℝ) :
    (1/Z)^(-a) = Z^a := by
  rw [one_div,Real.inv_rpow hZ.le,Real.rpow_neg hZ.le,inv_inv]

/-- Sharp cutoff form of the cube-extracted cubic sieve. The inner
support need not be squarefree or primary. -/
theorem unrestricted_cubic_operator_bound {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : Finset Eisenstein) (N Z : ℝ),
      1 ≤ N → 1 ≤ Z →
      (∀ p ∈ P, primary p ∧ Squarefree p ∧ norm p ≤ N) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ Z) →
      finiteCubicBound P H ≤ C*(N*Z)^ε*
        (N*Z^(1/3:ℝ)+(N*Z)^(2/3:ℝ)+Z^(4/3:ℝ)+Z) := by
  obtain ⟨C,hC,hbound⟩ := SieveExponent.dual_bound (ξ := (4/3:ℝ))
    (by norm_num) (by norm_num) sieveExponent_four_thirds hε hε₁
  refine ⟨256*C,by positivity,?_⟩
  intro P H N Z hN hZ hP hH
  have hZ0 : 0 < Z := by linarith
  have hN0 : 0 < N := by linarith
  have h := hbound P N (1/Z) hN (by positivity) hP
  simp only [inverse_negative_rpow hZ0] at h
  apply (finiteCubicBound_le_dualDyadicNorm P H (fun p hp => (hP p hp).1) hZ0 hH).trans
  apply (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 256)).trans_eq
  rw [Real.mul_rpow hN0.le hZ0.le,Real.mul_rpow hN0.le hZ0.le]
  rw [Real.rpow_add hZ0,Real.rpow_add hZ0,Real.rpow_add hZ0,Real.rpow_add hZ0,
    Real.rpow_one]
  ring

/-- Transposition of the actual finite cubic-character matrix. This does
not require reciprocity or primarity of the inner support. -/
lemma finiteCubicBound_controls_transpose (P H : Finset Eisenstein)
    (v : Eisenstein → ℂ) :
    (∑ p ∈ P, ‖∑ h ∈ H, v h*cubicSymbol p h‖^2) ≤
      finiteCubicBound P H * ∑ h ∈ H, ‖v h‖^2 := by
  let f (p : Eisenstein) := ∑ h ∈ H, v h*cubicSymbol p h
  let g (h : Eisenstein) := ∑ p ∈ P, f p*star (cubicSymbol p h)
  let E : ℝ := ∑ p ∈ P, ‖f p‖^2
  let V : ℝ := ∑ h ∈ H, ‖v h‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hdual : (E:ℂ) = ∑ h ∈ H, v h*star (g h) := by
    change ((∑ p ∈ P, ‖f p‖^2:ℝ):ℂ) = _
    have hcast : ((∑ p ∈ P, ‖f p‖^2:ℝ):ℂ) =
        ∑ p ∈ P, ((‖f p‖^2:ℝ):ℂ) := map_sum Complex.ofRealHom _ _
    rw [hcast]
    simp_rw [Complex.ofReal_pow,← Complex.mul_conj']
    conv_lhs => arg 2; ext p; lhs; unfold f
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h hh
    simp only [g,star_sum,star_mul,star_star,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [starRingEnd_apply]
    ring
  have hg : (∑ h ∈ H, ‖g h‖^2) ≤ finiteCubicBound P H*E := by
    have h := finiteCubicBound_controls_mass P H (fun p => star (f p))
    have he (h : Eisenstein) : g h = star (∑ p ∈ P, star (f p)*cubicSymbol p h) := by
      simp only [g,star_sum,star_mul,star_star,mul_comm]
    simpa only [he,norm_star] using h
  have hCS := complex_bilinear_rows_sq H v (fun h => star (g h))
  rw [← hdual,Complex.norm_real,Real.norm_of_nonneg hE] at hCS
  simp only [norm_star] at hCS
  change E^2 ≤ V*(∑ h ∈ H, ‖g h‖^2) at hCS
  have hmul := mul_le_mul_of_nonneg_left hg hV
  change E ≤ finiteCubicBound P H*V
  by_cases hz : E = 0
  · rw [hz]
    exact mul_nonneg (finiteCubicBound_nonneg _ _) hV
  · have hpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hz)
    nlinarith

theorem unrestricted_cubic_sieve {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : Finset Eisenstein) (N Z : ℝ),
      1 ≤ N → 1 ≤ Z →
      (∀ p ∈ P, primary p ∧ Squarefree p ∧ norm p ≤ N) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ Z) → ∀ v : Eisenstein → ℂ,
      (∑ p ∈ P, ‖∑ h ∈ H, v h*cubicSymbol p h‖^2) ≤
      C*(N*Z)^ε*(N*Z^(1/3:ℝ)+(N*Z)^(2/3:ℝ)+Z^(4/3:ℝ)+Z)*
        ∑ h ∈ H, ‖v h‖^2 := by
  obtain ⟨C,hC,hbound⟩ := unrestricted_cubic_operator_bound hε hε₁
  refine ⟨C,hC,?_⟩
  intro P H N Z hN hZ hP hH v
  exact (finiteCubicBound_controls_transpose P H v).trans
    (mul_le_mul_of_nonneg_right (hbound P H N Z hN hZ hP hH)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

end CubicFirstMoment

end

end OAI
