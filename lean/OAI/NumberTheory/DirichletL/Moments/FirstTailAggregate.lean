import OAI.NumberTheory.DirichletL.Moments.FirstDiscardedEnergy
import OAI.NumberTheory.DirichletL.Moments.SourceRow

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstTailAggregate
open ActualEisensteinCubic HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_norm_le_one (η : Character) (m A z : O) (t : ℝ)
    (I : Ideal O) (hI : I≠0) : ‖rowWeight η m A z t I‖≤1 := by
  have hp := norm_real_imaginary_power (Ideal.absNorm I:ℝ) t (norm_pos I hI)
  norm_cast at hp
  change ‖(idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)‖≤1
  rw [norm_mul,norm_mul,hp,mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (idealCoeff_norm_le_one η I)).trans (idealRowHom_norm _ _)

def discardedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

theorem discarded_energy_bound (Adec : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Ideal O))
        (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      (∀ I∈S,(Ideal.absNorm I:ℝ)≤Real.exp HN*X) →
      (∀ I : supportedColumns S,∀ J : supportedColumns S,∀ E∈inactiveSubsets I J,
        firstNominalScale I J (∏ P∈E,P.val) K X≤Tsec) →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖discardedEnergy η m A t S c W K Tsec Z ξ‖ ≤
      (∑ I∈S,‖c I‖)^2*(Real.exp HN*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := canonical_discarded_pair_bound Adec ε hε
  refine ⟨s,C,hC,?_⟩
  intro η m A t S c W K X HN Tsec Z Csec ξ hK hX hZ hCs hN hsec hthreshold
  let B := (Real.exp HN*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec)
  have hB : 0≤B := by dsimp only [B];positivity
  have hpair (I J : supportedColumns S) :
      ‖canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ‖≤B := by
    have hi := hN I (Finset.mem_filter.mp I.property).1
    have hj := hN J (Finset.mem_filter.mp J.property).1
    apply (ht W I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2
      K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj (hsec I J) hthreshold).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hi hε.le) hK.le
  have hcoeff (I : supportedColumns S) : ‖c I*rowWeight η m A 1 t I‖≤‖c I‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (rowWeight_norm_le_one η m A 1 t I (Finset.mem_filter.mp I.property).2.1)
  have hmass : (∑ I : supportedColumns S,‖c I‖)≤∑ I∈S,‖c I‖ := by
    rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ‖c I‖)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)
  have he : (∑ I : supportedColumns S,∑ J : supportedColumns S,‖c I‖*‖c J‖*B)=
      (∑ I : supportedColumns S,‖c I‖)^2*B := by
    rw [pow_two,Finset.sum_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro I hI
    rw [Finset.mul_sum,Finset.sum_mul]
  calc
    _ ≤ ∑ I : supportedColumns S,‖∑ J : supportedColumns S,
        ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
          canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
            (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ‖ := norm_sum_le _ _
    _ ≤ ∑ I : supportedColumns S,∑ J : supportedColumns S,‖c I‖*‖c J‖*B := by
      apply Finset.sum_le_sum
      intro I hI
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro J hJ
      rw [norm_mul,norm_mul,norm_star]
      exact mul_le_mul (mul_le_mul (hcoeff I) (hcoeff J) (norm_nonneg _) (norm_nonneg _))
        (hpair I J) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (∑ I : supportedColumns S,‖c I‖)^2*B := he
    _ ≤ (∑ I∈S,‖c I‖)^2*B := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hmass 2) hB
    _ = _ := by dsimp only [B];ring

end SevenEighths.CenteredMomentFirstTailAggregate

end

end OAI
