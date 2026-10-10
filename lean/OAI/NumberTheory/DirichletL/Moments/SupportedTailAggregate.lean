import OAI.NumberTheory.DirichletL.Moments.SecondTail
import OAI.NumberTheory.DirichletL.Moments.FirstTailAggregate
import OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSupportedTailAggregate
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentSecondTail CenteredMomentFirstTailAggregate CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstScale CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily
local notation "O" => ActualEisensteinCubic.O

private theorem pair_mass {α : Type*} [Fintype α] (c w : α → ℂ) (F : α → α → ℂ)
    (hw : ∀ i,‖w i‖≤1) (B : ℝ) (_hB : 0≤B)
    (hF : ∀ i j,c i≠0 → c j≠0 → ‖F i j‖≤B) :
    ‖∑ i,∑ j,((c i*w i)*star (c j*w j))*F i j‖≤(∑ i,‖c i‖)^2*B := by
  have ht (i j : α) : ‖((c i*w i)*star (c j*w j))*F i j‖≤‖c i‖*‖c j‖*B := by
    by_cases hi : c i=0
    · simp [hi]
    by_cases hj : c j=0
    · simp [hj]
    rw [norm_mul,norm_mul,norm_star]
    apply mul_le_mul _ (hF i j hi hj) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    apply mul_le_mul _ _ (norm_nonneg _) (norm_nonneg _)
    · rw [norm_mul];exact mul_le_of_le_one_right (norm_nonneg _) (hw i)
    · rw [norm_mul];exact mul_le_of_le_one_right (norm_nonneg _) (hw j)
  calc
    _ ≤ ∑ i,‖∑ j,((c i*w i)*star (c j*w j))*F i j‖ := norm_sum_le _ _
    _ ≤ ∑ i,∑ j,‖c i‖*‖c j‖*B := Finset.sum_le_sum (fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ht i j)))
    _ = _ := by rw [pow_two,Finset.sum_mul,Finset.sum_mul];apply Finset.sum_congr rfl;intro i hi;rw [Finset.mul_sum,Finset.sum_mul]

def secondDiscardedEnergy (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*heightCoeff η t I)*star (c J*heightCoeff η t J))*
      secondDiscardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

theorem second_discarded_energy_bound (Adec : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
      ∀ (η : Character) (t : ℝ) (S : Finset (Ideal O)) (c : Ideal O → ℂ)
        (W : 𝓢(ℝ,ℂ)) (K X H Tsec Z Csec ξ : ℝ),0<K → 0<X → 1<Z → 1≤Csec →
      (∀ I∈S,c I≠0 → (Ideal.absNorm I:ℝ)≤Real.exp H*X) →
      X^2/K≤Tsec → (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖secondDiscardedEnergy η t S c W K Tsec Z ξ‖≤
        (∑ I∈S,‖c I‖)^2*K*(Real.exp H*X)^2*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := second_discarded_pair_bound Adec
  refine ⟨s,C,hC,?_⟩
  intro η t S c W K X H Tsec Z Csec ξ hK hX hZ hCs hN hsec hthreshold
  let B := K*(Real.exp H*X)^2*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec)
  have hB : 0≤B := by dsimp only [B];positivity
  have hweight (I : supportedColumns S) : ‖heightCoeff η t I‖≤1 := by
    rw [heightCoeff_eq_fixed_rowWeight η t I (Finset.mem_filter.mp I.property).2]
    exact rowWeight_norm_le_one η fixedBadMask 1 1 t I (Finset.mem_filter.mp I.property).2.1
  have hp := pair_mass (fun I : supportedColumns S => c I) (fun I => heightCoeff η t I)
    (fun I J => secondDiscardedPair I J (Finset.mem_filter.mp I.property).2
      (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ) hweight B hB
    (fun I J hi hj => ht W I J (Finset.mem_filter.mp I.property).2
      (Finset.mem_filter.mp J.property).2 K X H Tsec Z Csec ξ hK hX hZ hCs
      (hN I (Finset.mem_filter.mp I.property).1 hi) (hN J (Finset.mem_filter.mp J.property).1 hj) hsec hthreshold)
  have hm : (∑ I : supportedColumns S,‖c I‖)≤∑ I∈S,‖c I‖ := by
    rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ‖c I‖)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)
  apply hp.trans
  convert mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (show 0 ≤ ∑ I : supportedColumns S, ‖c I‖ from
      Finset.sum_nonneg (fun I _ => norm_nonneg (c I))) hm 2) hB using 1 ; dsimp only [B];ring

theorem first_discarded_energy_bound (Adec : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Ideal O)) (c : Ideal O → ℂ)
        (W : 𝓢(ℝ,ℂ)) (K X H Tsec Z Csec ξ : ℝ),0<K → 0<X → 1<Z → 1≤Csec →
      (∀ I∈S,c I≠0 → (Ideal.absNorm I:ℝ)≤Real.exp H*X) →
      (∀ I : supportedColumns S,∀ J : supportedColumns S,c I≠0 → c J≠0 →
        ∀ E∈inactiveSubsets I J,firstNominalScale I J (∏ P∈E,P.val) K X≤Tsec) →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖discardedEnergy η m A t S c W K Tsec Z ξ‖≤
        (∑ I∈S,‖c I‖)^2*(Real.exp H*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := canonical_discarded_pair_bound Adec ε hε
  refine ⟨s,C,hC,?_⟩
  intro η m A t S c W K X H Tsec Z Csec ξ hK hX hZ hCs hN hsec hthreshold
  let B := (Real.exp H*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec)
  have hB : 0≤B := by dsimp only [B];positivity
  have hpair (I J : supportedColumns S) (hi : c I≠0) (hj : c J≠0) :
      ‖canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ‖≤B := by
    have hni := hN I (Finset.mem_filter.mp I.property).1 hi
    have hnj := hN J (Finset.mem_filter.mp J.property).1 hj
    apply (ht W I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2
      K X H Tsec Z Csec ξ hK hX hZ hCs hni hnj (hsec I J hi hj) hthreshold).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hni hε.le) hK.le
  have hp := pair_mass (fun I : supportedColumns S => c I)
    (fun I => CenteredMomentHeckeExpansion.rowWeight η m A 1 t I)
    (fun I J => canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
      (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ)
    (fun I => rowWeight_norm_le_one η m A 1 t I (Finset.mem_filter.mp I.property).2.1) B hB hpair
  have hm : (∑ I : supportedColumns S,‖c I‖)≤∑ I∈S,‖c I‖ := by
    rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ‖c I‖)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)
  apply hp.trans
  convert mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (show 0 ≤ ∑ I : supportedColumns S, ‖c I‖ from
      Finset.sum_nonneg (fun I _ => norm_nonneg (c I))) hm 2) hB using 1 ; dsimp only [B];ring

end SevenEighths.CenteredMomentSupportedTailAggregate

end

end OAI
