import Mathlib
import OAI.Analysis.LaughlinGap.PairDecomposition

namespace OAI

/-! Four Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct
open Occupation Filter Topology

lemma orbitalPair_orthonormal_twice {Q r s : ℕ} (hr : r ≤ Q) (hs : s ≤ Q)
    (hro : Odd r) (hso : Odd s)
    (l : Fin (2*Q-2*r+1)) (k : Fin (2*Q-2*s+1)) :
    (∑ a : PairLabel (Q+1), orbitalPairCoefficient Q r l.val a *
      orbitalPairCoefficient Q s k.val a) = if r=s ∧ l.val=k.val then 1 else 0 := by
  exact orbitalPair_orthonormal hr hs hro hso
    ⟨l.val, by omega⟩ ⟨k.val, by omega⟩

noncomputable def pairFactorInclusion (Q n r : ℕ)
    (x : (Fin (n+1) × Fin (2*Q-2*r+1)) → ℝ) :
    (Fin (n+1) × PairLabel (Q+1)) → ℝ := fun pa =>
  ∑ k : Fin (2*Q-2*r+1), x (pa.1,k) * orbitalPairCoefficient Q r k.val pa.2

lemma pairFactorInclusion_isometry {Q n r : ℕ} (hr : r ≤ Q) (ho : Odd r)
    (x y : (Fin (n+1) × Fin (2*Q-2*r+1)) → ℝ) :
    dotProduct (pairFactorInclusion Q n r x) (pairFactorInclusion Q n r y) =
      dotProduct x y := by
  classical
  simp only [dotProduct, Fintype.sum_prod_type, pairFactorInclusion]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans _ (by simp : (∑ k : Fin (2*Q-2*r+1),
    ∑ l : Fin (2*Q-2*r+1), x (p,l) * y (p,k) * if k=l then (1:ℝ) else 0) = _)
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  have he := orbitalPair_orthonormal_twice hr hr ho ho k l
  simp only [true_and, Fin.val_inj] at he
  rw [← he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma pairFactorInclusion_orthogonal {Q n r s : ℕ} (hr : r ≤ Q) (hs : s ≤ Q)
    (hro : Odd r) (hso : Odd s) (hrs : r ≠ s)
    (x : (Fin (n+1) × Fin (2*Q-2*r+1)) → ℝ)
    (y : (Fin (n+1) × Fin (2*Q-2*s+1)) → ℝ) :
    dotProduct (pairFactorInclusion Q n r x) (pairFactorInclusion Q n s y) = 0 := by
  simp only [dotProduct, Fintype.sum_prod_type, pairFactorInclusion,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro l hl
  have he := orbitalPair_orthonormal_twice hr hs hro hso l k
  simp only [hrs, false_and, ite_false] at he
  calc
    _ = (x (p,l) * y (p,k)) * ∑ a : PairLabel (Q+1),
        orbitalPairCoefficient Q r l.val a * orbitalPairCoefficient Q s k.val a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = 0 := by rw [he, mul_zero]

noncomputable def fourBodyCoupled (Q D T r : ℕ) :
    (Fin (2*Q-2+1) × PairLabel (Q+1)) → ℝ :=
  pairFactorInclusion Q (2*Q-2) r
    (coupledTensor (2*Q-2) (2*Q-2*r) (D-r) (T-D))

noncomputable def fourBodyCoefficient (Q D T r p j k : ℕ) : ℝ :=
  if r ≤ j+k ∧ p+j+k=T then
    Real.sqrt 2 * coupledCoefficient Q Q r (j+k-r) j *
      coupledCoefficient (2*Q-2) (2*Q-2*r) (D-r) (T-D) p
  else 0

theorem fourBodyCoupled_coefficient {Q D T r : ℕ} (hrD : r ≤ D)
    (hDT : D ≤ T) (hT : T ≤ Q) (p : Fin (2*Q-2+1)) (a : PairLabel (Q+1)) :
    fourBodyCoupled Q D T r (p,a) =
      fourBodyCoefficient Q D T r p.val a.val.1.val a.val.2.val := by
  classical
  unfold fourBodyCoupled pairFactorInclusion fourBodyCoefficient
  by_cases hw : r ≤ a.val.1.val+a.val.2.val ∧ p.val+a.val.1.val+a.val.2.val=T
  · rw [ite_eq_left hw]
    let l : Fin (2*Q-2*r+1) := ⟨a.val.1.val+a.val.2.val-r, by omega⟩
    rw [Finset.sum_eq_single l]
    · simp only [orbitalPairCoefficient, coupledTensor]
      rw [ite_eq_left (by dsimp [l]; omega), ite_eq_left (by dsimp [l]; omega)]
      dsimp [l]
      ring
    · intro k hk hkl
      have he : a.val.1.val+a.val.2.val ≠ r+k.val := by
        intro he
        apply hkl
        apply Fin.ext
        dsimp [l]
        omega
      simp only [orbitalPairCoefficient, coupledTensor, ite_eq_right he, mul_zero]
    · simp
  · rw [ite_eq_right hw]
    apply Finset.sum_eq_zero
    intro k hk
    simp only [coupledTensor, orbitalPairCoefficient]
    split_ifs with h₁ h₂ h₂ <;> try simp
    exfalso
    exact hw ⟨by omega, by omega⟩

lemma fourBodyCoupled_norm_sq {Q D T r : ℕ} (hr : r ≤ Q) (hro : Odd r)
    (hz : D-r ≤ min (2*Q-2) (2*Q-2*r))
    (hl : T-D ≤ (2*Q-2)+(2*Q-2*r)-2*(D-r)) :
    dotProduct (fourBodyCoupled Q D T r) (fourBodyCoupled Q D T r) = 1 := by
  rw [fourBodyCoupled, pairFactorInclusion_isometry hr hro]
  exact coupledTensor_norm_sq hz hl

lemma fourBodyCoupled_orthogonal {Q D T r s : ℕ} (hr : r ≤ Q) (hs : s ≤ Q)
    (hro : Odd r) (hso : Odd s) (h : r ≠ s) :
    dotProduct (fourBodyCoupled Q D T r) (fourBodyCoupled Q D T s) = 0 := by
  exact pairFactorInclusion_orthogonal hr hs hro hso h _ _

abbrev FourCopy (D : ℕ) := {r : Fin (D+1) // Odd r.val}

noncomputable def fourBodyHighestFamily (Q D : ℕ) (r : FourCopy D) :
    EuclideanSpace ℝ (Fin (2*Q-2+1) × PairLabel (Q+1)) :=
  WithLp.toLp 2 (fourBodyCoupled Q D D r.val.val)

theorem fourBodyHighestFamily_orthonormal {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q) :
    Orthonormal ℝ (fourBodyHighestFamily Q D) := by
  rw [orthonormal_iff_ite]
  intro r s
  simp only [fourBodyHighestFamily, EuclideanSpace.inner_toLp_toLp]
  by_cases he : r=s
  · subst s
    rw [ite_eq_left rfl]
    apply fourBodyCoupled_norm_sq (by omega) r.property
    · have : 1 ≤ r.val.val := r.property.pos
      omega
    · omega
  · rw [ite_eq_right he]
    exact fourBodyCoupled_orthogonal (by omega) (by omega) s.property r.property
      (by intro h; apply he; exact Subtype.ext (Fin.ext h.symm))

noncomputable def balancedCouplingCoefficient (z T p : ℕ) : ℝ :=
  if z ≤ T then monomialWeight T p *
    (couplingPolynomial (1/Real.sqrt 2) (1/Real.sqrt 2) z (T-z)).coeff p else 0

noncomputable def fourBodyCoefficientStar (D T r p j k : ℕ) : ℝ :=
  if r ≤ j+k ∧ p+j+k=T then
    Real.sqrt 2 * balancedCouplingCoefficient r (j+k) j *
      balancedCouplingCoefficient (D-r) (T-r) p
  else 0

lemma affine_twice_spin_tendsto (r : ℕ) :
    Tendsto (fun Q : ℕ => ((2*Q-2*r : ℕ) : ℝ)) atTop atTop := by
  apply tendsto_natCast_atTop_atTop.comp
  apply tendsto_atTop_mono (fun Q => show Q-r ≤ 2*Q-2*r by omega)
  exact tendsto_sub_atTop_nat r

lemma affine_twice_spin_ratio_tendsto (r : ℕ) :
    Tendsto (fun Q : ℕ => ((2*Q-2*r : ℕ) : ℝ) / (2*Q-2 : ℕ)) atTop (𝓝 (1:ℝ)) := by
  have h := ((tendsto_const_nhds (x := (1:ℝ))).sub
    ((tendsto_const_nhds (x := ((2*r:ℕ):ℝ)-2)).div_atTop (affine_twice_spin_tendsto 1)))
  simp only [sub_zero, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (max r 1+1)] with Q hQ
  have hr : 2*r ≤ 2*Q := by omega
  have h2 : 2 ≤ 2*Q := by omega
  have hd : ((2*Q-2 : ℕ):ℝ) ≠ 0 := by exact_mod_cast (show 2*Q-2 ≠ 0 by omega)
  simp only [Nat.cast_sub hr, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub h2]
  simp only [Nat.cast_sub h2, Nat.cast_mul, Nat.cast_ofNat] at hd
  calc
    _ = ((2*(Q:ℝ)-2) - (2*(r:ℝ)-2)) / (2*(Q:ℝ)-2) := by
      conv_rhs => rw [sub_div, div_self hd]
    _ = _ := by congr 1; ring

lemma equal_spin_ratio_tendsto :
    Tendsto (fun Q : ℕ => (Q:ℝ)/Q) atTop (𝓝 (1:ℝ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with Q hQ
  exact (div_self (Nat.cast_ne_zero.mpr (by omega))).symm

lemma balanced_coupling_limit {n m : ℕ → ℕ}
    (hn : Tendsto (fun Q => (n Q : ℝ)) atTop atTop)
    (hr : Tendsto (fun Q => (m Q : ℝ)/(n Q:ℝ)) atTop (𝓝 (1:ℝ)))
    {z T : ℕ} (hzT : z ≤ T) (p : ℕ) :
    Tendsto (fun Q => coupledCoefficient (n Q) (m Q) z (T-z) p) atTop
      (𝓝 (balancedCouplingCoefficient z T p)) := by
  have h := coupledCoefficient_tendsto_polynomial (by norm_num : (0:ℝ) ≤ 1) hn hr z (T-z) p
  simpa [balancedCouplingCoefficient, hzT, Nat.add_sub_of_le hzT,
    show (1:ℝ)+1=2 by norm_num] using h

theorem fourBodyCoefficient_tendsto {D T r : ℕ} (hrD : r ≤ D) (hDT : D ≤ T)
    (p j k : ℕ) :
    Tendsto (fun Q => fourBodyCoefficient Q D T r p j k) atTop
      (𝓝 (fourBodyCoefficientStar D T r p j k)) := by
  by_cases h : r ≤ j+k ∧ p+j+k=T
  · simp only [fourBodyCoefficient, fourBodyCoefficientStar, ite_eq_left h]
    have h₁ := balanced_coupling_limit tendsto_natCast_atTop_atTop
      equal_spin_ratio_tendsto h.1 j
    have h₂ := balanced_coupling_limit (affine_twice_spin_tendsto 1)
      (affine_twice_spin_ratio_tendsto r) (show D-r ≤ T-r by omega) p
    have he : T-r-(D-r)=T-D := by omega
    simpa only [he, mul_one] using (h₁.const_mul (Real.sqrt 2)).mul h₂
  · simp only [fourBodyCoefficient, fourBodyCoefficientStar, ite_eq_right h]
    exact tendsto_const_nhds

end LaughlinGap.Spin

end

end OAI
