import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic

namespace OAI

namespace PiExponent.WeightedBezout

open scoped BigOperators

variable {k σ τ : Type*} [Field k]

noncomputable def translatedPowerSubstitution (w : σ → ℕ) (a : σ → k) :
    MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (a i) + MvPolynomial.X i ^ w i)

@[simp] theorem translatedPowerSubstitution_X (w : σ → ℕ) (a : σ → k) (i : σ) :
    translatedPowerSubstitution w a (MvPolynomial.X i) =
      MvPolynomial.C (a i) + MvPolynomial.X i ^ w i := by
  simp [translatedPowerSubstitution]

@[simp] theorem translatedPowerSubstitution_C (w : σ → ℕ) (a : σ → k) (c : k) :
    translatedPowerSubstitution w a (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [translatedPowerSubstitution]

theorem totalDegree_aeval_monomial_le (w : σ → ℕ) (g : σ → MvPolynomial τ k)
    (hg : ∀ i, (g i).totalDegree ≤ w i) (d : σ →₀ ℕ) (c : k) :
    (MvPolynomial.aeval g (MvPolynomial.monomial d c)).totalDegree ≤
      Finsupp.weight w d := by
  classical
  rw [MvPolynomial.aeval_monomial]
  calc
    _ ≤ (MvPolynomial.C c).totalDegree +
        (d.prod fun i e => g i ^ e).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ ∑ i ∈ d.support, d i * w i := by
      simp only [MvPolynomial.totalDegree_C, zero_add, Finsupp.prod]
      apply (MvPolynomial.totalDegree_finsetProd _ _).trans
      exact Finset.sum_le_sum (fun i hi => (MvPolynomial.totalDegree_pow (g i) (d i)).trans
        (Nat.mul_le_mul_left (d i) (hg i)))
    _ = _ := by simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]

theorem totalDegree_aeval_le_weighted (w : σ → ℕ) (g : σ → MvPolynomial τ k)
    (hg : ∀ i, (g i).totalDegree ≤ w i) (p : MvPolynomial σ k) :
    (MvPolynomial.aeval g p).totalDegree ≤ p.weightedTotalDegree w := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p, map_sum]
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro d hd
  exact (totalDegree_aeval_monomial_le w g hg d (p.coeff d)).trans
    (MvPolynomial.le_weightedTotalDegree w hd)

theorem translatedPowerSubstitution_totalDegree (w : σ → ℕ) (a : σ → k)
    (p : MvPolynomial σ k) :
    (translatedPowerSubstitution w a p).totalDegree ≤ p.weightedTotalDegree w := by
  apply totalDegree_aeval_le_weighted
  intro i
  exact (MvPolynomial.totalDegree_add _ _).trans (by simp)

noncomputable def translation (a : σ → k) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (a i) + MvPolynomial.X i)

theorem translatedPowerSubstitution_factor (w : σ → ℕ) (a : σ → k) :
    translatedPowerSubstitution w a =
      (MvPolynomial.aeval (fun i => MvPolynomial.X i ^ w i)).comp (translation a) := by
  ext i
  simp [translatedPowerSubstitution, translation]

noncomputable def translationEquiv (a : σ → k) : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k :=
  AlgEquiv.ofAlgHom (translation a) (translation (-a))
    (by ext i; simp [translation])
    (by ext i; simp [translation])

noncomputable def pointIdeal (a : σ → k) : Ideal (MvPolynomial σ k) :=
  RingHom.ker (MvPolynomial.aeval a).toRingHom

instance pointIdeal_isMaximal (a : σ → k) : (pointIdeal a).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  exact ⟨MvPolynomial.C c, by simp⟩

@[simp] theorem mem_pointIdeal (a : σ → k) (p : MvPolynomial σ k) :
    p ∈ pointIdeal a ↔ MvPolynomial.aeval a p = 0 := Iff.rfl

theorem pointIdeal_eq_span (a : σ → k) :
    pointIdeal a = Ideal.span (Set.range (fun i =>
      MvPolynomial.X i - MvPolynomial.C (a i))) := by
  let J : Ideal (MvPolynomial σ k) := Ideal.span (Set.range (fun i =>
    MvPolynomial.X i - MvPolynomial.C (a i)))
  have hJ : J ≤ pointIdeal a := by
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    simp
  apply le_antisymm _ hJ
  have heval : Ideal.Quotient.mk J =
      ((Ideal.Quotient.mk J).comp MvPolynomial.C).comp (MvPolynomial.aeval a).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X]
      apply sub_eq_zero.mp
      rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨i, rfl⟩
  intro p hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [heval]
  simp only [RingHom.comp_apply]
  change (Ideal.Quotient.mk J) (MvPolynomial.C (MvPolynomial.aeval a p)) = 0
  rw [(mem_pointIdeal a p).mp hp, map_zero, map_zero]

theorem translatedPowerSubstitution_eval_origin (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) :
    (MvPolynomial.aeval (0 : σ → k)).comp (translatedPowerSubstitution w a) =
      MvPolynomial.aeval a := by
  ext i
  simp [translatedPowerSubstitution, zero_pow (hw i).ne']

theorem translatedPowerSubstitution_comap_origin (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) :
    (pointIdeal (0 : σ → k)).comap (translatedPowerSubstitution w a).toRingHom =
      pointIdeal a := by
  ext p
  change MvPolynomial.aeval (0 : σ → k) (translatedPowerSubstitution w a p) = 0 ↔ _
  have h := congrArg (fun f : MvPolynomial σ k →ₐ[k] k => f p)
    (translatedPowerSubstitution_eval_origin w a hw)
  change MvPolynomial.aeval (0 : σ → k) (translatedPowerSubstitution w a p) =
    MvPolynomial.aeval a p at h
  rw [h]
  rfl

theorem prime_over_pointIdeal_eq_origin (w : σ → ℕ) (a : σ → k)
    (Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (hQ : pointIdeal a ≤ Q.comap (translatedPowerSubstitution w a).toRingHom) :
    Q = pointIdeal (0 : σ → k) := by
  have hle : pointIdeal (0 : σ → k) ≤ Q := by
    rw [pointIdeal_eq_span]
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    have hi : MvPolynomial.X i - MvPolynomial.C (a i) ∈ pointIdeal a := by simp
    have hp := hQ hi
    change translatedPowerSubstitution w a (MvPolynomial.X i - MvPolynomial.C (a i)) ∈ Q at hp
    have hpow : MvPolynomial.X i ^ w i ∈ Q := by
      simpa only [map_sub, translatedPowerSubstitution_X, translatedPowerSubstitution_C,
        add_sub_cancel_left] using hp
    change MvPolynomial.X i - MvPolynomial.C (0 : k) ∈ Q
    rw [MvPolynomial.C_0, sub_zero]
    exact (inferInstance : Q.IsPrime).mem_of_pow_mem (w i) hpow
  exact ((inferInstance : (pointIdeal (0 : σ → k)).IsMaximal).eq_of_le
    (inferInstance : Q.IsPrime).ne_top hle).symm

theorem pointIdeal_map_translatedPowerSubstitution (w : σ → ℕ) (a : σ → k) :
    (pointIdeal a).map (translatedPowerSubstitution w a).toRingHom =
      Ideal.span (Set.range (fun i => (MvPolynomial.X i : MvPolynomial σ k) ^ w i)) := by
  rw [pointIdeal_eq_span, Ideal.map_span, ← Set.range_comp]
  congr 2
  funext i
  change translatedPowerSubstitution w a (MvPolynomial.X i - MvPolynomial.C (a i)) = _
  simp

theorem translatedPowerSubstitution_totalDegree_real (w : σ → ℕ) (a : σ → k)
    (ρ : σ → ℝ) (M N : ℝ) (hM : 0 ≤ M) (hMN : 0 ≤ M * N)
    (hw : ∀ i, (w i : ℝ) = M * ρ i) (p : MvPolynomial σ k)
    (hp : ∀ d ∈ p.support, (∑ i ∈ d.support, (d i : ℝ) * ρ i) ≤ N) :
    ((translatedPowerSubstitution w a p).totalDegree : ℝ) ≤ M * N := by
  have hb : p.weightedTotalDegree w ≤ ⌊M * N⌋₊ := by
    apply Finset.sup_le
    intro d hd
    apply (Nat.le_floor_iff hMN).mpr
    calc
      (Finsupp.weight w d : ℝ) = M * ∑ i ∈ d.support, (d i : ℝ) * ρ i := by
        rw [Finsupp.weight_apply]
        simp only [Finsupp.sum, smul_eq_mul, Nat.cast_sum, Nat.cast_mul]
        simp_rw [hw]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ M * N := mul_le_mul_of_nonneg_left (hp d hd) hM
  have hd := (translatedPowerSubstitution_totalDegree w a p).trans hb
  exact (Nat.cast_le.mpr hd).trans (Nat.floor_le hMN)

theorem origin_minimalPrimes_map (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) (I : Ideal (MvPolynomial σ k))
    (hI : pointIdeal a ∈ I.minimalPrimes) :
    pointIdeal (0 : σ → k) ∈
      (I.map (translatedPowerSubstitution w a).toRingHom).minimalPrimes := by
  let φ := (translatedPowerSubstitution w a).toRingHom
  have hc : (pointIdeal (0 : σ → k)).comap φ = pointIdeal a :=
    translatedPowerSubstitution_comap_origin w a hw
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · apply Ideal.map_le_iff_le_comap.mpr
    rw [hc]
    exact hI.1.2
  · intro Q hQ hQle
    let : Q.IsPrime := hQ.1
    have hIQ : I ≤ Q.comap φ := Ideal.map_le_iff_le_comap.mp hQ.2
    have hQP : Q.comap φ ≤ pointIdeal a := by
      rw [← hc]
      exact Ideal.comap_mono hQle
    have hPQ : pointIdeal a ≤ Q.comap φ := hI.2 ⟨inferInstance, hIQ⟩ hQP
    have heq := prime_over_pointIdeal_eq_origin w a Q hPQ
    exact heq.symm.le

end PiExponent.WeightedBezout

end OAI
