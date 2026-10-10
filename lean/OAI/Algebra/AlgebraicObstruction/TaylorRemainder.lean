import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.Differentiation

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
open scoped Classical
variable {R σ κ : Type*} [CommRing R] [Fintype κ]

noncomputable def monomialFactor (m : κ → σ →₀ ℕ) (f : MvPowerSeries σ R)
    (j : κ) : MvPowerSeries σ R := fun e => by
  classical
  exact if h : ∃ k, m k ≤ e + m j then
    if j = h.choose then coeff (e + m j) f else 0 else 0

 theorem coeff_monomialFactor (m : κ → σ →₀ ℕ) (f : MvPowerSeries σ R)
    (j : κ) (e : σ →₀ ℕ) :
    coeff e (monomial (m j) 1 * monomialFactor m f j) =
      if h : ∃ k, m k ≤ e then if j = h.choose then coeff e f else 0 else 0 := by
  classical
  rw [coeff_monomial_mul]
  by_cases hj : m j ≤ e
  · rw [ite_eq_left hj]
    simp only [one_mul, monomialFactor, coeff_apply, tsub_add_cancel_of_le hj]
  · rw [ite_eq_right hj]
    split_ifs with h heq
    · exact (hj (heq ▸ h.choose_spec)).elim
    all_goals rfl

 theorem monomial_factorization (m : κ → σ →₀ ℕ) (f : MvPowerSeries σ R)
    (hzero : ∀ e, (¬ ∃ k, m k ≤ e) → coeff e f = 0) :
    f = ∑ j, monomial (m j) 1 * monomialFactor m f j := by
  classical
  ext e
  simp only [map_sum, coeff_monomialFactor]
  by_cases h : ∃ k, m k ≤ e
  · simp only [dite_eq_left h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · simp only [dite_eq_right h, Finset.sum_const_zero, hzero e h]

 theorem monomialFactor_vanishes (m : κ → σ →₀ ℕ) (f : MvPowerSeries σ R)
    {a b : ℕ} (hf : Vanishes (a+b) f) (hm : ∀ j, (m j).degree = b) (j : κ) :
    Vanishes a (monomialFactor m f j) := by
  classical
  intro e he
  change (if h : ∃ k, m k ≤ e + m j then
    if j = h.choose then coeff (e + m j) f else 0 else 0) = 0
  split_ifs
  · apply hf
    simp only [map_add, hm]
    omega
  all_goals rfl

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
variable {R σ τ ι : Type*} [CommRing R]

theorem constantCoeff_killCompl (e : σ ↪ τ) (f : MvPowerSeries τ R) :
    constantCoeff (killCompl e f) = constantCoeff f := by
  change coeff 0 (killCompl e f) = coeff 0 f
  rw [coeff_killCompl, Finsupp.embDomain_zero]

theorem Jet.killCompl {n : ℕ} {f g : MvPowerSeries τ R}
    (e : σ ↪ τ) (h : Jet n f g) : Jet n (killCompl e f) (killCompl e g) := by
  apply Jet.iff_coeff.mpr
  intro d hd
  simp only [coeff_killCompl]
  apply Jet.iff_coeff.mp h
  simpa only [Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain] using hd

theorem killCompl_subst [Finite σ] [Finite τ] [Finite ι]
    (e : σ ↪ τ) (a : ι → MvPowerSeries τ R)
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries ι R) :
    killCompl e (subst a f) = subst (fun i => killCompl e (a i)) f := by
  classical
  ext d
  have hb : ∀ i, constantCoeff (killCompl e (a i)) = 0 := by
    intro i; rw [constantCoeff_killCompl, ha]
  let p := truncTotal (d.degree+1) f
  have hp : Jet (d.degree+1) f p.toMvPowerSeries := jet_trunc _ _
  have hl := (Jet.subst_series a ha hp).killCompl e
  have hr := Jet.subst_series (fun i => killCompl e (a i)) hb hp
  rw [Jet.iff_coeff.mp hl d (Nat.lt_succ_self _),
      Jet.iff_coeff.mp hr d (Nat.lt_succ_self _)]
  simp only [subst_coe, MvPolynomial.comp_aeval_apply]

def dropExponent (e : (σ ⊕ τ) →₀ ℕ) : σ →₀ ℕ :=
  e.comapDomain Sum.inl Sum.inl_injective.injOn

theorem embed_dropExponent (e : (σ ⊕ τ) →₀ ℕ) (h : ∀ i, e (Sum.inr i) = 0) :
    Finsupp.embDomain (Function.Embedding.inl : σ ↪ σ ⊕ τ) (dropExponent e) = e := by
  classical
  ext i
  cases i with
  | inl i => exact Finsupp.embDomain_apply_self _ _ i
  | inr i => simp [h]

theorem coeff_eq_zero_of_killCompl (f : MvPowerSeries (σ ⊕ τ) R)
    (hf : killCompl (Function.Embedding.inl : σ ↪ σ ⊕ τ) f = 0)
    (e : (σ ⊕ τ) →₀ ℕ) (he : ∀ i, e (Sum.inr i) = 0) : coeff e f = 0 := by
  have h := congrArg (coeff (dropExponent e)) hf
  simpa only [coeff_killCompl, embed_dropExponent e he, map_zero] using h

theorem single_le_exponent (i : σ) (e : σ →₀ ℕ) (h : 1 ≤ e i) :
    Finsupp.single i 1 ≤ e := (Finsupp.single_le_iff).mpr h

theorem no_delta_coeff (f : MvPowerSeries (σ ⊕ τ) R)
    (hf : killCompl (Function.Embedding.inl : σ ↪ σ ⊕ τ) f = 0)
    (e : (σ ⊕ τ) →₀ ℕ)
    (he : ¬ ∃ i : τ, Finsupp.single (Sum.inr i) 1 ≤ e) : coeff e f = 0 := by
  apply coeff_eq_zero_of_killCompl f hf e
  intro i
  have hi : ¬ 1 ≤ e (Sum.inr i) := fun hi => he ⟨i, single_le_exponent _ _ hi⟩
  omega

theorem no_two_delta_coeff (f : MvPowerSeries (σ ⊕ τ) R)
    (hf : killCompl (Function.Embedding.inl : σ ↪ σ ⊕ τ) f = 0)
    (hd : ∀ i, killCompl (Function.Embedding.inl : σ ↪ σ ⊕ τ) (MvPowerSeries.pderiv (R := R) (Sum.inr i) f) = 0)
    (e : (σ ⊕ τ) →₀ ℕ)
    (he : ¬ ∃ ij : τ × τ, Finsupp.single (Sum.inr ij.1) 1 + Finsupp.single (Sum.inr ij.2) 1 ≤ e) :
    coeff e f = 0 := by
  classical
  by_cases hone : ∃ i : τ, Finsupp.single (Sum.inr i) 1 ≤ e
  · obtain ⟨i, hi⟩ := hone
    let e' := e - Finsupp.single (Sum.inr i) 1
    have heq : e' + Finsupp.single (Sum.inr i) 1 = e := tsub_add_cancel_of_le hi
    have hz : ∀ j, e' (Sum.inr j) = 0 := by
      intro j
      by_contra hj
      have hj' : Finsupp.single (Sum.inr j) 1 ≤ e' := single_le_exponent _ _ (by omega)
      apply he
      refine ⟨(j,i), ?_⟩
      rw [← heq]
      exact add_le_add hj' le_rfl
    have hcoeff := coeff_eq_zero_of_killCompl _ (hd i) e' hz
    simpa only [coeff_pderiv, hz, Nat.cast_zero, zero_add, mul_one, heq] using hcoeff
  · exact no_delta_coeff f hf e hone

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
open scoped Classical
variable {R α ι : Type*} [CommRing R]

abbrev Extended := (α ⊕ ι) ⊕ ι

def baseArguments : (α ⊕ ι) → MvPowerSeries (Extended (α := α) (ι := ι)) R :=
  fun i => X (Sum.inl i)

def shiftedArguments : (α ⊕ ι) → MvPowerSeries (Extended (α := α) (ι := ι)) R :=
  Sum.elim (fun a => X (Sum.inl (Sum.inl a)))
    (fun i => X (Sum.inl (Sum.inr i)) + X (Sum.inr i))

theorem baseArguments_centered [Fintype α] [Fintype ι] (i : α ⊕ ι) :
    constantCoeff (baseArguments (R := R) i) = 0 := by simp [baseArguments]

theorem shiftedArguments_centered [Fintype α] [Fintype ι] (i : α ⊕ ι) :
    constantCoeff (shiftedArguments (R := R) i) = 0 := by
  cases i <;> simp [shiftedArguments]

abbrev dropDelta : MvPowerSeries (Extended (α := α) (ι := ι)) R →ₐ[R] MvPowerSeries (α ⊕ ι) R :=
  killCompl (Function.Embedding.inl : (α ⊕ ι) ↪ (α ⊕ ι) ⊕ ι)

theorem dropDelta_baseArguments [Fintype α] [Fintype ι] (i : α ⊕ ι) :
    dropDelta (baseArguments (R := R) i) = X i := by
  exact killCompl_X i

theorem dropDelta_X [Fintype α] [Fintype ι] (i : ι) :
    dropDelta (X (Sum.inr i) : MvPowerSeries (Extended (α := α)) R) = 0 := by
  apply killCompl_X_eq_zero
  simp

variable [Fintype α] [Fintype ι]

theorem dropDelta_shiftedArguments (i : α ⊕ ι) :
    dropDelta (shiftedArguments (R := R) i) = X i := by
  cases i with
  | inl i => exact dropDelta_baseArguments (Sum.inl i)
  | inr i =>
    change dropDelta (baseArguments (Sum.inr i) + X (Sum.inr i)) = _
    rw [map_add, dropDelta_baseArguments, dropDelta_X, add_zero]

theorem dropDelta_subst_base (f : MvPowerSeries (α ⊕ ι) R) :
    dropDelta (subst baseArguments f) = f := by
  rw [killCompl_subst _ _ baseArguments_centered]
  simp only [dropDelta_baseArguments, subst_self, id_eq]

theorem dropDelta_subst_shifted (f : MvPowerSeries (α ⊕ ι) R) :
    dropDelta (subst shiftedArguments f) = f := by
  rw [killCompl_subst _ _ shiftedArguments_centered]
  simp only [dropDelta_shiftedArguments, subst_self, id_eq]

theorem pderiv_delta_subst_base (f : MvPowerSeries (α ⊕ ι) R) (i : ι) :
    MvPowerSeries.pderiv (R := R) (Sum.inr i) (subst baseArguments f) = 0 := by
  rw [pderiv_subst _ baseArguments_centered]
  simp [baseArguments]

theorem pderiv_delta_subst_shifted (f : MvPowerSeries (α ⊕ ι) R) (i : ι) :
    MvPowerSeries.pderiv (R := R) (Sum.inr i) (subst shiftedArguments f) =
      subst shiftedArguments (MvPowerSeries.pderiv (R := R) (Sum.inr i) f) := by
  rw [pderiv_subst _ shiftedArguments_centered, Fintype.sum_sum_type]
  simp [shiftedArguments, MvPowerSeries.pderiv_X, Pi.single_apply]

noncomputable def universalDifference (f : MvPowerSeries (α ⊕ ι) R) : MvPowerSeries (Extended (α := α) (ι := ι)) R :=
  subst shiftedArguments f - subst baseArguments f

noncomputable def universalRemainder (f : MvPowerSeries (α ⊕ ι) R) : MvPowerSeries (Extended (α := α) (ι := ι)) R :=
  universalDifference f - ∑ i : ι, X (Sum.inr i) * subst baseArguments (MvPowerSeries.pderiv (R := R) (Sum.inr i) f)

theorem dropDelta_difference (f : MvPowerSeries (α ⊕ ι) R) :
    dropDelta (universalDifference f) = 0 := by
  simp only [universalDifference, map_sub, dropDelta_subst_base, dropDelta_subst_shifted, sub_self]

theorem dropDelta_remainder (f : MvPowerSeries (α ⊕ ι) R) :
    dropDelta (universalRemainder f) = 0 := by
  simp only [universalRemainder, map_sub, dropDelta_difference, map_sum, map_mul,
    dropDelta_X, zero_mul, Finset.sum_const_zero, sub_zero]

theorem dropDelta_pderiv_remainder (f : MvPowerSeries (α ⊕ ι) R) (i : ι) :
    dropDelta (MvPowerSeries.pderiv (R := R) (Sum.inr i) (universalRemainder f)) = 0 := by
  simp [universalRemainder, universalDifference, map_sub, map_sum,
    Derivation.leibniz, smul_eq_mul, pderiv_delta_subst_base, pderiv_delta_subst_shifted,
    dropDelta_subst_shifted, dropDelta_subst_base, MvPowerSeries.pderiv_X, Pi.single_apply]

theorem universalDifference_vanishes {n : ℕ} (f : MvPowerSeries (α ⊕ ι) R) (hf : Vanishes n f) :
    Vanishes n (universalDifference f) := by
  simpa only [universalDifference, sub_eq_add_neg] using
    (hf.subst _ shiftedArguments_centered).add (hf.subst _ baseArguments_centered).neg

theorem universalRemainder_vanishes (f : MvPowerSeries (α ⊕ ι) R) (hf : Vanishes 3 f) :
    Vanishes 3 (universalRemainder f) := by
  unfold universalRemainder
  rw [sub_eq_add_neg]
  apply (universalDifference_vanishes f hf).add
  apply Vanishes.neg
  apply Vanishes.sum
  intro i _
  have hx : Vanishes 1 (X (Sum.inr i) : MvPowerSeries (Extended (α := α)) R) :=
    Vanishes.one_iff.mpr (by simp)
  exact hx.mul ((hf.pderiv (Sum.inr i)).subst _ baseArguments_centered)

theorem exists_taylor_remainder (f : MvPowerSeries (α ⊕ ι) R) (hf : Vanishes 3 f) :
    ∃ H : Matrix ι ι (MvPowerSeries (Extended (α := α)) R),
      (∀ i j, Vanishes 1 (H i j)) ∧
      subst shiftedArguments f = subst baseArguments f +
        (∑ i, X (Sum.inr i) * subst baseArguments (MvPowerSeries.pderiv (R := R) (Sum.inr i) f)) +
        ∑ i, ∑ j, X (Sum.inr i) * H i j * X (Sum.inr j) := by
  let m : (ι × ι) → (Extended (α := α)) →₀ ℕ :=
    fun ij => Finsupp.single (Sum.inr ij.1) 1 + Finsupp.single (Sum.inr ij.2) 1
  let H : Matrix ι ι (MvPowerSeries (Extended (α := α)) R) :=
    fun i j => monomialFactor m (universalRemainder f) (i,j)
  have hH : ∀ i j, Vanishes 1 (H i j) := by
    intro i j
    apply monomialFactor_vanishes m _ (a := 1) (b := 2) (universalRemainder_vanishes f hf)
    intro ij
    simp [m]
  have hfac := monomial_factorization m (universalRemainder f)
    (no_two_delta_coeff _ (dropDelta_remainder f) (dropDelta_pderiv_remainder f))
  have hm (i j : ι) : monomial (m (i,j)) (1 : R) = X (Sum.inr i) * X (Sum.inr j) := by
    simp only [m, X, monomial_mul_monomial, one_mul]
  refine ⟨H,hH,?_⟩
  have heq : universalRemainder f = ∑ i, ∑ j, X (Sum.inr i) * H i j * X (Sum.inr j) := by
    rw [hfac, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hm]
    dsimp [H]
    ring
  dsimp [universalRemainder, universalDifference] at heq
  linear_combination heq

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
open scoped Classical
variable {R α ι : Type*} [CommRing R] [Fintype α] [Fintype ι]

theorem exists_first_remainder (f : MvPowerSeries (α ⊕ ι) R) :
    ∃ q : ι → MvPowerSeries (Extended (α := α) (ι := ι)) R,
      (∀ n, Vanishes (n+1) f → ∀ i, Vanishes n (q i)) ∧
      subst shiftedArguments f - subst baseArguments f = ∑ i, q i * X (Sum.inr i) := by
  let m : ι → (Extended (α := α) (ι := ι)) →₀ ℕ := fun i => Finsupp.single (Sum.inr i) 1
  let q := monomialFactor m (universalDifference f)
  refine ⟨q, ?_, ?_⟩
  · intro n hf i
    exact monomialFactor_vanishes m _ (universalDifference_vanishes f hf)
      (fun j => Finsupp.degree_single _ _) i
  · have hfac := monomial_factorization m (universalDifference f)
      (no_delta_coeff _ (dropDelta_difference f))
    change universalDifference f = _
    rw [hfac]
    apply Finset.sum_congr rfl
    intro i _
    change X (Sum.inr i) * q i = q i * X (Sum.inr i)
    exact mul_comm _ _

theorem exists_gradient_remainder (f : MvPowerSeries (α ⊕ ι) R) (hf : Vanishes 3 f) :
    ∃ G : Matrix ι ι (MvPowerSeries (Extended (α := α)) R),
      (∀ i j, Vanishes 1 (G i j)) ∧
      (∀ i, subst shiftedArguments (MvPowerSeries.pderiv (R := R) (Sum.inr i) f) -
          subst baseArguments (MvPowerSeries.pderiv (R := R) (Sum.inr i) f) =
        ∑ j, G i j * X (Sum.inr j)) := by
  choose G hG hdiff using fun i : ι => exists_first_remainder (MvPowerSeries.pderiv (R := R) (Sum.inr i) f)
  exact ⟨G, fun i j => hG i 1 (hf.pderiv _) j, hdiff⟩

end BoundaryOnly.FormalObstruction.FormalCorrection

end

end OAI
