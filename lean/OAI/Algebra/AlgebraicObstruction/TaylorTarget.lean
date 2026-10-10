import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.Differentiation

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement

theorem sup_pow_pred_le {R : Type*} [CommRing R] (I J : Ideal R)
    (n q : ℕ) (hq : 1 ≤ q) : (I ⊔ J) ^ (n + q - 1) ≤ I ^ n ⊔ J ^ q := by
  rw [← Ideal.add_eq_sup, ← Ideal.add_eq_sup, add_pow, Ideal.sum_eq_sup]
  apply Finset.sup_le
  intro i hi
  by_cases hn : n ≤ i
  · exact (Ideal.mul_le_left.trans (Ideal.mul_le_left.trans
      ((Ideal.pow_le_pow_right hn).trans le_sup_left)))
  · refine (Ideal.mul_le_left.trans (Ideal.mul_le_right.trans
      ((Ideal.pow_le_pow_right ?_).trans le_sup_right)))
    omega

theorem shifted_ideal_cofinal {R : Type*} [CommRing R]
    (J H S : Ideal R) (q : ℕ) (hq : 1 ≤ q) (hS : S ^ q = ⊥)
    (hs : J ⊔ S = H ⊔ S) (N : ℕ) :
    J ^ (N + q - 1) ≤ H ^ N ∧ H ^ (N + q - 1) ≤ J ^ N := by
  constructor
  · calc
      J ^ (N + q - 1) ≤ (J ⊔ S) ^ (N + q - 1) := pow_le_pow_left' le_sup_left _
      _ = (H ⊔ S) ^ (N + q - 1) := by rw [hs]
      _ ≤ H ^ N ⊔ S ^ q := sup_pow_pred_le H S N q hq
      _ = H ^ N := by rw [hS,sup_bot_eq]
  · calc
      H ^ (N + q - 1) ≤ (H ⊔ S) ^ (N + q - 1) := pow_le_pow_left' le_sup_left _
      _ = (J ⊔ S) ^ (N + q - 1) := by rw [hs]
      _ ≤ J ^ N ⊔ S ^ q := sup_pow_pred_le J S N q hq
      _ = J ^ N := by rw [hS,sup_bot_eq]

namespace TaylorTarget
variable (A α : Type*) [CommRing A]

abbrev variablesIdeal : Ideal (MvPolynomial α A) := MvPolynomial.idealOfVars α A
abbrev Ring (q : ℕ) := MvPolynomial α A ⧸ variablesIdeal A α ^ q

def mk (q : ℕ) : MvPolynomial α A →+* Ring A α q := Ideal.Quotient.mk _

def nilIdeal (q : ℕ) : Ideal (Ring A α q) := (variablesIdeal A α).map (mk A α q)

lemma variables_pow (q : ℕ) : nilIdeal A α q ^ q = ⊥ := by
  rw [nilIdeal,← Ideal.map_pow]
  exact Ideal.map_quotient_self _

lemma variables_fg [Finite α] (q : ℕ) : (nilIdeal A α q).FG :=
  (MvPolynomial.idealOfVars_fg α A).map _

lemma variables_ker : variablesIdeal A α = RingHom.ker MvPolynomial.constantCoeff := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    simp
  · intro p hp
    rw [← pow_one (variablesIdeal A α),MvPolynomial.mem_pow_idealOfVars_iff]
    intro e he
    have he0 : e ≠ 0 := by
      intro h
      subst e
      exact (MvPolynomial.mem_support_iff.mp he) hp
    exact Nat.one_le_iff_ne_zero.mpr (by simpa [Finsupp.degree_eq_zero_iff] using he0)

def reduction (q : ℕ) (hq : 1 ≤ q) : Ring A α q →+* A :=
  Ideal.Quotient.lift _ MvPolynomial.constantCoeff (by
    change variablesIdeal A α ^ q ≤ RingHom.ker MvPolynomial.constantCoeff
    rw [← variables_ker]
    exact Ideal.pow_le_self (by omega))

@[simp] lemma reduction_mk (q : ℕ) (hq : 1 ≤ q) (p : MvPolynomial α A) :
    reduction A α q hq (mk A α q p) = MvPolynomial.constantCoeff p := rfl

lemma reduction_surjective (q : ℕ) (hq : 1 ≤ q) :
    Function.Surjective (reduction A α q hq) := fun a ↦
  ⟨mk A α q (MvPolynomial.C a),by simp⟩

lemma reduction_ker (q : ℕ) (hq : 1 ≤ q) :
    RingHom.ker (reduction A α q hq) = nilIdeal A α q := by
  apply Ideal.comap_injective_of_surjective (mk A α q) (Ideal.Quotient.mk_surjective)
  rw [RingHom.comap_ker]
  change RingHom.ker MvPolynomial.constantCoeff = _
  rw [← variables_ker,nilIdeal]
  unfold mk
  rw [Ideal.comap_map_of_surjective _ (Ideal.Quotient.mk_surjective)]
  change _ = variablesIdeal A α ⊔ _
  rw [← RingHom.ker_eq_comap_bot,Ideal.mk_ker]
  exact (sup_eq_left.mpr (Ideal.pow_le_self (by omega))).symm

theorem finite_shifted (R : Type*) [CommRing R] [Algebra R A]
    [Module.Finite R A] [Finite α] (q : ℕ) (hq : 1 ≤ q)
    [halg : Algebra R (Ring A α q)]
    (hred : ∀ r : R, reduction A α q hq (algebraMap R (Ring A α q) r) =
      algebraMap R A r) :
    @Module.Finite R (Ring A α q) _ _ halg.toModule := by
  let f : Ring A α q →ₐ[R] A :=
    { reduction A α q hq with commutes' := hred }
  apply Module.finite_of_surjective_of_ker_le_nilradical f
    (reduction_surjective A α q hq)
  · change RingHom.ker (reduction A α q hq) ≤ _
    rw [reduction_ker]
    exact (variables_fg A α q).isNilpotent_iff_le_nilradical.mp ⟨q,variables_pow A α q⟩
  · change (RingHom.ker (reduction A α q hq)).FG
    rw [reduction_ker]
    exact variables_fg A α q

end TaylorTarget
end BoundaryOnly.FormalObstruction.AlgebraicReplacement

end

end OAI
