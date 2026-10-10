import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockDensityTensor
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardFermionSpectrum

namespace OAI

/-! The density interaction and its counterterm on the full half-filled
Fock sector, including the scalar off-site Coulomb shift. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock

def directChargeValue {m : ℕ} (U : ℝ) (V : Fin m → Fin m → ℝ)
    (o : Fin m → Fin 3) : ℝ :=
  U / 2 * (∑ i, ((o i : ℕ) : ℝ) * (((o i : ℕ) : ℝ) - 1)) +
    (1 / 2 : ℝ) * (∑ i, ∑ j, V i j * ((o i : ℕ) : ℝ) * ((o j : ℕ) : ℝ)) -
    (∑ i, (∑ j, V i j) * ((o i : ℕ) : ℝ))

def siteChargeOperator (m : ℕ) (U : ℝ) (V : Fin (m+1) → Fin (m+1) → ℝ) :
    Module.End ℂ (Space (2*m+1)) :=
  ((U / 2 : ℝ) : ℂ) • (∑ i, (siteNumber m i * siteNumber m i - siteNumber m i)) +
    (1 / 2 : ℂ) • (∑ i, ∑ j, (V i j : ℂ) • (siteNumber m i * siteNumber m j)) -
    ∑ i, ((∑ j, V i j : ℝ) : ℂ) • siteNumber m i

theorem siteChargeOperator_basis (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ)
    (A : Finset (Fin ((2*m+1)+1))) :
    siteChargeOperator m U V (fockBasis (2*m+1) A) =
      (directChargeValue U V (occupationAt m A) : ℂ) • fockBasis (2*m+1) A := by
  simp only [siteChargeOperator, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply,
    siteNumber_basis, map_smul, smul_smul, ← Finset.sum_smul,
    ← sub_smul, ← add_smul]
  congr 1
  simp only [directChargeValue, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_sum, Complex.ofReal_natCast, Complex.ofReal_one]
  congr 2
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem siteChargeOperator_eq_diagonal (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) :
    siteChargeOperator m U V =
      occupationDiagonal m (fun o => (directChargeValue U V o : ℂ)) := by
  apply (fockBasis (2*m+1)).ext
  intro A
  change siteChargeOperator m U V (fockBasis (2*m+1) A) =
    fockDiagonal (fun B => (directChargeValue U V (occupationAt m B):ℂ)) (fockBasis (2*m+1) A)
  rw [siteChargeOperator_basis,fockDiagonal_basis]

/-- The manuscript's scalar shift holds for every half-filled vector,
including charge defects and arbitrary spectator spins. -/
theorem siteChargeOperator_halfFilled (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (hsymm : ∀ i j, V i j = V j i)
    (x : Space (2*m+1)) (hx : IsHalfFilled m x) :
    siteChargeOperator m U V x = chargePenaltyFock m U V x -
      (((1 / 2 : ℝ) * ∑ i, ∑ j, V i j : ℝ) : ℂ) • x := by
  rw [siteChargeOperator_eq_diagonal]
  apply (fockBasis (2*m+1)).repr.injective
  ext A
  simp only [occupationDiagonal, chargePenaltyFock, fockDiagonal_coordinate,
    map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  by_cases hA : A.card = m+1
  · have hfill : ∑ i, (occupationAt m A i : ℕ) = m+1 :=
      (occupationAt_sum m A).trans hA
    have h := chargePenalty_offset_identity U V (occupationAt m A) hsymm hfill
    change directChargeValue U V (occupationAt m A) = _ at h
    rw [h, Complex.ofReal_sub, sub_mul]
  · rw [hx A hA]
    simp

def modeSite (m : ℕ) (a : Fin ((2*m+1)+1)) : Fin (m+1) :=
  ((siteModes m).symm a).1

theorem oneBodyOperator_siteDiagonal (m : ℕ) (f : Fin (m+1) → ℂ) :
    oneBodyOperator (fun a b => if a=b then f (modeSite m a) else 0) =
      ∑ i, f i • siteNumber m i := by
  unfold oneBodyOperator
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← (siteModes m).sum_comp]
  simp only [Fintype.sum_prod_type, modeSite, Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp only [siteNumber, smul_add, number, siteMode]

theorem densityInteraction_site (m : ℕ) (C : Fin (m+1) → Fin (m+1) → ℂ) :
    densityInteraction (fun a b => C (modeSite m a) (modeSite m b)) =
      ∑ i, ∑ j, C i j • (siteNumber m i * siteNumber m j) := by
  unfold densityInteraction
  rw [← (siteModes m).sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ σ : Fin 2, ∑ j : Fin (m+1), ∑ τ : Fin 2,
        C i j • (number (siteMode m i σ) * number (siteMode m j τ)) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [← (siteModes m).sum_comp]
      simp only [Fintype.sum_prod_type, modeSite, Equiv.symm_apply_apply, siteMode]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Fin.sum_univ_two, siteNumber, add_mul, mul_add, smul_add]
      abel

theorem densityInteraction_remove_self {Q : ℕ}
    (C : Fin (Q+1) → Fin (Q+1) → ℂ) :
    densityInteraction (fun a b => if a=b then 0 else C a b) =
      densityInteraction C - ∑ a, C a a • number a := by
  unfold densityInteraction
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hterm (b : Fin (Q+1)) :
      (if a=b then (0:ℂ) else C a b) • (number a * number b) =
        C a b • (number a * number b) -
          (if b=a then C a a • number a else 0) := by
    by_cases hab : a=b
    · subst b
      simp [number_idempotent]
    · simp [hab, Ne.symm hab]
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

def siteCoulombCoefficient {m : ℕ} (U : ℝ) (V : Fin m → Fin m → ℝ)
    (i j : Fin m) : ℂ := if i=j then (U:ℂ) else (V i j:ℂ)

theorem densityInteraction_siteCoulomb (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (hdiag : ∀ i, V i i = 0) :
    densityInteraction (fun a b => siteCoulombCoefficient U V (modeSite m a) (modeSite m b)) =
      (U:ℂ) • (∑ i, siteNumber m i * siteNumber m i) +
        ∑ i, ∑ j, (V i j:ℂ) • (siteNumber m i * siteNumber m j) := by
  rw [densityInteraction_site]
  have hC (i j : Fin (m+1)) : siteCoulombCoefficient U V i j =
      (if i=j then (U:ℂ) else 0) + (V i j:ℂ) := by
    by_cases hij : i=j
    · subst j
      simp [siteCoulombCoefficient,hdiag]
    · simp [siteCoulombCoefficient,hij]
  simp only [hC, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.smul_sum]

theorem sum_siteCoulomb_self (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) :
    (∑ a, siteCoulombCoefficient U V (modeSite m a) (modeSite m a) • number a) =
      (U:ℂ) • ∑ i, siteNumber m i := by
  simp only [siteCoulombCoefficient, ite_true]
  rw [← (siteModes m).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.smul_sum, siteNumber,
    smul_add, siteMode]

/-- The actual diagonal Coulomb CAR tensor and compensating one-body
matrix are the site-charge polynomial, before restricting particle number. -/
theorem directCoulomb_operator (m : ℕ) (U : ℝ)
    (V : Fin (m+1) → Fin (m+1) → ℝ) (hdiag : ∀ i, V i i = 0) :
    oneBodyOperator (fun a b => if a=b then
        -((∑ j, V (modeSite m a) j : ℝ):ℂ) else 0) +
      twoBodyOperator (fun a b c d => if a=c ∧ b=d then
        siteCoulombCoefficient U V (modeSite m a) (modeSite m b) else 0) =
      siteChargeOperator m U V := by
  rw [oneBodyOperator_siteDiagonal m (fun i => -((∑ j, V i j : ℝ):ℂ)), twoBodyOperator_density,
    densityInteraction_remove_self, densityInteraction_siteCoulomb m U V hdiag,
    sum_siteCoulomb_self]
  have hneg : (∑ i, (-((∑ j, V i j : ℝ):ℂ)) • siteNumber m i) =
      -(∑ i, ((∑ j, V i j : ℝ):ℂ) • siteNumber m i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact neg_smul (((∑ j, V i j : ℝ):ℂ)) (siteNumber m i)
  rw [hneg]
  simp only [siteChargeOperator, Finset.sum_sub_distrib,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  module

end ContinuumCoulomb.HubbardGlobal

end

end OAI
