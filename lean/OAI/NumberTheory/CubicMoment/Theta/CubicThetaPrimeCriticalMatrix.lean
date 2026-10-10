import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeAdditiveGauss
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDeterminant
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace OAI

/-! The finite three-class matrix built from the critical geometric shell
sums and the two cubic Gauss factors. This proves the algebraic rank-one
calculation in the tame cubic case of Deligne, Bourbaki 539, §§6.5--6.7.
Its identification with the local action on the global residue is separate. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimeCriticalShellSum (p : Eisenstein) : ℂ :=
  ∑' k : ℕ, ((norm p:ℂ)⁻¹)^k

lemma cubicThetaPrimeCriticalShellSum_eq {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCriticalShellSum p=(1-(norm p:ℂ)⁻¹)⁻¹ := by
  apply tsum_geometric_of_norm_lt_one
  rw [norm_inv,Complex.norm_of_nonneg (norm_nonneg p)]
  exact (inv_lt_one₀ (norm_pos_of_ne_zero hp.2.ne_zero)).mpr
    (cubicThetaPrimaryPrime_norm_gt_one hp)

lemma cubicThetaPrimeCriticalShellSum_cancel {p : Eisenstein} (hp : primaryPrime p) :
    (1-(norm p:ℂ)⁻¹)*cubicThetaPrimeCriticalShellSum p=1 := by
  rw [cubicThetaPrimeCriticalShellSum_eq hp]
  apply mul_inv_cancel₀
  intro hz
  have hq : (norm p:ℂ)⁻¹≠1 := by
    rw [inv_ne_one]
    exact_mod_cast (ne_of_gt (cubicThetaPrimaryPrime_norm_gt_one hp))
  exact hq (sub_eq_zero.mp hz).symm

def cubicThetaPrimeCriticalMatrix (p : Eisenstein) (hp : primaryPrime p)
    (h : Eisenstein) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(1-(norm p:ℂ)⁻¹)*cubicThetaPrimeCriticalShellSum p,
       cubicThetaPrimeAdditiveGauss p hp 1 h/(norm p:ℂ),0;
     cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ),
       (norm p:ℂ)⁻¹*((1-(norm p:ℂ)⁻¹)*cubicThetaPrimeCriticalShellSum p),0;
     0,0,(norm p:ℂ)⁻¹^2*((1-(norm p:ℂ)⁻¹)*cubicThetaPrimeCriticalShellSum p-1)]

lemma cubicThetaPrimeCriticalMatrix_eq {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) : cubicThetaPrimeCriticalMatrix p hp h=
      !![1,cubicThetaPrimeAdditiveGauss p hp 1 h/(norm p:ℂ),0;
         cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ),(norm p:ℂ)⁻¹,0;
         0,0,0] := by
  unfold cubicThetaPrimeCriticalMatrix
  rw [cubicThetaPrimeCriticalShellSum_cancel hp]
  simp

lemma cubicThetaPrimeCriticalMatrix_mulVec {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (v : Fin 3 → ℂ) :
    (cubicThetaPrimeCriticalMatrix p hp h).mulVec v=
      ![v 0+(cubicThetaPrimeAdditiveGauss p hp 1 h/(norm p:ℂ))*v 1,
        (cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ))*v 0+(norm p:ℂ)⁻¹*v 1,0] := by
  rw [cubicThetaPrimeCriticalMatrix_eq hp]
  ext i
  fin_cases i <;> simp [Matrix.mulVec,Matrix.vecHead,Matrix.vecTail]

lemma cubicThetaPrimeCriticalMatrix_range_relation {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) (v : Fin 3 → ℂ) :
    ((cubicThetaPrimeCriticalMatrix p hp h).mulVec v) 1=
      (cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ))*
        ((cubicThetaPrimeCriticalMatrix p hp h).mulVec v) 0 := by
  rw [cubicThetaPrimeCriticalMatrix_mulVec hp]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  have hg := cubicThetaPrimeAdditiveGauss_product hp h hh
  field_simp
  linear_combination -v 1*hg

theorem cubicThetaPrimeCriticalMatrix_range_iff {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) (w : Fin 3 → ℂ) :
    (∃ v : Fin 3 → ℂ, (cubicThetaPrimeCriticalMatrix p hp h).mulVec v=w) ↔
      w 1=(cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ))*w 0 ∧ w 2=0 := by
  constructor
  · rintro ⟨v,rfl⟩
    refine ⟨cubicThetaPrimeCriticalMatrix_range_relation hp h hh v,?_⟩
    rw [cubicThetaPrimeCriticalMatrix_mulVec hp]
    rfl
  · rintro ⟨h1,h2⟩
    refine ⟨![w 0,0,0],?_⟩
    rw [cubicThetaPrimeCriticalMatrix_mulVec hp]
    ext i
    fin_cases i <;> simp [h1,h2]

end CubicFirstMoment

end

end OAI
