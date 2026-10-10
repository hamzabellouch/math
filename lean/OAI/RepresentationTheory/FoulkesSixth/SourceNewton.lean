import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.HomogeneousPlethysm

namespace OAI

noncomputable section

namespace Foulkes.Complete
open MvPolynomial Finset Foulkes.Strips

def degreeCompositionEquiv (n b : ℕ) : Degree (Fin n) b ≃ Composition n b where
  toFun d := ⟨fun j => ⟨d.val j, by
      have hj := Finsupp.le_degree j d.val
      omega⟩, by simpa using (Finsupp.degree_eq_sum d.val).symm.trans d.property⟩
  invFun v := ⟨expVector (fun j => (v.val j).val), by
    rw [Lookup.degree_expVector]
    exact v.property⟩
  left_inv d := by apply Subtype.ext; ext j; rfl
  right_inv v := by apply Subtype.ext; funext j; apply Fin.ext; rfl

lemma powerAlphabet_eq_completePowers (n i b : ℕ) :
    (∑ d : Degree (Fin n) b,
      monomial (i • d.val) (1 : ℤ)) = completePowers n i b := by
  classical
  unfold completePowers
  apply Fintype.sum_equiv (degreeCompositionEquiv n b)
  intro d
  have he : i • d.val = Finsupp.equivFunOnFinite.symm
      (fun j => i*((degreeCompositionEquiv n b d).val j).val) := by
    ext j
    change i * d.val j = i * d.val j
    rfl
  rw [he]

lemma pleth_newton_powers (n j b : ℕ) :
    (j : ℤ) • pleth n j b =
      ∑ i ∈ Finset.Icc 1 j, completePowers n i b * pleth n (j-i) b := by
  simpa only [powerAlphabet_eq_completePowers] using pleth_newton n j b

end Foulkes.Complete

namespace Foulkes.Lookup
open MvPolynomial Finset Foulkes.Strips

def stripCoeff {n : ℕ} (b i : ℕ) (gamma mu : Fin n → ℕ) : ℤ :=
  (completePowers n i b * alternant (shifted mu)).coeff (expVector (shifted gamma))

theorem source_newton (n j b : ℕ) (gamma : Fin n → ℕ) :
    (j : ℤ) * schurCoeff (Complete.pleth n j b) gamma =
      ∑ i ∈ Finset.Icc 1 j,
        ∑ mu : Partition n ((j-i)*b),
          stripCoeff b i gamma (partVec mu) *
            schurCoeff (Complete.pleth n (j-i) b) (partVec mu) := by
  classical
  have hh := congrArg (fun p : MvPolynomial (Fin n) ℤ =>
    (p * alternant (staircase n)).coeff (expVector (shifted gamma)))
      (Complete.pleth_newton_powers n j b)
  change (((j : ℤ) • Complete.pleth n j b) * alternant (staircase n)).coeff
      (expVector (shifted gamma)) = _ at hh
  rw [smul_mul_assoc, coeff_smul] at hh
  simp only [zsmul_eq_mul, Finset.sum_mul, coeff_sum] at hh
  change (j : ℤ) * schurCoeff (Complete.pleth n j b) gamma = _ at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc]
  rw [homogeneous_schur_expansion (d := (j-i)*b) _ (Complete.rename_pleth n (j-i) b)
    (by simpa [Nat.mul_comm] using Complete.homogeneous_pleth n (j-i) b)]
  simp only [Finset.mul_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro mu hmu
  change (completePowers n i b *
    (schurCoeff (Complete.pleth n (j-i) b) (partVec mu) •
      alternant (shifted (partVec mu)))).coeff _ = _
  rw [mul_smul_comm, coeff_smul]
  exact mul_comm _ _

end Foulkes.Lookup

end

end OAI
