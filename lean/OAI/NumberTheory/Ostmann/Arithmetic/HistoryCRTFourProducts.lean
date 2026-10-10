import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTProjectedProducts

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCRTIntegration
open ResidueHaar
attribute [local instance 2000] Complex.commRing

def fourRingFactors (A D Q B : ℕ)
    (fA : ZMod A×ZMod A→ℂ) (fD : ZMod D×ZMod D→ℂ)
    (fQ : ZMod Q×ZMod Q→ℂ) (fB : ZMod B×ZMod B→ℂ) :
    ∀i : Fin 4,ZMod (fourModuli A D Q B i)×ZMod (fourModuli A D Q B i)→ℂ :=
  Fin.cases fA (Fin.cases fD (Fin.cases fQ (Fin.cases fB (fun i => Fin.elim0 i))))

@[simp] theorem fourRingFactors_zero (A D Q B : ℕ)
    (fA : ZMod A×ZMod A→ℂ) (fD : ZMod D×ZMod D→ℂ)
    (fQ : ZMod Q×ZMod Q→ℂ) (fB : ZMod B×ZMod B→ℂ) :
    fourRingFactors A D Q B fA fD fQ fB (0:Fin 4) = fA := rfl

@[simp] theorem fourRingFactors_one (A D Q B : ℕ)
    (fA : ZMod A×ZMod A→ℂ) (fD : ZMod D×ZMod D→ℂ)
    (fQ : ZMod Q×ZMod Q→ℂ) (fB : ZMod B×ZMod B→ℂ) :
    fourRingFactors A D Q B fA fD fQ fB (0:Fin 3).succ = fD := rfl

@[simp] theorem fourRingFactors_two (A D Q B : ℕ)
    (fA : ZMod A×ZMod A→ℂ) (fD : ZMod D×ZMod D→ℂ)
    (fQ : ZMod Q×ZMod Q→ℂ) (fB : ZMod B×ZMod B→ℂ) :
    fourRingFactors A D Q B fA fD fQ fB (0:Fin 2).succ.succ = fQ := rfl

@[simp] theorem fourRingFactors_three (A D Q B : ℕ)
    (fA : ZMod A×ZMod A→ℂ) (fD : ZMod D×ZMod D→ℂ)
    (fQ : ZMod Q×ZMod Q→ℂ) (fB : ZMod B×ZMod B→ℂ) :
    fourRingFactors A D Q B fA fD fQ fB (0:Fin 1).succ.succ.succ = fB := rfl

theorem four_unit_projected_product_average (A D Q B : ℕ)
    [NeZero A] [NeZero D] [NeZero Q] [NeZero B] {M : ℕ} [NeZero M]
    (hc : A.Coprime D ∧ A.Coprime Q ∧ A.Coprime B ∧
      D.Coprime Q ∧ D.Coprime B ∧ Q.Coprime B)
    (hd : A*D*Q*B∣M) (hA : A∣M) (hD : D∣M) (hQ : Q∣M) (hB : B∣M)
    (fA : ZMod A×ZMod A→ℂ) (fD : ZMod D×ZMod D→ℂ)
    (fQ : ZMod Q×ZMod Q→ℂ) (fB : ZMod B×ZMod B→ℂ) :
    average (fun z : UnitPair M =>
      fA (projectedRingPair hA ((z.1:ZMod M),(z.2:ZMod M)))*
      fD (projectedRingPair hD ((z.1:ZMod M),(z.2:ZMod M)))*
      fQ (projectedRingPair hQ ((z.1:ZMod M),(z.2:ZMod M)))*
      fB (projectedRingPair hB ((z.1:ZMod M),(z.2:ZMod M)))) =
      average (fun z : UnitPair A => fA (z.1,z.2))*
      average (fun z : UnitPair D => fD (z.1,z.2))*
      average (fun z : UnitPair Q => fQ (z.1,z.2))*
      average (fun z : UnitPair B => fB (z.1,z.2)) := by
  have hp : (∏i,fourModuli A D Q B i)∣M := by rw [fourModuli_prod]; exact hd
  have he := unit_projected_product_average (fourModuli A D Q B)
    (fourModuli_pairwise A D Q B hc) hp (fourRingFactors A D Q B fA fD fQ fB)
  simp only [fourModuli,Fin.prod_univ_succ,fourRingFactors_zero,fourRingFactors_one,
    fourRingFactors_two,fourRingFactors_three,Fin.prod_univ_zero,mul_one,mul_assoc,Matrix.cons_val_zero] at he ⊢
  convert he using 1
  congr 1
  rfl

theorem four_mixed_projected_product_average (A D Q B : ℕ)
    [NeZero A] [NeZero D] [NeZero Q] [NeZero B] {M : ℕ} [NeZero M]
    (hc : A.Coprime D ∧ A.Coprime Q ∧ A.Coprime B ∧
      D.Coprime Q ∧ D.Coprime B ∧ Q.Coprime B)
    (hd : A*D*Q*B∣M) (hA : A∣M) (hD : D∣M) (hQ : Q∣M) (hB : B∣M)
    (fA : ZMod A×ZMod A→ℂ) (fD : ZMod D×ZMod D→ℂ)
    (fQ : ZMod Q×ZMod Q→ℂ) (fB : ZMod B×ZMod B→ℂ) :
    average (fun z : MixedPair M =>
      fA (projectedRingPair hA (z.1,(z.2:ZMod M)))*
      fD (projectedRingPair hD (z.1,(z.2:ZMod M)))*
      fQ (projectedRingPair hQ (z.1,(z.2:ZMod M)))*
      fB (projectedRingPair hB (z.1,(z.2:ZMod M)))) =
      average (fun z : MixedPair A => fA (z.1,z.2))*
      average (fun z : MixedPair D => fD (z.1,z.2))*
      average (fun z : MixedPair Q => fQ (z.1,z.2))*
      average (fun z : MixedPair B => fB (z.1,z.2)) := by
  have hp : (∏i,fourModuli A D Q B i)∣M := by rw [fourModuli_prod]; exact hd
  have he := mixed_projected_product_average (fourModuli A D Q B)
    (fourModuli_pairwise A D Q B hc) hp (fourRingFactors A D Q B fA fD fQ fB)
  simp only [fourModuli,Fin.prod_univ_succ,fourRingFactors_zero,fourRingFactors_one,
    fourRingFactors_two,fourRingFactors_three,Fin.prod_univ_zero,mul_one,mul_assoc,Matrix.cons_val_zero] at he ⊢
  convert he using 1
  congr 1
  rfl

end Ostmann.Arithmetic.HistoryCRTIntegration

end

end OAI
