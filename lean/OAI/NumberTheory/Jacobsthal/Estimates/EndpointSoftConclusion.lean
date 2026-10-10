import OAI.NumberTheory.Jacobsthal.Partitions.GeometricSelectionHardMass

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEligible
open NumberTheoryLean ErdosVarianceWeighted ErdosVarianceEffective ErdosVarianceSmallPrime ErdosInverseBoxHeight
attribute [local instance] Classical.propDecidable

theorem soft_of_not_guarded_hard (Q : Finset ℚ) (z R theta : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf p : ℕ)
    (Cs eps : ℝ) (hr : r ∈ Q)
    (hH : (effectiveModulus a r qf : ℝ) ≤ R*(sourceZ z)^11)
    (hRatio : effectiveSize a r qf R/(effectiveModulus a r qf : ℝ) ≤ (sourceZ z)^12)
    (hbad : p ∈ badAligningPrimes (ErdosInversePrimeBin.primeBin R theta) (sourceY z) (sourceW z) a r qf eps)
    (hout : p ∉ rawHardPrimeUnion Q z R theta a qf Cs eps) :
    effectiveSize a r qf R < (sourceW z)^Cs := by
  by_contra! hhard
  apply hout
  exact (mem_rawHardPrimeUnion Q z R theta a qf Cs eps p).mpr ⟨r,hr,⟨hH,hRatio,hhard⟩,hbad⟩

theorem soft_guarded_point_eligible (Q : Finset ℚ) (z R theta : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf p : ℕ)
    (Cs eps : ℝ) (hr : r ∈ Q) (hq : Squarefree qf) (hp : p.Prime) (hR : 0 < R)
    (hRp : R ≤ (p : ℝ)) (hw : 2 ≤ sourceW z) (hY : p*qf ≤ sourceY z)
    (hH : (effectiveModulus a r qf : ℝ) ≤ R*(sourceZ z)^11)
    (hRatio : effectiveSize a r qf R/(effectiveModulus a r qf : ℝ) ≤ (sourceZ z)^12)
    (hbad : p ∈ badAligningPrimes (ErdosInversePrimeBin.primeBin R theta) (sourceY z) (sourceW z) a r qf eps)
    (hout : p ∉ rawHardPrimeUnion Q z R theta a qf Cs eps) :
    (r.den : ℝ) ≤ (sourceW z)^Cs ∧ (r.num.natAbs : ℝ) ≤ (sourceY z : ℝ)*(sourceW z)^(Cs+2) ∧
      ∀ t ∈ (p*qf).primeFactors,Cs < Real.logb (sourceW z) (t : ℝ) →
        ErdosInverseAlignment.aligns (fun u => (a u : ℤ)) r t := by
  have hsoft := soft_of_not_guarded_hard Q z R theta a r qf p Cs eps hr hH hRatio hbad hout
  have halign := ((mem_badAligningPrimes _ _ _ _ _ _ _ _).mp hbad).2.1
  exact soft_endpoint_eligible (sourceY z) a r qf hq p hp halign R (sourceW z) Cs hR hRp hw hY hsoft.le

end ErdosVarianceEligible

end

section

namespace ErdosVarianceEligible
open NumberTheoryLean ErdosVarianceWeighted ErdosVarianceEffective ErdosVarianceSmallPrime ErdosInverseBoxHeight
  ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection TwoPrimeObservableSum
attribute [local instance] Classical.propDecidable

theorem endpoint_soft_conclusion {n : ℕ} (Q : Finset ℚ) (top R theta : ℝ) (residue : ℕ → ℕ)
    (f : Fin n → Finset ℕ) (i : Fin n) (r : ℚ) (Cs eps : ℝ)
    (hr : r ∈ Q) (hSq : Squarefree (selectionProduct (eraseSelection f i)))
    (hp : (pickedPrime f i).Prime) (hR : 0 < R) (hRp : R ≤ (pickedPrime f i : ℝ))
    (hw : 2 ≤ sourceW top) (hY : pickedPrime f i*selectionProduct (eraseSelection f i) ≤ sourceY top)
    (hH : (effectiveModulus residue r (selectionProduct (eraseSelection f i)) : ℝ) ≤ R*(sourceZ top)^11)
    (hRatio : effectiveSize residue r (selectionProduct (eraseSelection f i)) R/
      (effectiveModulus residue r (selectionProduct (eraseSelection f i)) : ℝ) ≤ (sourceZ top)^12)
    (hbad : pickedPrime f i ∈ badAligningPrimes (ErdosInversePrimeBin.primeBin R theta) (sourceY top) (sourceW top)
      residue r (selectionProduct (eraseSelection f i)) eps)
    (hout : ¬hardSelection Q top R theta residue i Cs eps f) :
    (r.den : ℝ) ≤ (sourceW top)^Cs ∧ (r.num.natAbs : ℝ) ≤ (sourceY top : ℝ)*(sourceW top)^(Cs+2) ∧
      ∀ t ∈ (pickedPrime f i*selectionProduct (eraseSelection f i)).primeFactors,
        Cs < Real.logb (sourceW top) (t : ℝ) → ErdosInverseAlignment.aligns (fun u => (residue u : ℤ)) r t :=
  soft_guarded_point_eligible Q top R theta residue r (selectionProduct (eraseSelection f i)) (pickedPrime f i)
    Cs eps hr hSq hp hR hRp hw hY hH hRatio hbad hout

end ErdosVarianceEligible

end

end Erdos970

end OAI
