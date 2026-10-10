import OAI.Analysis.Mahler.SourceRawCoefficient
import OAI.Analysis.Mahler.RawReindexedDerivative
import OAI.Analysis.Mahler.SourceCoordinateForms

namespace OAI

open ContinuousAlternatingMap
namespace Mahler
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma rawPrefix_firstJet [FiniteDimensional ℝ E] (A : E →L[ℝ] E →L[ℝ] ℂ) :
    (rawPrefix (rawCovectorVariation (rawLinearJet A))).domDomCongr
      (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2) = rawFirstJet A := by
  ext v
  rfl

omit [FiniteDimensional ℝ E] in
lemma rawProduct_reindex_left [FiniteDimensional ℝ E] {ι κ ι' : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    [DecidableEq ι] [DecidableEq κ] [DecidableEq ι']
    (a : MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (b : MultilinearMap ℝ (fun _ : κ => E) ℂ) (e : ι ≃ ι') :
    (rawProduct a b).domDomCongr (Equiv.sumCongr e (Equiv.refl κ)) =
      rawProduct (a.domDomCongr e) b := by
  ext v
  rfl

lemma rawMain_firstJet (A : E →L[ℝ] E →L[ℝ] ℂ) (k : ℕ) :
    (wedge (rawPrefix (rawCovectorVariation (rawLinearJet A))).alternatization
      (wedgePower (rawFirstJet A).alternatization k)).domDomCongr
      (Equiv.sumCongr (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2)
        (Equiv.refl (WedgePowerSlots k))) =
    wedgePower (rawFirstJet A).alternatization (k+1) := by
  rw [← rawPower_alternatization, ← rawProduct_alternatization,
    ← raw_alternatization_reindex, rawProduct_reindex_left, rawPrefix_firstJet,
    rawProduct_alternatization, rawPower_alternatization]
  rfl

/-- Explicit order of the differentiated top form: first the two slots
created from derivative and one-form, then all existing interleaved pairs. -/
def sourceTopSlots (k : ℕ) : WedgePowerSlots (k+1) ≃ Fin ((2*k+1)+1) :=
  ((Equiv.sumCongr (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2)
      (Equiv.refl (WedgePowerSlots k))).symm.trans
    (Equiv.sumAssoc (Fin 1) (Fin 1) (WedgePowerSlots k))).trans
      ((Equiv.sumCongr (Equiv.refl (Fin 1)) (sourceBoundarySlots k)).trans
        (rawFrontFin (2*k+1)))

end
end Mahler

end OAI
