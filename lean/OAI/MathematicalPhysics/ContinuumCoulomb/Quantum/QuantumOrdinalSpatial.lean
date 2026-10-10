import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialExchange
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrdinalPlacement

namespace OAI

/-! Replace the abstract default slots by the explicit ordinal choice on the
encoded spin and interaction labels. The finite Hamiltonian is unchanged. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

namespace QMACellSlots
 def transport {Q R : Type*} {rows width A : ℕ} {cell : Q → QMAGridCell rows width}
    (e : Q ≃ R) (S : QMACellSlots (cell ∘ e.symm) A) : QMACellSlots cell A where
  index q := S.index (e q)
  injective := by
    intro q r hc hs
    apply e.injective
    apply S.injective _ hs
    simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hc
end QMACellSlots

private theorem relabel_density {Q R : Type*} [Fintype Q] [Fintype R]
    {rows width A : ℕ} (cell : Q → QMAGridCell rows width)
    (hd : ∀ p, (Finset.univ.filter (fun q => cell q=p)).card ≤ A) (e : Q ≃ R)
    (p : QMAGridCell rows width) :
    (Finset.univ.filter (fun r => (cell ∘ e.symm) r=p)).card ≤ A := by
  let f : {q // cell q=p} ≃ {r // (cell ∘ e.symm) r=p} :=
    Equiv.subtypeEquiv e (by intro q; simp)
  have hh := Fintype.card_congr f
  simp only [Fintype.card_subtype] at hh
  rw [← hh]
  exact hd p

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

 def withOrdinalSlots {m : ℕ} (labels : M.Term ≃ Fin m) : QMASpatialExchangeModel A B :=
  { M with
    qubitSlots := QuantumOrdinalPlacement.slots M.cell M.qubitDensity
    termSlots := (QuantumOrdinalPlacement.slots (M.anchor ∘ labels.symm)
      (relabel_density M.anchor M.termDensity labels)).transport labels }

@[simp] theorem withOrdinalSlots_energy {m : ℕ} (labels : M.Term ≃ Fin m) :
    (M.withOrdinalSlots labels).energy = M.energy := rfl

@[simp] theorem withOrdinalSlots_qubit_index {m : ℕ} (labels : M.Term ≃ Fin m) (q : Fin M.n) :
    ((M.withOrdinalSlots labels).qubitSlots.index q).val =
      QuantumOrdinalSlots.rank (QuantumOrdinalPlacement.coordinates M.cell) q := rfl

@[simp] theorem withOrdinalSlots_term_index {m : ℕ} (labels : M.Term ≃ Fin m) (e : M.Term) :
    ((M.withOrdinalSlots labels).termSlots.index e).val =
      QuantumOrdinalSlots.rank (QuantumOrdinalPlacement.coordinates (M.anchor ∘ labels.symm))
        (labels e) := rfl

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
