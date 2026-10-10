import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingListLayer

namespace OAI

/-! The literal crossing packet has exactly the sites, scale and scalar
shift of the rational crossing layer used by the spectral comparison. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListLayer
open QuantumCrossingListBlock
open scoped BigOperators Classical

def actualCrossing {r : ℕ} (C : QMARationalCrossingLayer r) (i : Fin r) : Crossing :=
  ((C.J i,C.K i),((C.site i 0).val,(C.site i 1).val),
    ((C.site i 2).val,(C.site i 3).val))
def actualInput {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) : Input :=
  ((N,C.base.n,QuantumListGraph.packed C.base labels,C.base.constant),
    List.ofFn (actualCrossing C))

theorem site_actual {r : ℕ} (C : QMARationalCrossingLayer r) (i : Fin r) (a : Fin 4) :
    site (actualCrossing C i).2 a=(C.site i a).val := by
  fin_cases a <;> rfl

theorem scaleInput_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    scaleInput (actualInput C N labels)=QuantumCrossingScaleProgram.actualInput C N labels := by
  simp only [scaleInput,actualInput,QuantumListGraph.packed,List.map_ofFn]
  rfl

theorem parameters_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    parameters (actualInput C N labels)=(C.base.n,C.scale N) := by
  unfold parameters
  rw [scaleInput_actual,QuantumCrossingScaleProgram.value_actual]
  rfl

theorem count_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    count (actualInput C N labels)=(C.output N).n := by
  simp only [count,actualInput,List.length_ofFn,QMARationalCrossingLayer.output]
  omega

theorem constant_actual {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    constant (actualInput C N labels)=(C.output N).constant := by
  unfold constant familyInput
  rw [parameters_actual]
  change C.base.constant+familyOffset ((C.base.n,C.scale N),List.ofFn (actualCrossing C)) = _
  simp only [familyOffset,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  change C.base.constant+(∑ i, (3/2+3*(C.J i)^2+3*(C.K i)^2+3*(C.scale N)^2)) =
    (C.base.constant+∑ i, (3/2+3*(C.J i)^2+3*(C.K i)^2))+3*(r:ℚ)*(C.scale N)^2
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem sites_bounded {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    ∀ c ∈ (actualInput C N labels).2, ∀ a, site c.2 a < (actualInput C N labels).1.2.1 := by
  intro c hc a
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
  rw [site_actual]
  exact (C.site i a).isLt

theorem sites_injective {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) :
    ∀ c ∈ (actualInput C N labels).2, Function.Injective (site c.2) := by
  intro c hc
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
  intro a b hab
  rw [site_actual,site_actual] at hab
  exact C.injective i (Fin.ext hab)

def actualGraph {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ) {m : ℕ}
    (labels : C.base.Edge ≃ Fin m) : QMARationalExchangeGraph :=
  graph (actualInput C N labels) (QuantumListGraph.packed_bounded C.base labels)
    (QuantumListGraph.packed_noLoops C.base labels)
    (sites_bounded C N labels) (sites_injective C N labels)

end ContinuumCoulomb.QuantumCrossingListLayer

end

end OAI
