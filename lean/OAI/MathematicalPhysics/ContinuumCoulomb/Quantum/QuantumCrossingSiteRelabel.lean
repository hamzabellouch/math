import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSiteProgram

namespace OAI

/-! The terminal scan is independent of the finite vertex enumeration.
It returns the actual terminal in the emitted position tape. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSiteProgram
open QuantumRouteCode QuantumCrossingListBlock
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) {D : ℕ} (hD : ∀ e, P.length e ≤ D) {n : ℕ}
    (σ : Fin n ≃ Fin (P.finishedGraph N D).n) (pos : Fin n → Pair)
    (hpos : ∀ v, P.finishedPosition N D (σ v)=pos v)

include hpos in
theorem relabeled_injective : Function.Injective pos := by
  intro v w h
  apply σ.injective
  apply (P.toEmbedding.iterate N D).position_injective
  change P.finishedPosition N D (σ v)=P.finishedPosition N D (σ w)
  rw [hpos,hpos]
  exact h

include hpos in
theorem terminal_relabeled (i : Fin P.crossingCells.card) (a : Fin 4) :
    terminal a (List.ofFn pos,(P.crossingCell i).val)=
      (σ.symm (P.crossingSiteFin N hD i a)).val := by
  have hp : pos (σ.symm (P.crossingSiteFin N hD i a))=
      qmaGridPort (P.crossingCell i).val (qmaPatchDirection a) := by
    rw [← hpos,Equiv.apply_symm_apply]
    exact P.crossingSite_spec N hD (P.crossingCell i) (qmaPatchDirection a)
  unfold terminal target
  rw [← hp]
  exact index_ofFn pos (relabeled_injective P N σ pos hpos) _

include hpos in
theorem sites_relabeled (i : Fin P.crossingCells.card) :
    sites (List.ofFn pos,(P.crossingCell i).val)=
      QuantumCrossingSelectProgram.encodedSites
        (fun i a => σ.symm (P.crossingSiteFin N hD i a)) i := by
  simp only [sites,terminal_relabeled P N hD σ pos hpos,
    QuantumCrossingSelectProgram.encodedSites]

include hpos in
theorem allSites_relabeled :
    allSites (List.ofFn pos,List.ofFn (fun i => (P.crossingCell i).val))=
      List.ofFn (QuantumCrossingSelectProgram.encodedSites
        (fun i a => σ.symm (P.crossingSiteFin N hD i a))) := by
  simp only [allSites,List.map_ofFn,Function.comp_def,sites_relabeled P N hD σ pos hpos]

theorem relabeled_sites_global : Function.Injective
    (fun t : Fin P.crossingCells.card × Fin 4 => σ.symm (P.crossingSiteFin N hD t.1 t.2)) := by
  intro x y h
  exact P.crossingSiteFin_global N hD (σ.symm.injective h)

include hpos in
theorem allSites_reordered {r : ℕ} (τ : Fin r ≃ Fin P.crossingCells.card) :
    allSites (List.ofFn pos,List.ofFn (fun i => (P.crossingCell (τ i)).val))=
      List.ofFn (QuantumCrossingSelectProgram.encodedSites
        (fun i a => σ.symm (P.crossingSiteFin N hD (τ i) a))) := by
  simp only [allSites,List.map_ofFn,Function.comp_def,sites_relabeled P N hD σ pos hpos]
  apply congrArg List.ofFn
  funext i
  rfl

theorem reordered_sites_global {r : ℕ} (τ : Fin r ≃ Fin P.crossingCells.card) :
    Function.Injective
      (fun t : Fin r × Fin 4 => σ.symm (P.crossingSiteFin N hD (τ t.1) t.2)) := by
  exact (relabeled_sites_global P N hD σ).comp
    (Equiv.prodCongr τ (Equiv.refl (Fin 4))).injective

end ContinuumCoulomb.QuantumCrossingSiteProgram

end

end OAI
