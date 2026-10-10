import OAI.Probability.InvariantIsing.Spectral.SpectralExcess
import Mathlib.Topology.Order.Lattice

namespace OAI

/-! Continuity of the finite nonempty spectral excess. -/
noncomputable section
namespace InvariantIsing

lemma spectralExcess_eq_max_sup {n : ℕ} (eig : Fin (n+1) → ℝ) (a b : ℝ) :
    spectralExcess eig a b = max 0
      (Finset.univ.sup' Finset.univ_nonempty (fun i => max (a-eig i) (eig i-b))) := by
  classical
  unfold spectralExcess
  rw [Finset.max'_insert _ _ (Finset.univ_nonempty.image _),Finset.max'_eq_sup',Finset.sup'_image]
  rfl

lemma continuous_spectralExcess {X : Type*} [TopologicalSpace X] {n : ℕ}
    (eig : X → Fin (n+1) → ℝ) (heig : ∀ i, Continuous (fun x => eig x i)) (a b : ℝ) :
    Continuous (fun x => spectralExcess (eig x) a b) := by
  simp_rw [spectralExcess_eq_max_sup]
  exact continuous_const.max (Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun i _ => (continuous_const.sub (heig i)).max ((heig i).sub continuous_const)))

end InvariantIsing

end

end OAI
