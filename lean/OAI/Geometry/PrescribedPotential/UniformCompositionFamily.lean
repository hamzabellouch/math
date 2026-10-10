import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.HigherJetComposition
import OAI.Geometry.PrescribedPotential.QuasilinearJetBasics

namespace OAI

/-! Uniform Composition Family. -/

section

noncomputable section
open Set Filter Topology Finset
open scoped ContDiff
namespace HigherJet
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma composition_family_jets {I : Type*} (f : I → E → F) {K : Set E}
    (hf : ∀ i x, x ∈ K → ContDiffAt ℝ ∞ (f i) x)
    (hjet : ∀ m : ℕ, ∃ C : ℝ, ∀ i x, x ∈ K → ‖iteratedFDeriv ℝ m (f i) x‖ ≤ C)
    {Q : Set F} (hQ : IsCompact Q) (hrange : ∀ i x, x ∈ K → f i x ∈ Q)
    (g : F → G) (hg : ∀ y ∈ Q, ContDiffAt ℝ ∞ g y) (m : ℕ) :
    ∃ C : ℝ, ∀ i x, x ∈ K → ‖iteratedFDeriv ℝ m (g ∘ f i) x‖ ≤ C := by
  classical
  choose C hC using hjet
  let B := 1+∑ j ∈ range (m+1), max 0 (C j)
  have hB : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  have hbound (i : I) (x : E) (hx : x ∈ K) (j : ℕ) (hj : j ≤ m) : ‖iteratedFDeriv ℝ j (f i) x‖ ≤ B := by
    exact (hC j i x hx).trans ((le_max_right _ _).trans ((Finset.single_le_sum
      (fun _ _ => le_max_left _ _) (mem_range.mpr (by omega))).trans (le_add_of_nonneg_left zero_le_one)))
  obtain ⟨A,hA,hAj⟩ := compact_coefficient_jets hQ hg m
  refine ⟨(Fintype.card (OrderedFinpartition m):ℝ)*A*B^m*1,fun i x hx => ?_⟩
  exact composition_top_jet_bound (hf i x hx) (hg _ (hrange i x hx)) (r := m+1)
    (by omega) hB le_rfl (by linarith) (fun j hj hjm => hbound i x hx j (by omega))
    (fun j hj hjm => (by omega)) (fun j hj => hAj j hj _ (hrange i x hx))

lemma pair_fixed_family_jets {I : Type*} (f : I → E → F) {v : E → G} {K : Set E}
    (hK : IsCompact K) (hf : ∀ i x, x ∈ K → ContDiffAt ℝ ∞ (f i) x)
    (hv : ∀ x ∈ K, ContDiffAt ℝ ∞ v x)
    (hjet : ∀ m : ℕ, ∃ C : ℝ, ∀ i x, x ∈ K → ‖iteratedFDeriv ℝ m (f i) x‖ ≤ C)
    (m : ℕ) : ∃ C : ℝ, ∀ i x, x ∈ K →
      ‖iteratedFDeriv ℝ m (fun y => (v y,f i y)) x‖ ≤ C := by
  obtain ⟨C,hC⟩ := hjet m
  obtain ⟨B,hB,hbound⟩ := compact_coefficient_jets hK hv m
  refine ⟨max B C,fun i x hx => ?_⟩
  rw [iteratedFDeriv_prodMk (hv x hx) (hf i x hx)
    (show (m:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top),ContinuousMultilinearMap.opNorm_prod]
  exact max_le_max (hbound m le_rfl x hx) (hC i x hx)

lemma parametric_composition_family_jets [FiniteDimensional ℝ F] {I : Type*}
    (f : I → E → F) {K : Set E} (hK : IsCompact K)
    (hf : ∀ i x, x ∈ K → ContDiffAt ℝ ∞ (f i) x)
    (hjet : ∀ m : ℕ, ∃ C : ℝ, ∀ i x, x ∈ K → ‖iteratedFDeriv ℝ m (f i) x‖ ≤ C)
    (g : E × F → G) (hg : ∀ x ∈ K, ∀ y, ContDiffAt ℝ ∞ g (x,y)) (m : ℕ) :
    ∃ C : ℝ, ∀ i x, x ∈ K → ‖iteratedFDeriv ℝ m (fun y => g (y,f i y)) x‖ ≤ C := by
  obtain ⟨R,hR⟩ := hjet 0
  let Q := K ×ˢ Metric.closedBall (0:F) (max 0 R)
  have hQ : IsCompact Q := hK.prod (isCompact_closedBall _ _)
  let ff : I → E → E × F := fun i x => (x,f i x)
  have hff : ∀ i x, x ∈ K → ContDiffAt ℝ ∞ (ff i) x := fun i x hx => contDiffAt_id.prodMk (hf i x hx)
  apply composition_family_jets ff hff (pair_fixed_family_jets f hK hf (fun _ _ => contDiffAt_id) hjet) hQ
  · intro i x hx
    exact ⟨hx,by simpa only [Metric.mem_closedBall,dist_zero_right,norm_iteratedFDeriv_zero] using
      (hR i x hx).trans (le_max_right 0 R)⟩
  · rintro ⟨x,y⟩ hxy
    exact hg x hxy.1 y
end HigherJet

end
end

end OAI
