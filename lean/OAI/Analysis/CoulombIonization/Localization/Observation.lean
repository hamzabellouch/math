import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.AnnularCellGeometryBarrier
import OAI.Analysis.CoulombIonization.Localization.FiniteCellObservation

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Filter Set
open scoped BigOperators

def SplitPositionSupport {N M : ℕ} (psi : FormVector (N+M)) (P Q : Space → Prop) : Prop :=
  ∀ (s : Spins N) (t : Spins M) (x : Configuration N) (v : Configuration M),
    psi.value (joinLists s t) (joinLists x v) ≠ 0 → (∀ i, P (x i)) ∧ (∀ i, Q (v i))

lemma orderedCutForm_nonzero_factors {N : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2=1)
    (psi : FormVector N) (c : Fin N → Fin 2)
    (s : Spins (cutCoreNumber c)) (t : Spins (cutOutNumber c))
    (x : Configuration (cutCoreNumber c)) (v : Configuration (cutOutNumber c))
    (hn : (orderedCutForm p hp psi c).value (joinLists s t) (joinLists x v) ≠ 0) :
    psi.value (joinLists s t ∘ (cutOrder c).symm) (joinLists x v ∘ (cutOrder c).symm) ≠ 0 ∧
    (∀ i, (p 0).value (x i) ≠ 0) ∧ (∀ i, (p 1).value (v i) ≠ 0) := by
  have hv := hn
  rw [orderedCutForm_value] at hv
  change (spatialProductValue p (coreCutLabels (cutCoreNumber c) (cutOutNumber c))
    (joinLists x v) : ℂ)*_ ≠ 0 at hv
  have hprod : spatialProductValue p (coreCutLabels (cutCoreNumber c) (cutOutNumber c))
      (joinLists x v) ≠ 0 := by
    intro hh
    exact hv (by rw [hh,Complex.ofReal_zero,zero_mul])
  refine ⟨(mul_ne_zero_iff.mp hv).2,?_,?_⟩
  · intro i hi
    apply hprod
    apply Finset.prod_eq_zero (Finset.mem_univ (finSumFinEquiv (Sum.inl i)))
    simpa only [coreCutLabels,joinLists_left] using hi
  · intro i hi
    apply hprod
    apply Finset.prod_eq_zero (Finset.mem_univ (finSumFinEquiv (Sum.inr i)))
    simpa only [coreCutLabels,joinLists_right] using hi

lemma SplitPositionSupport.observe {N M : ℕ} {psi : FormVector (N+M)} {P Q : Space → Prop}
    (hs : SplitPositionSupport psi P Q)
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2=1)
    (hQ : ∀ z, (p 1).value z ≠ 0 → Q z) (c : Fin N → Fin 2) :
    SplitPositionSupport (nextCoreObservation p hp psi c)
      (fun z => P z ∧ (p 0).value z ≠ 0) Q := by
  intro s t x v hn
  have htn : t = joinLists (leftList t) (rightList t) := (join_list_parts t).symm
  have hvn : v = joinLists (leftList v) (rightList v) := (join_list_parts v).symm
  have hh : (orderedCutForm p hp (coreSlice psi (rightList t) (rightList v)) c).value
      (joinLists s (leftList t)) (joinLists x (leftList v)) ≠ 0 := by
    change (coreSlice (nextCoreObservation p hp psi c) t v).value s x ≠ 0 at hn
    conv at hn => lhs; arg 1; rw [htn,hvn,nextCoreObservation_slice]
    exact hn
  obtain ⟨hpsi,hcore,hout⟩ := orderedCutForm_nonzero_factors p hp _ c s (leftList t) x (leftList v) hh
  obtain ⟨hP,hQold⟩ := hs _ _ _ _ hpsi
  refine ⟨fun i => ⟨?_,hcore i⟩,?_⟩
  · have hi := hP (cutOrder c (finSumFinEquiv (Sum.inl i)))
    simpa only [Function.comp_apply,Equiv.symm_apply_apply,joinLists_left] using hi
  · intro i
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
    cases j with
    | inl j => exact hQ _ (hout j)
    | inr j => exact hQold j

lemma SplitPositionSupport.mono {N M : ℕ} {psi : FormVector (N+M)} {P Q P' Q' : Space → Prop}
    (hs : SplitPositionSupport psi P Q) (hP : ∀ z, P z → P' z) (hQ : ∀ z, Q z → Q' z) :
    SplitPositionSupport psi P' Q' := by
  intro s t x v hn
  obtain ⟨hx,hv⟩ := hs s t x v hn
  exact ⟨fun i => hP _ (hx i),fun i => hQ _ (hv i)⟩

namespace CoreObservationGraph
 def supported (G : CoreObservationGraph) (P Q : Space → Prop) : Prop :=
    SplitPositionSupport G.vector P Q
 lemma initial_supported {N : ℕ} (psi : FormVector N) (hpsi : SobolevFermion psi) (Q : Space → Prop) :
    (initial psi hpsi).supported (fun _ => True) Q := by
    intro s t x v hn
    exact ⟨fun _ => trivial,fun i => Fin.elim0 i⟩
 lemma observe_supported (G : CoreObservationGraph) {P Q : Space → Prop}
    (hs : G.supported P Q) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2=1) (hQ : ∀ z, (p 1).value z ≠ 0 → Q z)
    (c : Fin G.coreSize → Fin 2) :
    (G.observe p hp c).supported (fun z => P z ∧ (p 0).value z ≠ 0) Q :=
    hs.observe p hp hQ c
end CoreObservationGraph
namespace CoreObservationEnsemble
 def supported (E : CoreObservationEnsemble) (P Q : Space → Prop) : Prop :=
    ∀ i, (E.graph i).supported P Q
 lemma initial_supported {N : ℕ} (psi : FormVector N) (hpsi : SobolevFermion psi) (Q : Space → Prop) :
    (initial psi hpsi).supported (fun _ => True) Q :=
    fun _ => CoreObservationGraph.initial_supported psi hpsi Q
 lemma observe_supported (E : CoreObservationEnsemble) {P Q : Space → Prop}
    (hs : E.supported P Q) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2=1) (hQ : ∀ z, (p 1).value z ≠ 0 → Q z) :
    (E.observe p hp).supported (fun z => P z ∧ (p 0).value z ≠ 0) Q :=
    fun ic => (hs ic.1).observe p hp hQ ic.2
end CoreObservationEnsemble

end
open MeasureTheory Set

lemma cell_core_nonzero_distance {y z : Space} (hy : y ≠ 0)
    (hn : (coreFirstRadialCut y (localCellRadius_pos hy).le (localCellRadius_pos hy) 0).value z ≠ 0) :
    localCellRadius y ≤ ‖z-y‖ := by
  by_contra hh
  exact hn (coreFirstRadialCut_core_zero y (localCellRadius_pos hy).le
    (localCellRadius_pos hy) z hh)

lemma cell_out_nonzero_norm {u : ℝ} (hu : 0 < u) {y z : Space}
    (hy : y ≠ 0) (hlo : u/2 ≤ ‖y‖)
    (hn : (coreFirstRadialCut y (localCellRadius_pos hy).le (localCellRadius_pos hy) 1).value z ≠ 0) :
    u/4 ≤ ‖z‖ := by
  have hd : ‖z-y‖ < localCellRadius y+localCellRadius y := by
    by_contra! hh
    exact hn (coreFirstRadialCut_out_zero y (localCellRadius_pos hy).le (localCellRadius_pos hy) z hh)
  have ht := norm_le_norm_sub_add y z
  rw [norm_sub_rev y z] at ht
  unfold localCellRadius at hd
  linarith

namespace CoreObservationEnsemble
lemma observeCells_supported (E : CoreObservationEnsemble) {P Q : Space → Prop}
    (hE : E.supported P Q) (ys : List Space)
    (hys : ∀ y ∈ ys, ∃ hy : y ≠ 0, ∀ z,
      (coreFirstRadialCut y (localCellRadius_pos hy).le (localCellRadius_pos hy) 1).value z ≠ 0 → Q z) :
    (E.observeCells ys).supported (fun z => P z ∧ ∀ y ∈ ys, localCellRadius y ≤ ‖z-y‖) Q := by
  induction ys generalizing E P with
  | nil =>
    exact fun i => (hE i).mono (fun _ h => ⟨h,by simp⟩) (fun _ h => h)
  | cons y ys ih =>
    obtain ⟨hy,hQ⟩ := hys y (List.mem_cons_self ..)
    have hs : (E.observeCell y).supported (fun z => P z ∧ localCellRadius y ≤ ‖z-y‖) Q := by
      rw [observeCell,dite_eq_right hy]
      intro i
      exact ((E.observe_supported hE _ _ hQ) i).mono
        (fun z h => ⟨h.1,cell_core_nonzero_distance hy h.2⟩) (fun _ h => h)
    have hh := ih _ hs (fun z hz => hys z (List.mem_cons_of_mem y hz))
    intro i
    exact (hh i).mono (fun z h => ⟨h.1.1,fun w hw => by
      rcases List.mem_cons.mp hw with rfl | hw
      · exact h.1.2
      · exact h.2 w hw⟩) (fun _ h => h)

lemma annular_stencil_support {N : ℕ} (psi : FormVector N) (hpsi : SobolevFermion psi)
    {u : ℝ} (hu : 0 < u) (ys : List Space)
    (hys : ∀ y ∈ ys, u/2 ≤ ‖y‖)
    (hcover : ∀ z : Space, u/2 ≤ ‖z‖ → ‖z‖ ≤ 4*u → ∃ y ∈ ys, ‖z-y‖ < localCellRadius y) :
    ((initial psi hpsi).observeCells ys).supported
      (fun z => ¬(u/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 4*u)) (fun z => u/4 ≤ ‖z‖) := by
  have hs := (initial psi hpsi).observeCells_supported (initial_supported psi hpsi (fun z => u/4 ≤ ‖z‖)) ys
    (by
      intro y hy
      have hn : y ≠ 0 := norm_pos_iff.mp (by linarith [hys y hy])
      refine ⟨hn,fun z hz => cell_out_nonzero_norm hu hn (hys y hy) hz⟩)
  intro i
  exact (hs i).mono (fun z hz h => by
    obtain ⟨y,hy,hd⟩ := hcover z h.1 h.2
    exact (not_lt_of_ge (hz.2 y hy)) hd) (fun _ h => h)
end CoreObservationEnsemble

lemma exists_scaled_shell_stencil :
    ∃ L : ℕ, ∀ u : ℝ, 0 < u → ∃ ys : List Space,
      ys.length = L ∧ (∀ y ∈ ys, u/2 ≤ ‖y‖ ∧ ‖y‖ ≤ 4*u) ∧
      ∀ z : Space, u/2 ≤ ‖z‖ → ‖z‖ ≤ 4*u → ∃ y ∈ ys, ‖z-y‖ < localCellRadius y := by
  classical
  obtain ⟨T,hT,hcover⟩ := exists_annularCellStencil (by norm_num : (0:ℝ)<1/2) 4
  refine ⟨T.card,fun u hu => ⟨(T.toList.map (fun v => u • v)),by simp,?_,?_⟩⟩
  · intro y hy
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hy
    have hvT := hT v (Finset.mem_toList.mp hv)
    rw [norm_smul,Real.norm_of_nonneg hu.le]
    constructor <;> nlinarith [hvT.1,hvT.2]
  · intro z hz hz4
    obtain ⟨y,hy,hd⟩ := annularCell_scaled_cover hu T hcover (by linarith) hz4
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    exact ⟨u • v,List.mem_map.mpr ⟨v,Finset.mem_toList.mpr hv,rfl⟩,hd⟩

end CoulombAtom

end

end OAI
