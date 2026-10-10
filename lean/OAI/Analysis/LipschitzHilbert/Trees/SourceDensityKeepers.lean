import OAI.Analysis.LipschitzHilbert.Estimates.TopAreaAverage
import Mathlib.Data.Finset.Max
import Mathlib.MeasureTheory.Measure.Real

namespace OAI

/-! Decreasing-length selection of the actual spatial and angular density
tests. Keeper witnesses are disjoint even when their spatial boxes overlap. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

def densitySpatialBox (T : SlopeBox) (K : ℝ) : Set (ℝ×ℝ) :=
  {z | |z.1-T.x| ≤ K*T.length ∧
    |(z.2-T.y)-T.slope*(z.1-T.x)| ≤ K*T.width}

def densityTest (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (T : SlopeBox)
    (omega : Set ℝ) (K : ℝ) : Set (ℝ×ℝ) :=
  E ∩ densitySpatialBox T K ∩ u ⁻¹' omega

def densityConflict {ι : Type*} (T : ι → SlopeBox) (omega : ι → Set ℝ)
    (K : ℝ) (i j : ι) : Prop :=
  (densitySpatialBox (T i) K ∩ densitySpatialBox (T j) K).Nonempty ∧
    (omega i ∩ omega j).Nonempty

theorem densityConflict_symm {ι : Type*} (T : ι → SlopeBox) (omega : ι → Set ℝ)
    (K : ℝ) {i j : ι} (h : densityConflict T omega K i j) :
    densityConflict T omega K j i := by
  simpa only [densityConflict,inter_comm] using h

theorem densityTest_disjoint_of_not_conflict {ι : Type*}
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (T : ι → SlopeBox)
    (omega : ι → Set ℝ) (K : ℝ) {i j : ι}
    (h : ¬densityConflict T omega K i j) :
    Disjoint (densityTest E u (T i) (omega i) K)
      (densityTest E u (T j) (omega j) K) := by
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  exact h ⟨⟨z,hzi.1.2,hzj.1.2⟩,⟨u z,hzi.2,hzj.2⟩⟩

theorem exists_density_keepers {ι : Type*} (candidates : Finset ι)
    (T : ι → SlopeBox) (omega : ι → Set ℝ) (K : ℝ) (hK : 0 ≤ K)
    (homega : ∀ i ∈ candidates, (omega i).Nonempty) :
    ∃ keepers : Finset ι, keepers ⊆ candidates ∧
      (∀ i ∈ keepers, ∀ j ∈ keepers, i ≠ j → ¬densityConflict T omega K i j) ∧
      (∀ i ∈ candidates, ∃ j ∈ keepers,
        (T i).length ≤ (T j).length ∧ densityConflict T omega K i j) := by
  classical
  induction candidates using Finset.strongInductionOn with
  | _ candidates ih =>
    by_cases hnonempty : candidates.Nonempty
    · obtain ⟨top,htop,hmax⟩ := candidates.exists_max_image (fun i => (T i).length) hnonempty
      have hself : densityConflict T omega K top top := by
        obtain ⟨s,hs⟩ := homega top htop
        refine ⟨⟨((T top).x,(T top).y),?_,?_⟩,⟨s,hs,hs⟩⟩ <;>
          simp only [densitySpatialBox,mem_ofPred_eq,sub_self,mul_zero,abs_zero]
        · exact ⟨mul_nonneg hK (T top).length_pos.le,mul_nonneg hK (T top).width_pos.le⟩
        · exact ⟨mul_nonneg hK (T top).length_pos.le,mul_nonneg hK (T top).width_pos.le⟩
      let rest := candidates.filter fun i => ¬densityConflict T omega K top i
      have hrest : rest ⊂ candidates := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.filter_subset _ _,?_⟩
        intro heq
        have : top ∈ rest := heq.symm ▸ htop
        exact (Finset.mem_filter.mp this).2 hself
      obtain ⟨keepers,hsub,hdisj,hcover⟩ := ih rest hrest
        (fun i hi => homega i (Finset.mem_filter.mp hi).1)
      refine ⟨insert top keepers,?_,?_,?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact htop
        · exact (Finset.mem_filter.mp (hsub hi)).1
      · intro i hi j hj hij
        rcases Finset.mem_insert.mp hi with hieq | hi'
        · subst i
          rcases Finset.mem_insert.mp hj with hjeq | hj'
          · exact (hij hjeq.symm).elim
          · exact (Finset.mem_filter.mp (hsub hj')).2
        · rcases Finset.mem_insert.mp hj with hjeq | hj'
          · subst j
            intro hconflict
            exact (Finset.mem_filter.mp (hsub hi')).2 (densityConflict_symm T omega K hconflict)
          · exact hdisj i hi' j hj' hij
      · intro i hi
        by_cases hc : densityConflict T omega K top i
        · exact ⟨top,Finset.mem_insert_self _ _,hmax i hi,densityConflict_symm T omega K hc⟩
        · obtain ⟨j,hj,hlen,hconflict⟩ := hcover i (Finset.mem_filter.mpr ⟨hi,hc⟩)
          exact ⟨j,Finset.mem_insert_of_mem hj,hlen,hconflict⟩
    · refine ⟨∅,Finset.empty_subset _,?_,?_⟩
      · simp
      · intro i hi
        exact (hnonempty ⟨i,hi⟩).elim

theorem density_keeper_area_budget {ι : Type*} (keepers : Finset ι)
    (T : ι → SlopeBox) (omega : ι → Set ℝ) (K eta : ℝ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (heta : 0 < eta)
    (hE : (volume.prod volume) E ≠ ∞)
    (hdisj : ∀ i ∈ keepers, ∀ j ∈ keepers, i ≠ j → ¬densityConflict T omega K i j)
    (hmeas : ∀ i ∈ keepers, MeasurableSet (densityTest E u (T i) (omega i) K))
    (hmass : ∀ i ∈ keepers, eta*(T i).area ≤
      (volume.prod volume).real (densityTest E u (T i) (omega i) K)) :
    ∑ i ∈ keepers, (T i).area ≤ (volume.prod volume).real E / eta := by
  have hsub (i : ι) : densityTest E u (T i) (omega i) K ⊆ E := fun _ hz => hz.1.1
  have hfinite (i : ι) : (volume.prod volume) (densityTest E u (T i) (omega i) K) ≠ ∞ :=
    measure_ne_top_of_subset (hsub i) hE
  have hpair : Set.PairwiseDisjoint (keepers : Set ι)
      (fun i => densityTest E u (T i) (omega i) K) := by
    intro i hi j hj hij
    exact densityTest_disjoint_of_not_conflict E u T omega K (hdisj i hi j hj hij)
  have hsum : (∑ i ∈ keepers, (volume.prod volume).real (densityTest E u (T i) (omega i) K)) ≤
      (volume.prod volume).real E := by
    rw [← measureReal_biUnion_finset hpair hmeas (fun i _ => hfinite i)]
    apply measureReal_mono _ hE
    intro z hz
    obtain ⟨i,hi,hz⟩ := mem_iUnion₂.mp hz
    exact hsub i hz
  apply (le_div_iff₀ heta).mpr
  calc
    (∑ i ∈ keepers, (T i).area)*eta = ∑ i ∈ keepers, eta*(T i).area := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ keepers, (volume.prod volume).real (densityTest E u (T i) (omega i) K) :=
      Finset.sum_le_sum hmass
    _ ≤ _ := hsum

end LipschitzHilbert

end

end OAI
