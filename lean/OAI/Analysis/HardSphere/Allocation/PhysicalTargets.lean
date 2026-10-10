import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalDatum

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

def unitTarget (c : Point) : Set Point :=
  Set.pi Set.univ (fun j ↦ Set.Ico (c j-1/2) (c j+1/2))

lemma unitTarget_measurable (c : Point) : MeasurableSet (unitTarget c) :=
  MeasurableSet.pi (Set.to_countable Set.univ) (fun _ _ ↦ measurableSet_Ico)

lemma unitTarget_volume (c : Point) : volume (unitTarget c)=1 := by
  rw [unitTarget, volume_pi_pi]
  simp only [Real.volume_Ico]
  have he (j : Fin 3) : c j+1/2-(c j-1/2)=(1:ℝ) := by ring
  simp only [he]
  norm_num

lemma unitTarget_radius (c u : Point) (hu : u∈unitTarget c) : ‖u-c‖≤1/2 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1/2)).mpr
  intro j
  have hj := hu j (Set.mem_univ j)
  change |u j-c j|≤1/2
  rw [abs_le]
  constructor <;> linarith [hj.1,hj.2]

def targetStep (j : Fin 7) : Point :=
  if j.val=0 then 0 else fun k ↦
    if k.val=(j.val-1)/2 then (if (j.val-1)%2=0 then 1 else -1) else 0

lemma targetStep_radius (j : Fin 7) : ‖targetStep j‖≤1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  intro k
  unfold targetStep
  change |(if j.val=0 then (0:Point) else fun k ↦
    if k.val=(j.val-1)/2 then (if (j.val-1)%2=0 then 1 else -1) else 0) k|≤1
  split_ifs <;> norm_num
  all_goals split_ifs <;> norm_num

lemma targetCell_radius (c : Point) (j : Fin 7) (u : Point)
    (hu : u∈unitTarget (c+targetStep j)) : ‖u-c‖≤3 := by
  have H := norm_add_le (u-(c+targetStep j)) (targetStep j)
  have he : u-(c+targetStep j)+targetStep j = u-c := by abel
  rw [he] at H
  linarith [unitTarget_radius (c+targetStep j) u hu,targetStep_radius j]

def datumSuccess {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N) :
    PhysicalDatum N K M G L × Point → ℝ≥0∞ := fun p ↦
  trialKernel t (datumStart hL p.1 i) (datumEnd hL p.1 i) p.2
    (Prod.mk p.1 ⁻¹' datumPermitted hL g m r R C S u i)

lemma datumSuccess_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N) :
    Measurable (datumSuccess (M:=M) hL g m t r R C S u i) := by
  let κ := parameterTrialKernel t (fun d : PhysicalDatum N K M G L ↦ datumStart hL d i)
    (fun d ↦ datumEnd hL d i) (datumStart_measurable hL i) (datumEnd_measurable hL i)
  have h := Kernel.measurable_kernel_prodMk_left (κ:=κ)
    (exposedSuccess_measurable (datumPermitted_measurable (M:=M) hL g m r R C S u i))
  convert h using 1
  funext p
  obtain ⟨d,U⟩ := p
  simp only [κ,datumSuccess,parameterTrialKernel_apply]
  rfl

def datumTarget {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N) (j : Fin 7) :
    Set (PhysicalDatum N K M G L × Point) :=
  {p | p.2∈unitTarget (anchorPoint (datumHome hL p.1 i)+targetStep j) ∧
    ENNReal.ofReal (9/10:ℝ)≤datumSuccess hL g m t r R C S u i p}

lemma datumTarget_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N) (j : Fin 7) :
    MeasurableSet (datumTarget (M:=M) hL g m t r R C S u i j) := by
  simp only [datumTarget,Set.ofPred_and]
  apply MeasurableSet.inter
  · have he : {p : PhysicalDatum N K M G L × Point |
        p.2∈unitTarget (anchorPoint (datumHome hL p.1 i)+targetStep j)} =
        ⋂k : Fin 3, {p | anchorPoint (datumHome hL p.1 i) k+targetStep j k-1/2≤p.2 k ∧
        p.2 k<anchorPoint (datumHome hL p.1 i) k+targetStep j k+1/2} := by
      ext p
      simp [unitTarget]
    rw [he]
    apply MeasurableSet.iInter
    intro k
    have hc : Measurable (fun p : PhysicalDatum N K M G L × Point ↦ anchorPoint (datumHome hL p.1 i) k) :=
      ((measurable_pi_apply k).comp ((datumAnchor_measurable (M:=M) hL i).comp measurable_fst))
    exact (measurableSet_le ((hc.add_const _).sub_const _)
      ((measurable_pi_apply k).comp measurable_snd)).inter
        (measurableSet_lt ((measurable_pi_apply k).comp measurable_snd)
          ((hc.add_const _).add_const _))
  · exact measurableSet_le measurable_const (datumSuccess_measurable hL g m t r R C S u i)

def datumAccessible {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N) (d : PhysicalDatum N K M G L) : Prop :=
  ∀j : Fin 7, ENNReal.ofReal (99/100:ℝ)≤
    volume (Prod.mk d ⁻¹' datumTarget hL g m t r R C S u i j)

lemma datumAccessible_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (i : Fin N) :
    MeasurableSet {d : PhysicalDatum N K M G L | datumAccessible hL g m t r R C S u i d} := by
  unfold datumAccessible
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply measurableSet_le measurable_const
  exact Kernel.measurable_kernel_prodMk_left (κ:=Kernel.const (PhysicalDatum N K M G L) volume)
    (datumTarget_measurable hL g m t r R C S u i j)

def datumAccessibleLabels {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (v : Fin 3 → Fin K)
    (d : PhysicalDatum N K M G L) : Finset (Fin N) :=
  (datumSelected g d).filter fun i ↦ datumHome hL d i=v ∧ datumAccessible hL g m t r R C S u i d

lemma datumAccessibleLabels_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) (v : Fin 3 → Fin K) :
    Measurable (datumAccessibleLabels (N:=N) (M:=M) hL g m t r R C S u v) := by
  apply measurable_to_countable'
  intro f
  change MeasurableSet {d | _ = f}
  have he : {d : PhysicalDatum N K M G L | datumAccessibleLabels hL g m t r R C S u v d=f} =
      ⋂i : Fin N, {d | (i∈datumSelected g d ∧ datumHome hL d i=v ∧
        datumAccessible hL g m t r R C S u i d) ↔ i∈f} := by
    ext d
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    rw [Finset.ext_iff]
    simp only [datumAccessibleLabels,Finset.mem_filter]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  have hs : MeasurableSet {d : PhysicalDatum N K M G L | i∈datumSelected g d} := by
    exact (measurable_snd.snd.snd.fst)
      ((Set.to_countable {a : GridAllocation N K (G*M) | i∈groupUnion g a}).measurableSet)
  have hh := hs.inter ((measurableSet_eq_fun (datumHome_measurable hL i) (measurable_const (a:=v))).inter
    (datumAccessible_measurable hL g m t r R C S u i))
  by_cases hi : i∈f
  · simpa only [hi,iff_true,Set.ofPred_and] using hh
  · simpa only [hi,iff_false,Set.ofPred_and,←Set.compl_ofPred] using hh.compl

def datumBad {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time)
    (d : PhysicalDatum N K M G L) : Finset (Fin 3 → Fin K) :=
  Finset.univ.filter fun v ↦ 2*(datumAccessibleLabels hL g m t r R C S u v d).card<M

lemma datumBad_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (g : Fin G)
    (m : ℕ) (t r R C S : ℝ) (u : Time) :
    Measurable (datumBad (N:=N) (M:=M) hL g m t r R C S u) := by
  apply measurable_to_countable'
  intro f
  change MeasurableSet {d | _ = f}
  have he : {d : PhysicalDatum N K M G L | datumBad hL g m t r R C S u d=f} =
    ⋂v : Fin 3 → Fin K, {d | (2*(datumAccessibleLabels hL g m t r R C S u v d).card<M) ↔ v∈f} := by
    ext d
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    rw [Finset.ext_iff]
    simp only [datumBad,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [he]
  apply MeasurableSet.iInter
  intro v
  have hh := (datumAccessibleLabels_measurable (M:=M) hL g m t r R C S u v)
    ((Set.to_countable {s : Finset (Fin N) | 2*s.card<M}).measurableSet)
  by_cases hv : v∈f
  · simpa only [hv,iff_true,Set.preimage_ofPred_eq] using hh
  · simpa only [hv,iff_false,Set.preimage_ofPred_eq,←Set.compl_ofPred] using hh.compl

end HardSphere.Groups
end
end

end OAI
