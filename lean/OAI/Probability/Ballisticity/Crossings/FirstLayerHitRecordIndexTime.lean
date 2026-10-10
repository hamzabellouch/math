import Mathlib
import OAI.Probability.Ballisticity.Geometry.SignedHeight
import OAI.Probability.Ballisticity.Estimates.SurvivingLane

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma firstLayerHit_recordIndexTime {d : ℕ} (e : Direction d) (X : Path d)
    (h0 : X 0 = 0) (hD : X ∈ NoDrop (realPosition (step e)) 0)
    (hnn : ∀ n, ∃ f, X (n+1) = X n+step f) {k n : ℕ} (hk : 0 < k)
    (hX : X ∈ FirstLayerHit (signedHeight e) k n) :
    recordIndexTime (realPosition (step e)) k X = n := by
  let ℓ := realPosition (step e)
  have hs (j : ℕ) : signedHeight e (X (j+1)) ≤ signedHeight e (X j)+1 := by
    obtain ⟨f,hf⟩ := hnn j
    rw [hf]
    exact signedHeight_step_le e _ f
  have hr := firstLayerHit_record ℓ (signedHeight e) (signedHeight_projection e) k n X hX
  have hc := recordCount_eq_height_at_record ℓ (signedHeight e) (signedHeight_projection e) X hs hr
  have hz : signedHeight e (0 : Lattice d) = 0 := by simp [signedHeight]
  have hn : 0 < n := by
    by_contra hh
    have he : n = 0 := by omega
    have hh := hX.1
    rw [he,h0,hz] at hh
    omega
  apply recordIndexTime_eq ℓ k n X
  refine ⟨hn,hr,?_,fun j _ => hD j⟩
  rw [hX.1,h0,hz,zero_add] at hc
  exact_mod_cast hc.symm

lemma noDrop_firstLayerHit_exists {d : ℕ} (e : Direction d) (X : Path d)
    (h0 : X 0 = 0) (hnn : ∀ n, ∃ f, X (n+1) = X n+step f)
    (ht : X ∈ TransientPaths (realPosition (step e))) {k : ℕ} (hk : 0 < k) :
    ∃ n, X ∈ FirstLayerHit (signedHeight e) k n := by
  apply firstLayerHit_exists (signedHeight e) (signedHeight_step_le e) X hnn
  · simpa only [TransientPaths,Set.mem_ofPred_eq,signedHeight_projection] using ht
  · rw [h0]
    simp only [signedHeight,Pi.zero_apply,ite_self,neg_zero]
    exact_mod_cast hk

lemma survivingLane_record_iff {d : ℕ} (e : Direction d) (x : Lattice d)
    (X : Path d) (h0 : X 0 = x) (hD : X ∈ NoDrop (realPosition (step e)) x)
    (hnn : ∀ n, ∃ f, X (n+1) = X n+step f)
    (ht : X ∈ TransientPaths (realPosition (step e))) {k : ℕ} (hk : 0 < k)
    (A : Set (Lattice d)) :
    X ∈ SurvivingLane {z | dot (realPosition x) (realPosition (step e)) ≤
        dot (realPosition z) (realPosition (step e))} (Upper (realPosition (step e)) x k) A ↔
      recordIndexPosition (realPosition (step e)) k (fun j => X j-x)+x ∈ A := by
  let ℓ := realPosition (step e)
  let Y : Path d := fun j => X j-x
  have hy0 : Y 0 = 0 := by simp [Y,h0]
  have hyD : Y ∈ NoDrop ℓ 0 := by
    change X ∈ (fun Z : Path d => fun j => Z j-x) ⁻¹' NoDrop ℓ 0
    rw [noDrop_translation]
    simpa only [add_zero] using hD
  have hyn : ∀ n, ∃ f, Y (n+1) = Y n+step f := by
    intro n
    obtain ⟨f,hf⟩ := hnn n
    refine ⟨f,?_⟩
    simp only [Y,hf]
    abel
  have hyt : Y ∈ TransientPaths ℓ := by
    change Tendsto (fun n => dot (realPosition (X n-x)) ℓ) atTop atTop
    simp only [dot_realPosition_sub]
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-dot (realPosition x) ℓ) ht
  obtain ⟨n,hn⟩ := noDrop_firstLayerHit_exists e Y hy0 hyn hyt hk
  have hi := firstLayerHit_recordIndexTime e Y hy0 hyD hyn hk hn
  have he : recordIndexPosition ℓ k Y+x = X n := by
    change X (recordIndexTime (realPosition (step e)) k Y)-x+x = _
    rw [hi,sub_add_cancel]
  rw [he]
  have hend : dot (realPosition (X n)) ℓ = dot (realPosition x) ℓ+k := by
    have hh := congrArg (fun z : ℤ => (z : ℝ)) hn.1
    rw [← signedHeight_projection e] at hh
    change dot (realPosition (X n-x)) ℓ = (k : ℝ) at hh
    rw [dot_realPosition_sub] at hh
    linarith
  have hpre (j : ℕ) (hj : j < n) : dot (realPosition (X j)) ℓ < dot (realPosition x) ℓ+k := by
    have hh : (signedHeight e (Y j) : ℝ) < (k : ℝ) := by exact_mod_cast hn.2 j hj
    rw [← signedHeight_projection e] at hh
    change dot (realPosition (X j-x)) ℓ < _ at hh
    rw [dot_realPosition_sub] at hh
    linarith
  constructor
  · rintro ⟨_,hh⟩
    obtain ⟨m,hm⟩ := Set.mem_iUnion.mp hh
    have hm' : m = n := by
      by_contra h
      rcases lt_or_gt_of_ne h with h | h
      · exact (not_lt_of_ge hm.1.1) (hpre m h)
      · exact (hm.2 n h).2 hend.ge
    simpa only [hm'] using hm.1.2
  · intro hA
    refine ⟨hD,Set.mem_iUnion.mpr ⟨n,⟨hend.ge,hA⟩,fun j hj => ?_⟩⟩
    exact ⟨hD j,not_le.mpr (hpre j hj)⟩

lemma sharedConditionedPairLaw_absolutelyContinuous {d : ℕ} (ν : Measure (Row d))
    (ℓ : Vector d) (x y : Lattice d) :
    sharedConditionedPairLaw ν ℓ x y ≪ sharedPairLaw ν x y :=
  (Measure.smul_absolutelyContinuous).trans Measure.absolutelyContinuous_restrict

lemma sharedConditionedPairLaw_noDrop {d : ℕ} (ν : Measure (Row d))
    (ℓ : Vector d) (x y : Lattice d) :
    ∀ᵐ Z ∂sharedConditionedPairLaw ν ℓ x y, Z.1 ∈ NoDrop ℓ x ∧ Z.2 ∈ NoDrop ℓ y := by
  change ∀ᵐ Z ∂((sharedNoDropMass ν ℓ x y)⁻¹ •
    (sharedPairLaw ν x y).restrict (NoDrop ℓ x ×ˢ NoDrop ℓ y)), _
  apply Measure.smul_absolutelyContinuous.ae_le
  exact ae_restrict_mem ((measurableSet_noDrop ℓ x).prod (measurableSet_noDrop ℓ y))

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
