import Mathlib
import OAI.Analysis.CoulombRadii.Packets.ScreenBox

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma le_sqrt_sum_squares {C : Type*} [Fintype C] (f : C → ℝ) (c : C) :
    f c≤Real.sqrt (∑ v, (f v)^2) := by
  apply le_trans (le_abs_self _)
  apply (Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).mpr
  rw [sq_abs]
  exact Finset.single_le_sum (fun v _ => sq_nonneg (f v)) (Finset.mem_univ c)

def atomicPatchCap {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) (y : Space) : ℝ :=
  Real.sqrt (∑ z : {z : Space // z∈atomicPatchMesh},
    (localFarCap S u x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2)+
      2*(m:ℝ)/(3*atomicCellScale y)

lemma atomicPatchCap_nonneg {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) {y : Space} (hy : y≠0) : 0≤atomicPatchCap S u x y := by
  have ha := atomicCellScale_pos hy
  unfold atomicPatchCap
  positivity

lemma coreField_le_atomicPatchCap {J m k : ℕ} (S : Nuclei J) (hatom : ∀ j, S.position j=0)
    (u : H1Vector k) (x : Configuration m) {y : Space} (hy : y≠0) {w : Space}
    (hw : ‖w-y‖≤80*atomicCellScale y) : coreScreenedField S u w≤atomicPatchCap S u x y := by
  obtain ⟨z,hz,hwz⟩ := atomicMesh_cover hy w hw
  have hz0 : atomicMeshCenter y z≠0 := atomicCellScale_near_nonzero hy
    (by nlinarith [atomicMeshCenter_distance y z hz,atomicCellScale_nonneg y])
  have hza := atomicCellScale_pos hz0
  have H := coreField_le_local_far_cap S u x hza (atomicMeshCenter y z) w hwz
    (fun j => by rw [hatom j]; exact atomicCellScale_nucleus_far _)
  have hcap := le_sqrt_sum_squares
    (fun v : {z : Space // z∈atomicPatchMesh} =>
      localFarCap S u x (atomicMeshCenter y v.val) (atomicCellScale (atomicMeshCenter y v.val)))
    (⟨z,hz⟩ : {z : Space // z∈atomicPatchMesh})
  have hcount : (m:ℝ)/(3*atomicCellScale (atomicMeshCenter y z))≤2*(m:ℝ)/(3*atomicCellScale y) := by
    calc
      _≤(m:ℝ)/(3*(atomicCellScale y/2)) := div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (by positivity [atomicCellScale_pos hy]) (by linarith [(atomicMeshCenter_comparable y z hz).1])
      _=_ := by ring
  exact H.trans (add_le_add hcap hcount)

lemma atomicPatchCap_square_le {J m k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (x : Configuration m) (y : Space) : (atomicPatchCap S u x y)^2≤
      2*∑ z : {z : Space // z∈atomicPatchMesh},
        (localFarCap S u x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2+
      8*(m:ℝ)^2/(9*(atomicCellScale y)^2) := by
  have hs := Real.sq_sqrt (x := ∑ z : {z : Space // z∈atomicPatchMesh},
    (localFarCap S u x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2)
    (Finset.sum_nonneg (fun z _ => sq_nonneg
    (localFarCap S u x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))))
  unfold atomicPatchCap
  have H := sq_nonneg (Real.sqrt (∑ z : {z : Space // z∈atomicPatchMesh},
    (localFarCap S u x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2)-
      2*(m:ℝ)/(3*atomicCellScale y))
  rw [show 8*(m:ℝ)^2/(9*(atomicCellScale y)^2)=2*(2*(m:ℝ)/(3*atomicCellScale y))^2 by ring]
  nlinarith

lemma atomicPatchCap_slice_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m) (y : Space) :
    AEStronglyMeasurable (fun x => atomicPatchCap S (u.coreSlice s x).normalized x y) volume := by
  apply AEStronglyMeasurable.add_const
  apply Real.continuous_sqrt.comp_aestronglyMeasurable
  exact Finset.aestronglyMeasurable_fun_sum _ (fun z _ =>
    (localFarCap_normalized_slice_aestronglyMeasurable S u s _ _).pow 2)

lemma atomicPatchCap_weight_integrable {J m k : ℕ} (S : Nuclei J)
    (hatom : ∀ j, S.position j=0) (u : H1Vector (m+k)) (s : Spins m) {y : Space} (hy : y≠0) :
    Integrable (fun x => mass (u.coreSlice s x)*(atomicPatchCap S (u.coreSlice s x).normalized x y)^2) := by
  let C := {z : Space // z∈atomicPatchMesh}
  have hi (z : C) : Integrable (fun x => mass (u.coreSlice s x)*
      (localFarCap S (u.coreSlice s x).normalized x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2) := by
    apply localFarCap_weight_integrable S u s
    · exact atomicCellScale_pos (atomicCellScale_near_nonzero hy (by
        nlinarith [atomicMeshCenter_distance y z.val z.property,atomicCellScale_nonneg y]))
    · intro j
      rw [hatom j]
      exact atomicCellScale_nucleus_far _
  have HR : Integrable (fun x => 2*(∑ z : C, mass (u.coreSlice s x)*
      (localFarCap S (u.coreSlice s x).normalized x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2)+
      mass (u.coreSlice s x)*(8*(m:ℝ)^2/(9*(atomicCellScale y)^2))) :=
    ((integrable_finsetSum _ (fun z _ => hi z)).const_mul 2).add ((mass_coreSlice_integrable u s).mul_const _)
  apply HR.mono'
    ((mass_coreSlice_integrable u s).aestronglyMeasurable.mul ((atomicPatchCap_slice_aestronglyMeasurable S u s y).pow 2))
  filter_upwards [] with x
  simp only [Pi.mul_apply,Pi.pow_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (mass_nonneg _) (sq_nonneg _))]
  have H := mul_le_mul_of_nonneg_left (atomicPatchCap_square_le S (u.coreSlice s x).normalized x y) (mass_nonneg (u.coreSlice s x))
  simpa only [Pi.add_apply,mul_add,Finset.mul_sum,mul_left_comm (mass _) 2] using H

theorem atomicPatchCap_ensemble_square {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ j, S.position j=0) (T : RecordedEnsemble n) {y : Space} (hy : y≠0) {H : ℝ}
    (hraw : ∀ v, AtomicScaleWindow (atomicCellScale y) 4 v → T.rawSquare S v (atomicCellScale v)≤H) :
    (∑ p, sliceExpectation (T.vector p) (fun s x => (atomicPatchCap S ((T.vector p).coreSlice s x).normalized x y)^2))≤
      16*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*H+
        8*(∑ p, (T.out p:ℝ)^2*mass (T.vector p))/(9*(atomicCellScale y)^2) := by
  let C := {z : Space // z∈atomicPatchMesh}
  have hz (z : C) : atomicMeshCenter y z.val≠0 := atomicCellScale_near_nonzero hy (by
    nlinarith [atomicMeshCenter_distance y z.val z.property,atomicCellScale_nonneg y])
  have hnuc (z : C) (j) : 4*atomicCellScale (atomicMeshCenter y z.val)≤‖S.position j-atomicMeshCenter y z.val‖ := by
    rw [hatom j]
    exact atomicCellScale_nucleus_far _
  have Hcap (z : C) : (∑ p, sliceExpectation (T.vector p) (fun s x =>
      (localFarCap S ((T.vector p).coreSlice s x).normalized x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2))≤8*H := by
    apply atomic_cap_sq_le_of_raw_bound S T.out T.core T.vector (hz z) (hnuc z)
    intro v hv
    apply hraw v
    have hw : AtomicScaleWindow (atomicCellScale y) 1 y := by constructor <;> simp
    simpa only [mul_one] using hw.mesh_near zero_le_one z.property hv
  have Hp (p : T.index) : sliceExpectation (T.vector p) (fun s x => (atomicPatchCap S ((T.vector p).coreSlice s x).normalized x y)^2)≤
      2*(∑ z : C, sliceExpectation (T.vector p) (fun s x =>
        (localFarCap S ((T.vector p).coreSlice s x).normalized x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2))+
      (8*(T.out p:ℝ)^2/(9*(atomicCellScale y)^2))*mass (T.vector p) := by
    rw [←sliceExpectation_number (T.vector p) (8*(T.out p:ℝ)^2/(9*(atomicCellScale y)^2))]
    unfold sliceExpectation
    rw [Finset.sum_comm,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s hs
    rw [←integral_finsetSum _ (fun z _ => localFarCap_weight_integrable S (T.vector p) s (atomicCellScale_pos (hz z)) _ (hnuc z) 2),←integral_const_mul,
      ←integral_add ((integrable_finsetSum _ (fun z _ => localFarCap_weight_integrable S (T.vector p) s (atomicCellScale_pos (hz z)) _ (hnuc z) 2)).const_mul 2)
        ((mass_coreSlice_integrable (T.vector p) s).mul_const _)]
    apply integral_mono_ae (atomicPatchCap_weight_integrable S hatom (T.vector p) s hy)
      (((integrable_finsetSum _ (fun z _ => localFarCap_weight_integrable S (T.vector p) s (atomicCellScale_pos (hz z)) _ (hnuc z) 2)).const_mul 2).add
        ((mass_coreSlice_integrable (T.vector p) s).mul_const _))
    filter_upwards [] with x
    have HH := mul_le_mul_of_nonneg_left (atomicPatchCap_square_le S ((T.vector p).coreSlice s x).normalized x y)
      (mass_nonneg ((T.vector p).coreSlice s x))
    simpa only [Pi.add_apply,mul_add,Finset.mul_sum,mul_left_comm (mass _) 2] using HH
  calc
    _≤∑ p, (2*(∑ z : C, sliceExpectation (T.vector p) (fun s x =>
        (localFarCap S ((T.vector p).coreSlice s x).normalized x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2))+
      (8*(T.out p:ℝ)^2/(9*(atomicCellScale y)^2))*mass (T.vector p)) := Finset.sum_le_sum (fun p _ => Hp p)
    _=2*(∑ z : C, ∑ p, sliceExpectation (T.vector p) (fun s x =>
        (localFarCap S ((T.vector p).coreSlice s x).normalized x (atomicMeshCenter y z.val) (atomicCellScale (atomicMeshCenter y z.val)))^2))+
      8*(∑ p, (T.out p:ℝ)^2*mass (T.vector p))/(9*(atomicCellScale y)^2) := by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_comm]
      congr 1
      simp only [Finset.mul_sum,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _≤2*(∑ _z : C, 8*H)+8*(∑ p, (T.out p:ℝ)^2*mass (T.vector p))/(9*(atomicCellScale y)^2) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun z _ => Hcap z)) (show (0:ℝ)≤2 by norm_num)) le_rfl
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_coe, C]; ring

end Coulomb
end

end
end

end OAI
