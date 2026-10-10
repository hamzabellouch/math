import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.WeightedExterior
import OAI.Analysis.CoulombRadii.RandomFields.WeightedDeletion

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

theorem atomic_weighted_exterior_deletion : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ j, S.position j=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E : ℝ}, (E:EReal) ≤ unrestrictedFormBottom S → form S ψ ≤ E →
    ∀ {t : ℝ}, 0<t → ∀ w : Space → ℝ, Measurable w →
      (∀ y, 0 ≤ w y) → (∀ y, w y ≤ 1) →
      (∀ y, ‖y‖<t → w y=0) →
      potentialForm (weightedInnerField S (t/4) w) ψ ≤
        C*(screenMass 0 (t/4))^2/t := by
  obtain ⟨C,hC,H⟩ := atomic_weighted_shell_deletion
  refine ⟨4*C,by positivity,?_⟩
  intro J n S hatom ψ hψ hm E hE hstate t ht w hwm hw0 hw1 hws
  have hwabs y : |w y| ≤ 1 := by rw [abs_of_nonneg (hw0 y)]; exact hw1 y
  have hterm k :
      potentialForm (weightedInnerField S (t/4) (fun y => ∑ j∈Finset.range k, deletionShellWeight t w j y)) ψ ≤
        4*C*(screenMass 0 (t/4))^2/t := by
    have hfun : weightedInnerField (n:=n) S (t/4) (fun y => ∑ j∈Finset.range k, deletionShellWeight t w j y)=
        (fun x => ∑ j∈Finset.range k, weightedInnerField S (t/4) (deletionShellWeight t w j) x) :=
      funext (weightedInnerField_sum_weights S (t/4) (Finset.range k) (deletionShellWeight t w))
    rw [hfun,potentialForm_sum_values]
    · calc
        _ ≤ ∑ j∈Finset.range k, C*(screenMass 0 (t/4))^2*((j:ℝ)+1)/((2:ℝ)^j*t) := by
          apply Finset.sum_le_sum
          intro j hj
          exact H S hatom ψ hψ hm hE hstate ht j (deletionShellWeight t w j)
            (deletionShellWeight_measurable hwm t j) (deletionShellWeight_nonneg hw0 t j)
            (deletionShellWeight_le_one hw1 t j) (deletionShellWeight_supported t w j)
        _ = (C*(screenMass 0 (t/4))^2/t)*∑ j∈Finset.range k, ((j:ℝ)+1)*(1/2:ℝ)^j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          simp only [div_pow,one_pow]
          field_simp
        _ ≤ (C*(screenMass 0 (t/4))^2/t)*4 :=
          mul_le_mul_of_nonneg_left (deletion_geometric_sum k) (by positivity)
        _ = _ := by ring
    · intro j hj s
      apply boundedObservable_integrable ψ _ (weightedInnerField_measurable S (t/4)
        (deletionShellWeight_measurable hwm t j))
      have hpow : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
      have hu : 0<(2:ℝ)^j*t := by positivity
      exact weightedInnerField_abs_le S hatom hu (by nlinarith)
        (fun y => by rw [abs_of_nonneg (deletionShellWeight_nonneg hw0 t j y)]; exact deletionShellWeight_le_one hw1 t j y)
        (deletionShellWeight_supported t w j)
  exact le_of_tendsto (weightedInnerField_shell_partial_tendsto S hatom ψ ht hwm hwabs hws)
    (Eventually.of_forall hterm)

end Coulomb
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

def particleInnerExterior {J n : ℕ} (S : Nuclei J) (h t : ℝ)
    (i : Fin n) (x : Configuration n) : ℝ :=
  if t ≤ ‖position x i‖ then
    rawSignedField (attraction S (position x i)) (Metric.ball 0 h) (position x i) x else 0

lemma particleInnerExterior_measurable {J n : ℕ} (S : Nuclei J) (h t : ℝ) (i : Fin n) :
    Measurable (particleInnerExterior S h t i) := by
  have hp : Measurable (fun x : Configuration n => position x i) := (continuous_position i).measurable
  have hr : Measurable (fun x : Configuration n => restrictedOutPotential x (Metric.ball 0 h) (position x i)) :=
    (restrictedOutPotential_joint_measurable (m:=n) (A:=Metric.ball (0:Space) h) measurableSet_ball).comp
      (f:=fun x : Configuration n => (x,position x i)) (measurable_id.prodMk hp)
  exact Measurable.ite (measurableSet_le measurable_const hp.norm)
    (((attraction_measurable S).comp hp).sub hr) measurable_const

lemma particleInnerExterior_abs_le {J n : ℕ} (S : Nuclei J) (hatom : ∀ j,S.position j=0)
    {h t : ℝ} (ht : 0<t) (hh : h ≤ t/2) (i : Fin n) (x : Configuration n) :
    |particleInnerExterior S h t i x| ≤ totalCharge S/t+(n:ℝ)/(t/2) := by
  let w : Space → ℝ := fun y => if t≤‖y‖ then 1 else 0
  have hw y : |w y| ≤ 1 := by dsimp [w]; split_ifs <;> norm_num
  have hs y (hy : ‖y‖<t) : w y=0 := ite_eq_right (not_le.mpr hy)
  have H := weighted_raw_inner_exterior_abs_le S hatom ht hh hw hs (position x i) x
  simpa only [w,particleInnerExterior,ite_mul,one_mul,zero_mul] using H

lemma particleInnerExterior_reindex {J m n : ℕ} (S : Nuclei J) (h t : ℝ)
    (e : Fin m ≃ Fin n) (i : Fin m) (x : Configuration m) :
    particleInnerExterior S h t (e i) (reindexConfiguration e x)=particleInnerExterior S h t i x := by
  simp only [particleInnerExterior,position_reindex,rawSignedField_reindex]

def outerDeletionField {J m k : ℕ} (S : Nuclei J) (h t : ℝ) (v : Configuration (m+k)) : ℝ :=
  ∑ i : Fin m, particleInnerExterior S h t (Fin.castAdd k i) v

lemma outerDeletionField_measurable {J m k : ℕ} (S : Nuclei J) (h t : ℝ) :
    Measurable (@outerDeletionField J m k S h t) :=
  Finset.measurable_fun_sum _ (fun index _ => particleInnerExterior_measurable S h t (Fin.castAdd k index))

lemma outerDeletionField_abs_le {J m k : ℕ} (S : Nuclei J) (hatom : ∀ j,S.position j=0)
    {h t : ℝ} (ht : 0<t) (hh : h ≤ t/2) (v : Configuration (m+k)) :
    |outerDeletionField (m:=m) (k:=k) S h t v| ≤ (m:ℝ)*(totalCharge S/t+((m+k:ℕ):ℝ)/(t/2)) := by
  exact (Finset.abs_sum_le_sum_abs ..).trans (by
    have H := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => particleInnerExterior_abs_le S hatom ht hh (Fin.castAdd k i) v)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using H)

lemma outerDeletionField_ge_attraction_sub_cross {J m k : ℕ} (S : Nuclei J)
    {h t : ℝ} (hh : h ≤ t) (x : Configuration m) (z : Configuration k)
    (hx : ∀ i, t ≤ ‖position x i‖) :
    nuclearPotential S x-crossPotential x z ≤ outerDeletionField S h t (joinConfiguration m k (x,z)) := by
  have hzero (y : Space) : restrictedOutPotential x (Metric.ball 0 h) y=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply ite_eq_right
    simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hh.trans (hx i)
  have hle (i : Fin m) : restrictedOutPotential z (Metric.ball 0 h) (position x i) ≤
      ∑ j : Fin k, coulombKernel (position x i-position z j) := by
    apply Finset.sum_le_sum
    intro j hj
    split_ifs
    · exact le_of_eq (coulombKernel_sub_comm ..)
    · exact inv_nonneg.mpr (norm_nonneg _)
  simp only [outerDeletionField,particleInnerExterior,position_join_left,ite_eq_left (hx _),rawSignedField,
    restrictedOutPotential_join,hzero,zero_add,nuclearPotential,crossPotential,←Finset.sum_sub_distrib]
  exact Finset.sum_le_sum (fun i _ => sub_le_sub_left (hle i) _)

lemma slice_core_form_le_raw_deletion {J m k : ℕ} (S : Nuclei J)
    (hatom : ∀ j,S.position j=0) (v : H1Vector (m+k)) {h t : ℝ} (ht : 0<t) (hh : h ≤ t/2)
    (hs : PartlySupported v (outIndexSet m k) {y | t ≤ ‖y‖}) :
    sliceExpectation v (fun s x => form S (v.coreSlice s x).normalized) ≤
      form S v+potentialForm (outerDeletionField (m:=m) (k:=k) S h t) v := by
  have hfield : potentialForm (fun q => nuclearPotential S ((joinConfiguration m k).symm q).1) v-
      potentialForm (fun q => crossPotential ((joinConfiguration m k).symm q).1 ((joinConfiguration m k).symm q).2) v ≤
      potentialForm (outerDeletionField (m:=m) (k:=k) S h t) v := by
    unfold potentialForm
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro s hsu
    rw [←integral_sub (v.outer_nuclear_integrable S s) (v.cross_integrable s)]
    apply integral_mono_ae ((v.outer_nuclear_integrable S s).sub (v.cross_integrable s))
      (boundedObservable_integrable v _ (outerDeletionField_measurable S h t)
        (outerDeletionField_abs_le S hatom ht hh) s)
    filter_upwards [hs s] with q hq
    by_cases hz : v.value s q=0
    · simp [hz]
    · have hx i : t ≤ ‖position ((joinConfiguration m k).symm q).1 i‖ := by
        have he : position q (Fin.castAdd k i)=position ((joinConfiguration m k).symm q).1 i := by
          have H := position_join_left ((joinConfiguration m k).symm q).1 ((joinConfiguration m k).symm q).2 i
          simpa only [Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply] using H
        rw [←he]
        exact by_contra (fun hn => hz (hq _ ⟨i,rfl⟩ hn))
      have H := outerDeletionField_ge_attraction_sub_cross S (show h≤t by linarith)
        ((joinConfiguration m k).symm q).1 ((joinConfiguration m k).symm q).2 hx
      simp only [Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply] at H
      simpa only [Pi.sub_apply,sub_mul] using mul_le_mul_of_nonneg_right H (sq_nonneg ‖v.value s q‖)
  have hp : 0 ≤ potentialForm (fun q => pairPotential ((joinConfiguration m k).symm q).1) v :=
    Finset.sum_nonneg (fun s _ => integral_nonneg (fun q =>
      mul_nonneg (pairPotential_nonneg_pointwise _) (sq_nonneg _)))
  have hk := outerKinetic_nonneg v
  change (∑ s, ∫ x, mass (v.coreSlice s x)*form S (v.coreSlice s x).normalized) ≤ _
  rw [conditional_core_form_identity]
  change _ ≤ kinetic v-nuclearEnergy S v+pairEnergy v+_
  rw [kinetic_split,nuclearEnergy_split,pairEnergy_split]
  linarith

end Coulomb
end

end

end OAI
