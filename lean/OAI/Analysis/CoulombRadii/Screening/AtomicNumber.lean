import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.AtomicWeightGeometry

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical
noncomputable section
namespace Coulomb
lemma bounded_potential_integrable {n:ℕ} (u:H1Vector n) (f:Configuration n → ℝ)
    (hf:AEStronglyMeasurable f volume) {C:ℝ} (hb:∀ᵐ x,‖f x‖≤C) (s:Spins n):
    Integrable (fun x => f x*‖u.value s x‖^2) :=
  (u.value_L2 s).norm.integrable_sq.bdd_mul hf hb
lemma fraction_pair_integrable {n:ℕ} (u:H1Vector n) (i j:Fin n) {e:ℝ} (he:0<e) (s:Spins n):
    Integrable (fun x => atomicFraction e (position x i)*atomicFraction e (position x j)*‖u.value s x‖^2) := by
  apply bounded_potential_integrable u _
    ((((atomicFraction_measurable e).comp (continuous_position i).measurable).mul
      ((atomicFraction_measurable e).comp (continuous_position j).measurable)).aestronglyMeasurable)
    (C:=1) _ s
  exact Eventually.of_forall fun x => by
    dsimp only [Function.comp_apply,Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (atomicFraction_nonneg he _) (atomicFraction_nonneg he _))]
    exact (mul_le_of_le_one_left (atomicFraction_nonneg he _)
      (atomicFraction_le_one he _)).trans (atomicFraction_le_one he _)
lemma weighted_attraction_le {n:ℕ} (Z:ℕ) (u:H1Vector n) (hm:mass u=1) (i:Fin n)
    {e:ℝ} (he:0<e):
    potentialForm (fun x => (Z:ℝ)*coulombKernel (position x i)*atomicWeight e (position x i)) u≤Z := by
  have hi:∀ s,Integrable (fun x => (Z:ℝ)*atomicFraction e (position x i)*‖u.value s x‖^2) := by
    intro s
    apply bounded_potential_integrable u _
      (((atomicFraction_measurable e).comp (continuous_position i).measurable).const_mul (Z:ℝ)).aestronglyMeasurable
      (C:=(Z:ℝ)) _ s
    exact Eventually.of_forall fun x => by
      dsimp only [Function.comp_apply,Pi.mul_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (atomicFraction_nonneg he _))]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) (atomicFraction_le_one he _)
  have H:=potentialForm_mono_ae u (fun x => (Z:ℝ)*atomicFraction e (position x i)) (fun _ => (Z:ℝ)) hi
    (fun s => (u.value_L2 s).norm.integrable_sq.const_mul _) (Eventually.of_forall fun x =>
      mul_le_of_le_one_right (Nat.cast_nonneg _) (atomicFraction_le_one he _))
  rw [potentialForm_const,hm,mul_one] at H
  simpa only [atomicFraction,mul_assoc] using H
lemma atomic_fraction_pair_bound (Z:ℕ) (hZ:1≤Z) {k:ℕ}
    (u:H1Vector (1+k)) (ha:Antisymmetric u) (hm:mass u=1)
    (hmin:(form (atom Z hZ) u:EReal)=sectorFormBottom (atom Z hZ) (1+k))
    {e:ℝ} (he:0<e):
    (∑ j:Fin k,potentialForm (fun x => atomicFraction e (position x 0)*
      atomicFraction e (position x (Fin.natAdd 1 j))) u)≤2*(Z:ℝ) := by
  have hne(j:Fin k):(0:Fin (1+k))≠Fin.natAdd 1 j:=by
    intro hh; have H:=congrArg Fin.val hh; simp only [Fin.val_zero,Fin.val_natAdd] at H; omega
  let F:Fin k → Configuration (1+k) → ℝ:=fun j x =>
    coulombKernel (position x 0-position x (Fin.natAdd 1 j))*atomicWeight e (position x 0)
  have hi:∀ j:Fin k,∀ s,Integrable (fun x => F j x*‖u.value s x‖^2):=fun j s =>
    pair_weight_integrable u 0 (Fin.natAdd 1 j) 0 (hne j) he s
  have hj(j:Fin k):potentialForm (fun x => atomicFraction e (position x 0)*
      atomicFraction e (position x (Fin.natAdd 1 j))) u≤2*potentialForm (F j) u := by
    have hi':∀ s,Integrable (fun x => coulombKernel (position x 0-position x (Fin.natAdd 1 j))*
        atomicWeight e (position x (Fin.natAdd 1 j))*‖u.value s x‖^2):=fun s =>
      pair_weight_integrable u 0 (Fin.natAdd 1 j) (Fin.natAdd 1 j) (hne j) he s
    have H:=potentialForm_mono_ae u _
      (fun x => F j x+coulombKernel (position x 0-position x (Fin.natAdd 1 j))*atomicWeight e (position x (Fin.natAdd 1 j)))
      (fraction_pair_integrable u 0 (Fin.natAdd 1 j) he)
      (fun s => ((hi j s).add (hi' s)).congr (Eventually.of_forall fun x => by dsimp only; rw [add_mul]; rfl)) (by
        filter_upwards [ae_position_ne (1+k) 0,ae_position_injective (1+k)] with x hx hp
        simpa only [F,mul_add] using atomic_weight_triangle he (hx 0) (hx (Fin.natAdd 1 j))
          (fun h => hne j (hp h)))
    rw [potentialForm_add _ _ _ (hi j) hi',pair_weight_symmetry u ha] at H
    linarith only [H]
  have Hsum:=Finset.sum_le_sum (fun j (_:j∈(Finset.univ:Finset (Fin k))) => hj j)
  rw [←Finset.mul_sum,←potentialForm_finsetSum u Finset.univ F (fun j _ => hi j)] at Hsum
  have hid:(fun x => ∑ j:Fin k,F j x)=(fun x => atomicCross x*atomicWeight e (position x 0)):=by
    funext x; simp only [F,atomicCross,Finset.sum_mul]
  rw [hid] at Hsum
  exact Hsum.trans (mul_le_mul_of_nonneg_left
    ((regularized_weighted_core_limit Z hZ u ha hm hmin e he).trans (weighted_attraction_le Z u hm 0 he)) (by norm_num))
lemma atomicFraction_tendsto {e:ℕ → ℝ} (ht:Tendsto e atTop (𝓝 0)) {x:Space} (hx:x≠0):
    Tendsto (fun j => atomicFraction (e j) x) atTop (𝓝 1) := by
  have hr:0<coulombKernel x:=inv_pos.mpr (norm_pos_iff.mpr hx)
  have H:=(tendsto_const_nhds (x:=coulombKernel x)).mul ((tendsto_const_nhds.add ht).inv₀ (by simpa using hr.ne'))
  simpa only [atomicFraction,atomicWeight,add_zero,mul_inv_cancel₀ hr.ne'] using H
lemma atom_minimizer_number_bound (Z:ℕ) (hZ:1≤Z) {k:ℕ}
    (u:H1Vector (1+k)) (ha:Antisymmetric u) (hm:mass u=1)
    (hmin:(form (atom Z hZ) u:EReal)=sectorFormBottom (atom Z hZ) (1+k)):
    k≤2*Z := by
  let e:ℕ → ℝ:=fun j => ((j:ℝ)+1)⁻¹
  have he:∀ j,0<e j:=fun j => by dsimp [e]; positivity
  have ht:Tendsto e atTop (𝓝 0):=by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)
  have hlim(j:Fin k):Tendsto (fun q => potentialForm (fun x => atomicFraction (e q) (position x 0)*
      atomicFraction (e q) (position x (Fin.natAdd 1 j))) u) atTop (𝓝 1) := by
    have H:=potentialForm_tendsto_bdd u (fun _ => 1)
      (fun s => by simpa using (u.value_L2 s).norm.integrable_sq)
      (fun q x => atomicFraction (e q) (position x 0)*atomicFraction (e q) (position x (Fin.natAdd 1 j)))
      (fun _ => 1) 1
      (fun q => by
        apply AEStronglyMeasurable.mul
        · exact ((atomicFraction_measurable (e q)).comp (continuous_position 0).measurable).aestronglyMeasurable
        · exact ((atomicFraction_measurable (e q)).comp (continuous_position (Fin.natAdd 1 j)).measurable).aestronglyMeasurable)
      (fun q => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (atomicFraction_nonneg (he q) _) (atomicFraction_nonneg (he q) _))]
        exact (mul_le_of_le_one_left (atomicFraction_nonneg (he q) _)
          (atomicFraction_le_one (he q) _)).trans (atomicFraction_le_one (he q) _))
      (by
        filter_upwards [ae_position_ne (1+k) 0] with x hx
        simpa only [one_mul] using (atomicFraction_tendsto ht (hx 0)).mul
          (atomicFraction_tendsto ht (hx (Fin.natAdd 1 j))))
    simpa only [one_mul,potentialForm_const,hm,mul_one] using H
  have Hlim:=tendsto_finsetSum Finset.univ (fun j _ => hlim j)
  have H:=le_of_tendsto Hlim (Eventually.of_forall fun q => atomic_fraction_pair_bound Z hZ u ha hm hmin (he q))
  have H':(k:ℝ)≤2*(Z:ℝ):=by simpa using H
  exact_mod_cast H'
end Coulomb
end

end

end OAI
