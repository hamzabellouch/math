import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.Add
import OAI.Analysis.CoulombRadii.Packets.OrbitalKernel
import OAI.Analysis.CoulombRadii.Localization.TruncatedCoulomb

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma spinConfiguration_integral {n : ℕ} (F : Spins n → Configuration n → ℝ)
    (hF : ∀ s, Integrable (F s)) :
    (∫ z, F ((spinCubeEquiv n) z).1 (WithLp.toLp 2 ((spinCubeEquiv n) z).2)
      ∂(Measure.pi fun _ : Fin n => spinSpaceMeasure)) = ∑ s, ∫ x, F s x := by
  rw [(spinCubeEquiv_full_measurePreserving n).integral_comp'
    (fun sx => F sx.1 (WithLp.toLp 2 sx.2))]
  have hm : MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin n × Fin 3) → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp _
  rw [integral_finite_count_prod _ (fun s => hm.integrable_comp_of_integrable (hF s))]
  apply Finset.sum_congr rfl
  intro s _
  exact hm.integral_comp' (F s)

lemma sum_pair_symmetric {n : ℕ} (w : Fin n → Fin n → ℝ)
    (hw : ∀ i j, w i j = w j i) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, w i j) =
      2 * ∑ i, ∑ j, if i < j then w i j else 0 := by
  have he (i : Fin n) : (∑ j ∈ Finset.univ.erase i, w i j) =
      (∑ j, if i < j then w i j else 0) + (∑ j, if j < i then w i j else 0) := by
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    have hpoint (j : Fin n) : w i j = (if i < j then w i j else 0) +
        (if j < i then w i j else 0) + (if j = i then w i i else 0) := by
      rcases lt_trichotomy i j with h|h|h
      · simp [h, h.not_gt, h.ne'];
      · subst j; simp
      · simp [h, h.not_gt, h.ne]
    conv_lhs => lhs; arg 2; ext j; rw [hpoint j]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  have hs : (∑ i : Fin n, ∑ j : Fin n, if j < i then w i j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then w i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hw j i]
  rw [hs]
  ring

lemma cubeState_pair_energy {n : ℕ} (ψ : H1Vector n) :
    (∫ z, (∑ i, ∑ j ∈ Finset.univ.erase i,
      coulombKernel (WithLp.toLp 2 (z i).2-WithLp.toLp 2 (z j).2)) * ‖cubeState ψ z‖^2
      ∂(Measure.pi fun _ : Fin n => spinSpaceMeasure)) = 2*pairEnergy ψ := by
  have hs (z : Fin n → Fin 2 × (Fin 3 → ℝ)) := sum_pair_symmetric
    (fun i j => coulombKernel (WithLp.toLp 2 (z i).2-WithLp.toLp 2 (z j).2))
    (fun i j => congrArg (fun r : ℝ => r⁻¹) (norm_sub_rev _ _))
  simp_rw [hs, mul_assoc]
  rw [integral_const_mul]
  congr 1
  exact spinConfiguration_integral
    (fun s x => (∑ i : Fin n, ∑ j : Fin n, if i < j then
      coulombKernel (position x i-position x j) else 0)*‖ψ.value s x‖^2)
    ψ.pair_integrable

lemma slaterState_pair_upper_flat {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) :
    pairEnergy (slaterState v hv hC) ≤ (1/2:ℝ)*
      (∑ a, ∑ b, ∫ xy : (Fin 2 × (Fin 3 → ℝ)) × (Fin 2 × (Fin 3 → ℝ)),
        coulombKernel (WithLp.toLp 2 xy.1.2-WithLp.toLp 2 xy.2.2) *
          (‖flatSpinOrbital (v a) xy.1‖^2*‖flatSpinOrbital (v b) xy.2‖^2)
          ∂(spinSpaceMeasure.prod spinSpaceMeasure)) := by
  have hV (a : Fin n) (s : Fin 2) : MemLp (fun x => v a x s) 2 volume :=
    (hv a s).continuous.memLp_of_hasCompactSupport (hC a s)
  have hO (a b : Fin n) : (∫ x, star (flatSpinOrbital (v a) x)*flatSpinOrbital (v b) x
      ∂spinSpaceMeasure) = if a = b then (1:ℂ) else 0 := by
    rw [flatSpinOrbital_inner (v a) (v b) (hV a) (hV b)]
    exact ho a b
  have H := slaterWave_two_body_upper (fun a => flatSpinOrbital (v a))
    (fun x y => coulombKernel (WithLp.toLp 2 x.2-WithLp.toLp 2 y.2))
    (fun a => flatSpinOrbital_memLp (v a) (hV a)) hO
    (flatSpinOrbital_coulomb_cross_integrable v hv hC)
    (fun x y => coulombKernel_nonneg _)
  rw [← slaterState_cubeState v hv hC, cubeState_pair_energy] at H
  linarith
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma spinPair_integral (F : Fin 2 → Fin 2 → Space × Space → ℝ)
    (hF : ∀ s t, Integrable (F s t)) :
    (∫ xy : (Fin 2 × (Fin 3 → ℝ)) × (Fin 2 × (Fin 3 → ℝ)),
      F xy.1.1 xy.2.1 (WithLp.toLp 2 xy.1.2, WithLp.toLp 2 xy.2.2)
      ∂(spinSpaceMeasure.prod spinSpaceMeasure)) = ∑ s, ∑ t, ∫ xy, F s t xy := by
  have hm0 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp _
  have hm : MeasurePreserving ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).prodCongr
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))) volume volume := hm0.prod hm0
  have hR := pairRegroup_measurePreserving (Measure.count : Measure (Fin 2))
    (volume : Measure (Fin 3 → ℝ)) (Measure.count : Measure (Fin 2)) (volume : Measure (Fin 3 → ℝ))
  rw [count_prod_count] at hR
  let G (sz : (Fin 2 × Fin 2) × ((Fin 3 → ℝ) × (Fin 3 → ℝ))) : ℝ :=
    F sz.1.1 sz.1.2 (WithLp.toLp 2 sz.2.1, WithLp.toLp 2 sz.2.2)
  change (∫ p, G (pairRegroup p) ∂((Measure.count.prod volume).prod (Measure.count.prod volume))) = _
  rw [hR.integral_comp' G, integral_finite_count_prod (μ := volume.prod volume) G
    (fun st => hm.integrable_comp_of_integrable (hF st.1 st.2))]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  exact hm.integral_comp' (F s t)

lemma compact_coulomb_direct_integrable (f g : Space → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Integrable (fun xy : Space × Space => coulombKernel (xy.1-xy.2)*(‖f xy.1‖^2*‖g xy.2‖^2)) := by
  have h := compact_coulomb_cross_integrable f g f g hf hg hf hg hfc hgc
  simp only [complex_star_mul_self, ← Complex.ofReal_mul] at h
  exact h.re

noncomputable def slaterDensity {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ) (x : Space) : ℝ :=
  ∑ a, ∑ s : Fin 2, ‖v a x s‖^2

lemma slaterState_pair_upper {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) :
    pairEnergy (slaterState v hv hC) ≤ (1/2:ℝ)*
      ∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(slaterDensity v xy.1*slaterDensity v xy.2) := by
  have hI (a b : Fin n) (s t : Fin 2) := compact_coulomb_direct_integrable
    (fun x => v a x s) (fun x => v b x t) (hv a s).continuous (hv b t).continuous (hC a s) (hC b t)
  have H := slaterState_pair_upper_flat v hv hC ho
  have he (a b : Fin n) : (∫ xy : (Fin 2 × (Fin 3 → ℝ)) × (Fin 2 × (Fin 3 → ℝ)),
      coulombKernel (WithLp.toLp 2 xy.1.2-WithLp.toLp 2 xy.2.2) *
        (‖flatSpinOrbital (v a) xy.1‖^2*‖flatSpinOrbital (v b) xy.2‖^2)
        ∂(spinSpaceMeasure.prod spinSpaceMeasure)) =
      ∑ s, ∑ t, ∫ xy : Space × Space,
        coulombKernel (xy.1-xy.2)*(‖v a xy.1 s‖^2*‖v b xy.2 t‖^2) :=
    spinPair_integral (fun s t xy => coulombKernel (xy.1-xy.2)*(‖v a xy.1 s‖^2*‖v b xy.2 t‖^2))
      (hI a b)
  simp_rw [he] at H
  suffices heq : (∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*
      (slaterDensity v xy.1*slaterDensity v xy.2)) =
      ∑ a, ∑ b, ∑ s, ∑ t, ∫ xy : Space × Space,
        coulombKernel (xy.1-xy.2)*(‖v a xy.1 s‖^2*‖v b xy.2 t‖^2) by rwa [heq]
  have hp (xy : Space × Space) : coulombKernel (xy.1-xy.2)*
      (slaterDensity v xy.1*slaterDensity v xy.2) =
      ∑ a, ∑ b, ∑ s, ∑ t, coulombKernel (xy.1-xy.2)*(‖v a xy.1 s‖^2*‖v b xy.2 t‖^2) := by
    unfold slaterDensity
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
  simp_rw [hp]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _
    (fun b _ => integrable_finsetSum _ (fun s _ => integrable_finsetSum _ (fun t _ => hI a b s t))))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _
    (fun s _ => integrable_finsetSum _ (fun t _ => hI a b s t)))]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun t _ => hI a b s t))]
  apply Finset.sum_congr rfl
  intro s _
  exact integral_finsetSum _ (fun t _ => hI a b s t)
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
