import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.WeightedExchangeAlgebra

namespace OAI

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
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma finiteProd_sum {ι : Type*} [Fintype ι] (W : ℝ) (a b : ι → ℝ) :
    W*((∑ i, a i)*(∑ j, b j)) = ∑ i, ∑ j, W*(a i*b j) := by
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]

lemma finite_weighted_bilinear_integrable {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    (μ : Measure A) (u v : ι → A → ℝ) (lam : ι → ℝ) (W : A → A → ℝ)
    (hW : ∀ a b, Integrable (fun xy : A × A => W xy.1 xy.2*(u a xy.1*v b xy.2)) (μ.prod μ)) :
    Integrable (fun xy : A × A => W xy.1 xy.2 *
      ((∑ i, lam i*u i xy.1)*(∑ j, lam j*v j xy.2))) (μ.prod μ) := by
  have H := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hW i j).const_mul (lam i*lam j)))
  apply H.congr
  filter_upwards [] with xy
  rw [finiteProd_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma exists_le_weighted_average {ι : Type*} [Fintype ι] [Nonempty ι]
    (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) :
    ∃ i, f i ≤ ∑ j, p j*f j := by
  classical
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  refine ⟨i, ?_⟩
  calc
    f i = ∑ j, p j*f i := by rw [← Finset.sum_mul, hpsum, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hmin j hj) (hp j))

lemma finiteFermiDensity_direct_flat {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s)) (lam : ι → ℝ) :
    (∫ xy : (Fin 2 × (Fin 3 → ℝ)) × (Fin 2 × (Fin 3 → ℝ)),
      coulombKernel (WithLp.toLp 2 xy.1.2-WithLp.toLp 2 xy.2.2) *
        ((∑ i, lam i*‖flatSpinOrbital (v i) xy.1‖^2)*
          (∑ j, lam j*‖flatSpinOrbital (v j) xy.2‖^2))
        ∂(spinSpaceMeasure.prod spinSpaceMeasure)) =
    ∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*
      (finiteFermiDensity v lam xy.1*finiteFermiDensity v lam xy.2) := by
  let F (s t : Fin 2) (xy : Space × Space) : ℝ := coulombKernel (xy.1-xy.2)*
    ((∑ i, lam i*‖v i xy.1 s‖^2)*(∑ j, lam j*‖v j xy.2 t‖^2))
  have hF (s t : Fin 2) : Integrable (F s t) :=
    finite_weighted_bilinear_integrable volume (fun i x => ‖v i x s‖^2)
      (fun i x => ‖v i x t‖^2) lam (fun x y => coulombKernel (x-y))
      (fun i j => compact_coulomb_direct_integrable (fun x => v i x s) (fun x => v j x t)
        (hv i s).continuous (hv j t).continuous (hC i s) (hC j t))
  change (∫ xy : (Fin 2 × (Fin 3 → ℝ)) × (Fin 2 × (Fin 3 → ℝ)),
    F xy.1.1 xy.2.1 (WithLp.toLp 2 xy.1.2, WithLp.toLp 2 xy.2.2)
      ∂(spinSpaceMeasure.prod spinSpaceMeasure)) = _
  rw [spinPair_integral F hF]
  simp_rw [← integral_finsetSum _ (fun t _ => hF _ t)]
  rw [← integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun t _ => hF s t))]
  apply integral_congr_ae
  filter_upwards [] with xy
  have hs (x : Space) : (∑ s, ∑ i, lam i*‖v i x s‖^2) = finiteFermiDensity v lam x := by
    rw [Finset.sum_comm]
    simp only [finiteFermiDensity, Finset.mul_sum]
  change (∑ s, ∑ t, F s t xy) = _
  rw [← hs xy.1, ← hs xy.2, finiteProd_sum]

lemma bernoulli_slater_pairEnergy_upper {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) (lam : ι → ℝ) :
    (∑ w : ι → Bool, bernoulliWeight lam w * pairEnergy (selectedSlater v hv hC w)) ≤
      (1/2:ℝ)*∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*
        (finiteFermiDensity v lam xy.1*finiteFermiDensity v lam xy.2) := by
  have hV (i : ι) (s : Fin 2) : MemLp (fun x => v i x s) 2 volume :=
    (hv i s).continuous.memLp_of_hasCompactSupport (hC i s)
  have hO (i j : ι) : (∫ x, star (flatSpinOrbital (v i) x)*flatSpinOrbital (v j) x
      ∂spinSpaceMeasure) = if i = j then (1:ℂ) else 0 := by
    rw [flatSpinOrbital_inner (v i) (v j) (hV i) (hV j)]
    exact ho i j
  have H := bernoulli_slater_pair_upper (fun i => flatSpinOrbital (v i))
    (fun x y => coulombKernel (WithLp.toLp 2 x.2-WithLp.toLp 2 y.2)) lam
    (fun i => flatSpinOrbital_memLp (v i) (hV i)) hO
    (flatSpinOrbital_coulomb_cross_integrable v hv hC)
    (fun x y => coulombKernel_nonneg _)
  have he (w : ι → Bool) :
      (∫ x : Fin (Fintype.card {i // w i = true}) → Fin 2 × (Fin 3 → ℝ),
        (∑ i, ∑ j ∈ Finset.univ.erase i,
          coulombKernel (WithLp.toLp 2 (x i).2-WithLp.toLp 2 (x j).2)) *
        ‖slaterWave (fun a => flatSpinOrbital (v (occupiedIndex w a))) x‖^2
          ∂(Measure.pi fun _ => spinSpaceMeasure)) = 2*pairEnergy (selectedSlater v hv hC w) := by
    rw [← slaterState_cubeState (fun a => v (occupiedIndex w a))
      (fun a s => hv _ s) (fun a s => hC _ s), cubeState_pair_energy]
    rfl
  simp_rw [he] at H
  rw [finiteFermiDensity_direct_flat v hv hC lam] at H
  have hm : (∑ w : ι → Bool, bernoulliWeight lam w * (2*pairEnergy (selectedSlater v hv hC w))) =
      2*∑ w : ι → Bool, bernoulliWeight lam w * pairEnergy (selectedSlater v hv hC w) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [hm] at H
  linarith

lemma bernoulli_slater_form_upper {ι : Type*} [Fintype ι] {M : ℕ}
    (S : Nuclei M) (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) (lam : ι → ℝ) :
    (∑ w : ι → Bool, bernoulliWeight lam w * form S (selectedSlater v hv hC w)) ≤
      (1/2:ℝ)*(∑ i, lam i * ∑ s, ∑ b : Fin 3,
        ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2) -
      (∫ x, attraction S x*finiteFermiDensity v lam x) +
      (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*
        (finiteFermiDensity v lam xy.1*finiteFermiDensity v lam xy.2)) := by
  simp only [form, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [bernoulli_slater_kinetic_mean v hv hC ho lam, bernoulli_slater_nuclear_mean S v hv hC ho lam]
  gcongr
  exact bernoulli_slater_pairEnergy_upper v hv hC ho lam

theorem finite_fermi_coulomb_trial {ι : Type*} [Fintype ι] {M : ℕ}
    (S : Nuclei M) (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) (lam : ι → ℝ)
    (h0 : ∀ i, 0 ≤ lam i) (h1 : ∀ i, lam i ≤ 1) :
    ∃ n : ℕ, ∃ ψ : H1Vector n, Antisymmetric ψ ∧ mass ψ = 1 ∧
      form S ψ ≤
      (1/2:ℝ)*(∑ i, lam i * ∑ s, ∑ b : Fin 3,
        ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2) -
      (∫ x, attraction S x*finiteFermiDensity v lam x) +
      (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*
        (finiteFermiDensity v lam xy.1*finiteFermiDensity v lam xy.2)) := by
  obtain ⟨w, hw⟩ := exists_le_weighted_average (bernoulliWeight lam)
    (fun w => form S (selectedSlater v hv hC w))
    (bernoulliWeight_nonneg lam h0 h1) (bernoulliWeight_sum lam)
  exact ⟨_, selectedSlater v hv hC w, selectedSlater_antisymmetric v hv hC w,
    selectedSlater_normalized v hv hC ho w,
    hw.trans (bernoulli_slater_form_upper S v hv hC ho lam)⟩
end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff

end OAI
