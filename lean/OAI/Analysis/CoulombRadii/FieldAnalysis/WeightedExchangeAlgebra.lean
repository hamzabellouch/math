import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.DeterminantBodyReal
import OAI.Analysis.CoulombRadii.FieldAnalysis.Occupancy

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
lemma weighted_exchange_algebra {A ι : Type*} [Fintype ι]
    (v : ι → A → ℂ) (lam : ι → ℝ) (x y : A) :
    (∑ i, ∑ j, (lam i : ℂ)*(lam j : ℂ)*
      ((star (v i x)*v j x)*(star (v j y)*v i y))) =
      (↑(‖∑ i, (lam i : ℂ)*(v i x*star (v i y))‖^2) : ℂ) := by
  have hs (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  rw [← complex_star_mul_self]
  simp only [star_sum, star_mul, star_star, hs, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma weighted_exchange_integral {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    (μ : Measure A) (v : ι → A → ℂ) (lam : ι → ℝ) (W : A → A → ℝ)
    (hW : ∀ i j, Integrable (fun xy : A × A => (W xy.1 xy.2 : ℂ)*
      ((star (v i xy.1)*v j xy.1)*(star (v j xy.2)*v i xy.2))) (μ.prod μ)) :
    (∑ i, ∑ j, (lam i : ℂ)*(lam j:ℂ)*
      (∫ xy : A × A, (W xy.1 xy.2 : ℂ)*
        ((star (v i xy.1)*v j xy.1)*(star (v j xy.2)*v i xy.2)) ∂(μ.prod μ))) =
    (↑(∫ xy : A × A, W xy.1 xy.2 *
      ‖∑ i, (lam i : ℂ)*(v i xy.1*star (v i xy.2))‖^2 ∂(μ.prod μ)) : ℂ) := by
  simp_rw [← integral_const_mul]
  calc
    _ = ∫ xy : A × A, ∑ i, ∑ j, (lam i : ℂ)*(lam j:ℂ)*((W xy.1 xy.2 : ℂ)*
        ((star (v i xy.1)*v j xy.1)*(star (v j xy.2)*v i xy.2))) ∂(μ.prod μ) := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
        (hW i j).const_mul _))]
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum _ (fun j _ => (hW i j).const_mul _)).symm
    _ = ∫ xy : A × A, ((W xy.1 xy.2 *
        ‖∑ i, (lam i : ℂ)*(v i xy.1*star (v i xy.2))‖^2 : ℝ) : ℂ) ∂(μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards [] with xy
      rw [Complex.ofReal_mul, ← weighted_exchange_algebra v lam xy.1 xy.2]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := integral_complex_ofReal

lemma weighted_slaterPairEntry_upper {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    (μ : Measure A) (v : ι → A → ℂ) (lam : ι → ℝ) (W : A → A → ℝ)
    (hW : ∀ a b c d, Integrable (fun xy : A × A => (W xy.1 xy.2 : ℂ)*
      ((star (v a xy.1)*v c xy.1)*(star (v b xy.2)*v d xy.2))) (μ.prod μ))
    (hW0 : ∀ x y, 0 ≤ W x y) :
    (∑ i, ∑ j, lam i*lam j*slaterPairEntry μ v W i j) ≤
      ∫ xy : A × A, W xy.1 xy.2 *
        ((∑ i, lam i*‖v i xy.1‖^2)*(∑ j, lam j*‖v j xy.2‖^2)) ∂(μ.prod μ) := by
  have hd (i j : ι) : Integrable
      (fun xy : A × A => W xy.1 xy.2*(‖v i xy.1‖^2*‖v j xy.2‖^2)) (μ.prod μ) := by
    have h := (hW i j i j).re
    simp only [complex_star_mul_self, ← Complex.ofReal_mul] at h
    change Integrable (fun xy : A × A => (↑(W xy.1 xy.2*(‖v i xy.1‖^2*‖v j xy.2‖^2)) : ℂ).re) _ at h
    simpa only [Complex.ofReal_re] using h
  have he := congrArg Complex.re (weighted_exchange_integral μ v lam W (fun i j => hW i j j i))
  simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, add_zero] at he
  simp only [slaterPairEntry, complex_star_mul_self, ← Complex.ofReal_mul,
    integral_complex_ofReal, Complex.ofReal_re, mul_sub, Finset.sum_sub_distrib]
  rw [he]
  have hdir : (∑ i, ∑ j, lam i*lam j*
      (∫ xy : A × A, W xy.1 xy.2*(‖v i xy.1‖^2*‖v j xy.2‖^2) ∂(μ.prod μ))) =
      ∫ xy : A × A, W xy.1 xy.2 *
        ((∑ i, lam i*‖v i xy.1‖^2)*(∑ j, lam j*‖v j xy.2‖^2)) ∂(μ.prod μ) := by
    simp_rw [← integral_const_mul]
    calc
      _ = ∫ xy : A × A, ∑ i, ∑ j, lam i*lam j *
          (W xy.1 xy.2*(‖v i xy.1‖^2*‖v j xy.2‖^2)) ∂(μ.prod μ) := by
        rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hd i j).const_mul _))]
        apply Finset.sum_congr rfl
        intro i _
        exact (integral_finsetSum _ (fun j _ => (hd i j).const_mul _)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with xy
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [hdir]
  exact sub_le_self _ (integral_nonneg (fun xy => mul_nonneg (hW0 _ _) (sq_nonneg _)))

lemma bernoulli_chosen_sum {ι : Type*} [Fintype ι] (lam f : ι → ℝ) :
    (∑ w : ι → Bool, bernoulliWeight lam w * ∑ a, f (occupiedIndex w a)) =
      ∑ i, lam i*f i := by
  simp_rw [sum_occupiedIndex_real]
  exact bernoulli_linear_mean lam f

lemma bernoulli_slater_pair_upper {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] (v : ι → A → ℂ) (W : A → A → ℝ)
    (lam : ι → ℝ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (hW : ∀ a b c d, Integrable (fun xy : A × A => (W xy.1 xy.2 : ℂ) *
      ((star (v a xy.1)*v c xy.1)*(star (v b xy.2)*v d xy.2))) (μ.prod μ))
    (hW0 : ∀ x y, 0 ≤ W x y) :
    (∑ w : ι → Bool, bernoulliWeight lam w *
      (∫ x : Fin (Fintype.card {i // w i = true}) → A,
        (∑ i, ∑ j ∈ Finset.univ.erase i, W (x i) (x j)) *
        ‖slaterWave (fun a => v (occupiedIndex w a)) x‖^2 ∂(Measure.pi fun _ => μ))) ≤
      ∫ xy : A × A, W xy.1 xy.2 *
        ((∑ i, lam i*‖v i xy.1‖^2)*(∑ j, lam j*‖v j xy.2‖^2)) ∂(μ.prod μ) := by
  rw [bernoulli_slater_pair_mean v W lam hv ho hW]
  exact weighted_slaterPairEntry_upper μ v lam W hW hW0

noncomputable def selectedSlater {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s)) (w : ι → Bool) :
    H1Vector (Fintype.card {i // w i = true}) :=
  slaterState (fun index => v (occupiedIndex w index))
    (fun index spin => hv (occupiedIndex w index) spin)
    (fun index spin => hC (occupiedIndex w index) spin)

lemma selectedSlater_antisymmetric {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s)) (w : ι → Bool) :
    Antisymmetric (selectedSlater v hv hC w) :=
  slaterState_antisymmetric _ _ _

lemma selectedSlater_normalized {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) (w : ι → Bool) :
    mass (selectedSlater v hv hC w) = 1 := by
  apply slaterState_normalized
  intro a b
  simp only [ho, (occupiedIndex w).injective.eq_iff]

lemma bernoulli_slater_kinetic_mean {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) (lam : ι → ℝ) :
    (∑ w : ι → Bool, bernoulliWeight lam w * kinetic (selectedSlater v hv hC w)) =
      (1/2:ℝ)*∑ i, lam i * ∑ s, ∑ b : Fin 3,
        ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2 := by
  have hk (w : ι → Bool) := slaterState_kinetic
    (fun a => v (occupiedIndex w a)) (fun a s => hv _ s) (fun a s => hC _ s)
    (fun a b => by simp only [ho, (occupiedIndex w).injective.eq_iff])
  simp only [selectedSlater, hk]
  simp_rw [mul_left_comm (bernoulliWeight lam _) (1/2:ℝ)]
  rw [← Finset.mul_sum]
  congr 1
  exact bernoulli_chosen_sum lam (fun i => ∑ s, ∑ b : Fin 3,
    ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2)

noncomputable def finiteFermiDensity {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ) (lam : ι → ℝ) (x : Space) : ℝ :=
  ∑ i, lam i * ∑ s, ‖v i x s‖^2

lemma selectedSlater_density {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ) (w : ι → Bool) (x : Space) :
    slaterDensity (fun a => v (occupiedIndex w a)) x =
      ∑ i, occupancy (w i)*∑ s, ‖v i x s‖^2 :=
  sum_occupiedIndex_real w (fun i => ∑ s, ‖v i x s‖^2)

lemma finiteFermiDensity_nuclear_integrable {ι : Type*} [Fintype ι] {M : ℕ}
    (S : Nuclei M) (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s)) (lam : ι → ℝ) :
    Integrable (fun x => attraction S x*finiteFermiDensity v lam x) := by
  have hi (i : ι) (s : Fin 2) : Integrable (fun x => attraction S x*‖v i x s‖^2) := by
    have h := compact_attraction_cross_integrable S (fun x => v i x s) (fun x => v i x s)
      (hv i s).continuous (hv i s).continuous (hC i s)
    simp_rw [complex_star_mul_self, ← Complex.ofReal_mul] at h
    exact h.re
  have H := integrable_finsetSum Finset.univ (fun i _ =>
    (integrable_finsetSum Finset.univ (fun s _ => hi i s)).const_mul (lam i))
  apply H.congr
  filter_upwards [] with x
  simp only [finiteFermiDensity, Finset.mul_sum]
  congr 1
  funext i
  congr 1
  funext s
  ring

lemma bernoulli_slater_nuclear_mean {ι : Type*} [Fintype ι] {M : ℕ}
    (S : Nuclei M) (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) (lam : ι → ℝ) :
    (∑ w : ι → Bool, bernoulliWeight lam w * nuclearEnergy S (selectedSlater v hv hC w)) =
      ∫ x, attraction S x*finiteFermiDensity v lam x := by
  have hn (w : ι → Bool) := slaterState_nuclear S
    (fun a => v (occupiedIndex w a)) (fun a s => hv _ s) (fun a s => hC _ s)
    (fun a b => by simp only [ho, (occupiedIndex w).injective.eq_iff])
  simp only [selectedSlater, hn, selectedSlater_density]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun w _ =>
    (finiteFermiDensity_nuclear_integrable S v hv hC (fun i => occupancy (w i))).const_mul _)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp_rw [mul_left_comm (bernoulliWeight lam _) (attraction S x)]
  rw [← Finset.mul_sum, bernoulli_linear_mean]
  rfl
end Coulomb

end OAI
