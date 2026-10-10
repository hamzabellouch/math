import Mathlib
import OAI.Probability.SKRatio.Dynamics.Assembly
import OAI.Probability.SKRatio.Calculus.SpectralLower

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

lemma replace_difference_le {n : ℕ} (f : Observables n) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ x i, |halfDiff i f x| ≤ a) (x : Spin n) (i : Fin n) (b : Bool) :
    |f (replace x i b)-f x| ≤ 2*a := by
  by_cases hb : b = x i
  · subst b
    rw [replace_self,sub_self,abs_zero]
    positivity
  · have he : b = !(x i) := by cases hi : x i <;> cases b <;> simp_all
    rw [he]
    change |f (flip i x)-f x| ≤ 2*a
    rw [flip_sub,abs_mul,abs_mul]
    have hs : |spin x i| = 1 := by cases hi : x i <;> simp [spin,hi]
    rw [hs]
    norm_num
    linarith [h x i]

lemma oscillation_le_of_halfDiff {n : ℕ} (f : Observables n) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ x i, |halfDiff i f x| ≤ a) (x y : Spin n) :
    |f x-f y| ≤ 2*(n:ℝ)*a := by
  have hp (k : ℕ) (hk : k ≤ n) :
      |f (updatePath x y k)-f x| ≤ 2*(k:ℝ)*a := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hk' : k < n := by omega
      have hstep := replace_difference_le f ha h (updatePath x y k) ⟨k,hk'⟩ (y ⟨k,hk'⟩)
      change |f (Function.update (updatePath x y k) ⟨k,hk'⟩ (y ⟨k,hk'⟩)) -
        f (updatePath x y k)| ≤ 2*a at hstep
      rw [←updatePath_succ x y k hk'] at hstep
      have htri := abs_sub_le (f (updatePath x y (k+1))) (f (updatePath x y k)) (f x)
      have hprev := ih (by omega)
      push_cast
      linarith
  simpa only [updatePath_end,abs_sub_comm] using hp n le_rfl

lemma halfDiff_le_sqrt_gradient {n : ℕ} (f : Observables n) {B : ℝ}
    (hB : ∀ x, unweightedGradient f x ≤ B) (x : Spin n) (i : Fin n) :
    |halfDiff i f x| ≤ Real.sqrt B := by
  have hsq : (halfDiff i f x)^2 ≤ B :=
    (Finset.single_le_sum (fun j _ => sq_nonneg (halfDiff j f x)) (Finset.mem_univ i)).trans (hB x)
  exact (Real.sqrt_sq_eq_abs _).symm ▸ Real.sqrt_le_sqrt hsq

lemma mean_difference_le_of_oscillation {n : ℕ} (g : Disorder n) (f : Observables n)
    {B : ℝ} (hosc : ∀ x y, |f x-f y| ≤ B) (x : Spin n) :
    |f x-FiniteLaw.mean (mass g 0) f| ≤ B := by
  have hid : f x-FiniteLaw.mean (mass g 0) f =
      ∑ y, mass g 0 y*(f x-f y) := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,sum_mass,one_mul,FiniteLaw.mean]
  rw [hid]
  calc
    _ ≤ ∑ y, |mass g 0 y*(f x-f y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, mass g 0 y*B := by
      apply Finset.sum_le_sum
      intro y _
      rw [abs_mul,abs_of_nonneg (mass_nonneg g 0 y)]
      exact mul_le_mul_of_nonneg_left (hosc x y) (mass_nonneg g 0 y)
    _ = B := by rw [←Finset.sum_mul,sum_mass,one_mul]

theorem distance_upper_of_uniform_gradient_drift {n : ℕ} (g : Disorder n) {κ t : ℝ}
    (ht : 0 ≤ t)
    (hgrad : ∀ f : Observables n, ∀ r : ℝ, ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          -κ*unweightedGradient (semigroup (coupling g) r f) y) :
    continuousDistance g t ≤ (n:ℝ)*Real.sqrt ((n:ℝ)*Real.exp (-κ*t)) := by
  apply Finset.sup'_le
  intro x _
  apply FiniteLaw.totalVariation_le_of_tests
  intro f hf
  rw [←semigroup_eq_kernel,←gibbsMean_semigroup g t f]
  have hB (y : Spin n) : unweightedGradient (semigroup (coupling g) t f) y ≤
      (n:ℝ)*Real.exp (-κ*t) := by
    simpa only [mul_comm] using gradient_envelope_of_drift (coupling g) f ht
      (fun r _ y => hgrad f r y) (unweightedGradient_le_dim f hf) y
  have ho := oscillation_le_of_halfDiff (semigroup (coupling g) t f) (Real.sqrt_nonneg _)
    (halfDiff_le_sqrt_gradient _ hB)
  exact (mean_difference_le_of_oscillation g _ ho x).trans_eq (by ring)

theorem uniform_median_upper_of_uniform_gradient
    (G : ∀ n : ℕ, Set (Disorder n)) {κ : ℝ} (hκ : 0 < κ)
    (hgrad : ∀ n, ∀ g ∈ G n, ∀ f : Observables n, ∀ r : ℝ, ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          -κ*unweightedGradient (semigroup (coupling g) r f) y) :
    ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, medianTime g ≤ (4/κ)*Real.log n := by
  have hlim := (dimensionDecay_tendsto_zero (by norm_num : (0:ℝ)<1)).sqrt
  simp only [Real.sqrt_zero] at hlim
  filter_upwards [eventually_gt_atTop (1:ℕ), hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))]
    with n hn hbound
  intro g hg
  have ht : 0 ≤ (4/κ)*Real.log n := by positivity
  have he : -κ*((4/κ)*Real.log n) = -(4:ℝ)*Real.log n := by field_simp
  have hid : (n:ℝ)*Real.sqrt ((n:ℝ)*Real.exp (-κ*((4/κ)*Real.log n))) =
      Real.sqrt (dimensionDecay 1 n) := by
    rw [he]
    change (n:ℝ)*Real.sqrt ((n:ℝ)*dimensionDecay 4 n) = _
    have hsq : (n:ℝ)^2*((n:ℝ)*dimensionDecay 4 n) = dimensionDecay 1 n := by
      calc
        _ = (n:ℝ)*((n:ℝ)*((n:ℝ)*dimensionDecay 4 n)) := by ring
        _ = (n:ℝ)*((n:ℝ)*dimensionDecay 3 n) := by rw [nat_mul_dimensionDecay (by omega)];norm_num
        _ = (n:ℝ)*dimensionDecay 2 n := by rw [nat_mul_dimensionDecay (by omega)];norm_num
        _ = dimensionDecay 1 n := by rw [nat_mul_dimensionDecay (by omega)];norm_num
    rw [←hsq,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _)]
  apply (medianTime_le_iff g ht).mpr
  exact (distance_upper_of_uniform_gradient_drift g ht (hgrad n g hg)).trans (hid ▸ hbound.le)

theorem ratio_cutoff_of_uniform_gradient (β ε η : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hη : 0 < η)
    (G : ∀ n : ℕ, Set (Disorder n)) {κ γ K : ℝ}
    (hκ : 0 < κ) (hγ : 0 < γ) (hK : 0 < K)
    (hG : Tendsto (fun n => disorderLaw β n (G n)ᶜ) atTop (𝓝 0))
    (hnorm : ∀ n, ∀ g ∈ G n, euclideanOpNorm (coupling g) ≤ K)
    (hgap : ∀ n, ∀ g ∈ G n, ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (hgrad : ∀ n, ∀ g ∈ G n, ∀ f : Observables n, ∀ r : ℝ, ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          -κ*unweightedGradient (semigroup (coupling g) r f) y) :
    Tendsto
      (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1+η <
          (mixingTime g ε : ℝ)/(mixingTime g (1-ε) : ℝ)})
      atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1-ε)) := by
  let bad : ∀ n, Disorder n → Set (Spin n) := fun _ _ => ∅
  have hgp : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f := Eventually.of_forall hgap
  have hgd (D : ℝ) (_hD : 0 < D) : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      ∀ f : Observables n, ∀ r ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad n g then 0 else 0)*
            unweightedGradient (semigroup (coupling g) r f) y := by
    apply Eventually.of_forall
    intro n g hg f r hr y
    simpa only [ite_self,add_zero] using hgrad n g hg f r y
  have hav (D m : ℝ) (_hD : 0 < D) (_hm : 0 < m) :
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ u ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ x,
      semigroup (coupling g) u (fun y => if y ∈ bad n g then 1 else 0) x ≤ dimensionDecay m n := by
    apply Eventually.of_forall
    intro n g hg u hu x
    simpa [bad,semigroup_const] using (dimensionDecay_pos m n).le
  have hrow : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ i, ∑ j, coupling g i j ^ 2 ≤ K^2 := by
    apply Eventually.of_forall
    intro n g hg i
    exact row_squares_le_opNorm (coupling g) (coupling_symm g) hK.le (hnorm n g hg) i
  have hfields := uniform_field_tails_of_small_set G bad hκ (le_refl 0) (le_refl 0)
    hγ (sq_nonneg K) hrow hgp (by simpa only [ite_self] using hgd)
      (by simpa only [bad,Set.mem_empty_iff_false,ite_false] using hav)
  have hlag := uniform_positive_lag_of_small_set_gradient G bad hκ (le_refl 0)
    (le_refl 0) hγ hgp (by simpa only [ite_self] using hgd)
      (by simpa only [bad,Set.mem_empty_iff_false,ite_false] using hav) hfields
  have hlo := uniform_median_lower_of_small_set G bad hκ (le_refl 0) (le_refl 0) hγ hgp (by simpa only [ite_self] using hgd)
      (by simpa only [bad,Set.mem_empty_iff_false,ite_false] using hav)
  have hup := uniform_median_upper_of_uniform_gradient G hκ hgrad
  apply ratio_cutoff_of_positive_lag β ε η hε hε1 hη G (c := 1/4) (C := 4/κ)
    (by norm_num) hK hnorm hG _ hlag
  filter_upwards [hlo,hup] with n hnlo hnup
  intro g hg
  exact ⟨by simpa only [one_div_mul_eq_div] using hnlo g hg,hnup g hg⟩

end SKRatio.Calculus

end
end

end OAI
