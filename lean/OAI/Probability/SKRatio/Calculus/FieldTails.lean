import Mathlib
import OAI.Probability.SKRatio.Dynamics.PositiveLag

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

def reversal {n : ℕ} (x : Spin n) : Spin n := fun i => !(x i)

@[simp] lemma reversal_reversal {n : ℕ} (x : Spin n) : reversal (reversal x) = x := by
  funext i
  simp [reversal]

@[simp] lemma spin_reversal {n : ℕ} (x : Spin n) (i : Fin n) :
    spin (reversal x) i = -spin x i := by
  cases h : x i <;> simp [spin, reversal, h]

@[simp] lemma mass_reversal {n : ℕ} (g : Disorder n) (x : Spin n) :
    mass g 0 (reversal x) = mass g 0 x := by
  have hv (i : Fin n) : spinValue (reversal x i) = -spinValue (x i) :=
    spin_reversal x i
  simp [mass, weight, hamiltonian, hv]

@[simp] lemma field_reversal {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    field J (reversal x) i = -field J x i := by
  simp [field, spin_reversal, Finset.sum_neg_distrib]

lemma gibbsMean_field_zero {n : ℕ} (g : Disorder n) (i : Fin n) :
    FiniteLaw.mean (mass g 0) (fun x => field (coupling g) x i) = 0 := by
  let e : Spin n ≃ Spin n := Function.Involutive.toPerm reversal (fun x => reversal_reversal x)
  have he := Equiv.sum_comp e (fun x => mass g 0 x * field (coupling g) x i)
  change (∑ x, mass g 0 (reversal x) * field (coupling g) (reversal x) i) = _ at he
  simp only [mass_reversal, field_reversal, mul_neg, Finset.sum_neg_distrib] at he
  unfold FiniteLaw.mean
  linarith only [he]

lemma halfDiff_field {n : ℕ} (J : Interaction n) (i j : Fin n) (x : Spin n) :
    halfDiff j (fun y => field J y i) x = J i j := by
  unfold field
  rw [halfDiff_sum]
  have hlin (l : Fin n) : halfDiff j (fun y => J i l * spin y l) x =
      J i l * halfDiff j (fun y => spin y l) x := by unfold halfDiff; ring
  simp only [hlin, halfDiff_spin, mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq]

lemma unweightedGradient_field {n : ℕ} (J : Interaction n) (i : Fin n) (x : Spin n) :
    unweightedGradient (fun y => field J y i) x = ∑ j, J i j ^ 2 := by
  simp [unweightedGradient, halfDiff_field]

lemma stationary_field_variance_le {n : ℕ} (g : Disorder n) {γ R : ℝ}
    (hγ : 0 < γ) (hrow : ∀ i, ∑ j, coupling g i j ^ 2 ≤ R)
    (hgap : ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f) (i : Fin n) :
    FiniteLaw.variance (mass g 0) (fun y => field (coupling g) y i) ≤ 2*R/γ := by
  apply (le_div_iff₀ hγ).mpr
  have h := hgap (fun y => field (coupling g) y i)
  have hE : stationaryEnergy g (fun y => field (coupling g) y i) ≤ 2*R := by
    unfold stationaryEnergy FiniteLaw.mean
    calc
      _ ≤ ∑ x, mass g 0 x * (2*R) := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ (mass_nonneg g 0 x)
        have hh := weightedGradient_le (coupling g) (fun y => field (coupling g) y i) x
        rw [unweightedGradient_field] at hh
        exact hh.trans (mul_le_mul_of_nonneg_left (hrow i) (by norm_num))
      _ = _ := by rw [← Finset.sum_mul, sum_mass, one_mul]
  linarith only [h, hE]

lemma field_mean_of_overlap {n : ℕ} (g : Disorder n) {t ε V W : ℝ}
    (ht : 0 ≤ t) (hε : 0 < ε) (hoverlap : continuousDistance g t ≤ 1-ε)
    (hvar : ∀ x i, FiniteLaw.variance (continuousKernel (coupling g) t x)
      (fun y => field (coupling g) y i) ≤ V)
    (hstat : ∀ i, FiniteLaw.variance (mass g 0) (fun y => field (coupling g) y i) ≤ W)
    (x : Spin n) (i : Fin n) :
    |semigroup (coupling g) t (fun y => field (coupling g) y i) x| ≤
      (Real.sqrt V+Real.sqrt W)/Real.sqrt ε := by
  have h := FiniteLaw.common_mass_means (continuousKernel (coupling g) t x) (mass g 0)
    (fun y => field (coupling g) y i)
    (continuousKernel_nonneg _ t ht x) (mass_nonneg g 0)
    (continuousKernel_sum _ t x) (sum_mass g 0) hε
    ((tv_le_continuousDistance g t x).trans hoverlap)
  rw [gibbsMean_field_zero, sub_zero] at h
  rw [← semigroup_eq_kernel] at h
  exact h.trans (div_le_div_of_nonneg_right
    (add_le_add (Real.sqrt_le_sqrt (hvar x i)) (Real.sqrt_le_sqrt (hstat i)))
      (Real.sqrt_nonneg _))

lemma exp_abs_le_sum (z : ℝ) : Real.exp |z| ≤ Real.exp z + Real.exp (-z) := by
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    linarith [Real.exp_pos (-z)]
  · rw [abs_of_nonpos hz]
    linarith [Real.exp_pos z]

lemma indicator_max_le_exp {n : ℕ} (u c : Fin n → ℝ) {θ H m : ℝ}
    (hθ : 0 ≤ θ) (hc : ∀ i, |c i| ≤ m) :
    (if ∃ i, H < |u i| then (1:ℝ) else 0) ≤
      Real.exp (-θ*(H-m)) * ∑ i, (Real.exp (θ*(u i-c i)) + Real.exp (-θ*(u i-c i))) := by
  classical
  by_cases hu : ∃ i, H < |u i|
  · simp only [hu, ↓reduceIte]
    obtain ⟨i, hi⟩ := hu
    have htri : H-m ≤ |u i-c i| := by
      have hh : |u i| ≤ |u i-c i|+|c i| := by
        simpa only [sub_add_cancel] using abs_add_le (u i-c i) (c i)
      linarith [hc i]
    have hs : Real.exp (θ*|u i-c i|) ≤
        ∑ j, (Real.exp (θ*(u j-c j)) + Real.exp (-θ*(u j-c j))) := by
      have hh := exp_abs_le_sum (θ*(u i-c i))
      rw [abs_mul, abs_of_nonneg hθ] at hh
      have hh' : Real.exp (θ*|u i-c i|) ≤
          Real.exp (θ*(u i-c i))+Real.exp (-θ*(u i-c i)) := by
        simpa only [neg_mul] using hh
      exact hh'.trans (Finset.single_le_sum (f := fun j =>
        Real.exp (θ*(u j-c j))+Real.exp (-θ*(u j-c j)))
        (fun j _ => by positivity) (Finset.mem_univ i))
    calc
      1 ≤ Real.exp (-θ*(H-m))*Real.exp (θ*|u i-c i|) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]
        have hh := mul_le_mul_of_nonneg_left htri hθ
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
  · simp only [hu, ↓reduceIte]
    positivity

lemma semigroup_max_tail {n : ℕ} (J : Interaction n) (f : Fin n → Observables n)
    {t θ H m C : ℝ} (ht : 0 ≤ t) (hθ : 0 ≤ θ) (x : Spin n)
    (hmean : ∀ i, |semigroup J t (f i) x| ≤ m)
    (hmgf : ∀ i, ∀ σ ∈ ({-1,1}:Set ℝ),
      semigroup J t (fun y => Real.exp (σ*θ*(f i y-semigroup J t (f i) x))) x ≤ C) :
    semigroup J t (fun y => if ∃ i, H < |f i y| then (1:ℝ) else 0) x ≤
      2*(n:ℝ)*C*Real.exp (-θ*(H-m)) := by
  classical
  have hh := semigroup_mono J ht _ _ (fun y =>
    indicator_max_le_exp (fun i => f i y) (fun i => semigroup J t (f i) x) (H := H) hθ hmean) x
  have he : (fun y => Real.exp (-θ*(H-m))*∑ i,
      (Real.exp (θ*(f i y-semigroup J t (f i) x)) +
       Real.exp (-θ*(f i y-semigroup J t (f i) x)))) =
      Real.exp (-θ*(H-m)) • ∑ i : Fin n,
        ((fun y => Real.exp (θ*(f i y-semigroup J t (f i) x))) +
         (fun y => Real.exp (-θ*(f i y-semigroup J t (f i) x)))) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.add_apply]
  rw [he, map_smul, map_sum] at hh
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, map_add, Pi.add_apply] at hh
  have hib : ∀ i : Fin n,
      semigroup J t (fun y => Real.exp (θ*(f i y-semigroup J t (f i) x))) x +
      semigroup J t (fun y => Real.exp (-θ*(f i y-semigroup J t (f i) x))) x ≤ 2*C := by
    intro i
    have hpos := hmgf i 1 (by simp)
    have hneg := hmgf i (-1) (by simp)
    simp only [one_mul, neg_one_mul] at hpos hneg
    linarith
  calc
    _ ≤ _ := hh
    _ ≤ Real.exp (-θ*(H-m))*∑ _i : Fin n, 2*C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hib i)) (Real.exp_pos _).le
    _ = _ := by simp; ring

theorem uniform_field_tails_of_moments
    (G : ∀ n : ℕ, Set (Disorder n)) {V W : ℝ}
    (hstat : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ i,
      FiniteLaw.variance (mass g 0) (fun y => field (coupling g) y i) ≤ W)
    (hvar : ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      ∀ t ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ x i,
      FiniteLaw.variance (continuousKernel (coupling g) t x)
        (fun y => field (coupling g) y i) ≤ V)
    (hmgf : ∀ D θ : ℝ, 0 < D → 0 < θ → ∃ M : ℝ,
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ t ∈ Set.Icc (0:ℝ) (D*Real.log n),
      ∀ x i, ∀ σ ∈ ({-1,1}:Set ℝ), semigroup (coupling g) t
        (fun y => Real.exp (σ*θ*(field (coupling g) y i-
          semigroup (coupling g) t (fun z => field (coupling g) z i) x))) x ≤ M) :
    ∀ ε δ D m : ℝ, 0 < ε → 0 < δ → 0 < D → 0 < m →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ t ∈ Set.Icc (0:ℝ) (D*Real.log n),
      continuousDistance g t ≤ 1-ε → ∀ x, semigroup (coupling g) t
        (fun y => if ∃ i, δ*Real.log n < |field (coupling g) y i| then 1 else 0) x ≤
          dimensionDecay m n := by
  intro ε δ D m hε hδ hD hm
  let θ := (m+2)/δ
  have hθ : 0 < θ := div_pos (by linarith only [hm]) hδ
  have hθδ : θ*δ = m+2 := div_mul_cancel₀ _ (ne_of_gt hδ)
  let B := (Real.sqrt V+Real.sqrt W)/Real.sqrt ε
  obtain ⟨M,hM⟩ := hmgf D θ hD hθ
  have herr := (dimensionDecay_tendsto_zero (by norm_num : (0:ℝ)<1)).const_mul
    (2*M*Real.exp (θ*B))
  simp only [mul_zero] at herr
  have herr' : ∀ᶠ n : ℕ in atTop,
      (2*M*Real.exp (θ*B))*dimensionDecay 1 n ≤ 1 := by
    filter_upwards [herr.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
    simpa only [mul_zero] using hn.le
  filter_upwards [hstat,hvar D hD,hM,herr',eventually_gt_atTop 0]
    with n hnstat hnvar hnmgf hnerr hn
  intro g hg t ht ho x
  have hmean := field_mean_of_overlap g ht.1 hε ho (hnvar g hg t ht) (hnstat g hg) x
  have h := semigroup_max_tail (coupling g) (fun i y => field (coupling g) y i)
    (H := δ*Real.log n) ht.1 hθ.le x hmean (hnmgf g hg t ht x)
  have he : 2*(n:ℝ)*M*Real.exp (-θ*(δ*Real.log n-B)) =
      ((2*M*Real.exp (θ*B))*dimensionDecay 1 n)*dimensionDecay m n := by
    have he' : Real.exp (-θ*(δ*Real.log n-B)) =
        Real.exp (θ*B)*dimensionDecay (m+2) n := by
      unfold dimensionDecay
      rw [← Real.exp_add]
      congr 1
      calc
        _ = θ*B-(θ*δ)*Real.log n := by ring
        _ = _ := by rw [hθδ]; ring
    rw [he']
    calc
      _ = (2*M*Real.exp (θ*B))*((n:ℝ)*dimensionDecay (m+2) n) := by ring
      _ = (2*M*Real.exp (θ*B))*dimensionDecay (m+2-1) n := by
        rw [nat_mul_dimensionDecay hn]
      _ = (2*M*Real.exp (θ*B))*(dimensionDecay 1 n*dimensionDecay m n) := by
        congr 1
        unfold dimensionDecay
        rw [← Real.exp_add]
        congr 1
        ring
      _ = _ := by ring
  change _ ≤ 2*(n:ℝ)*M*Real.exp (-θ*(δ*Real.log n-B)) at h
  rw [he] at h
  exact h.trans (by simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right hnerr (dimensionDecay_pos m n).le))

end SKRatio.Calculus

end
end

end OAI
