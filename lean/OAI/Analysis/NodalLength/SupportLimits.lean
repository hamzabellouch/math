import OAI.Analysis.NodalLength.Normalization

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

abbrev SupportIndex (v : ℕ → Plane → ℝ) := Σ j : ℕ, {x : Plane // x ∈ tsupport (v j)}

def supportFilter (v : ℕ → Plane → ℝ) : Filter (SupportIndex v) :=
  Filter.comap (fun z => z.1) Filter.atTop

def SupportLimit (v f : ℕ → Plane → ℝ) (A : ℝ) : Prop :=
  Filter.Tendsto (fun z : SupportIndex v => f z.1 z.2.1) (supportFilter v) (𝓝 A)

open Filter in
lemma eventually_support_iff (v : ℕ → Plane → ℝ) (P : ℕ → Plane → Prop) :
    (∀ᶠ z : SupportIndex v in supportFilter v, P z.1 z.2.1) ↔
      ∀ᶠ j in atTop, ∀ x ∈ tsupport (v j), P j x := by
  rw [supportFilter, eventually_comap]
  constructor
  · intro h
    filter_upwards [h] with j hj x hx
    exact hj ⟨j, x, hx⟩ rfl
  · intro h
    filter_upwards [h] with j hj z hz
    subst j
    exact hj z.2.1 z.2.2

lemma SupportLimit.eventually_abs_sub_le {v f : ℕ → Plane → ℝ} {A ε : ℝ}
    (h : SupportLimit v f A) (hε : 0 < ε) :
    ∀ᶠ j in Filter.atTop, ∀ x ∈ tsupport (v j), |f j x-A| ≤ ε := by
  apply (eventually_support_iff v _).mp
  have hh := (Metric.tendsto_nhds.mp h) ε hε
  filter_upwards [hh] with z hz
  exact (show |f z.1 z.2.1-A| < ε from hz).le

lemma SupportLimit.const {v : ℕ → Plane → ℝ} (A : ℝ) :
    SupportLimit v (fun _ _ => A) A := tendsto_const_nhds

open Filter in
lemma SupportLimit.of_seq {v : ℕ → Plane → ℝ} {r : ℕ → ℝ} {A : ℝ}
    (h : Tendsto r atTop (𝓝 A)) : SupportLimit v (fun j _ => r j) A :=
  h.comp tendsto_comap

lemma SupportLimit.add {v f g : ℕ → Plane → ℝ} {A B : ℝ}
    (hf : SupportLimit v f A) (hg : SupportLimit v g B) :
    SupportLimit v (fun j x => f j x + g j x) (A+B) := Filter.Tendsto.add hf hg

lemma SupportLimit.sub {v f g : ℕ → Plane → ℝ} {A B : ℝ}
    (hf : SupportLimit v f A) (hg : SupportLimit v g B) :
    SupportLimit v (fun j x => f j x - g j x) (A-B) := Filter.Tendsto.sub hf hg

lemma SupportLimit.mul {v f g : ℕ → Plane → ℝ} {A B : ℝ}
    (hf : SupportLimit v f A) (hg : SupportLimit v g B) :
    SupportLimit v (fun j x => f j x * g j x) (A*B) := Filter.Tendsto.mul hf hg

lemma SupportLimit.neg {v f : ℕ → Plane → ℝ} {A : ℝ}
    (hf : SupportLimit v f A) : SupportLimit v (fun j x => -f j x) (-A) := Filter.Tendsto.neg hf

lemma SupportLimit.pow {v f : ℕ → Plane → ℝ} {A : ℝ}
    (hf : SupportLimit v f A) (n : ℕ) : SupportLimit v (fun j x => (f j x)^n) (A^n) := Filter.Tendsto.pow hf n

open Filter in
lemma coefficient_square_tendsto_const_support {a v : ℕ → Plane → ℝ} {A : ℝ}
    (ha : ∀ j, Smooth (a j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j) = 1)
    (hlim : SupportLimit v a A) :
    Tendsto (fun j => ∫ x, a j x * (v j x * v j x)) atTop (𝓝 A) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := hlim.eventually_abs_sub_le (half_pos hε)
  filter_upwards [he] with j hj
  have hb := integral_coefficient_square_abs_le ((ha j).sub contDiff_const) (hv j) (hcv j)
    (half_pos hε).le hj
  have hid := integral_coefficient_difference A (ha j) (hv j) (hv j) (hcv j)
  simp only [mul_assoc] at hid
  rw [hid] at hb
  change |(∫ x, a j x * (v j x*v j x))-A*l2sq (v j)| ≤ ε/2*l2sq (v j) at hb
  rw [hv1 j, mul_one, mul_one] at hb
  exact hb.trans_lt (half_lt_self hε)

open Filter in
lemma coefficient_pairing_support_zero_of_bound {a v f g : ℕ → Plane → ℝ} {r : ℕ → ℝ} {E : ℝ}
    (ha : ∀ j, Smooth (a j)) (hf : ∀ j, Smooth (f j)) (hg : ∀ j, Smooth (g j))
    (hcf : ∀ j, HasCompactSupport (f j)) (hcg : ∀ j, HasCompactSupport (g j))
    (hsub : ∀ j, tsupport (f j) ⊆ tsupport (v j))
    (hlim : SupportLimit v a 0)
    (hbound : ∀ j, l2sq (f j)+l2sq (g j) ≤ r j)
    (henergy : Tendsto r atTop (𝓝 E)) :
    Tendsto (fun j => ∫ x, a j x * f j x * g j x) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let B := |E|+1
  have hB : 0 < B := by dsimp [B]; linarith only [abs_nonneg E]
  have hEB : E < B := by dsimp [B]; linarith only [le_abs_self E]
  have he := hlim.eventually_abs_sub_le (div_pos hε hB)
  have hEB' := henergy.eventually_lt_const hEB
  filter_upwards [he, hEB'] with j hj hEj
  have hb := integral_coefficient_mul_abs_le (ha j) (hf j) (hg j) (hcf j) (hcg j)
    (div_pos hε hB).le (fun x hx => by simpa only [sub_zero] using hj x (hsub j hx))
  rw [Real.dist_eq, sub_zero]
  calc
    _ ≤ ε/B/2*(l2sq (f j)+l2sq (g j)) := hb
    _ ≤ ε/B/2*B := mul_le_mul_of_nonneg_left ((hbound j).trans hEj.le) (div_nonneg (div_pos hε hB).le (by norm_num))
    _ = ε/2 := by field_simp
    _ < ε := half_lt_self hε

def hessianGradientEnergy (T v : Plane → ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    ∫ x, coordPartial (coordPartial T j) i x * coordPartial T j x * coordPartial T i x * (v x*v x)

lemma carleman_commutator_energy {T p v : Plane → ℝ}
    (hT : Smooth T) (hp : Smooth p) (hv : Smooth v) (hc : HasCompactSupport v) (K : ℝ) :
    2 * (∫ x, plusPart (fun x => gradientSquared T x + K^2*p x) v x * skewPart T v x) =
      4*hessianEnergy T v + 4*hessianGradientEnergy T v - bilaplacianEnergy T v +
        2*K^2*potentialTransport p T v := by
  rw [show plusPart (fun x => gradientSquared T x + K^2*p x) v =
      (fun x => euclideanLaplacian v x + (gradientSquared T x + K^2*p x)*v x) from rfl,
    carleman_commutator hT hp hv hc]
  simp only [hessianEnergy, hessianGradientEnergy, bilaplacianEnergy, potentialTransport,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  ring

lemma integral_normalized_hessianGradient (T v : Plane → ℝ) (S D : ℝ) (i j : Fin 2) :
    (∫ x, (coordPartial (coordPartial T j) i x / S) *
      (coordPartial T j x / D) * (coordPartial T i x / D) * (v x*v x)) =
    (∫ x, coordPartial (coordPartial T j) i x * coordPartial T j x * coordPartial T i x * (v x*v x)) /
      (S*D^2) := by
  calc
    _ = ∫ x, (coordPartial (coordPartial T j) i x * coordPartial T j x * coordPartial T i x * (v x*v x)) /
        (S*D^2) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := integral_div _ _

open Filter in
lemma normalized_hessianGradient_limit {T v : ℕ → Plane → ℝ} {S D : ℕ → ℝ}
    (a : Fin 2 → ℝ) (H : Fin 2 → Fin 2 → ℝ)
    (hT : ∀ j, Smooth (T j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j)=1)
    (hgrad : ∀ i, SupportLimit v (fun j x => coordPartial (T j) i x / D j) (a i))
    (hH : ∀ i k, SupportLimit v (fun j x => coordPartial (coordPartial (T j) k) i x / S j) (H i k)) :
    Tendsto (fun j => hessianGradientEnergy (T j) (v j)/(S j*(D j)^2)) atTop
      (𝓝 (∑ i : Fin 2, ∑ k : Fin 2, H i k * a k * a i)) := by
  have hi (i k : Fin 2) := coefficient_square_tendsto_const_support
    (fun j => (((smooth_partial (smooth_partial (hT j) k) i).div_const _).mul
        ((smooth_partial (hT j) k).div_const _)).mul ((smooth_partial (hT j) i).div_const _))
    hv hcv hv1 (((hH i k).mul (hgrad k)).mul (hgrad i))
  have hs := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun k _ => hi i k))
  simpa only [integral_normalized_hessianGradient, hessianGradientEnergy, Finset.sum_div] using hs

open Filter in
lemma variable_quadratic_difference_support_limit {v h₀ h₁ h₂ f g : ℕ → Plane → ℝ}
    {A B C E : ℝ}
    (hh₀ : ∀ j, Smooth (h₀ j)) (hh₁ : ∀ j, Smooth (h₁ j)) (hh₂ : ∀ j, Smooth (h₂ j))
    (hf : ∀ j, Smooth (f j)) (hg : ∀ j, Smooth (g j))
    (hcf : ∀ j, HasCompactSupport (f j)) (hcg : ∀ j, HasCompactSupport (g j))
    (hsubf : ∀ j, tsupport (f j) ⊆ tsupport (v j))
    (hsubg : ∀ j, tsupport (g j) ⊆ tsupport (v j))
    (hb₀ : SupportLimit v h₀ A) (hb₁ : SupportLimit v h₁ B) (hb₂ : SupportLimit v h₂ C)
    (henergy : Tendsto (fun j => l2sq (f j) + l2sq (g j)) atTop (𝓝 E)) :
    Tendsto (fun j =>
      ((∫ x, h₀ j x * f j x * f j x) + 2*(∫ x, h₁ j x * f j x * g j x) +
        (∫ x, h₂ j x * g j x * g j x)) - quadraticEnergy A B C (f j) (g j))
      atTop (𝓝 0) := by
  have hfbound (j : ℕ) : l2sq (f j) + l2sq (f j) ≤ 2*(l2sq (f j)+l2sq (g j)) := by
    linarith only [l2sq_nonneg (g j)]
  have hgbound (j : ℕ) : l2sq (g j) + l2sq (g j) ≤ 2*(l2sq (f j)+l2sq (g j)) := by
    linarith only [l2sq_nonneg (f j)]
  have h₀lim : SupportLimit v (fun j x => h₀ j x-A) 0 := by
    simpa only [sub_self] using hb₀.sub (SupportLimit.const A)
  have h₁lim : SupportLimit v (fun j x => h₁ j x-B) 0 := by
    simpa only [sub_self] using hb₁.sub (SupportLimit.const B)
  have h₂lim : SupportLimit v (fun j x => h₂ j x-C) 0 := by
    simpa only [sub_self] using hb₂.sub (SupportLimit.const C)
  have h₀zero := coefficient_pairing_support_zero_of_bound
    (fun j => (hh₀ j).sub contDiff_const) hf hf hcf hcf hsubf h₀lim hfbound (henergy.const_mul 2)
  have h₁zero := coefficient_pairing_support_zero_of_bound
    (fun j => (hh₁ j).sub contDiff_const) hf hg hcf hcg hsubf h₁lim (fun _ => le_rfl) henergy
  have h₂zero := coefficient_pairing_support_zero_of_bound
    (fun j => (hh₂ j).sub contDiff_const) hg hg hcg hcg hsubg h₂lim hgbound (henergy.const_mul 2)
  have hi (j : ℕ) :
      (∫ x, (h₀ j x-A)*f j x*f j x) + 2*(∫ x, (h₁ j x-B)*f j x*g j x) +
      (∫ x, (h₂ j x-C)*g j x*g j x) =
      ((∫ x, h₀ j x * f j x * f j x) + 2*(∫ x, h₁ j x * f j x * g j x) +
        (∫ x, h₂ j x * g j x * g j x)) - quadraticEnergy A B C (f j) (g j) := by
    rw [integral_coefficient_difference A (hh₀ j) (hf j) (hf j) (hcf j),
      integral_coefficient_difference B (hh₁ j) (hf j) (hg j) (hcf j),
      integral_coefficient_difference C (hh₂ j) (hg j) (hg j) (hcg j)]
    unfold quadraticEnergy l2sq
    ring
  simpa only [hi, mul_zero, add_zero] using (h₀zero.add (h₁zero.const_mul 2)).add h₂zero

open Filter in
lemma normalized_hessian_trace_support_limit {T v : ℕ → Plane → ℝ} {S D : ℕ → ℝ}
    (a₀ a₁ A B C : ℝ) (ha : a₀^2+a₁^2 ≠ 0)
    (hT : ∀ j, Smooth (T j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j))
    (hb₀ : SupportLimit v (fun j x => coordPartial (coordPartial (T j) 0) 0 x/S j) A)
    (hb₁ : SupportLimit v (fun j x => coordPartial (coordPartial (T j) 0) 1 x/S j) B)
    (hb₂ : SupportLimit v (fun j x => coordPartial (coordPartial (T j) 1) 1 x/S j) C)
    (henergy : Tendsto (fun j => l2sq (normalizedPartial (v j) (D j) 0) +
      l2sq (normalizedPartial (v j) (D j) 1)) atTop (𝓝 (a₀^2+a₁^2)))
    (hparallel : Tendsto (fun j => l2sq (fun x => a₀ * normalizedPartial (v j) (D j) 0 x +
      a₁ * normalizedPartial (v j) (D j) 1 x)) atTop (𝓝 0)) :
    Tendsto (fun j => hessianEnergy (T j) (v j) / (S j*(D j)^2) +
      (A*a₀^2+2*B*a₀*a₁+C*a₁^2)) atTop (𝓝 ((a₀^2+a₁^2)*(A+C))) := by
  have htrace := plane_trace_energy_limit a₀ a₁ A B C ha
    (fun j => smooth_normalizedPartial (hv j) _ _) (fun j => smooth_normalizedPartial (hv j) _ _)
    (fun j => compact_normalizedPartial (hcv j) _ _) (fun j => compact_normalizedPartial (hcv j) _ _)
    henergy hparallel
  have herr := variable_quadratic_difference_support_limit
    (fun j => (smooth_partial (smooth_partial (hT j) 0) 0).div_const _)
    (fun j => (smooth_partial (smooth_partial (hT j) 0) 1).div_const _)
    (fun j => (smooth_partial (smooth_partial (hT j) 1) 1).div_const _)
    (fun j => smooth_normalizedPartial (hv j) _ _) (fun j => smooth_normalizedPartial (hv j) _ _)
    (fun j => compact_normalizedPartial (hcv j) _ _) (fun j => compact_normalizedPartial (hcv j) _ _)
    (fun j => normalizedPartial_tsupport_subset _ _ _) (fun j => normalizedPartial_tsupport_subset _ _ _)
    hb₀ hb₁ hb₂ henergy
  have hsum := herr.add htrace
  convert hsum using 1
  · ext j
    rw [normalized_hessian_expansion (hT j)]
    ring
  · simp only [zero_add]

open Filter in
lemma normalized_gradient_energy_support_limit {q v : ℕ → Plane → ℝ} {S D : ℕ → ℝ} {C A : ℝ}
    (hq : ∀ j, Smooth (q j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j) = 1)
    (hS : ∀ j, 1 ≤ S j) (hD : ∀ j, S j ≤ D j) (hSinf : Tendsto S atTop atTop)
    (hbound : ∀ j, l2norm (plusPart (q j) (v j)) ≤ C * (Real.sqrt (S j) * D j))
    (hlim : SupportLimit v (fun j x => q j x/(D j)^2) A) :
    Tendsto (fun j => l2sq (normalizedPartial (v j) (D j) 0) +
      l2sq (normalizedPartial (v j) (D j) 1)) atTop (𝓝 A) := by
  have hpair := pairing_div_square_tendsto_zero (fun j => smooth_plus (hq j) (hv j)) hv
    (fun j => compact_plus (hcv j)) hcv hv1 hS hD hSinf hbound
  have hcoeff := coefficient_square_tendsto_const_support (fun j => (hq j).div_const ((D j)^2)) hv
    hcv hv1 hlim
  have hi (j : ℕ) : l2sq (normalizedPartial (v j) (D j) 0) +
      l2sq (normalizedPartial (v j) (D j) 1) =
      (∫ x, (q j x / (D j)^2) * (v j x * v j x)) -
        (∫ x, plusPart (q j) (v j) x * v j x) / (D j)^2 := by
    rw [normalizedPartial_energy, normalized_coefficient_integral, plus_energy_identity (hq j) (hv j) (hcv j)]
    ring
  simpa only [← hi, sub_zero] using hcoeff.sub hpair

open Filter in
lemma l2sq_coefficient_mul_support_zero {a v f : ℕ → Plane → ℝ} {r : ℕ → ℝ} {E : ℝ}
    (ha : ∀ j, Smooth (a j)) (hf : ∀ j, Smooth (f j))
    (hcf : ∀ j, HasCompactSupport (f j)) (hsub : ∀ j, tsupport (f j) ⊆ tsupport (v j))
    (hlim : SupportLimit v a 0)
    (hbound : ∀ j, l2sq (f j) ≤ r j) (hr : Tendsto r atTop (𝓝 E)) :
    Tendsto (fun j => l2sq (fun x => a j x*f j x)) atTop (𝓝 0) := by
  have hlim2 : SupportLimit v (fun j x => (a j x)^2) 0 := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hlim.pow 2
  have h := coefficient_pairing_support_zero_of_bound (fun j => (ha j).pow 2) hf hf hcf hcf hsub hlim2
    (fun j => by linarith only [hbound j] : ∀ j, l2sq (f j)+l2sq (f j) ≤ 2*r j) (hr.const_mul 2)
  convert h using 1
  ext j
  unfold l2sq
  apply integral_congr_ae
  filter_upwards [] with x
  ring

open Filter in
lemma normalized_parallel_support_limit {T v : ℕ → Plane → ℝ} {S D : ℕ → ℝ} {c C E : ℝ}
    (a : Fin 2 → ℝ)
    (hT : ∀ j, Smooth (T j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j) = 1)
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hS : ∀ j, 1 ≤ S j) (hD : ∀ j, S j ≤ D j)
    (hSinf : Tendsto S atTop atTop)
    (hY : ∀ j, l2norm (skewPart (T j) (v j)) ≤ C*(Real.sqrt (S j)*D j))
    (hH : ∀ j i k x, x ∈ tsupport (v j) → |coordPartial (coordPartial (T j) k) i x| ≤ c*S j)
    (hgrad : ∀ i, SupportLimit v (fun j x => coordPartial (T j) i x / D j) (a i))
    (henergy : Tendsto (fun j => l2sq (normalizedPartial (v j) (D j) 0) +
      l2sq (normalizedPartial (v j) (D j) 1)) atTop (𝓝 E)) :
    Tendsto (fun j => l2sq (fun x => a 0 * normalizedPartial (v j) (D j) 0 x +
      a 1 * normalizedPartial (v j) (D j) 1 x)) atTop (𝓝 0) := by
  let f := fun j i => normalizedPartial (v j) (D j) i
  let q := fun j i x => a i - coordPartial (T j) i x / D j
  have hf (j i) : Smooth (f j i) := smooth_normalizedPartial (hv j) _ _
  have hcf (j i) : HasCompactSupport (f j i) := compact_normalizedPartial (hcv j) _ _
  have hq (j i) : Smooth (q j i) := contDiff_const.sub ((smooth_partial (hT j) i).div_const _)
  have htotal (j : ℕ) (i : Fin 2) : l2sq (f j i) ≤ l2sq (f j 0)+l2sq (f j 1) := by
    fin_cases i
    · change l2sq (f j 0) ≤ l2sq (f j 0)+l2sq (f j 1)
      linarith only [l2sq_nonneg (f j 1)]
    · change l2sq (f j 1) ≤ l2sq (f j 0)+l2sq (f j 1)
      linarith only [l2sq_nonneg (f j 0)]
  have hzero (i : Fin 2) : Tendsto (fun j => l2sq (fun x => q j i x*f j i x)) atTop (𝓝 0) := by
    apply l2sq_coefficient_mul_support_zero (fun j => hq j i) (fun j => hf j i)
      (fun j => hcf j i) (fun j => normalizedPartial_tsupport_subset _ _ _) _
      (fun j => htotal j i) henergy
    simpa only [q, sub_self] using (SupportLimit.const (a i)).sub (hgrad i)
  have hcorr := l2sq_add_tendsto_zero
    (fun j => (hq j 0).mul (hf j 0)) (fun j => (hq j 1).mul (hf j 1))
    (fun j => (hcf j 0).mul_left) (fun j => (hcf j 1).mul_left) (hzero 0) (hzero 1)
  have htransport := normalized_transport_square_limit hT hv hcv hv1 hc hC hS hD hSinf hY hH
  have hsum := l2sq_add_tendsto_zero (fun j => smooth_normalizedTransport (hT j) (hv j) _)
    (fun j => ((hq j 0).mul (hf j 0)).add ((hq j 1).mul (hf j 1)))
    (fun j => compact_normalizedTransport (hcv j) _)
    (fun j => (hcf j 0).mul_left.add (hcf j 1).mul_left) htransport hcorr
  convert hsum using 1
  ext j
  congr 1
  ext x
  dsimp [normalizedTransport, f, q]
  ring

lemma normalized_potential_coefficient_limit {T p v : ℕ → Plane → ℝ} {D K : ℕ → ℝ}
    (a : Fin 2 → ℝ)
    (hgrad : ∀ i, SupportLimit v (fun j x => coordPartial (T j) i x/D j) (a i))
    (hp : SupportLimit v (fun j x => (K j)^2*p j x/(D j)^2) 0) :
    SupportLimit v (fun j x => (gradientSquared (T j) x+(K j)^2*p j x)/(D j)^2)
      ((a 0)^2+(a 1)^2) := by
  have h := ((hgrad 0).pow 2).add ((hgrad 1).pow 2) |>.add hp
  convert h using 1
  · ext j x
    simp only [gradientSquared, Fin.sum_univ_two, div_pow]
    ring
  · simp only [add_zero]

open Filter in
lemma normalized_bilaplacian_limit {T v : ℕ → Plane → ℝ} {S D : ℕ → ℝ}
    (hT : ∀ j, Smooth (T j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j)=1)
    (hB : ∀ i k, SupportLimit v (fun j x =>
      coordPartial (coordPartial (coordPartial (coordPartial (T j) k) k) i) i x / (S j*(D j)^2)) 0) :
    Tendsto (fun j => bilaplacianEnergy (T j) (v j)/(S j*(D j)^2)) atTop (𝓝 0) := by
  have hi (i k : Fin 2) := coefficient_square_tendsto_const_support
    (fun j => (smooth_partial (smooth_partial (smooth_partial (smooth_partial (hT j) k) k) i) i).div_const _)
    hv hcv hv1 (hB i k)
  have hnorm (j : ℕ) (i k : Fin 2) :
      (∫ x, (coordPartial (coordPartial (coordPartial (coordPartial (T j) k) k) i) i x /
        (S j*(D j)^2))*(v j x*v j x)) =
      (∫ x, coordPartial (coordPartial (coordPartial (coordPartial (T j) k) k) i) i x *
        (v j x*v j x))/(S j*(D j)^2) := by
    simp only [div_mul_eq_mul_div]
    exact integral_div _ _
  simpa only [hnorm, bilaplacianEnergy, Finset.sum_div, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun k _ => tendsto_finsetSum Finset.univ (fun i _ => hi i k))

open Filter in
lemma normalized_potentialTransport_limit {T p v : ℕ → Plane → ℝ} {S D K : ℕ → ℝ}
    (hT : ∀ j, Smooth (T j)) (hp : ∀ j, Smooth (p j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j)=1)
    (hP : ∀ i, SupportLimit v (fun j x =>
      (K j)^2*coordPartial (p j) i x*coordPartial (T j) i x/(S j*(D j)^2)) 0) :
    Tendsto (fun j => (K j)^2*potentialTransport (p j) (T j) (v j)/(S j*(D j)^2)) atTop (𝓝 0) := by
  have hi (i : Fin 2) := coefficient_square_tendsto_const_support
    (fun j => ((contDiff_const.mul (smooth_partial (hp j) i)).mul (smooth_partial (hT j) i)).div_const _)
    hv hcv hv1 (hP i)
  have hnorm (j : ℕ) (i : Fin 2) :
      (∫ x, ((K j)^2*coordPartial (p j) i x*coordPartial (T j) i x/(S j*(D j)^2))*(v j x*v j x)) =
      (K j)^2*(∫ x, coordPartial (p j) i x*coordPartial (T j) i x*(v j x*v j x))/(S j*(D j)^2) := by
    simp only [div_mul_eq_mul_div, mul_assoc]
    rw [integral_div, integral_const_mul]
  simpa only [hnorm, potentialTransport, Finset.sum_div, Finset.mul_sum, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun i _ => hi i)

lemma hessian_form_expansion (a : Fin 2 → ℝ) (H : Fin 2 → Fin 2 → ℝ)
    (hsym : H 0 1=H 1 0) :
    (∑ i : Fin 2, ∑ k : Fin 2, H i k*a k*a i) =
      H 0 0*(a 0)^2 + 2*H 1 0*a 0*a 1 + H 1 1*(a 1)^2 := by
  simp only [Fin.sum_univ_two, hsym]
  ring

open Filter in

lemma normalized_commutator_trace_limit {T p v : ℕ → Plane → ℝ} {S D K : ℕ → ℝ}
    (a : Fin 2 → ℝ) (H : Fin 2 → Fin 2 → ℝ)
    (ha : (a 0)^2+(a 1)^2 ≠ 0) (hsym : H 0 1=H 1 0)
    (hT : ∀ j, Smooth (T j)) (hp : ∀ j, Smooth (p j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j)=1)
    (hgrad : ∀ i, SupportLimit v (fun j x => coordPartial (T j) i x/D j) (a i))
    (hH : ∀ i k, SupportLimit v (fun j x => coordPartial (coordPartial (T j) k) i x/S j) (H i k))
    (hB : ∀ i k, SupportLimit v (fun j x =>
      coordPartial (coordPartial (coordPartial (coordPartial (T j) k) k) i) i x / (S j*(D j)^2)) 0)
    (hP : ∀ i, SupportLimit v (fun j x =>
      (K j)^2*coordPartial (p j) i x*coordPartial (T j) i x/(S j*(D j)^2)) 0)
    (henergy : Tendsto (fun j => l2sq (normalizedPartial (v j) (D j) 0) +
      l2sq (normalizedPartial (v j) (D j) 1)) atTop (𝓝 ((a 0)^2+(a 1)^2)))
    (hparallel : Tendsto (fun j => l2sq (fun x => a 0 * normalizedPartial (v j) (D j) 0 x +
      a 1 * normalizedPartial (v j) (D j) 1 x)) atTop (𝓝 0)) :
    Tendsto (fun j => (2*(∫ x, plusPart (fun x => gradientSquared (T j) x+(K j)^2*p j x) (v j) x *
      skewPart (T j) (v j) x))/(S j*(D j)^2)) atTop
      (𝓝 (4*((a 0)^2+(a 1)^2)*(H 0 0+H 1 1))) := by
  let A := H 0 0*(a 0)^2+2*H 1 0*a 0*a 1+H 1 1*(a 1)^2
  have ht := normalized_hessian_trace_support_limit (a 0) (a 1) (H 0 0) (H 1 0) (H 1 1) ha
    hT hv hcv (hH 0 0) (hH 1 0) (hH 1 1) henergy hparallel
  have hh := normalized_hessianGradient_limit a H hT hv hcv hv1 hgrad hH
  rw [hessian_form_expansion a H hsym] at hh
  have hb := normalized_bilaplacian_limit hT hv hcv hv1 hB
  have hp' := normalized_potentialTransport_limit hT hp hv hcv hv1 hP
  have h := (((ht.add (hh.sub_const A)).const_mul 4).sub hb).add (hp'.const_mul 2)
  convert h using 1
  · ext j
    rw [carleman_commutator_energy (hT j) (hp j) (hv j) (hcv j)]
    dsimp [A]
    ring
  · dsimp [A]
    ring_nf


end Carleman
end SharpNodal

end

end OAI
