import OAI.Analysis.NodalLength.SupportLimits

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

open Filter in

theorem no_normalized_quasimodes {T p v : ℕ → Plane → ℝ} {S D K : ℕ → ℝ} {c : ℝ}
    (a : Fin 2 → ℝ) (H : Fin 2 → Fin 2 → ℝ)
    (ha : (a 0)^2+(a 1)^2 ≠ 0) (hsym : H 0 1=H 1 0) (htrace : 0 < H 0 0+H 1 1)
    (hT : ∀ j, Smooth (T j)) (hp : ∀ j, Smooth (p j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j)=1)
    (hc : 1 ≤ c) (hS : ∀ j, 1 ≤ S j) (hD : ∀ j, S j ≤ D j) (hSinf : Tendsto S atTop atTop)
    (hgrad : ∀ i, SupportLimit v (fun j x => coordPartial (T j) i x/D j) (a i))
    (hH : ∀ i k, SupportLimit v (fun j x => coordPartial (coordPartial (T j) k) i x/S j) (H i k))
    (hB : ∀ i k, SupportLimit v (fun j x =>
      coordPartial (coordPartial (coordPartial (coordPartial (T j) k) k) i) i x / (S j*(D j)^2)) 0)
    (hP : ∀ i, SupportLimit v (fun j x =>
      (K j)^2*coordPartial (p j) i x*coordPartial (T j) i x/(S j*(D j)^2)) 0)
    (hpot : SupportLimit v (fun j x => (K j)^2*p j x/(D j)^2) 0)
    (hqbound : ∀ j x, x ∈ tsupport (v j) → |gradientSquared (T j) x+(K j)^2*p j x| ≤ c*(D j)^2)
    (hHbound : ∀ j i k x, x ∈ tsupport (v j) →
      |coordPartial (coordPartial (T j) k) i x| ≤ c*S j)
    (hBbound : ∀ j i k x, x ∈ tsupport (v j) →
      |coordPartial (coordPartial (coordPartial (coordPartial (T j) k) k) i) i x| ≤ c*S j*(D j)^2)
    (hqTbound : ∀ j i x, x ∈ tsupport (v j) →
      |coordPartial (fun x => gradientSquared (T j) x+(K j)^2*p j x) i x * coordPartial (T j) i x| ≤ c*S j*(D j)^2)
    (hsmall : ∀ j, l2sq (fun x => plusPart (fun x => gradientSquared (T j) x+(K j)^2*p j x) (v j) x +
      skewPart (T j) (v j) x) ≤ S j*(D j)^2)
    (hzero : Tendsto (fun j => l2sq (fun x => plusPart (fun x => gradientSquared (T j) x+(K j)^2*p j x) (v j) x +
      skewPart (T j) (v j) x)/(S j*(D j)^2)) atTop (𝓝 0)) : False := by
  let q := fun j x => gradientSquared (T j) x+(K j)^2*p j x
  have hq (j) : Smooth (q j) := (smooth_gradientSquared (hT j)).add (contDiff_const.mul (hp j))
  have hboot (j) := operator_bootstrap (hq j) (hT j) (hv j) (hcv j) hc (hS j) (hD j) (hv1 j)
    (hqbound j) (hHbound j) (hBbound j) (hqTbound j) (hsmall j)
  have henergy := normalized_gradient_energy_support_limit hq hv hcv hv1 hS hD hSinf
    (fun j => (hboot j).1) (normalized_potential_coefficient_limit a hgrad hpot)
  have hparallel := normalized_parallel_support_limit a hT hv hcv hv1 (by linarith : 0 ≤ c)
    (by linarith : 0 ≤ 16*c+4) hS hD hSinf (fun j => (hboot j).2.1) hHbound hgrad henergy
  have hcomm := normalized_commutator_trace_limit a H ha hsym hT hp hv hcv hv1 hgrad hH hB hP henergy hparallel
  have hle (j) : (2*(∫ x, plusPart (q j) (v j) x*skewPart (T j) (v j) x))/(S j*(D j)^2) ≤
      l2sq (fun x => plusPart (q j) (v j) x+skewPart (T j) (v j) x)/(S j*(D j)^2) :=
    div_le_div_of_nonneg_right
      (commutator_le_sum_square (smooth_plus (hq j) (hv j)) (smooth_skew (hT j) (hv j))
        (compact_plus (hcv j)) (compact_skew (hcv j)))
      (mul_nonneg (by linarith only [hS j]) (sq_nonneg _))
  have hlimle := le_of_tendsto_of_tendsto hcomm hzero (Filter.Eventually.of_forall hle)
  have hapos : 0 < (a 0)^2+(a 1)^2 := lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) ha.symm
  have hpos : 0 < 4*((a 0)^2+(a 1)^2)*(H 0 0+H 1 1) := mul_pos (mul_pos (by norm_num) hapos) htrace
  exact (not_le_of_gt hpos) hlimle

open Filter in
lemma SupportLimit.reindex {v f : ℕ → Plane → ℝ} {A : ℝ} {φ : ℕ → ℕ}
    (h : SupportLimit v f A) (hφ : Tendsto φ atTop atTop) :
    SupportLimit (fun j => v (φ j)) (fun j => f (φ j)) A := by
  let F : SupportIndex (fun j => v (φ j)) → SupportIndex v := fun z => ⟨φ z.1, z.2⟩
  have hF : Tendsto F (supportFilter (fun j => v (φ j))) (supportFilter v) := by
    apply tendsto_comap_iff.mpr
    exact hφ.comp tendsto_comap
  exact h.comp hF

open Filter in
lemma SupportLimit.finite_bound {ι : Type*} [Fintype ι]
    {v : ℕ → Plane → ℝ} {f : ι → ℕ → Plane → ℝ} {A : ι → ℝ}
    (h : ∀ i, SupportLimit v (f i) (A i)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ j in atTop, ∀ i x, x ∈ tsupport (v j) → |f i j x| ≤ C := by
  let C := 1+∑ i, |A i|
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  refine ⟨C, hC, ?_⟩
  have hi (i : ι) := (h i).eventually_abs_sub_le (by norm_num : (0 : ℝ)<1)
  have he := eventually_all.mpr hi
  filter_upwards [he] with j hj i x hx
  have hAi : |A i| ≤ ∑ k, |A k| := Finset.single_le_sum (fun k _ => abs_nonneg (A k)) (Finset.mem_univ i)
  calc
    |f i j x| = |(f i j x-A i)+A i| := by rw [sub_add_cancel]
    _ ≤ |f i j x-A i|+|A i| := abs_add_le _ _
    _ ≤ C := add_le_add (hj i x hx) hAi

lemma normalized_derivative_potential_limit {T p v : ℕ → Plane → ℝ} {S D K : ℕ → ℝ}
    (a : Fin 2 → ℝ) (H : Fin 2 → Fin 2 → ℝ)
    (hT : ∀ j, Smooth (T j)) (hp : ∀ j, Smooth (p j))
    (hgrad : ∀ i, SupportLimit v (fun j x => coordPartial (T j) i x/D j) (a i))
    (hH : ∀ i k, SupportLimit v (fun j x => coordPartial (coordPartial (T j) k) i x/S j) (H i k))
    (hP : ∀ i, SupportLimit v (fun j x =>
      (K j)^2*coordPartial (p j) i x*coordPartial (T j) i x/(S j*(D j)^2)) 0)
    (i : Fin 2) :
    SupportLimit v (fun j x =>
      coordPartial (fun x => gradientSquared (T j) x+(K j)^2*p j x) i x * coordPartial (T j) i x /
        (S j*(D j)^2)) (2*(H i 0*a 0*a i+H i 1*a 1*a i)) := by
  have hh := (((hH i 0).mul (hgrad 0)).mul (hgrad i)).add
    (((hH i 1).mul (hgrad 1)).mul (hgrad i))
  have h := ((SupportLimit.const 2).mul hh).add (hP i)
  convert h using 1
  · ext j x
    rw [partial_add (smooth_gradientSquared (hT j)) (contDiff_const.mul (hp j)),
      partial_gradientSquared (hT j), partial_const_mul (hp j)]
    simp only [Fin.sum_univ_two, div_eq_mul_inv, mul_inv_rev]
    ring
  · simp only [add_zero]

lemma abs_le_mul_of_div {x d C : ℝ} (hd : 0<d) (h : |x/d|≤C) : |x|≤C*d := by
  rw [abs_div, abs_of_pos hd, div_le_iff₀ hd] at h
  exact h

open Filter in

theorem no_asymptotic_quasimodes {T p v : ℕ → Plane → ℝ} {S D K : ℕ → ℝ}
    (a : Fin 2 → ℝ) (H : Fin 2 → Fin 2 → ℝ)
    (ha : (a 0)^2+(a 1)^2 ≠ 0) (hsym : H 0 1=H 1 0) (htrace : 0 < H 0 0+H 1 1)
    (hT : ∀ j, Smooth (T j)) (hp : ∀ j, Smooth (p j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j)=1)
    (hD : ∀ j, S j ≤ D j) (hSinf : Tendsto S atTop atTop)
    (hgrad : ∀ i, SupportLimit v (fun j x => coordPartial (T j) i x/D j) (a i))
    (hH : ∀ i k, SupportLimit v (fun j x => coordPartial (coordPartial (T j) k) i x/S j) (H i k))
    (hB : ∀ i k, SupportLimit v (fun j x =>
      coordPartial (coordPartial (coordPartial (coordPartial (T j) k) k) i) i x / (S j*(D j)^2)) 0)
    (hP : ∀ i, SupportLimit v (fun j x =>
      (K j)^2*coordPartial (p j) i x*coordPartial (T j) i x/(S j*(D j)^2)) 0)
    (hpot : SupportLimit v (fun j x => (K j)^2*p j x/(D j)^2) 0)
    (hzero : Tendsto (fun j => l2sq (fun x => plusPart (fun x => gradientSquared (T j) x+(K j)^2*p j x) (v j) x +
      skewPart (T j) (v j) x)/(S j*(D j)^2)) atTop (𝓝 0)) : False := by
  have hq := normalized_potential_coefficient_limit a hgrad hpot
  obtain ⟨Cq, hCq, hqe⟩ := SupportLimit.finite_bound (fun _ : Unit => hq)
  obtain ⟨CH, hCH, hHe⟩ := SupportLimit.finite_bound (fun z : Fin 2 × Fin 2 => hH z.1 z.2)
  obtain ⟨CB, hCB, hBe⟩ := SupportLimit.finite_bound (fun z : Fin 2 × Fin 2 => hB z.1 z.2)
  obtain ⟨CT, hCT, hTe⟩ := SupportLimit.finite_bound
    (normalized_derivative_potential_limit a H hT hp hgrad hH hP)
  let c := max (max Cq CH) (max CB CT)
  have hqc : Cq ≤ c := (le_max_left Cq CH).trans (le_max_left _ _)
  have hHc : CH ≤ c := (le_max_right Cq CH).trans (le_max_left _ _)
  have hBc : CB ≤ c := (le_max_left CB CT).trans (le_max_right _ _)
  have hTc : CT ≤ c := (le_max_right CB CT).trans (le_max_right _ _)
  have hc : 1 ≤ c := hCq.trans hqc
  have heS : ∀ᶠ j in atTop, 1 ≤ S j := hSinf.eventually (eventually_ge_atTop 1)
  have hesmall := hzero.eventually_lt_const (by norm_num : (0 : ℝ)<1)
  have he : ∀ᶠ j in atTop, 1 ≤ S j ∧
      (∀ x ∈ tsupport (v j), |gradientSquared (T j) x+(K j)^2*p j x| ≤ c*(D j)^2) ∧
      (∀ i k x, x ∈ tsupport (v j) → |coordPartial (coordPartial (T j) k) i x|≤c*S j) ∧
      (∀ i k x, x ∈ tsupport (v j) →
        |coordPartial (coordPartial (coordPartial (coordPartial (T j) k) k) i) i x|≤c*S j*(D j)^2) ∧
      (∀ i x, x ∈ tsupport (v j) →
        |coordPartial (fun x => gradientSquared (T j) x+(K j)^2*p j x) i x * coordPartial (T j) i x|≤c*S j*(D j)^2) ∧
      l2sq (fun x => plusPart (fun x => gradientSquared (T j) x+(K j)^2*p j x) (v j) x+
        skewPart (T j) (v j) x)≤S j*(D j)^2 := by
    filter_upwards [heS, hqe, hHe, hBe, hTe, hesmall] with j hj hqj hHj hBj hTj hsj
    have hSpos : 0<S j := by linarith
    have hDpos : 0<D j := hSpos.trans_le (hD j)
    have hden : 0<S j*(D j)^2 := mul_pos hSpos (sq_pos_of_pos hDpos)
    refine ⟨hj, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact abs_le_mul_of_div (sq_pos_of_pos hDpos) ((hqj () x hx).trans hqc)
    · intro i k x hx
      exact abs_le_mul_of_div hSpos ((hHj (i,k) x hx).trans hHc)
    · intro i k x hx
      simpa only [mul_assoc] using abs_le_mul_of_div hden ((hBj (i,k) x hx).trans hBc)
    · intro i x hx
      simpa only [mul_assoc] using abs_le_mul_of_div hden ((hTj i x hx).trans hTc)
    · exact (div_le_one hden).mp hsj.le
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  have hn (j : ℕ) := hN (j+N) (Nat.le_add_left N j)
  have hφ := tendsto_add_atTop_nat N
  exact no_normalized_quasimodes a H ha hsym htrace
    (fun j => hT (j+N)) (fun j => hp (j+N)) (fun j => hv (j+N))
    (fun j => hcv (j+N)) (fun j => hv1 (j+N)) hc
    (fun j => (hn j).1) (fun j => hD (j+N)) (hSinf.comp hφ)
    (fun i => (hgrad i).reindex hφ) (fun i k => (hH i k).reindex hφ)
    (fun i k => (hB i k).reindex hφ) (fun i => (hP i).reindex hφ) (hpot.reindex hφ)
    (fun j => (hn j).2.1) (fun j => (hn j).2.2.1) (fun j => (hn j).2.2.2.1)
    (fun j => (hn j).2.2.2.2.1) (fun j => (hn j).2.2.2.2.2) (hzero.comp hφ)

def tiltedWeight (B : Plane) (S : ℝ) (χ : Plane → ℝ) (x : Plane) : ℝ :=
  -inner ℝ B x-S*χ x

lemma smooth_tiltedWeight (B : Plane) (S : ℝ) {χ : Plane → ℝ} (hχ : Smooth χ) :
    Smooth (tiltedWeight B S χ) :=
  ((innerSL ℝ B).contDiff.neg).sub (contDiff_const.mul hχ)

lemma partial_linear (B : Plane) (i : Fin 2) (x : Plane) :
    coordPartial (fun y => inner ℝ B y) i x = B i := by
  unfold coordPartial
  change fderiv ℝ (innerSL ℝ B) x (EuclideanSpace.single i 1) = B i
  rw [(innerSL ℝ B).fderiv]
  simp [EuclideanSpace.inner_single_right]

lemma partial_neg {f : Plane → ℝ} (hf : Smooth f) (i : Fin 2) (x : Plane) :
    coordPartial (fun y => -f y) i x = -coordPartial f i x := by
  simpa only [neg_one_mul] using partial_const_mul hf (-1) i x

lemma partial_sub {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (i : Fin 2) (x : Plane) :
    coordPartial (fun y => f y-g y) i x = coordPartial f i x-coordPartial g i x := by
  simp only [sub_eq_add_neg, partial_add hf hg.neg, partial_neg hg]

lemma partial_const (c : ℝ) (i : Fin 2) (x : Plane) :
    coordPartial (fun _ => c) i x = 0 := by simp [coordPartial]

lemma partial_tiltedWeight (B : Plane) (S : ℝ) {χ : Plane → ℝ} (hχ : Smooth χ)
    (i : Fin 2) (x : Plane) :
    coordPartial (tiltedWeight B S χ) i x = -B i-S*coordPartial χ i x := by
  change coordPartial (fun y => -(innerSL ℝ B) y-S*χ y) i x = _
  rw [partial_sub ((innerSL ℝ B).contDiff.neg) (contDiff_const.mul hχ),
    partial_neg (innerSL ℝ B).contDiff]
  change -coordPartial (fun y => inner ℝ B y) i x-coordPartial (fun y => S*χ y) i x = _
  rw [partial_linear, partial_const_mul hχ]

lemma partial2_tiltedWeight (B : Plane) (S : ℝ) {χ : Plane → ℝ} (hχ : Smooth χ)
    (i k : Fin 2) (x : Plane) :
    coordPartial (coordPartial (tiltedWeight B S χ) k) i x =
      -S*coordPartial (coordPartial χ k) i x := by
  simp_rw [funext (partial_tiltedWeight B S hχ k)]
  rw [partial_sub contDiff_const (contDiff_const.mul (smooth_partial hχ k)),
    partial_const, partial_const_mul (smooth_partial hχ k)]
  ring

lemma partial4_tiltedWeight (B : Plane) (S : ℝ) {χ : Plane → ℝ} (hχ : Smooth χ)
    (i k : Fin 2) (x : Plane) :
    coordPartial (coordPartial (coordPartial (coordPartial (tiltedWeight B S χ) k) k) i) i x =
      -S*coordPartial (coordPartial (coordPartial (coordPartial χ k) k) i) i x := by
  simp_rw [funext (partial2_tiltedWeight B S hχ k k)]
  simp_rw [funext (partial_const_mul (smooth_partial (smooth_partial hχ k) k) (-S) i)]
  exact partial_const_mul (smooth_partial (smooth_partial (smooth_partial hχ k) k) i) (-S) i x

open Filter in

def ShrinkingSupports (v : ℕ → Plane → ℝ) (x₀ : Plane) : Prop :=
  Tendsto (fun z : SupportIndex v => z.2.1) (supportFilter v) (𝓝 x₀)

lemma ShrinkingSupports.continuousAt {v : ℕ → Plane → ℝ} {x₀ : Plane}
    (hv : ShrinkingSupports v x₀) {f : Plane → ℝ} (hf : ContinuousAt f x₀) :
    SupportLimit v (fun _ x => f x) (f x₀) := hf.tendsto.comp hv

open Filter in
lemma SupportLimit.congr_eventually {v f g : ℕ → Plane → ℝ} {A : ℝ}
    (hf : SupportLimit v f A) (hfg : ∀ᶠ j in atTop, ∀ x ∈ tsupport (v j), f j x=g j x) :
    SupportLimit v g A :=
  hf.congr' ((eventually_support_iff v (fun j x => f j x=g j x)).mpr hfg)

open Filter in
lemma SupportLimit.zero_of_bound {v f : ℕ → Plane → ℝ} {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0))
    (hf : ∀ᶠ j in atTop, ∀ x ∈ tsupport (v j), |f j x| ≤ r j) :
    SupportLimit v f 0 := by
  have h := (eventually_support_iff v (fun j x => |f j x|≤r j)).mpr hf
  have hr' : Tendsto (fun z : SupportIndex v => r z.1) (supportFilter v) (𝓝 0) :=
    hr.comp tendsto_comap
  exact squeeze_zero_norm' (h.mono (fun z hz => by simpa only [Real.norm_eq_abs] using hz)) hr'

open Filter in
lemma tilted_gradient_limit {v : ℕ → Plane → ℝ} {χ : Plane → ℝ} {B : ℕ → Plane}
    {S D : ℕ → ℝ} {b : Plane} {d : ℝ} {x₀ : Plane}
    (hχ : Smooth χ) (hv : ShrinkingSupports v x₀)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d)) (i : Fin 2) :
    SupportLimit v (fun j x => coordPartial (tiltedWeight (B j) (S j) χ) i x/D j)
      (-b i-d*coordPartial χ i x₀) := by
  have hbi : Tendsto (fun j => B j i/D j) atTop (𝓝 (b i)) := by
    have ht : Tendsto (fun j => ((D j)⁻¹ • B j) i) atTop (𝓝 (b i)) :=
      (EuclideanSpace.proj i).continuous.tendsto b |>.comp hb
    simpa only [PiLp.smul_apply, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using ht
  have h := (SupportLimit.of_seq hbi).neg.sub
    ((SupportLimit.of_seq hd).mul (hv.continuousAt (smooth_partial hχ i).continuous.continuousAt))
  convert h using 1
  ext j x
  rw [partial_tiltedWeight _ _ hχ]
  ring

open Filter in
lemma tilted_hessian_limit {v : ℕ → Plane → ℝ} {χ : Plane → ℝ} {B : ℕ → Plane}
    {S : ℕ → ℝ} {x₀ : Plane} (hχ : Smooth χ) (hv : ShrinkingSupports v x₀)
    (hS : Tendsto S atTop atTop) (i k : Fin 2) :
    SupportLimit v (fun j x => coordPartial (coordPartial (tiltedWeight (B j) (S j) χ) k) i x/S j)
      (-coordPartial (coordPartial χ k) i x₀) := by
  apply (hv.continuousAt (smooth_partial (smooth_partial hχ k) i).continuous.continuousAt).neg.congr_eventually
  filter_upwards [hS.eventually (eventually_gt_atTop 0)] with j hj x _
  rw [partial2_tiltedWeight _ _ hχ]
  field_simp

open Filter in
lemma tilted_bilaplacian_limit {v : ℕ → Plane → ℝ} {χ : Plane → ℝ} {B : ℕ → Plane}
    {S D : ℕ → ℝ} {x₀ : Plane} (hχ : Smooth χ) (hv : ShrinkingSupports v x₀)
    (hS : Tendsto S atTop atTop) (hD : Tendsto D atTop atTop) (i k : Fin 2) :
    SupportLimit v (fun j x =>
      coordPartial (coordPartial (coordPartial (coordPartial (tiltedWeight (B j) (S j) χ) k) k) i) i x /
        (S j*(D j)^2)) 0 := by
  have hd : Tendsto (fun j => (D j)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hD
  have hx := (hv.continuousAt
    (smooth_partial (smooth_partial (smooth_partial (smooth_partial hχ k) k) i) i).continuous.continuousAt).neg
  have h := hx.mul ((SupportLimit.of_seq hd).pow 2)
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero] at h
  apply h.congr_eventually
  filter_upwards [hS.eventually (eventually_gt_atTop 0)] with j hj x _
  rw [partial4_tiltedWeight _ _ hχ]
  field_simp

def coordinateGradient (χ : Plane → ℝ) (x : Plane) : Plane :=
  WithLp.toLp 2 (fun i => coordPartial χ i x)

lemma coordinateGradient_apply (χ : Plane → ℝ) (x : Plane) (i : Fin 2) :
    coordinateGradient χ x i = coordPartial χ i x := rfl

open Filter in
lemma normalized_small_potential {p v : ℕ → Plane → ℝ} {K D : ℕ → ℝ} {C : ℝ}
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hp : ∀ᶠ j in atTop, ∀ x ∈ tsupport (v j), |p j x|≤C) :
    SupportLimit v (fun j x => (K j)^2*p j x/(D j)^2) 0 := by
  have hr : Tendsto (fun j => (K j/D j)^2*C) atTop (𝓝 0) := by
    simpa using (hK.pow 2).mul_const C
  apply SupportLimit.zero_of_bound hr
  filter_upwards [hp] with j hj x hx
  rw [mul_div_right_comm, abs_mul, abs_div, abs_pow, abs_pow, sq_abs, sq_abs]
  rw [div_pow] at *
  exact mul_le_mul_of_nonneg_left (hj x hx) (div_nonneg (sq_nonneg _) (sq_nonneg _))

open Filter in
lemma normalized_potential_gradient_limit {T p v : ℕ → Plane → ℝ} {S D K : ℕ → ℝ}
    (a : Fin 2 → ℝ)
    (hgrad : ∀ i, SupportLimit v (fun j x => coordPartial (T j) i x/D j) (a i))
    (hp : ∀ i, SupportLimit v (fun j x => (K j)^2*coordPartial (p j) i x/(S j*D j)) 0)
    (i : Fin 2) :
    SupportLimit v (fun j x => (K j)^2*coordPartial (p j) i x*coordPartial (T j) i x/
      (S j*(D j)^2)) 0 := by
  have h := (hp i).mul (hgrad i)
  simp only [zero_mul] at h
  convert h using 1
  ext j x
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

open Filter in

theorem no_tilted_quasimodes {p v : ℕ → Plane → ℝ} {χ : Plane → ℝ}
    {B : ℕ → Plane} {S D K : ℕ → ℝ} {b : Plane} {d Cp : ℝ} {x₀ : Plane}
    (hχ : Smooth χ) (hp : ∀ j, Smooth (p j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j)=1)
    (hshr : ShrinkingSupports v x₀)
    (hS : Tendsto S atTop atTop) (hD : ∀ j, S j≤D j)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d))
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hpbound : ∀ᶠ j in atTop, ∀ x ∈ tsupport (v j), |p j x|≤Cp)
    (hpgrad : ∀ i, SupportLimit v (fun j x => (K j)^2*coordPartial (p j) i x/(S j*D j)) 0)
    (htrace : euclideanLaplacian χ x₀<0)
    (ha : b+d • coordinateGradient χ x₀ ≠ 0)
    (hzero : Tendsto (fun j => l2sq (fun x =>
      plusPart (fun x => gradientSquared (tiltedWeight (B j) (S j) χ) x+(K j)^2*p j x) (v j) x+
      skewPart (tiltedWeight (B j) (S j) χ) (v j) x)/(S j*(D j)^2)) atTop (𝓝 0)) : False := by
  let a : Fin 2 → ℝ := fun i => -b i-d*coordPartial χ i x₀
  let H : Fin 2 → Fin 2 → ℝ := fun i k => -coordPartial (coordPartial χ k) i x₀
  have ha' : (a 0)^2+(a 1)^2 ≠ 0 := by
    intro hz
    have h₀ : a 0=0 := by nlinarith [sq_nonneg (a 1)]
    have h₁ : a 1=0 := by nlinarith [sq_nonneg (a 0)]
    apply ha
    ext i
    dsimp [a] at h₀ h₁
    fin_cases i
    · change b 0+d*coordPartial χ 0 x₀=0
      linarith
    · change b 1+d*coordPartial χ 1 x₀=0
      linarith
  have hsym : H 0 1=H 1 0 := by dsimp [H]; rw [partial_partial hχ]
  have ht : 0<H 0 0+H 1 1 := by
    dsimp [euclideanLaplacian] at htrace
    simp only [Fin.sum_univ_two] at htrace
    dsimp [H]
    linarith
  have hdinf : Tendsto D atTop atTop := tendsto_atTop_mono hD hS
  have hg (i : Fin 2) := tilted_gradient_limit hχ hshr hb hd i
  exact no_asymptotic_quasimodes a H ha' hsym ht
    (fun j => smooth_tiltedWeight _ _ hχ) hp hv hcv hv1 hD hS hg
    (fun i k => tilted_hessian_limit hχ hshr hS i k)
    (fun i k => tilted_bilaplacian_limit hχ hshr hS hdinf i k)
    (normalized_potential_gradient_limit a hg hpgrad)
    (normalized_small_potential hK hpbound) hzero

def conjugatedOperator (T p : Plane → ℝ) (K : ℝ) (v : Plane → ℝ) (x : Plane) : ℝ :=
  plusPart (fun y => gradientSquared T y+K^2*p y) v x+skewPart T v x

lemma laplacian_const_mul {v : Plane → ℝ} (hv : Smooth v) (c : ℝ) :
    euclideanLaplacian (fun x => c*v x) = fun x => c*euclideanLaplacian v x := by
  ext x
  unfold euclideanLaplacian
  simp_rw [funext (partial_const_mul hv c _)]
  simp_rw [partial_const_mul (smooth_partial hv _) c]
  rw [Finset.mul_sum]

lemma skew_const_mul {v : Plane → ℝ} (hv : Smooth v) (T : Plane → ℝ) (c : ℝ) :
    skewPart T (fun x => c*v x) = fun x => c*skewPart T v x := by
  ext x
  unfold skewPart
  simp only [partial_const_mul hv, Fin.sum_univ_two]
  ring

lemma conjugatedOperator_const_mul {v : Plane → ℝ} (hv : Smooth v)
    (T p : Plane → ℝ) (K c : ℝ) :
    conjugatedOperator T p K (fun x => c*v x) = fun x => c*conjugatedOperator T p K v x := by
  ext x
  simp only [conjugatedOperator, plusPart, laplacian_const_mul hv, skew_const_mul hv]
  ring

open Filter in
lemma ShrinkingSupports.of_ball {v : ℕ → Plane → ℝ} {r : ℕ → ℝ} {x₀ : Plane}
    (hr : Tendsto r atTop (𝓝 0)) (hv : ∀ j, tsupport (v j) ⊆ Metric.ball x₀ (r j)) :
    ShrinkingSupports v x₀ := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  apply (eventually_support_iff v (fun _ x => dist x x₀<ε)).mpr
  filter_upwards [hr.eventually_lt_const hε] with j hj x hx
  exact (hv j hx).trans hj

open Filter in

theorem local_carleman_conjugated {p : ℕ → Plane → ℝ} {χ : Plane → ℝ}
    {B : ℕ → Plane} {S D K e : ℕ → ℝ} {b : Plane} {d Cp r₀ : ℝ} {x₀ : Plane}
    (hχ : Smooth χ) (hp : ∀ j, Smooth (p j)) (hr₀ : 0<r₀)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop) (hD : ∀ j, S j≤D j)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d))
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hpbound : ∀ j x, x ∈ Metric.ball x₀ r₀ → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x ∈ Metric.ball x₀ r₀ →
      |(K j)^2*coordPartial (p j) i x/(S j*D j)|≤e j)
    (htrace : euclideanLaplacian χ x₀<0)
    (ha : b+d • coordinateGradient χ x₀ ≠ 0) :
    ∃ r : ℝ, 0<r ∧ ∃ c : ℝ, 0<c ∧ ∃ j₀ : ℕ, ∀ j≥j₀, ∀ v : Plane → ℝ,
      Smooth v → HasCompactSupport v → tsupport v ⊆ Metric.ball x₀ r →
      c*S j*(D j)^2*l2sq v ≤ l2sq (conjugatedOperator (tiltedWeight (B j) (S j) χ) (p j) (K j) v) := by
  by_contra hn
  push Not at hn
  have hf (n : ℕ) : ∃ j : ℕ, n≤j ∧ ∃ v : Plane → ℝ,
      Smooth v ∧ HasCompactSupport v ∧ tsupport v ⊆ Metric.ball x₀ (min r₀ (1/((n : ℝ)+1))) ∧
      l2sq (conjugatedOperator (tiltedWeight (B j) (S j) χ) (p j) (K j) v) <
        (1/((n : ℝ)+1))*S j*(D j)^2*l2sq v :=
    hn _ (lt_min hr₀ (by positivity)) _ (by positivity) n
  choose j hj v hv hcv hsup hsmall using hf
  have hjinf : Tendsto j atTop atTop := tendsto_atTop_mono hj tendsto_id
  have hvne (n : ℕ) : v n ≠ 0 := by
    intro hz
    have hl2 : l2sq (v n)=0 := by rw [hz]; simp [l2sq]
    have hh := hsmall n
    rw [hl2, mul_zero] at hh
    exact (not_lt_of_ge (l2sq_nonneg _)) hh
  let w : ℕ → Plane → ℝ := fun n x => (l2norm (v n))⁻¹*v n x
  have hw (n : ℕ) : Smooth (w n) := contDiff_const.mul (hv n)
  have hcw (n : ℕ) : HasCompactSupport (w n) := (hcv n).mul_left
  have hw1 (n : ℕ) : l2sq (w n)=1 := normalize_l2sq (hv n) (hcv n) (hvne n)
  have hsupp (n : ℕ) : tsupport (w n) ⊆ tsupport (v n) := tsupport_mul_subset_right
  have hball (n : ℕ) : tsupport (w n) ⊆ Metric.ball x₀ (1/((n : ℝ)+1)) :=
    (hsupp n).trans ((hsup n).trans (Metric.ball_subset_ball (min_le_right _ _)))
  have hball₀ (n : ℕ) : tsupport (w n) ⊆ Metric.ball x₀ r₀ :=
    (hsupp n).trans ((hsup n).trans (Metric.ball_subset_ball (min_le_left _ _)))
  have hshr : ShrinkingSupports w x₀ := ShrinkingSupports.of_ball
    tendsto_one_div_add_atTop_nhds_zero_nat hball
  have hpb : ∀ᶠ n in atTop, ∀ x ∈ tsupport (w n), |p (j n) x|≤Cp :=
    Eventually.of_forall fun n x hx => hpbound _ _ (hball₀ n hx)
  have hpg (i : Fin 2) : SupportLimit w (fun n x =>
      (K (j n))^2*coordPartial (p (j n)) i x/(S (j n)*D (j n))) 0 := by
    apply SupportLimit.zero_of_bound (he.comp hjinf)
    exact Eventually.of_forall fun n x hx => hpgrad _ _ _ (hball₀ n hx)
  have hres (n : ℕ) : l2sq (conjugatedOperator (tiltedWeight (B (j n)) (S (j n)) χ)
      (p (j n)) (K (j n)) (w n))/(S (j n)*(D (j n))^2) < 1/((n : ℝ)+1) := by
    have hdpos := (hSpos (j n)).trans_le (hD (j n))
    have hden := mul_pos (hSpos (j n)) (sq_pos_of_pos hdpos)
    have hlpos : 0<l2norm (v n) := Real.sqrt_pos.mpr (l2sq_pos (hv n) (hcv n) (hvne n))
    apply (div_lt_iff₀ hden).mpr
    dsimp [w]
    rw [conjugatedOperator_const_mul (hv n), l2sq_const_mul]
    have hh := mul_lt_mul_of_pos_left (hsmall n) (sq_pos_of_pos (inv_pos.mpr hlpos))
    have hnrm : (l2norm (v n))⁻¹^2*l2sq (v n)=1 := by
      simpa only [w, l2sq_const_mul] using hw1 n
    calc
      _ < (l2norm (v n))⁻¹^2*((1/((n : ℝ)+1))*S (j n)*(D (j n))^2*l2sq (v n)) := hh
      _ = (1/((n : ℝ)+1))*(S (j n)*(D (j n))^2) := by
        calc
          _ = ((1/((n : ℝ)+1))*(S (j n)*(D (j n))^2))*((l2norm (v n))⁻¹^2*l2sq (v n)) := by ring
          _ = _ := by rw [hnrm, mul_one]
  have hzero : Tendsto (fun n => l2sq (conjugatedOperator (tiltedWeight (B (j n)) (S (j n)) χ)
      (p (j n)) (K (j n)) (w n))/(S (j n)*(D (j n))^2)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => div_nonneg (l2sq_nonneg _)
      (mul_nonneg (hSpos _).le (sq_nonneg _)))
      (Eventually.of_forall fun n => (hres n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact no_tilted_quasimodes hχ (fun n => hp (j n)) hw hcw hw1 hshr
    (hS.comp hjinf) (fun n => hD (j n)) (hb.comp hjinf) (hd.comp hjinf) (hK.comp hjinf)
    hpb hpg htrace ha hzero

open Filter in

theorem local_carleman {p : ℕ → Plane → ℝ} {χ : Plane → ℝ}
    {B : ℕ → Plane} {S D K e : ℕ → ℝ} {b : Plane} {d Cp r₀ : ℝ} {x₀ : Plane}
    (hχ : Smooth χ) (hp : ∀ j, Smooth (p j)) (hr₀ : 0<r₀)
    (hSpos : ∀ j, 0<S j) (hS : Tendsto S atTop atTop) (hD : ∀ j, S j≤D j)
    (hb : Tendsto (fun j => (D j)⁻¹ • B j) atTop (𝓝 b))
    (hd : Tendsto (fun j => S j/D j) atTop (𝓝 d))
    (hK : Tendsto (fun j => K j/D j) atTop (𝓝 0))
    (hpbound : ∀ j x, x ∈ Metric.ball x₀ r₀ → |p j x|≤Cp)
    (he : Tendsto e atTop (𝓝 0))
    (hpgrad : ∀ j i x, x ∈ Metric.ball x₀ r₀ →
      |(K j)^2*coordPartial (p j) i x/(S j*D j)|≤e j)
    (htrace : euclideanLaplacian χ x₀<0)
    (ha : b+d • coordinateGradient χ x₀ ≠ 0) :
    ∃ r : ℝ, 0<r ∧ ∃ c : ℝ, 0<c ∧ ∃ j₀ : ℕ, ∀ j≥j₀, ∀ w : Plane → ℝ,
      Smooth w → HasCompactSupport w → tsupport w ⊆ Metric.ball x₀ r →
      c*Real.sqrt (S j)*D j*l2norm (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*w x) ≤
        l2norm (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*
          (euclideanLaplacian w x+(K j)^2*p j x*w x)) := by
  obtain ⟨r, hr, c, hc, j₀, h⟩ := local_carleman_conjugated hχ hp hr₀ hSpos hS hD hb hd hK
    hpbound he hpgrad htrace ha
  refine ⟨r, hr, Real.sqrt c, Real.sqrt_pos.mpr hc, j₀, ?_⟩
  intro j hj w hw hcw hsupp
  have hT := smooth_tiltedWeight (B j) (S j) hχ
  have hv := hT.exp.mul hw
  have hcv : HasCompactSupport (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*w x) := hcw.mul_left
  have hsupv : tsupport (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*w x) ⊆ Metric.ball x₀ r :=
    tsupport_mul_subset_right.trans hsupp
  have hineq := h j hj _ hv hcv hsupv
  have hconj : conjugatedOperator (tiltedWeight (B j) (S j) χ) (p j) (K j)
      (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*w x) =
      (fun x => Real.exp (tiltedWeight (B j) (S j) χ x)*(euclideanLaplacian w x+(K j)^2*p j x*w x)) :=
    funext (conjugation hT hw (p j) (K j))
  rw [hconj] at hineq
  have hh := Real.sqrt_le_sqrt hineq
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hc.le (hSpos j).le) (sq_nonneg _)),
    Real.sqrt_mul (mul_nonneg hc.le (hSpos j).le), Real.sqrt_mul hc.le,
    Real.sqrt_sq ((hSpos j).le.trans (hD j))] at hh
  exact hh


end Carleman
end SharpNodal

end

end OAI
