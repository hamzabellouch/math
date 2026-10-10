import Mathlib
import OAI.Computability.MinUncut.Estimates.Basic

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
namespace MinUncut.GaussianHermite
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma mem_range_bump [DecidableEq ι] (i : ι) (a : ι → ℕ) :
    a ∈ Set.range (bump i) ↔ 0 < a i := by
  constructor
  · rintro ⟨b,rfl⟩
    simp [bump]
  · intro ha
    refine ⟨Function.update a i (a i-1), ?_⟩
    funext j
    by_cases hj : j=i
    · subst j
      simp only [bump, Function.update_self]
      omega
    · simp [bump, Function.update_of_ne hj]

lemma productHermiteBasis_apply (a : ι → ℕ) :
    productHermiteBasis a = psiVec a := by
  simp only [productHermiteBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

lemma coeff_eq_inner {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι)) (a : ι → ℕ) :
    coeff f a = inner ℝ (productHermiteBasis a) (hf.toLp f) := by
  rw [productHermiteBasis_apply]
  exact (integral_inner_toLp (memLp_psi a) hf).symm

lemma hasSum_coeff_sq {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι)) :
    HasSum (fun a => (coeff f a)^2) (∫ x, (f x)^2 ∂γpi ι) := by
  have hs := productHermiteBasis.hasSum_inner_mul_inner (hf.toLp f) (hf.toLp f)
  have hc (a : ι → ℕ) : inner ℝ (hf.toLp f) (productHermiteBasis a) = coeff f a := by
    rw [real_inner_comm]
    exact (coeff_eq_inner hf a).symm
  simp only [hc, ← coeff_eq_inner hf, ← pow_two] at hs
  simpa only [integral_inner_toLp hf hf, ← pow_two] using hs

lemma parseval {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι)) :
    (∑' a, (coeff f a)^2) = ∫ x, (f x)^2 ∂γpi ι := (hasSum_coeff_sq hf).tsum_eq

lemma coeff_const_mul (r : ℝ) (f : (ι → ℝ) → ℝ) (a : ι → ℕ) :
    coeff (fun x => r*f x) a = r*coeff f a := by
  unfold coeff
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

def gradient (ρ s : ℝ) (Q : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  (ρ/s)*score ρ s Q i x

lemma memLp_gradient (ρ s : ℝ) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q)
    (hb : ∀ x, |Q x| ≤ 1) (i : ι) : MemLp (gradient ρ s Q i) 2 (γpi ι) :=
  (memLp_score ρ s hQ hb i).const_mul (ρ/s)

lemma gradient_coefficient [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1) (hs : s ≠ 0)
    {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1)
    (a : ι → ℕ) (i : ι) :
    coeff (gradient ρ s Q i) a =
      Real.sqrt (a i+1:ℝ)*ρ^(degree a+1)*coeff Q (bump i a) := by
  change coeff (fun x => (ρ/s)*score ρ s Q i x) a = _
  rw [coeff_const_mul]
  unfold coeff
  rw [score_coefficient ρ s h hQ hb]
  dsimp [degree, bump]
  rw [pow_succ]
  field_simp

lemma gradient_coefficient_sq [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1) (hs : s ≠ 0)
    {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1)
    (a : ι → ℕ) (i : ι) :
    (coeff (gradient ρ s Q i) a)^2 =
      (bump i a i : ℝ)*ρ^(2*degree (bump i a))*(coeff Q (bump i a))^2 := by
  rw [gradient_coefficient ρ s h hs hQ hb, mul_pow, mul_pow,
    Real.sq_sqrt (by positivity), ← pow_mul, degree_bump]
  simp only [bump, Function.update_self, Nat.cast_add, Nat.cast_one]
  congr 2
  ring

lemma hasSum_gradient_energy_coord [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1)
    (hs : s ≠ 0) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1) (i : ι) :
    HasSum (fun a => (a i : ℝ)*ρ^(2*degree a)*(coeff Q a)^2)
      (∫ x, (gradient ρ s Q i x)^2 ∂γpi ι) := by
  apply (bump_injective i).hasSum_iff (fun a ha => ?_) |>.mp
  · simpa only [Function.comp_def, ← gradient_coefficient_sq ρ s h hs hQ hb] using
      hasSum_coeff_sq (memLp_gradient ρ s hQ hb i)
  · have hz : a i = 0 := by
      rw [mem_range_bump] at ha
      omega
    simp [hz]

lemma hasSum_gradient_energy [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1)
    (hs : s ≠ 0) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1) :
    HasSum (fun a => (degree a : ℝ)*ρ^(2*degree a)*(coeff Q a)^2)
      (∑ i, ∫ x, (gradient ρ s Q i x)^2 ∂γpi ι) := by
  have hh := hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_gradient_energy_coord ρ s h hs hQ hb i)
  simpa only [← Finset.sum_mul, ← Nat.cast_sum, degree] using hh

lemma memLp_noise (ρ s : ℝ) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q)
    (hb : ∀ x, |Q x| ≤ 1) : MemLp (noise ρ s Q) 2 (γpi ι) :=
  MemLp.of_bound (measurable_noise ρ s hQ).aestronglyMeasurable 1
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using noise_bound ρ s hb x)

lemma coeff_noise (ρ s : ℝ) (h : ρ^2+s^2=1) {Q : (ι → ℝ) → ℝ}
    (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1) (a : ι → ℕ) :
    coeff (noise ρ s Q) a = ρ^(degree a)*coeff Q a := noise_coefficient ρ s h hQ hb a

lemma coeff_noise_sq (ρ s : ℝ) (h : ρ^2+s^2=1) {Q : (ι → ℝ) → ℝ}
    (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1) (a : ι → ℕ) :
    (coeff (noise ρ s Q) a)^2 = ρ^(2*degree a)*(coeff Q a)^2 := by
  rw [coeff_noise ρ s h hQ hb, mul_pow, ← pow_mul, mul_comm (degree a) 2]

@[simp] lemma psi_zero (x : ι → ℝ) : psi 0 x = 1 := by
  simp [psi, H]

@[simp] lemma coeff_zero (f : (ι → ℝ) → ℝ) : coeff f 0 = ∫ x, f x ∂γpi ι := by
  simp [coeff]

lemma degree_eq_zero_iff (a : ι → ℕ) : degree a = 0 ↔ a = 0 := by
  simp only [degree, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies,
    funext_iff, Pi.zero_apply]

lemma poincare [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1) (hs : s ≠ 0)
    {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1)
    (hmean : (∫ x, noise ρ s Q x ∂γpi ι) = 0) :
    (∫ x, (noise ρ s Q x)^2 ∂γpi ι) ≤
      ∑ i, ∫ x, (gradient ρ s Q i x)^2 ∂γpi ι := by
  apply hasSum_le (fun a => ?_) (hasSum_coeff_sq (memLp_noise ρ s hQ hb))
    (hasSum_gradient_energy ρ s h hs hQ hb)
  by_cases ha : degree a = 0
  · have haz := (degree_eq_zero_iff a).mp ha
    subst a
    simp only [coeff_zero, hmean, zero_pow (by omega : 2 ≠ 0), degree]
    simp
  · rw [coeff_noise_sq ρ s h hQ hb]
    have hd : (1:ℝ) ≤ degree a := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha
    calc
      _ = 1*(ρ^(2*degree a)*(coeff Q a)^2) := by ring
      _ ≤ (degree a : ℝ)*(ρ^(2*degree a)*(coeff Q a)^2) := by
        apply mul_le_mul_of_nonneg_right hd
        rw [pow_mul]
        exact mul_nonneg (pow_nonneg (sq_nonneg ρ) _) (sq_nonneg _)
      _ = _ := by ring

def low [DecidableEq ι] (d : ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset (fun _ : ι => Finset.range (d+1))).filter (fun a => degree a ≤ d)

@[simp] lemma mem_low [DecidableEq ι] (d : ℕ) (a : ι → ℕ) :
    a ∈ low d ↔ degree a ≤ d := by
  simp only [low, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    refine ⟨fun i => ?_, h⟩
    have hi : a i ≤ degree a := Finset.single_le_sum (fun j _ => Nat.zero_le (a j))
      (Finset.mem_univ i)
    omega

def project [DecidableEq ι] (d : ℕ) (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ a ∈ low d, coeff f a * psi a x

lemma memLp_project [DecidableEq ι] (d : ℕ) (f : (ι → ℝ) → ℝ) :
    MemLp (project d f) 2 (γpi ι) := by
  exact memLp_finsetSum _ (fun a _ => (memLp_psi a).const_mul _)

lemma coeff_project [DecidableEq ι] (d : ℕ) (f : (ι → ℝ) → ℝ) (a : ι → ℕ) :
    coeff (project d f) a = if degree a ≤ d then coeff f a else 0 := by
  unfold coeff project
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun b _ =>
    ((memLp_psi a).integrable_mul (memLp_psi b)).const_mul (coeff f b) |>.congr
      (ae_of_all _ fun x => by dsimp; ring))]
  simp_rw [show ∀ b : ι → ℕ, (fun x => psi a x * (coeff f b * psi b x)) =
    (fun x => coeff f b * (psi a x * psi b x)) by intro b; funext x; ring,
    integral_const_mul, psi_product]
  simp [coeff, mem_low]

lemma coeff_sub {f g : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι))
    (hg : MemLp g 2 (γpi ι)) (a : ι → ℕ) :
    coeff (fun x => f x-g x) a = coeff f a-coeff g a := by
  unfold coeff
  simp_rw [mul_sub]
  exact integral_sub ((memLp_psi a).integrable_mul hf) ((memLp_psi a).integrable_mul hg)

lemma coeff_residual [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : MemLp f 2 (γpi ι))
    (d : ℕ) (a : ι → ℕ) :
    coeff (fun x => f x-project d f x) a = if d < degree a then coeff f a else 0 := by
  rw [coeff_sub hf (memLp_project d f), coeff_project]
  split_ifs <;> simp_all; omega

lemma hasSum_gradient_tail_coord [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1)
    (hs : s ≠ 0) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1)
    (d : ℕ) (i : ι) :
    HasSum (fun a => if d+2 ≤ degree a then
      (a i : ℝ)*ρ^(2*degree a)*(coeff Q a)^2 else 0)
      (∫ x, (gradient ρ s Q i x-project d (gradient ρ s Q i) x)^2 ∂γpi ι) := by
  apply (bump_injective i).hasSum_iff (fun a ha => ?_) |>.mp
  · convert hasSum_coeff_sq ((memLp_gradient ρ s hQ hb i).sub
      (memLp_project d (gradient ρ s Q i))) using 1
    · funext a
      change (if d+2 ≤ degree (bump i a) then
        (bump i a i : ℝ)*ρ^(2*degree (bump i a))*(coeff Q (bump i a))^2 else 0) =
        (coeff (fun x => gradient ρ s Q i x-project d (gradient ρ s Q i) x) a)^2
      rw [coeff_residual (memLp_gradient ρ s hQ hb i)]
      split_ifs with hd he he
      · exact (gradient_coefficient_sq ρ s h hs hQ hb a i).symm
      · rw [degree_bump] at hd; omega
      · rw [degree_bump] at hd; omega
      · simp
  · have hz : a i = 0 := by rw [mem_range_bump] at ha; omega
    simp [hz]

lemma hasSum_gradient_tail [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1)
    (hs : s ≠ 0) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1)
    (d : ℕ) :
    HasSum (fun a => if d+2 ≤ degree a then
      (degree a : ℝ)*ρ^(2*degree a)*(coeff Q a)^2 else 0)
      (∑ i, ∫ x, (gradient ρ s Q i x-project d (gradient ρ s Q i) x)^2 ∂γpi ι) := by
  have hh := hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_gradient_tail_coord ρ s h hs hQ hb d i)
  convert hh using 1
  funext a
  split_ifs <;> simp [← Finset.sum_mul, degree, Nat.cast_sum]

lemma gradient_tail_le [DecidableEq ι] (ρ s : ℝ) (h : ρ^2+s^2=1)
    (hs : s ≠ 0) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1)
    (d : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (hd : ∀ k : ℕ, d+2 ≤ k → (k:ℝ)*ρ^(2*k) ≤ ε) :
    (∑ i, ∫ x, (gradient ρ s Q i x-project d (gradient ρ s Q i) x)^2 ∂γpi ι) ≤ ε := by
  have hq : MemLp Q 2 (γpi ι) := MemLp.of_bound hQ.aestronglyMeasurable 1
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have he := hasSum_le (f := fun a => if d+2 ≤ degree a then
      (degree a : ℝ)*ρ^(2*degree a)*(coeff Q a)^2 else 0)
    (g := fun a => ε*(coeff Q a)^2) (fun a => ?_)
    (hasSum_gradient_tail ρ s h hs hQ hb d) ((hasSum_coeff_sq hq).mul_left ε)
  · have hi : (∫ x, Q x^2 ∂γpi ι) ≤ 1 := by
      calc
        _ ≤ ∫ _ : ι → ℝ, (1:ℝ) ∂γpi ι := integral_mono
          (hq.integrable_sq) (integrable_const 1) (fun x => by
            have ha := hb x; nlinarith [sq_abs (Q x), abs_nonneg (Q x)])
        _ = 1 := by simp
    exact he.trans (by nlinarith)
  · split_ifs with ha
    · exact mul_le_mul_of_nonneg_right (hd _ ha) (sq_nonneg _)
    · positivity

lemma exists_cutoff {ρ ε : ℝ} (hρ : |ρ| < 1) (hε : 0 < ε) :
    ∃ d : ℕ, ∀ k : ℕ, d+2 ≤ k → (k:ℝ)*ρ^(2*k) ≤ ε := by
  have hh : ρ^2 < 1 := by nlinarith [sq_abs ρ, abs_nonneg ρ]
  have ht := tendsto_self_mul_const_pow_of_lt_one (sq_nonneg ρ) hh
  obtain ⟨d, hd⟩ := (eventually_atTop.1 (ht.eventually (gt_mem_nhds hε)))
  refine ⟨d, fun k hk => ?_⟩
  have he := hd k (by omega)
  simpa only [pow_mul] using he.le

end MinUncut.GaussianHermite

end

end OAI
