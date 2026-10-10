import Mathlib
import OAI.Probability.SKRatio.Calculus.SpectralLower

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory Filter ContinuousLinearMap
namespace SKRatio.FiniteLaw
variable {α : Type*} [Fintype α]
attribute [local instance] Classical.propDecidable

def entropy (q f : α → ℝ) : ℝ :=
  mean q (fun x => f x * Real.log (f x)) - mean q f * Real.log (mean q f)

def relativeEntropy (p q : α → ℝ) : ℝ := ∑ x, p x * Real.log (p x / q x)

lemma mul_log_div (p q : ℝ) (hq : q ≠ 0) :
    p * Real.log (p/q) = p * Real.log p - p * Real.log q := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [Real.log_div hp hq, mul_sub]

lemma relativeEntropy_nonneg (p q : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 < q x) (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) :
    0 ≤ relativeEntropy p q := by
  have h (x : α) : p x-q x ≤ p x*Real.log (p x/q x) := by
    have hl := mul_le_mul_of_nonneg_left
      (Real.self_sub_one_le_mul_log (div_nonneg (hp x) (hq x).le)) (hq x).le
    calc
      p x-q x = q x*(p x/q x-1) := by field_simp [ne_of_gt (hq x)]
      _ ≤ q x*(p x/q x*Real.log (p x/q x)) := hl
      _ = p x*Real.log (p x/q x) := by field_simp [ne_of_gt (hq x)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => h x)
  simpa only [Finset.sum_sub_distrib,hp1,hq1,sub_self,relativeEntropy] using hs

lemma entropy_density (p q : α → ℝ) (hq : ∀ x, q x ≠ 0)
    (hp1 : ∑ x, p x = 1) :
    entropy q (fun x => p x/q x) = relativeEntropy p q := by
  have hm : mean q (fun x => p x/q x) = 1 := by
    simpa only [mean,mul_div_cancel₀ _ (hq _)] using hp1
  rw [entropy,hm,Real.log_one,mul_zero,sub_zero]
  unfold mean relativeEntropy
  exact Finset.sum_congr rfl (fun x _ => by field_simp [hq x])

lemma relativeEntropy_continuous (q : α → ℝ) (hq : ∀ x, q x ≠ 0) :
    Continuous (fun p : α → ℝ => relativeEntropy p q) := by
  simp only [relativeEntropy,mul_log_div _ _ (hq _)]
  exact continuous_finsetSum _ (fun x _ =>
    (Real.continuous_mul_log.comp (continuous_apply x)).sub ((continuous_apply x).mul continuous_const))

lemma entropy_variational (p q a : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 < q x) (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) :
    mean p a ≤ relativeEntropy p q + Real.log (mean q (fun x => Real.exp (a x))) := by
  have : Nonempty α := by
    by_contra h
    have : IsEmpty α := not_nonempty_iff.mp h
    simp at hq1
  let Z := mean q (fun x => Real.exp (a x))
  have hZ : 0 < Z := Finset.sum_pos (fun x _ => mul_pos (hq x) (Real.exp_pos _)) Finset.univ_nonempty
  let r (x : α) := q x*Real.exp (a x)/Z
  have hr (x : α) : 0 < r x := div_pos (mul_pos (hq x) (Real.exp_pos _)) hZ
  have hr1 : ∑ x, r x = 1 := by
    rw [show (∑ x, r x) = Z/Z by simp only [r,Z,mean,Finset.sum_div]]
    exact div_self (ne_of_gt hZ)
  have h := relativeEntropy_nonneg p r hp hr hp1 hr1
  have he (x : α) : p x*Real.log (p x/r x) =
      p x*Real.log (p x/q x) - p x*a x + p x*Real.log Z := by
    rw [mul_log_div _ _ (ne_of_gt (hr x)),mul_log_div _ _ (ne_of_gt (hq x))]
    rw [show Real.log (r x) = Real.log (q x) + a x - Real.log Z by
      dsimp only [r]
      rw [Real.log_div (ne_of_gt (mul_pos (hq x) (Real.exp_pos _))) (ne_of_gt hZ),
        Real.log_mul (ne_of_gt (hq x)) (Real.exp_ne_zero _),Real.log_exp]]
    ring
  simp only [relativeEntropy,he,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.sum_mul,hp1,one_mul] at h
  dsimp only [mean,relativeEntropy,Z] at *
  linarith only [h]

lemma event_entropy_bound (p q : α → ℝ) (B : Set α) (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 < q x) (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1)
    {a : ℝ} (hsmall : mean q (fun x => if x ∈ B then 1 else 0) ≤ Real.exp (-a)) :
    a*mean p (fun x => if x ∈ B then 1 else 0) ≤ relativeEntropy p q+Real.log 2 := by
  classical
  have h := entropy_variational p q (fun x => if x ∈ B then a else 0) hp hq hp1 hq1
  have hm : mean q (fun x => Real.exp (if x ∈ B then a else 0)) ≤ 2 := by
    calc
      _ ≤ ∑ x, (q x + Real.exp a*(q x*(if x ∈ B then 1 else 0))) := by
        apply Finset.sum_le_sum
        intro x _
        by_cases hx : x ∈ B <;> simp only [hx,↓reduceIte,Real.exp_zero,mul_one,mul_zero]
        · nlinarith only [hq x]
        · simp
      _ = 1+Real.exp a*mean q (fun x => if x ∈ B then 1 else 0) := by
        simp only [Finset.sum_add_distrib,← Finset.mul_sum,hq1,mean]
      _ ≤ 1+Real.exp a*Real.exp (-a) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hsmall (Real.exp_nonneg _))
      _ = 2 := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]; norm_num
  have hmpos : 0 < mean q (fun x => Real.exp (if x ∈ B then a else 0)) := by
    have : Nonempty α := by
      by_contra h
      have : IsEmpty α := not_nonempty_iff.mp h
      simp at hp1
    exact Finset.sum_pos (fun x _ => mul_pos (hq x) (Real.exp_pos _)) Finset.univ_nonempty
  have hlog := Real.log_le_log hmpos hm
  have he : mean p (fun x => if x ∈ B then a else 0) =
      a*mean p (fun x => if x ∈ B then 1 else 0) := by
    simp only [mean,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  rw [he] at h
  linarith only [h,hlog]

lemma hellinger_pointwise {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    2*p-2*Real.sqrt p*Real.sqrt q ≤ p*Real.log (p/q) := by
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · simp [← hp0]
  have hp' := Real.sqrt_pos.mpr hp0
  have hq' := Real.sqrt_pos.mpr hq
  have hlog := Real.log_le_sub_one_of_pos (div_pos hq' hp')
  have h := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2*p)
  have he : Real.log (Real.sqrt q/Real.sqrt p) = -(Real.log (p/q))/2 := by
    rw [Real.log_div (ne_of_gt hq') (ne_of_gt hp'),Real.log_sqrt hq.le,Real.log_sqrt hp,
      Real.log_div (ne_of_gt hp0) (ne_of_gt hq)]
    ring
  rw [he] at h
  have hr : p*(Real.sqrt q/Real.sqrt p) = Real.sqrt p*Real.sqrt q := by
    nth_rw 1 [← Real.sq_sqrt hp]
    field_simp
  nlinarith only [h,hr]

lemma hellinger_le_entropy (p q : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 < q x) (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) :
    (∑ x, (Real.sqrt (p x)-Real.sqrt (q x))^2) ≤ relativeEntropy p q := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => hellinger_pointwise (hp x) (hq x))
  have he (x : α) : (Real.sqrt (p x)-Real.sqrt (q x))^2 =
      p x+q x-2*Real.sqrt (p x)*Real.sqrt (q x) := by
    nlinarith only [Real.sq_sqrt (hp x),Real.sq_sqrt (hq x).le]
  simp only [he,Finset.sum_sub_distrib,Finset.sum_add_distrib,hp1,hq1]
  simpa only [Finset.sum_sub_distrib,← Finset.mul_sum,hp1,relativeEntropy,
    mul_one,show (1:ℝ)+1=2 by norm_num] using h

lemma totalVariation_square_le_entropy (p q : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 < q x) (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) :
    totalVariation p q ^ 2 ≤ relativeEntropy p q := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => |Real.sqrt (p x)-Real.sqrt (q x)|)
    (fun x => Real.sqrt (p x)+Real.sqrt (q x))
  have he (x : α) : |Real.sqrt (p x)-Real.sqrt (q x)| *
      (Real.sqrt (p x)+Real.sqrt (q x)) = |p x-q x| := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),← abs_mul]
    congr 1
    nlinarith only [Real.sq_sqrt (hp x),Real.sq_sqrt (hq x).le]
  have hrest : ∑ x, (Real.sqrt (p x)+Real.sqrt (q x))^2 ≤ 4 := by
    calc
      _ ≤ ∑ x, (2*p x+2*q x) := by
        apply Finset.sum_le_sum
        intro x _
        nlinarith only [sq_nonneg (Real.sqrt (p x)-Real.sqrt (q x)),
          Real.sq_sqrt (hp x),Real.sq_sqrt (hq x).le]
      _ = 4 := by simp only [Finset.sum_add_distrib,← Finset.mul_sum,hp1,hq1]; norm_num
  simp only [he,sq_abs] at hcs
  have hb := mul_le_mul_of_nonneg_left hrest (Finset.sum_nonneg (s := Finset.univ) (fun x _ => sq_nonneg
    (Real.sqrt (p x)-Real.sqrt (q x))))
  have hh := hellinger_le_entropy p q hp hq hp1 hq1
  unfold totalVariation
  nlinarith only [hcs,hb,hh]

end SKRatio.FiniteLaw

namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

lemma continuousKernel_balance {n : ℕ} (g : Disorder n) (t : ℝ) (x y : Spin n) :
    mass g 0 x*continuousKernel (coupling g) t x y =
      mass g 0 y*continuousKernel (coupling g) t y x := by
  have hs := semigroup_symmetric g t (fun z => if z = x then 1 else 0)
    (fun z => if z = y then 1 else 0)
  simpa only [stationaryInner,FiniteLaw.mean,ite_mul,one_mul,zero_mul,mul_ite,
    mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,continuousKernel]
      using hs

def transitionDensity {n : ℕ} (g : Disorder n) (t : ℝ) (x : Spin n) : Observables n :=
  fun y => continuousKernel (coupling g) t x y/mass g 0 y

lemma transitionDensity_eq_semigroup {n : ℕ} (g : Disorder n) (t : ℝ) (x : Spin n) :
    transitionDensity g t x = semigroup (coupling g) t
      (fun y => if y = x then (mass g 0 x)⁻¹ else 0) := by
  funext y
  rw [semigroup_eq_kernel]
  simp only [FiniteLaw.mean,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
  dsimp only [transitionDensity]
  field_simp [ne_of_gt (mass_pos g 0 x),ne_of_gt (mass_pos g 0 y)]
  nlinarith only [continuousKernel_balance g t x y]

lemma transitionDensity_pos {n : ℕ} (g : Disorder n) {t : ℝ} (ht : 0 < t) (x y : Spin n) :
    0 < transitionDensity g t x y := div_pos (continuousKernel_pos g ht x y) (mass_pos g 0 y)

lemma transitionDensity_mean {n : ℕ} (g : Disorder n) (t : ℝ) (x : Spin n) :
    FiniteLaw.mean (mass g 0) (transitionDensity g t x) = 1 := by
  simp only [FiniteLaw.mean,transitionDensity,mul_div_cancel₀ _ (ne_of_gt (mass_pos g 0 _)),
    continuousKernel_sum]

lemma transitionDensity_hasDerivAt {n : ℕ} (g : Disorder n) (x : Spin n) (t : ℝ) :
    HasDerivAt (fun t => transitionDensity g t x)
      (generator (coupling g) (transitionDensity g t x)) t := by
  simp_rw [transitionDensity_eq_semigroup]
  exact semigroup_apply_hasDerivAt' _ _ _

def transitionEntropy {n : ℕ} (g : Disorder n) (x : Spin n) (t : ℝ) : ℝ :=
  FiniteLaw.relativeEntropy (continuousKernel (coupling g) t x) (mass g 0)

lemma transitionEntropy_eq {n : ℕ} (g : Disorder n) (x : Spin n) (t : ℝ) :
    transitionEntropy g x t =
      FiniteLaw.mean (mass g 0) (fun y => transitionDensity g t x y *
        Real.log (transitionDensity g t x y)) := by
  rw [transitionEntropy,← FiniteLaw.entropy_density _ _ (fun y => ne_of_gt (mass_pos g 0 y))
    (continuousKernel_sum _ t x)]
  change FiniteLaw.entropy (mass g 0) (transitionDensity g t x) = _
  simp only [FiniteLaw.entropy,transitionDensity_mean,Real.log_one,mul_zero,sub_zero]

lemma transitionEntropy_continuous {n : ℕ} (g : Disorder n) (x : Spin n) :
    Continuous (transitionEntropy g x) := by
  exact (FiniteLaw.relativeEntropy_continuous (mass g 0) (fun y => ne_of_gt (mass_pos g 0 y))).comp
    (continuous_pi (continuousKernel_continuous_time (coupling g) x))

lemma transitionEntropy_zero {n : ℕ} (g : Disorder n) (x : Spin n) :
    transitionEntropy g x 0 = Real.log (1/mass g 0 x) := by
  simp [transitionEntropy,FiniteLaw.relativeEntropy,Matrix.one_apply,ite_mul,ite_div]

lemma transitionEntropy_hasDerivAt {n : ℕ} (g : Disorder n) (x : Spin n)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (transitionEntropy g x)
      (stationaryInner g (generator (coupling g) (transitionDensity g t x))
        (fun y => Real.log (transitionDensity g t x y))) t := by
  have hd (y : Spin n) := hasDerivAt_pi.mp (transitionDensity_hasDerivAt g x t) y
  have hp (y : Spin n) := (Real.hasDerivAt_mul_log
      (ne_of_gt (transitionDensity_pos g ht x y))).comp t (hd y)
  have hm := (gibbsMeanCLM g).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_pi.mpr hp)
  have he : (fun t => gibbsMeanCLM g (fun y => transitionDensity g t x y*
      Real.log (transitionDensity g t x y))) = transitionEntropy g x := by
    funext t
    rw [gibbsMeanCLM_apply,transitionEntropy_eq]
  change HasDerivAt (fun r => gibbsMeanCLM g
    (fun y => transitionDensity g r x y*Real.log (transitionDensity g r x y))) _ t at hm
  rw [he] at hm
  apply hm.congr_deriv
  have hz := gibbsMean_generator g (transitionDensity g t x)
  simp only [gibbsMeanCLM_apply,FiniteLaw.mean] at hz ⊢
  simp only [stationaryInner,FiniteLaw.mean,add_mul,one_mul,mul_add,Finset.sum_add_distrib,hz,
    add_zero]
  exact Finset.sum_congr rfl (fun y _ => by ring)

theorem transitionEntropy_decay {n : ℕ} (g : Disorder n) {χ : ℝ}
    (hmlsi : ∀ F : Observables n, (∀ y, 0 < F y) → FiniteLaw.mean (mass g 0) F = 1 →
      χ*FiniteLaw.entropy (mass g 0) F ≤
        -stationaryInner g (generator (coupling g) F) (fun y => Real.log (F y)))
    (x : Spin n) {t : ℝ} (ht : 0 ≤ t) :
    transitionEntropy g x t ≤ Real.exp (-χ*t)*Real.log (1/mass g 0 x) := by
  let H (r : ℝ) := Real.exp (χ*r)*transitionEntropy g x r
  have hd (r : ℝ) (hr : 0 < r) : HasDerivAt H
      (Real.exp (χ*r)*(χ*transitionEntropy g x r+
        stationaryInner g (generator (coupling g) (transitionDensity g r x))
          (fun y => Real.log (transitionDensity g r x y)))) r := by
    have h := (((hasDerivAt_id r).const_mul χ).exp).mul (transitionEntropy_hasDerivAt g x hr)
    convert! h using 1
    first | rfl | (simp only [id_eq]; ring)
  have hc : Continuous H := (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (transitionEntropy_continuous g x)
  have hanti : AntitoneOn H (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) hc.continuousOn
    · intro r hr
      rw [interior_Ici,Set.mem_Ioi] at hr
      exact (hd r hr).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Ici,Set.mem_Ioi] at hr
      rw [(hd r hr).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
      have h := hmlsi (transitionDensity g r x) (transitionDensity_pos g hr x)
        (transitionDensity_mean g r x)
      rw [FiniteLaw.entropy,transitionDensity_mean,Real.log_one,mul_zero,sub_zero,
        ← transitionEntropy_eq] at h
      linarith only [h]
  have h := hanti (by simp) ht ht
  have hzero : H 0 = Real.log (1/mass g 0 x) := by simp [H,transitionEntropy_zero]
  rw [hzero] at h
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_nonneg (-χ*t))
  calc
    _ = Real.exp (-χ*t)*H t := by
      dsimp only [H]
      rw [← mul_assoc,← Real.exp_add,show -χ*t+χ*t=0 by ring,Real.exp_zero,one_mul]
    _ ≤ _ := hm

lemma abs_hamiltonian_le_norm {n : ℕ} (g : Disorder n) (x : Spin n) :
    |hamiltonian g 0 x| ≤ euclideanOpNorm (coupling g)*(n:ℝ)/2 := by
  let X : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => spinValue (x i))
  have hid : hamiltonian g 0 x = (1/2:ℝ)*inner ℝ X
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (coupling g) X) := by
    rw [Matrix.inner_toEuclideanCLM (coupling g : Matrix (Fin n) (Fin n) ℝ) X X]
    simp only [hamiltonian,Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero,dotProduct,
      Matrix.mulVec,Finset.mul_sum,X,mul_assoc]
  have hX : ‖X‖^2 = (n:ℝ) := by
    simp [X,EuclideanSpace.real_norm_sq_eq,Independent.spinValue_sq]
  rw [hid,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  calc
    _ ≤ (1/2:ℝ)*(‖X‖*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (coupling g) X‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
    _ ≤ (1/2:ℝ)*(‖X‖*(euclideanOpNorm (coupling g)*‖X‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (coupling g)).le_opNorm X)
          (norm_nonneg X)) (by norm_num)
    _ = _ := by rw [← hX]; ring

lemma log_inverse_mass_le {n : ℕ} (g : Disorder n) (x : Spin n) :
    Real.log (1/mass g 0 x) ≤ (n:ℝ)*(Real.log 2+euclideanOpNorm (coupling g)) := by
  let b := euclideanOpNorm (coupling g)*(n:ℝ)/2
  have he (y : Spin n) : |hamiltonian g 0 y| ≤ b := abs_hamiltonian_le_norm g y
  have hp : partition g 0 ≤ (2:ℝ)^n*Real.exp b := by
    calc
      _ ≤ ∑ y : Spin n, Real.exp b := Finset.sum_le_sum
        (fun y _ => Real.exp_le_exp.mpr ((le_abs_self _).trans (he y)))
      _ = _ := by simp [Spin]
  have hlog := Real.log_le_log (partition_pos g 0) hp
  rw [Real.log_mul (by positivity : (2:ℝ)^n ≠ 0) (Real.exp_ne_zero _),
    Real.log_pow,Real.log_exp] at hlog
  have hinv : Real.log (1/mass g 0 x) = Real.log (partition g 0)-hamiltonian g 0 x := by
    rw [mass,weight,one_div_div,Real.log_div (ne_of_gt (partition_pos g 0)) (Real.exp_ne_zero _),
      Real.log_exp]
  rw [hinv]
  have hl := (abs_le.mp (he x)).1
  dsimp only [b] at hlog hl
  linarith only [hlog,hl]

lemma continuousDistance_square_le_entropy {n : ℕ} (g : Disorder n) {t H : ℝ}
    (ht : 0 ≤ t) (hH : ∀ x, transitionEntropy g x t ≤ H) :
    continuousDistance g t ^ 2 ≤ H := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun x : Spin n => totalVariation (continuousKernel (coupling g) t x) (mass g 0))
  change (Finset.univ.sup' _ _)^2 ≤ _
  rw [hx]
  exact (FiniteLaw.totalVariation_square_le_entropy _ _ (continuousKernel_nonneg _ t ht x)
    (mass_pos g 0) (continuousKernel_sum _ t x) (sum_mass g 0)).trans (hH x)

lemma continuousDistance_square_decay {n : ℕ} (g : Disorder n) {χ : ℝ}
    (hmlsi : ∀ F : Observables n, (∀ y, 0 < F y) → FiniteLaw.mean (mass g 0) F = 1 →
      χ*FiniteLaw.entropy (mass g 0) F ≤
        -stationaryInner g (generator (coupling g) F) (fun y => Real.log (F y)))
    {t : ℝ} (ht : 0 ≤ t) :
    continuousDistance g t ^ 2 ≤
      Real.exp (-χ*t)*(n:ℝ)*(Real.log 2+euclideanOpNorm (coupling g)) := by
  apply continuousDistance_square_le_entropy g ht
  intro x
  exact (transitionEntropy_decay g hmlsi x ht).trans
    (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (log_inverse_mass_le g x) (Real.exp_nonneg (-χ*t)))

theorem uniform_median_upper_of_mlsi
    (G : ∀ n : ℕ, Set (Disorder n)) {χ K : ℝ} (hχ : 0 < χ)
    (hnorm : ∀ n, ∀ g ∈ G n, euclideanOpNorm (coupling g) ≤ K)
    (hmlsi : ∀ n, ∀ g ∈ G n, ∀ F : Observables n,
      (∀ y, 0 < F y) → FiniteLaw.mean (mass g 0) F = 1 →
      χ*FiniteLaw.entropy (mass g 0) F ≤
        -stationaryInner g (generator (coupling g) F) (fun y => Real.log (F y))) :
    ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, medianTime g ≤ (2/χ)*Real.log n := by
  have hvan := (dimensionDecay_tendsto_zero (by norm_num : (0:ℝ)<1)).mul_const (Real.log 2+K)
  simp only [zero_mul] at hvan
  filter_upwards [hvan.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4)),
    eventually_ge_atTop 1] with n hnsmall hn
  intro g hg
  have htime : 0 ≤ (2/χ)*Real.log n := mul_nonneg (by positivity)
    (Real.log_nonneg (by exact_mod_cast hn))
  apply (medianTime_le_iff g htime).mpr
  have h := continuousDistance_square_decay g (hmlsi n g hg) htime
  have hcoeff : Real.exp (-χ*((2/χ)*Real.log n))*(n:ℝ) = dimensionDecay 1 n := by
    have hed : -χ*((2/χ)*Real.log n) = -2*Real.log n := by field_simp
    rw [hed,mul_comm,← dimensionDecay,nat_mul_dimensionDecay (by omega)]
    norm_num
  rw [hcoeff] at h
  have hkn := mul_le_mul_of_nonneg_left (add_le_add_left (hnorm n g hg) (Real.log 2))
    (dimensionDecay_pos 1 n).le
  have hnD := continuousDistance_nonneg g ((2/χ)*Real.log n)
  nlinarith only [h,hkn,hnsmall,hnD]

end SKRatio.Calculus

end
end

end OAI
