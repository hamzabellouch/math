import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.ProjectionDefect

namespace OAI

noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal NNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma cfc_projection_zero {q : A} (hq : IsStarProjection q)
    (f : ℝ → ℝ) (hf0 : f 0 = 0) : cfc f q = (f 1) • q := by
  calc
    cfc f q = cfc (fun t : ℝ => (f 1)*t) q := by
      apply cfc_congr
      intro t ht
      have ht' := hq.isIdempotentElem.spectrum_subset ℝ ht
      rcases Set.mem_insert_iff.mp ht' with rfl | ht'
      · simp [hf0]
      · have he : t=1 := Set.mem_singleton_iff.mp ht'
        simp [he]
    _ = (f 1) • q := cfc_const_mul_id (f 1) q hq.isSelfAdjoint

omit [PartialOrder A] [StarOrderedRing A] in
lemma positiveCut_projection {q : A} (hq : IsStarProjection q)
    {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    directPositiveCut η q = (1-η) • q := by
  rw [directPositiveCut,cfc_projection_zero hq _ (by simp [max_eq_right (neg_nonpos.mpr hη)])]
  rw [max_eq_left (sub_nonneg.mpr hη1)]

omit [PartialOrder A] [StarOrderedRing A] in
lemma cutoff_projection {q : A} (hq : IsStarProjection q)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) : directCutoff η q = q := by
  rw [directCutoff,cfc_projection_zero hq _ (by simp)]
  rw [min_eq_right ((le_div_iff₀ hη).mpr (by simpa using hη1)),one_smul]

variable [Nontrivial A] [Nonempty (TracialState A)]
variable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
local notation "D" => FamilyUltrapower (fun τ : TracialState A => τ) U
local notation "Λ" => familyLimitTrace (fun τ : TracialState A => τ) U

include hfree in

theorem proportional_subprojection (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hcmp : StrictComparison A)
    {q : D} (hq : IsStarProjection q) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ∃ p : D, IsStarProjection p ∧ p ≤ q ∧
      ∀ s : ℕ → TracialState A, (Λ s).functional p = (t : ℂ)*(Λ s).functional q := by
  rcases eq_or_lt_of_le ht.1 with he | ht0
  · subst t
    exact ⟨0,IsStarProjection.zero _,hq.nonneg,by intro s;simp⟩
  rcases eq_or_lt_of_le ht.2 with he | ht1
  · subst t
    exact ⟨q,hq,le_rfl,by intro s;simp⟩
  obtain ⟨p,hp,hqp,hpq,htr⟩ := projection_supply U hfree hsimple hinf hcmp q
    hq.nonneg hq.norm_le (1-t) (sub_pos.mpr ht1) (sub_lt_self _ ht0)
  rw [cutoff_projection hq (sub_pos.mpr ht1) (sub_le_self _ ht.1)] at hqp hpq
  refine ⟨p,hp,(hp.le_iff_mul_eq_left hq).mpr hpq,?_⟩
  intro s
  rw [htr s,positiveCut_projection hq (sub_nonneg.mpr ht.2) (sub_le_self _ ht.1),
    sub_sub_cancel]
  exact ((Λ s).functional.toLinearMap.restrictScalars ℝ).map_smul t q

include hfree in

theorem corner_symmetry (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hcmp : StrictComparison A)
    {q : D} (hq : IsStarProjection q) :
    ∃ r : D, IsSelfAdjoint r ∧ q*r=r ∧ r*q=r ∧ r*r=q ∧
      ∀ s : ℕ → TracialState A, (Λ s).functional r=0 := by
  obtain ⟨p,hp,hpq,htr⟩ := proportional_subprojection U hfree hsimple hinf hcmp hq
    (show (1/2 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
  have hpq' := (hp.le_iff_mul_eq_left hq).mp hpq
  have hqp' := (hp.le_iff_mul_eq_right hq).mp hpq
  refine ⟨2*p-q,?_,?_,?_,?_,?_⟩
  · rw [two_mul]
    exact (hp.isSelfAdjoint.add hp.isSelfAdjoint).sub hq.isSelfAdjoint
  · simp only [mul_sub,mul_assoc,←mul_assoc q 2,Commute.ofNat_right q 2 |>.eq,
      mul_assoc,hqp',hq.isIdempotentElem.eq]
  · simp only [sub_mul,mul_assoc,hpq',hq.isIdempotentElem.eq]
  · noncomm_ring [hp.isIdempotentElem.eq,hq.isIdempotentElem.eq,hpq',hqp']
  · intro s
    rw [two_mul,map_sub,map_add,htr s]
    push_cast
    ring

end DirectComparison

namespace DirectComparison
open Pureness CurrentMain
open scoped ComplexOrder

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [PartialOrder D] [StarOrderedRing D] in
lemma compress_selfAdjoint {u : D} (hu : IsStarProjection u)
    {x : D} (hx : IsSelfAdjoint x) : IsSelfAdjoint (ProjectionCorner.compress hu x) := by
  apply Subtype.ext
  change star (u*x*u)=u*x*u
  simp only [star_mul,hu.isSelfAdjoint.star_eq,hx.star_eq,mul_assoc]

omit [PartialOrder D] [StarOrderedRing D] in
lemma compress_norm_le {u : D} (hu : IsStarProjection u) (x : D) :
    ‖ProjectionCorner.compress hu x‖ ≤ ‖x‖ := by
  change ‖u*x*u‖ ≤ ‖x‖
  calc
    _ ≤ ‖u‖*‖x‖*‖u‖ := (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1*‖x‖*1 := mul_le_mul (mul_le_mul_of_nonneg_right hu.norm_le (norm_nonneg _)) hu.norm_le (norm_nonneg _) (by positivity)
    _ = _ := by ring

omit [PartialOrder D] [StarOrderedRing D] in

def cornerCFC {u : D} (hu : IsStarProjection u) (x : D) (f : ℝ → ℝ) : D :=
  (cfc f (ProjectionCorner.compress hu x) : ProjectionCorner hu)

omit [PartialOrder D] [StarOrderedRing D] in
lemma cornerCFC_eq {u : D} (hu : IsStarProjection u) {x : D} (hx : IsSelfAdjoint x)
    {f : ℝ → ℝ} (hf : Continuous f) :
    cornerCFC hu x f = cfc f (u*x*u) - f 0 • (1-u) := by
  have hsa := compress_selfAdjoint hu hx
  have hsa' := ProjectionCorner.isSelfAdjoint_coe hu hsa
  have he := ProjectionCorner.coe_cfc hu hsa (fun t : ℝ => f t-f 0)
    (hf.sub continuous_const) (sub_self _)
  rw [cfc_sub f (fun _ : ℝ => f 0) _ hf.continuousOn continuous_const.continuousOn,
    cfc_const (f 0) _ hsa,
    cfc_sub f (fun _ : ℝ => f 0) _ hf.continuousOn continuous_const.continuousOn,
    cfc_const (f 0) _ hsa'] at he
  simp only [Algebra.algebraMap_eq_smul_one] at he
  change cornerCFC hu x f - f 0 • u = cfc f (u*x*u) - f 0 • (1:D) at he
  rw [smul_sub]
  calc
    _ = (cornerCFC hu x f - f 0 • u) + f 0 • u := by abel
    _ = _ := by rw [he]; abel

lemma traceTwoNorm_real_smul (τ : TracialState D) (r : ℝ) (a : D) :
    traceTwoNorm τ (r • a) = |r| * traceTwoNorm τ a := by
  rw [←Complex.coe_smul,traceTwoNorm_smul,Complex.norm_real,Real.norm_eq_abs]

lemma traceTwoNorm_pow_sub (τ : TracialState D) {a b : D}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (k : ℕ) :
    traceTwoNorm τ (a^k-b^k) ≤ k * traceTwoNorm τ (a-b) := by
  have hpow (n : ℕ) : ‖b^n‖ ≤ 1 := by
    induction n with
    | zero => simpa only [pow_zero] using (IsStarProjection.one D).norm_le
    | succ n hn => simpa only [pow_succ] using
        (norm_mul_le (b^n) b).trans ((mul_le_of_le_one_left (norm_nonneg _) hn).trans hb)
  induction k with
  | zero => simp
  | succ k ih =>
    have he : a^(k+1)-b^(k+1) = (a^k-b^k)*a+b^k*(a-b) := by noncomm_ring
    rw [he]
    calc
      _ ≤ traceTwoNorm τ ((a^k-b^k)*a) + traceTwoNorm τ (b^k*(a-b)) := traceTwoNorm_add_le _ _ _
      _ ≤ ‖a‖*traceTwoNorm τ (a^k-b^k)+‖b^k‖*traceTwoNorm τ (a-b) :=
        add_le_add (traceTwoNorm_mul_right _ _ _) (traceTwoNorm_mul_left _ _ _)
      _ ≤ 1*(k*traceTwoNorm τ (a-b))+1*traceTwoNorm τ (a-b) :=
        add_le_add (mul_le_mul ha ih (traceTwoNorm_nonneg _ _) zero_le_one)
          (mul_le_mul_of_nonneg_right (hpow k) (traceTwoNorm_nonneg _ _))
      _ = _ := by push_cast;ring

lemma compression_traceTwoNorm_sub (τ : TracialState D) {u v : D}
    (hu : IsStarProjection u) (hv : IsStarProjection v) {x : D} (hx : ‖x‖ ≤ 1) :
    traceTwoNorm τ (u*x*u-v*x*v) ≤ 2*traceTwoNorm τ (u-v) := by
  have he : u*x*u-v*x*v=(u-v)*x*u+v*x*(u-v) := by noncomm_ring
  have hxu : ‖x*u‖ ≤ 1 :=
    (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hx).trans hu.norm_le)
  have hvx : ‖v*x‖ ≤ 1 :=
    (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hv.norm_le).trans hx)
  rw [he,mul_assoc (u-v)]
  calc
    _ ≤ traceTwoNorm τ ((u-v)*(x*u))+traceTwoNorm τ (v*x*(u-v)) := traceTwoNorm_add_le _ _ _
    _ ≤ ‖x*u‖*traceTwoNorm τ (u-v)+‖v*x‖*traceTwoNorm τ (u-v) :=
      add_le_add (traceTwoNorm_mul_right _ _ _) (traceTwoNorm_mul_left _ _ _)
    _ ≤ 1*traceTwoNorm τ (u-v)+1*traceTwoNorm τ (u-v) :=
      add_le_add (mul_le_mul_of_nonneg_right hxu (traceTwoNorm_nonneg _ _))
        (mul_le_mul_of_nonneg_right hvx (traceTwoNorm_nonneg _ _))
    _ = _ := by ring

def cornerPolynomialConstant (P : Polynomial ℝ) : ℝ :=
  |P.coeff 0| + 2 * ∑ k ∈ Finset.range (P.natDegree+1), |P.coeff k| * k

lemma cornerPolynomialConstant_nonneg (P : Polynomial ℝ) : 0 ≤ cornerPolynomialConstant P := by
  unfold cornerPolynomialConstant
  positivity

lemma polynomial_traceTwoNorm_sub (τ : TracialState D) (P : Polynomial ℝ)
    {a b : D} (hsa : IsSelfAdjoint a) (hsb : IsSelfAdjoint b)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    traceTwoNorm τ (cfc P.eval a - cfc P.eval b) ≤
      (∑ k ∈ Finset.range (P.natDegree+1), |P.coeff k| * k) * traceTwoNorm τ (a-b) := by
  rw [cfc_polynomial P a hsa,cfc_polynomial P b hsb,
    Polynomial.aeval_eq_sum_range,Polynomial.aeval_eq_sum_range,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range (P.natDegree+1), traceTwoNorm τ (P.coeff k • a^k - P.coeff k • b^k) := traceTwoNorm_sum_le _ _ _
    _ ≤ ∑ k ∈ Finset.range (P.natDegree+1), (|P.coeff k| *k)*traceTwoNorm τ (a-b) := by
      apply Finset.sum_le_sum
      intro k _
      rw [←smul_sub,traceTwoNorm_real_smul,mul_assoc]
      exact mul_le_mul_of_nonneg_left (traceTwoNorm_pow_sub τ ha hb k) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

lemma corner_polynomial_modulus (τ : TracialState D) (P : Polynomial ℝ)
    {u v : D} (hu : IsStarProjection u) (hv : IsStarProjection v)
    {x : D} (hx : IsSelfAdjoint x) (hxn : ‖x‖ ≤ 1) :
    ‖τ.functional (cornerCFC hu x P.eval) - τ.functional (cornerCFC hv x P.eval)‖ ≤
      cornerPolynomialConstant P * traceTwoNorm τ (u-v) := by
  have hux : ‖u*x*u‖ ≤ 1 := (compress_norm_le hu x).trans hxn
  have hvx : ‖v*x*v‖ ≤ 1 := (compress_norm_le hv x).trans hxn
  have huxa := ProjectionCorner.isSelfAdjoint_coe hu (compress_selfAdjoint hu hx)
  have hvxa := ProjectionCorner.isSelfAdjoint_coe hv (compress_selfAdjoint hv hx)
  have hS : 0 ≤ ∑ k ∈ Finset.range (P.natDegree+1), |P.coeff k| *(k:ℝ) := by positivity
  rw [←map_sub,cornerCFC_eq hu hx P.continuous,cornerCFC_eq hv hx P.continuous]
  have he : (cfc P.eval (u*x*u)-P.eval 0 • (1-u)) -
      (cfc P.eval (v*x*v)-P.eval 0 • (1-v)) =
      (cfc P.eval (u*x*u)-cfc P.eval (v*x*v))+P.coeff 0 • (u-v) := by
    simp only [←Polynomial.coeff_zero_eq_eval_zero,smul_sub]; abel
  rw [he]
  calc
    _ ≤ traceTwoNorm τ ((cfc P.eval (u*x*u)-cfc P.eval (v*x*v))+P.coeff 0 • (u-v)) := trace_norm_le_twoNorm _ _
    _ ≤ traceTwoNorm τ (cfc P.eval (u*x*u)-cfc P.eval (v*x*v))+
      traceTwoNorm τ (P.coeff 0 • (u-v)) := traceTwoNorm_add_le _ _ _
    _ ≤ (∑ k ∈ Finset.range (P.natDegree+1), |P.coeff k| *k)* (2*traceTwoNorm τ (u-v)) +
        |P.coeff 0| *traceTwoNorm τ (u-v) := by
      rw [traceTwoNorm_real_smul]
      exact add_le_add ((polynomial_traceTwoNorm_sub τ P huxa hvxa hux hvx).trans
        (mul_le_mul_of_nonneg_left (compression_traceTwoNorm_sub τ hu hv hxn) hS)) le_rfl
    _ = _ := by unfold cornerPolynomialConstant; ring

omit [PartialOrder D] [StarOrderedRing D] in
lemma spectrum_subset_unit_interval {a : D} (ha : IsSelfAdjoint a) (han : ‖a‖ ≤ 1) :
    spectrum ℝ a ⊆ Set.Icc (-1) 1 := by
  intro t ht
  have hb : |t| ≤ 1 := by
    have he := norm_apply_le_norm_cfc (fun t : ℝ => t) a ht continuous_id.continuousOn ha
    rw [cfc_id' ℝ a ha,Real.norm_eq_abs] at he
    exact he.trans han
  exact abs_le.mp hb

omit [PartialOrder D] [StarOrderedRing D] in
lemma cornerCFC_approx {u : D} (hu : IsStarProjection u)
    {x : D} (hx : IsSelfAdjoint x) (hxn : ‖x‖ ≤ 1)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a : ℝ} (ha : 0 ≤ a) (hfg : ∀ t ∈ Set.Icc (-1:ℝ) 1, |f t-g t| ≤ a) :
    ‖cornerCFC hu x f - cornerCFC hu x g‖ ≤ a := by
  change ‖((cfc f (ProjectionCorner.compress hu x)-cfc g (ProjectionCorner.compress hu x) :
    ProjectionCorner hu) : D)‖ ≤ a
  rw [←show ‖(cfc f (ProjectionCorner.compress hu x)-cfc g (ProjectionCorner.compress hu x) :
    ProjectionCorner hu)‖ = ‖((cfc f (ProjectionCorner.compress hu x)-cfc g (ProjectionCorner.compress hu x) :
    ProjectionCorner hu) : D)‖ from rfl]
  rw [←cfc_sub _ _ _ hf.continuousOn hg.continuousOn]
  apply norm_cfc_le ha
  intro t ht
  exact hfg t (spectrum_subset_unit_interval (compress_selfAdjoint hu hx) ((compress_norm_le hu x).trans hxn) ht)

theorem moving_corner_modulus (τ : TracialState D) (P : Polynomial ℝ)
    {u v : D} (hu : IsStarProjection u) (hv : IsStarProjection v)
    {x : D} (hx : IsSelfAdjoint x) (hxn : ‖x‖ ≤ 1)
    {f : ℝ → ℝ} (hf : Continuous f) {a : ℝ} (ha : 0 ≤ a)
    (happrox : ∀ t ∈ Set.Icc (-1:ℝ) 1, |f t-P.eval t| ≤ a) :
    ‖τ.functional (cornerCFC hu x f) - τ.functional (cornerCFC hv x f)‖ ≤
      2*a + cornerPolynomialConstant P * traceTwoNorm τ (u-v) := by
  have huP := (trace_norm_le_norm τ (cornerCFC hu x f-cornerCFC hu x P.eval)).trans
    (cornerCFC_approx hu hx hxn hf P.continuous ha happrox)
  have hvP := (trace_norm_le_norm τ (cornerCFC hv x f-cornerCFC hv x P.eval)).trans
    (cornerCFC_approx hv hx hxn hf P.continuous ha happrox)
  rw [map_sub] at huP hvP
  have he : τ.functional (cornerCFC hu x f)-τ.functional (cornerCFC hv x f) =
      (τ.functional (cornerCFC hu x f)-τ.functional (cornerCFC hu x P.eval))+
      (τ.functional (cornerCFC hu x P.eval)-τ.functional (cornerCFC hv x P.eval))-
      (τ.functional (cornerCFC hv x f)-τ.functional (cornerCFC hv x P.eval)) := by abel
  rw [he]
  calc
    _ ≤ ‖τ.functional (cornerCFC hu x f)-τ.functional (cornerCFC hu x P.eval)‖ +
        ‖τ.functional (cornerCFC hu x P.eval)-τ.functional (cornerCFC hv x P.eval)‖ +
        ‖τ.functional (cornerCFC hv x f)-τ.functional (cornerCFC hv x P.eval)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by linarith [corner_polynomial_modulus τ P hu hv hx hxn]

end DirectComparison
end

end OAI
