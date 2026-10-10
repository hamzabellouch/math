import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples

lemma reciprocal_iterated_derivative_bound (j : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    ‖iteratedFDerivWithin ℝ j (fun y : ℝ => 1/y) (Ioi 0) t‖ ≤ (j.factorial : ℝ) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_one_div j isOpen_Ioi ht0]
  have he : (-1-(j:ℤ)) = -((j+1 : ℕ):ℤ) := by omega
  dsimp only
  rw [he,zpow_neg,zpow_natCast]
  simp only [norm_mul,norm_pow,Real.norm_eq_abs,abs_neg,abs_one,one_pow,
    Nat.abs_cast,one_mul,norm_inv]
  have hp : 1 ≤ t^(j+1) := one_le_pow₀ ht
  have hi : |(t^(j+1))⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg ht0.le _))]
    exact inv_le_one_of_one_le₀ hp
  simpa only [mul_one,abs_inv,abs_pow] using mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg j.factorial)

theorem normalized_reciprocal_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {x : E} (hx : 1 ≤ f x)
    (h : ℕ) (D : ℝ)
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j f x‖ ≤ D^j) :
    ‖iteratedFDeriv ℝ h (fun y => 1/f y) x‖ ≤ (h.factorial : ℝ)^2*D^h := by
  let S := {y | 0 < f y}
  have hS : IsOpen S := isOpen_lt continuous_const hf.continuous
  have hxS : x ∈ S := zero_lt_one.trans_le hx
  have hg : ContDiffOn ℝ ∞ (fun y : ℝ => 1/y) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id (fun y hy => hy.ne')
  have hb := norm_iteratedFDerivWithin_comp_le hg hf.contDiffOn (show (h:ℕ∞ω) ≤ (∞ : ℕ∞ω) from le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
    isOpen_Ioi.uniqueDiffOn hS.uniqueDiffOn (fun y (hy : y ∈ S) => hy) hxS
    (C:=(h.factorial:ℝ)) (D:=D) (fun j hj =>
      (reciprocal_iterated_derivative_bound j hx).trans (by exact_mod_cast Nat.factorial_le hj))
    (fun j hj hjh => by
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hS.uniqueDiffOn (hf.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))).contDiffAt hxS]
      exact hD j hj hjh)
  change ‖iteratedFDerivWithin ℝ h (fun y => 1/f y) S x‖ ≤ _ at hb
  have hrec : ContDiffAt ℝ h (fun y => 1/f y) x :=
    (contDiffAt_const.div hf.contDiffAt (zero_lt_one.trans_le hx).ne').of_le
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hS.uniqueDiffOn hrec hxS] at hb
  simpa only [Function.comp_apply,pow_two,mul_assoc] using hb

theorem weighted_reciprocal_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {x : E} (h : ℕ)
    {δ W M R : ℝ} (hδ : 0 < δ) (hW : 0 < W) (hR : 0 ≤ R) (hx : δ*W^2 ≤ f x)
    (hjet : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j f x‖ ≤ M*R^j*W^2) :
    ‖iteratedFDeriv ℝ h (fun y => 1/f y) x‖ ≤
      (h.factorial : ℝ)^2 * (max 1 (M/δ)*R)^h / (δ*W^2) := by
  let c := δ*W^2
  have hc : 0 < c := mul_pos hδ (sq_pos_of_pos hW)
  let F : E → ℝ := fun y => c⁻¹*f y
  have hF : ContDiff ℝ ∞ F := contDiff_const.mul hf
  have hxF : 1 ≤ F x := by
    dsimp only [F]
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hc).mpr (by simpa only [one_mul] using hx)
  have hD : ∀ j : ℕ, 1 ≤ j → j ≤ h →
      ‖iteratedFDeriv ℝ j F x‖ ≤ (max 1 (M/δ)*R)^j := by
    intro j hj hjh
    have hej : iteratedFDeriv ℝ j F x = c⁻¹ • iteratedFDeriv ℝ j f x := by
      simpa only [F,smul_eq_mul] using
        (iteratedFDeriv_const_smul_apply' (a:=c⁻¹) (x:=x) (hf.of_le
          (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))).contDiffAt)
    rw [hej,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hc)]
    calc
      c⁻¹*‖iteratedFDeriv ℝ j f x‖ ≤ c⁻¹*(M*R^j*W^2) :=
        mul_le_mul_of_nonneg_left (hjet j hj hjh) (inv_nonneg.mpr hc.le)
      _ = (M/δ)*R^j := by dsimp only [c]; field_simp
      _ ≤ (max 1 (M/δ))^j*R^j := mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_self_pow₀ (le_max_left _ _) (by omega))) (pow_nonneg hR j)
      _ = (max 1 (M/δ)*R)^j := (mul_pow _ _ _).symm
  have hb := normalized_reciprocal_jet_bound hF hxF h (max 1 (M/δ)*R) hD
  have hfx : f x ≠ 0 := (hc.trans_le hx).ne'
  have hrec : ContDiffAt ℝ h (fun y => 1/f y) x :=
    (contDiffAt_const.div hf.contDiffAt hfx).of_le
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
  have he : (fun y => 1/F y) = fun y => c • (1/f y) := by
    funext y
    simp only [F,one_div,smul_eq_mul,mul_inv_rev,inv_inv]
    ring
  rw [he,iteratedFDeriv_const_smul_apply' hrec,norm_smul,
    Real.norm_eq_abs,abs_of_pos hc] at hb
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hb)

lemma geometric_product_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (h : ℕ) {F G R S : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*R^j)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G*S^j) :
    ‖iteratedFDeriv ℝ h (fun y => f y*g y) x‖ ≤ F*G*(R+S)^h := by
  calc
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (h-i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*(F*R^i)*(G*S^(h-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ h := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul_of_nonneg
        (mul_le_mul_of_nonneg le_rfl (hfj i hi') (Nat.cast_nonneg _)
          (mul_nonneg hF (pow_nonneg hR _)))
        (hgj (h-i) (Nat.sub_le _ _))
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        (mul_nonneg hG (pow_nonneg hS _))
    _ = F*G*(R+S)^h := by
      rw [add_pow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem weighted_quotient_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f d : E → ℝ} (hf : ContDiff ℝ ∞ f) (hd : ContDiff ℝ ∞ d)
    (hdne : ∀ y, d y ≠ 0) (x : E) (h : ℕ)
    {δ W M N R S : ℝ} (hδ : 0 < δ) (hW : 0 < W)
    (hN : 0 ≤ N) (hR : 0 ≤ R) (hS : 0 ≤ S) (hx : δ*W^2 ≤ d x)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ N*R^j*W^2)
    (hdj : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j d x‖ ≤ M*S^j*W^2) :
    ‖iteratedFDeriv ℝ h (fun y => f y/d y) x‖ ≤
      N*(h.factorial : ℝ)^2/δ*(R+max 1 (M/δ)*S)^h := by
  have hrec : ContDiff ℝ ∞ (fun y => 1/d y) := contDiff_const.div hd hdne
  have hinv : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => 1/d y) x‖ ≤
      ((h.factorial:ℝ)^2/(δ*W^2))*(max 1 (M/δ)*S)^j := by
    intro j hj
    have hb := weighted_reciprocal_jet_bound hd j hδ hW hS hx
      (fun i hi hij => hdj i hi (hij.trans hj))
    calc
      _ ≤ (j.factorial:ℝ)^2*(max 1 (M/δ)*S)^j/(δ*W^2) := hb
      _ ≤ (h.factorial:ℝ)^2*(max 1 (M/δ)*S)^j/(δ*W^2) := by
        gcongr
      _ = _ := by ring
  have hb := geometric_product_jet_bound hf hrec x h
    (F:=N*W^2) (G:=(h.factorial:ℝ)^2/(δ*W^2))
    (mul_nonneg hN (sq_nonneg _)) (by positivity) hR
    (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hS)
    (fun j hj => by simpa only [mul_assoc,mul_left_comm,mul_comm] using hfj j hj) hinv
  have he : (N*W^2)*((h.factorial:ℝ)^2/(δ*W^2)) = N*(h.factorial:ℝ)^2/δ := by
    field_simp
  simpa only [one_div,← div_eq_mul_inv,he] using hb

theorem frequency_weighted_quotient_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f d : E → ℝ} (hf : ContDiff ℝ ∞ f) (hd : ContDiff ℝ ∞ d)
    (hdne : ∀ y, d y ≠ 0) (x : E) (h B a D : ℕ)
    {n W F C : ℝ} (hn : 1 ≤ n) (hW : 0 < W) (hF : 0 ≤ F)
    (hx : W^2/(2*n^(2*B)) ≤ d x)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*n^(a+j)/(n^D)*W^2)
    (hdj : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j d x‖ ≤ C*n^(j+10)*W^2) :
    ‖iteratedFDeriv ℝ h (fun y => f y/d y) x‖ ≤
      (2*F*(h.factorial:ℝ)^2*(1+max 1 (2*C))^h)*
        n^(a+2*B+(2*B+11)*h)/(n^D) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  let δ : ℝ := 1/(2*n^(2*B))
  let N : ℝ := F*n^a/(n^D)
  let M : ℝ := C*n^10
  let q : ℝ := max 1 (2*C)
  let t : ℕ := 2*B+11
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hx' : δ*W^2 ≤ d x := by simpa only [δ,one_div,div_eq_mul_inv,mul_comm,one_mul] using hx
  have hfj' : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ N*n^j*W^2 := by
    intro j hj
    calc
      _ ≤ F*n^(a+j)/(n^D)*W^2 := hfj j hj
      _ = _ := by dsimp only [N]; rw [pow_add]; ring
  have hdj' : ∀ j : ℕ, 1 ≤ j → j ≤ h →
      ‖iteratedFDeriv ℝ j d x‖ ≤ M*n^j*W^2 := by
    intro j hj hjh
    calc
      _ ≤ C*n^(j+10)*W^2 := hdj j hj hjh
      _ = _ := by dsimp only [M]; rw [pow_add]; ring
  have hb := weighted_quotient_jet_bound hf hd hdne x h hδ hW hN hn0.le hn0.le hx' hfj' hdj'
  have heM : M/δ = 2*C*n^(2*B+10) := by
    dsimp only [M,δ]
    rw [pow_add]
    field_simp
  have hq : 1 ≤ q := le_max_left _ _
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hpow : 1 ≤ n^(2*B+10) := one_le_pow₀ hn
  have hmax : max 1 (M/δ) ≤ q*n^(2*B+10) := by
    apply max_le
    · exact hq.trans (le_mul_of_one_le_right hq0 hpow)
    · rw [heM]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hn0.le _)
  have hsum : n+max 1 (M/δ)*n ≤ (1+q)*n^t := by
    have hnle : n ≤ n^t := by
      simpa only [pow_one] using pow_le_pow_right₀ hn (show 1 ≤ t by dsimp only [t]; omega)
    have hm : max 1 (M/δ)*n ≤ q*n^t := by
      calc
        _ ≤ (q*n^(2*B+10))*n := mul_le_mul_of_nonneg_right hmax hn0.le
        _ = q*n^t := by dsimp only [t]; rw [show 2*B+11=(2*B+10)+1 by omega,pow_succ]; ring
    calc
      _ ≤ n^t+q*n^t := add_le_add hnle hm
      _ = _ := by ring
  calc
    _ ≤ N*(h.factorial:ℝ)^2/δ*(n+max 1 (M/δ)*n)^h := hb
    _ ≤ N*(h.factorial:ℝ)^2/δ*((1+q)*n^t)^h := by
      gcongr
    _ = _ := by
      dsimp only [N,δ,t,q]
      simp only [mul_pow,pow_add,pow_mul]
      field_simp

theorem frequency_weighted_quotient_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f d : E → ℝ} (hf : ContDiff ℝ ∞ f) (hd : ContDiff ℝ ∞ d)
    (hdne : ∀ y, d y ≠ 0) (x : E) (h B a D : ℕ)
    {n W F C : ℝ} (hn : 1 ≤ n) (hW : 0 < W) (hF : 0 ≤ F)
    (hx : W^2/(2*n^(2*B)) ≤ d x)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*n^(a+j)/(n^D)*W^2)
    (hdj : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j d x‖ ≤ C*n^(j+10)*W^2) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y/d y) x‖ ≤
      (2*F*(h.factorial:ℝ)^2*(1+max 1 (2*C))^h)*
        n^(a+2*B+(2*B+11)*h)/(n^D) := by
  intro j hj
  apply (frequency_weighted_quotient_bound hf hd hdne x j B a D hn hW hF hx
    (fun i hi => hfj i (hi.trans hj)) (fun i hi hij => hdj i hi (hij.trans hj))).trans
  gcongr
  have := le_max_left (1:ℝ) (2*C)
  linarith

theorem frequency_weighted_product_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (h a b D : ℕ) {n W F G : ℝ}
    (hn : 1 ≤ n) (hW : 0 < W) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*n^(a+j)/(n^D)*W)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G*n^(b+j)*W) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y*g y) x‖ ≤
      (2^h*F*G)*n^(a+b+j)/(n^D)*W^2 := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hfj' : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ (F*n^a/(n^D)*W)*n^j := by
    intro j hj
    calc
      _ ≤ F*n^(a+j)/(n^D)*W := hfj j hj
      _ = _ := by rw [pow_add]; ring
  have hgj' : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ (G*n^b*W)*n^j := by
    intro j hj
    calc
      _ ≤ G*n^(b+j)*W := hgj j hj
      _ = _ := by rw [pow_add]; ring
  intro j hj
  calc
    _ ≤ (F*n^a/(n^D)*W)*(G*n^b*W)*(n+n)^j :=
      geometric_product_jet_bound hf hg x j (by positivity) (by positivity) hn0.le hn0.le
        (fun i hi => hfj' i (hi.trans hj)) (fun i hi => hgj' i (hi.trans hj))
    _ = (2^j*F*G)*n^(a+b+j)/(n^D)*W^2 := by
      rw [show n+n=2*n by ring,mul_pow]
      simp only [pow_add]
      ring
    _ ≤ (2^h*F*G)*n^(a+b+j)/(n^D)*W^2 := by
      gcongr
      norm_num

end YauCounterexamples

end

end OAI
