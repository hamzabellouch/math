import OAI.Combinatorics.SparsestCut.Profiles

namespace OAI

universe u1 u2 u3 u4 u5 u6

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.MetricKernel
open MeasureTheory Set
open scoped RealInnerProductSpace BigOperators
variable {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type u2} {κ : Type u3} [Fintype ι] [Fintype κ]

omit [Fintype ι] in
lemma gram_eq_kernel (g : κ → E) (θ : ι → E) (α : ι → κ → ℝ)
    (q ε : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (v w : ι) :
    CommonKernel.gram g θ α q ε a b v w =
      Profile.kernel g q ε a b (θ v) (θ w) (α v) (α w) := by
  have hf (k : κ) := CommonKernel.circle_integrable g θ α ha hab v w k
  have hi := CommonKernel.gaussian_integrable θ ha hab v w
  have hiS : IntervalIntegrable (fun σ => ∑ i, inner ℝ
      (CommonKernel.circle (inner ℝ (g i) (θ v)/σ) (α v i))
      (CommonKernel.circle (inner ℝ (g i) (θ w)/σ) (α w i))/σ) volume a b := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ => hf i) using 1
    funext σ
    simp only [Finset.sum_apply]
  unfold CommonKernel.gram Profile.kernel Profile.pairing
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_finsetSum (fun k _ => hf k),
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (hi.const_mul q)
      (hiS.const_mul ε)]
  apply intervalIntegral.integral_congr
  intro σ hσ
  rw [norm_sub_rev (θ w) (θ v)]

  simp only [CommonKernel.circle_inner, inner_sub_right, sub_div, ← Finset.sum_div]
  ring

lemma kernel_psd (g : κ → E) (θ : ι → E) (α : ι → κ → ℝ)
    {q ε a b : ℝ} (hq : 0 ≤ q) (hε : 0 ≤ ε) (ha : 0 < a) (hab : a ≤ b) :
    Matrix.PosSemidef (fun v w => Profile.kernel g q ε a b (θ v) (θ w) (α v) (α w)) := by
  have he : (fun v w => Profile.kernel g q ε a b (θ v) (θ w) (α v) (α w)) =
      CommonKernel.gram g θ α q ε a b := by
    funext v w; exact (gram_eq_kernel g θ α q ε ha hab v w).symm
  rw [he]
  exact CommonKernel.gram_posSemidef g θ α hq hε ha hab

lemma base_pairing (g : κ → E) (q ε σ : ℝ) (θ η : E) :
    Profile.pairing g q ε σ θ θ 0 0 + Profile.pairing g q ε σ η η 0 0 -
      2*Profile.pairing g q ε σ θ η 0 0 =
      2*q*KernelApprox.scaled ‖η-θ‖ σ +
        2*ε/σ*∑ i, (1-Real.cos (inner ℝ (g i) (η-θ)/σ)) := by
  simp only [Profile.pairing, Pi.zero_apply, mul_zero, zero_mul, add_zero,
     sub_self, norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0), neg_zero,
    zero_div, Real.exp_zero, inner_zero_right, Real.cos_zero, Real.sin_zero, one_mul,
    Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_sub_distrib, KernelApprox.scaled]
  ring

omit [InnerProductSpace ℝ E] in
lemma gaussian_scaled_integrable (θ η : E) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (KernelApprox.scaled ‖η-θ‖) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  unfold KernelApprox.scaled
  apply continuousOn_const.sub
  apply Real.continuous_exp.comp_continuousOn
  exact continuousOn_const.div (by fun_prop) (fun σ hσ => by have := ha.trans_le hσ.1; positivity)

omit [Fintype κ] in
lemma cos_integrable (g : κ → E) (θ η : E) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (i : κ) :
    IntervalIntegrable (fun σ => (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  have hn : ∀ σ ∈ Icc a b, σ ≠ 0 := fun σ hσ => (ha.trans_le hσ.1).ne'
  exact (continuousOn_const.sub (Real.continuous_cos.comp_continuousOn
    (continuousOn_const.div continuousOn_id hn))).div continuousOn_id hn

omit [Fintype κ] in
lemma cos_integral_bound (g : κ → E) (θ η : E) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (i : κ) :
    |∫ σ in a..b, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ| ≤ 2*Real.log (b/a) := by
  have hi := cos_integrable g θ η ha hab i
  have hii : IntervalIntegrable (fun σ : ℝ => σ⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact continuousOn_id.inv₀ (fun σ hσ => (ha.trans_le hσ.1).ne')
  have hn : 0 ≤ ∫ σ in a..b, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ := by
    apply intervalIntegral.integral_nonneg hab
    intro σ hσ
    exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (ha.trans_le hσ.1).le
  rw [abs_of_nonneg hn]
  calc
    _ ≤ ∫ σ in a..b, 2*σ⁻¹ := by
      apply intervalIntegral.integral_mono_on hab hi (hii.const_mul 2)
      intro σ hσ
      rw [← div_eq_mul_inv]
      apply div_le_div_of_nonneg_right _ (ha.trans_le hσ.1).le
      linarith [Real.neg_one_le_cos (inner ℝ (g i) (η-θ)/σ)]
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha (ha.trans_le hab)]

lemma base_distance_error (g : κ → E) {q ε a b : ℝ} (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (ha : 0 < a) (hab : a ≤ b) (θ η : E) :
    |Profile.kernel g q ε a b θ θ 0 0 + Profile.kernel g q ε a b η η 0 0 -
      2*Profile.kernel g q ε a b θ η 0 0 - KernelApprox.cstar*q*‖η-θ‖| ≤
      q*(2*a+‖η-θ‖^2/b)+4*ε*(Fintype.card κ : ℝ)*Real.log (b/a) := by
  have hi1 := Profile.pairing_integrable g q ε θ θ 0 0 ha hab
  have hi2 := Profile.pairing_integrable g q ε η η 0 0 ha hab
  have hi3 := Profile.pairing_integrable g q ε θ η 0 0 ha hab
  have hic (i : κ) := cos_integrable g θ η ha hab i
  have hig := gaussian_scaled_integrable θ η ha hab
  have hiS : IntervalIntegrable (fun σ => ∑ i, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ) volume a b := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ => hic i) using 1
    funext σ
    simp only [Finset.sum_apply]
  have he : Profile.kernel g q ε a b θ θ 0 0 + Profile.kernel g q ε a b η η 0 0 -
      2*Profile.kernel g q ε a b θ η 0 0 =
      2*q*(∫ σ in a..b, KernelApprox.scaled ‖η-θ‖ σ) +
      2*ε*(∑ i, ∫ σ in a..b, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ) := by
    unfold Profile.kernel
    rw [← intervalIntegral.integral_add hi1 hi2, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hi1.add hi2) (hi3.const_mul 2)]
    have hi : (fun σ => Profile.pairing g q ε σ θ θ 0 0 + Profile.pairing g q ε σ η η 0 0 -
        2*Profile.pairing g q ε σ θ η 0 0) =
        (fun σ => 2*q*KernelApprox.scaled ‖η-θ‖ σ +
          2*ε*∑ i, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ) := by
      funext σ; rw [base_pairing]; simp only [← Finset.sum_div]; ring
    rw [hi, intervalIntegral.integral_add (hig.const_mul _) (hiS.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun i _ => hic i)]
  rw [he]
  have ht := KernelApprox.truncated_error (norm_nonneg (η-θ)) ha hab
  rw [← intervalIntegral.integral_of_le hab] at ht
  have hs : |∑ i, ∫ σ in a..b, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ| ≤
      (Fintype.card κ : ℝ)*(2*Real.log (b/a)) := by
    calc
      _ ≤ ∑ i, |∫ σ in a..b, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : κ, 2*Real.log (b/a) := Finset.sum_le_sum (fun i _ => cos_integral_bound g θ η ha hab i)
      _ = _ := by simp
  have hsplit : 2*q*(∫ σ in a..b, KernelApprox.scaled ‖η-θ‖ σ) +
      2*ε*(∑ i, ∫ σ in a..b, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ) -
      KernelApprox.cstar*q*‖η-θ‖ =
      q*(2*(∫ σ in a..b, KernelApprox.scaled ‖η-θ‖ σ)-KernelApprox.cstar*‖η-θ‖)+
      2*ε*(∑ i, ∫ σ in a..b, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ) := by ring
  rw [hsplit]
  calc
    _ ≤ |q*(2*(∫ σ in a..b, KernelApprox.scaled ‖η-θ‖ σ)-KernelApprox.cstar*‖η-θ‖)|+
        |2*ε*(∑ i, ∫ σ in a..b, (1-Real.cos (inner ℝ (g i) (η-θ)/σ))/σ)| := abs_add_le ..
    _ ≤ q*(2*a+‖η-θ‖^2/b)+2*ε*((Fintype.card κ : ℝ)*(2*Real.log (b/a))) := by
      simp only [abs_mul, abs_of_nonneg hq, abs_of_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hε)]
      exact add_le_add (mul_le_mul_of_nonneg_left ht hq) (mul_le_mul_of_nonneg_left hs (by positivity))
    _ = _ := by ring

end UniformSparsestCut.MetricKernel

namespace UniformSparsestCut.MetricKernel
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
variable {E : Type u4} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {S : Type u5} {N : Type u6} [Fintype S] [Fintype N] [DecidableEq S]

lemma full_differential_bound (g : S → N → E) (s : S)
    {q ε σ k γ G A V H D₀ : ℝ} (θ η v : E) (h : N → ℝ) (α β : S × N → ℝ)
    (hq : 0 < q) (hε : 0 < ε) (hσ : 0 < σ) (hk : k = q^2/(Fintype.card N : ℝ))
    (hG : 0 ≤ G) (hA : 0 ≤ A) (hV : 0 ≤ V) (hH : 0 ≤ H) (hD : 0 ≤ D₀) (hγ : 0 ≤ γ)
    (hg : ∀ s i, ‖g s i‖ ≤ G) (hv : ‖v‖ ≤ V*H) (hh : ∑ i, |h i| ≤ H)
    (hα : ∀ i, |α i| ≤ A) (hβ : ∀ i, |β i| ≤ A)
    (hδ : ∀ i : S × N, |(if i.1 = s then k/ε*(h i.2-inner ℝ (g i.1 i.2) v/q) else 0)| ≤ D₀*H)
    (hf : ‖Real.exp (-‖(σ⁻¹:ℝ) • (η-θ)‖^2/2) • ((σ⁻¹:ℝ) • (η-θ)) -
       ((Fintype.card N : ℝ)⁻¹) • ∑ i, Real.sin (inner ℝ (g s i) (η-θ)/σ) • g s i‖ ≤ γ) :
    |Profile.differential (fun j : S × N => g j.1 j.2) q ε σ θ η v α β
      (fun j => if j.1 = s then k/ε*(h j.2-inner ℝ (g j.1 j.2) v/q) else 0)| ≤
      ((k+q*γ*V+ε*((Fintype.card S : ℝ)*(Fintype.card N : ℝ))*D₀*A)*H)/σ +
      (ε*((Fintype.card S : ℝ)*(Fintype.card N : ℝ))*G*V*(1+A^2+2*A)*H)/σ^2 := by
  let δ : S × N → ℝ := fun j => if j.1 = s then k/ε*(h j.2-inner ℝ (g j.1 j.2) v/q) else 0
  let c : ℝ := (Fintype.card S : ℝ)*(Fintype.card N : ℝ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  have hg0 := Profile.active_bound g s θ η v h hq hε hσ hk hg hf
  have hcorr := Profile.differential_correction (q := q) (fun j : S × N => g j.1 j.2) hε.le hσ θ η v α β δ
  have hc' : (∑ i : S × N, (|δ i| *|β i|+|inner ℝ (g i.1 i.2) v|/σ*
      (|α i| *|β i|+|α i|+|β i|))) ≤ c*(D₀*H*A+G*(V*H)/σ*(A^2+2*A)) := by
    calc
      _ ≤ ∑ _i : S × N, (D₀*H*A+G*(V*H)/σ*(A^2+2*A)) := by
        apply Finset.sum_le_sum; intro i _
        apply add_le_add
        · exact mul_le_mul (hδ i) (hβ i) (abs_nonneg _) (mul_nonneg hD hH)
        · apply mul_le_mul
          · apply div_le_div_of_nonneg_right _ hσ.le
            exact (abs_real_inner_le_norm _ v).trans (mul_le_mul (hg i.1 i.2) hv (norm_nonneg v) hG)
          · have hp := mul_le_mul (hα i) (hβ i) (abs_nonneg _) hA
            nlinarith [hα i,hβ i]
          · positivity
          · positivity
      _ = _ := by simp [c,Fintype.card_prod]; ring
  have hb0 : k/σ*(∑ i, |h i|) + q*γ/σ*‖v‖ + ε/σ^2*(c*G)*‖v‖ ≤
      k/σ*H+q*γ/σ*(V*H)+ε/σ^2*(c*G)*(V*H) := by
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hh (by positivity))
      (mul_le_mul_of_nonneg_left hv (by positivity))) (mul_le_mul_of_nonneg_left hv (by positivity))
  calc
    _ ≤ |Profile.differential (fun j : S × N => g j.1 j.2) q ε σ θ η v 0 0 δ|+
      |Profile.differential (fun j : S × N => g j.1 j.2) q ε σ θ η v α β δ -
        Profile.differential (fun j : S × N => g j.1 j.2) q ε σ θ η v 0 0 δ| := by
      simpa only [add_sub_cancel] using abs_add_le
        (Profile.differential (fun j : S × N => g j.1 j.2) q ε σ θ η v 0 0 δ)
        (Profile.differential (fun j : S × N => g j.1 j.2) q ε σ θ η v α β δ-
          Profile.differential (fun j : S × N => g j.1 j.2) q ε σ θ η v 0 0 δ)
    _ ≤ (k/σ*H+q*γ/σ*(V*H)+ε/σ^2*(c*G)*(V*H))+
        ε/σ*(c*(D₀*H*A+G*(V*H)/σ*(A^2+2*A))) :=
      add_le_add (hg0.trans hb0) (hcorr.trans (mul_le_mul_of_nonneg_left hc' (by positivity)))
    _ = _ := by dsimp [c]; field_simp; ring

end UniformSparsestCut.MetricKernel

end

end OAI
