import OAI.Combinatorics.SparsestCut.CommonKernel

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.Profile
variable {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type u2} [Fintype ι]

def pairing (g : ι → E) (q ε σ : ℝ) (θ η : E) (α β : ι → ℝ) : ℝ :=
  q*Real.exp (-‖η-θ‖^2/(2*σ^2)) + ε/σ*(∑ i, (
    (1+α i*β i)*Real.cos (inner ℝ (g i) (η-θ)/σ) +
      (α i-β i)*Real.sin (inner ℝ (g i) (η-θ)/σ)))

def differential (g : ι → E) (q ε σ : ℝ) (θ η v : E)
    (α β δ : ι → ℝ) : ℝ :=
  q/σ*(inner ℝ ((σ⁻¹:ℝ) • (η-θ)) v)*Real.exp (-‖η-θ‖^2/(2*σ^2)) +
    ε/σ*(∑ i, (δ i*(β i*Real.cos (inner ℝ (g i) (η-θ)/σ)+Real.sin (inner ℝ (g i) (η-θ)/σ)) +
      (inner ℝ (g i) v/σ)*((1+α i*β i)*Real.sin (inner ℝ (g i) (η-θ)/σ)-
        (α i-β i)*Real.cos (inner ℝ (g i) (η-θ)/σ))))

lemma pairing_hasDeriv (g : ι → E) (q ε σ : ℝ) (θ η v : E)
    (α β δ : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun t => pairing g q ε σ (θ+t • v) η (fun i => α i+t*δ i) β)
      (differential g q ε σ (θ+t • v) η v (fun i => α i+t*δ i) β δ) t := by
  have hx : HasDerivAt (fun t : ℝ => η-(θ+t • v)) (-v) t :=
    by simpa using (((hasDerivAt_id t).smul_const v).const_add θ).const_sub η
  have hn := hx.norm_sq.neg.div_const (2*σ^2)
  have he := hn.exp.const_mul q
  have hi (i : ι) : HasDerivAt (fun t : ℝ => inner ℝ (g i) (η-(θ+t • v))/σ)
      (-inner ℝ (g i) v/σ) t := by
    convert ((innerSL ℝ (g i)).hasFDerivAt.comp_hasDerivAt t hx).div_const σ using 1 <;> try rfl
    simp only [innerSL_apply_apply, inner_neg_right]
  have hd (i : ι) : HasDerivAt (fun t : ℝ => α i+t*δ i) (δ i) t := by
    simpa using ((hasDerivAt_id t).mul_const (δ i)).const_add (α i)
  have hs (i : ι) := ((((hd i).mul_const (β i)).const_add 1).mul (hi i).cos).add
    (((hd i).sub_const (β i)).mul (hi i).sin)
  have hsum := (HasDerivAt.sum (u := Finset.univ) (fun i _ => hs i)).const_mul (ε/σ)
  convert he.add hsum using 1 <;> try rfl
  · funext z; simp [pairing, Finset.sum_apply]
  · simp only [differential, real_inner_smul_left, inner_neg_right, Pi.neg_apply]
    congr 1
    · ring
    · congr 1; apply Finset.sum_congr rfl; intro i _; ring

lemma differential_correction (g : ι → E) {q ε σ : ℝ} (hε : 0 ≤ ε) (hσ : 0 < σ)
    (θ η v : E) (α β δ : ι → ℝ) :
    |differential g q ε σ θ η v α β δ - differential g q ε σ θ η v 0 0 δ| ≤
      ε/σ*(∑ i, (|δ i| * |β i| + |inner ℝ (g i) v|/σ*(|α i| * |β i| + |α i| + |β i|))) := by
  have heq : differential g q ε σ θ η v α β δ - differential g q ε σ θ η v 0 0 δ =
      ε/σ*(∑ i, (δ i*β i*Real.cos (inner ℝ (g i) (η-θ)/σ) +
       (inner ℝ (g i) v/σ)*(α i*β i*Real.sin (inner ℝ (g i) (η-θ)/σ)-
         α i*Real.cos (inner ℝ (g i) (η-θ)/σ)+β i*Real.cos (inner ℝ (g i) (η-θ)/σ)))) := by
    unfold differential
    simp only [Pi.zero_apply, mul_zero, zero_mul, add_zero, sub_zero]
    rw [show ∀ a b c : ℝ, (a+b)-(a+c)=b-c by intros; ring]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [heq, abs_mul, abs_of_nonneg (div_nonneg hε hσ.le)]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hε hσ.le)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  let t := inner ℝ (g i) (η-θ)/σ
  have hc : |Real.cos t| ≤ 1 := Real.abs_cos_le_one t
  have hs : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
  have hp : |α i*β i*Real.sin t-α i*Real.cos t+β i*Real.cos t| ≤
      |α i| * |β i| + |α i| + |β i| := by
    calc
      _ ≤ |α i*β i*Real.sin t| + |α i*Real.cos t| + |β i*Real.cos t| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ _ := by
        simp only [abs_mul]
        exact add_le_add (add_le_add
          (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hs)
          (mul_le_of_le_one_right (abs_nonneg _) hc))
          (mul_le_of_le_one_right (abs_nonneg _) hc)
  calc
    _ ≤ |δ i*β i*Real.cos t| + |(inner ℝ (g i) v/σ)*
        (α i*β i*Real.sin t-α i*Real.cos t+β i*Real.cos t)| := abs_add_le _ _
    _ = |δ i| * |β i| * |Real.cos t| + |inner ℝ (g i) v|/σ*
        |α i*β i*Real.sin t-α i*Real.cos t+β i*Real.cos t| := by
      simp only [abs_mul, abs_div, abs_of_pos hσ]
    _ ≤ _ := add_le_add
      (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hc)
      (mul_le_mul_of_nonneg_left hp (div_nonneg (abs_nonneg _) hσ.le))

lemma cancellation (g : ι → E) (q ε σ k : ℝ) (θ η v : E) (h : ι → ℝ)
    (hq : q ≠ 0) (hσ : σ ≠ 0) (hk : k = q^2/(Fintype.card ι : ℝ))
    (hε : ε ≠ 0) :
    differential g q ε σ θ η v 0 0
      (fun i => k/ε*(h i-inner ℝ (g i) v/q)) =
    k/σ*(∑ i, h i*Real.sin (inner ℝ (g i) (η-θ)/σ)) +
    q/σ*inner ℝ
      (Real.exp (-‖(σ⁻¹:ℝ) • (η-θ)‖^2/2) • ((σ⁻¹:ℝ) • (η-θ)) -
       ((Fintype.card ι : ℝ)⁻¹) • ∑ i, Real.sin (inner ℝ (g i) (η-θ)/σ) • g i) v +
    ε/σ^2*(∑ i, inner ℝ (g i) v*Real.sin (inner ℝ (g i) (η-θ)/σ)) := by
  have hn : ‖(σ⁻¹:ℝ) • (η-θ)‖^2 = ‖η-θ‖^2/σ^2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow]; ring
  simp only [differential, Pi.zero_apply, mul_zero, zero_mul, add_zero, sub_zero,
    zero_add, one_mul, inner_sub_left, real_inner_smul_left, sum_inner, hn]
  have he : - (‖η-θ‖^2/σ^2)/2 = -‖η-θ‖^2/(2*σ^2) := by ring
  rw [he]
  simp only [Finset.mul_sum]
  have hterm (i : ι) : ε/σ * (k/ε*(h i-inner ℝ (g i) v/q)*Real.sin (inner ℝ (g i) (η-θ)/σ) +
      (inner ℝ (g i) v/σ)*Real.sin (inner ℝ (g i) (η-θ)/σ)) =
      k/σ*(h i*Real.sin (inner ℝ (g i) (η-θ)/σ)) -
      q/σ*((Fintype.card ι : ℝ)⁻¹)*(Real.sin (inner ℝ (g i) (η-θ)/σ)*inner ℝ (g i) v) +
      ε/σ^2*(inner ℝ (g i) v*Real.sin (inner ℝ (g i) (η-θ)/σ)) := by
    rw [hk]
    field_simp

  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end UniformSparsestCut.Profile

namespace UniformSparsestCut.Profile
variable {E : Type u3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {S : Type u4} {N : Type u5} [Fintype S] [DecidableEq S] [Fintype N]

lemma active_cancellation (g : S → N → E) (s : S) (q ε σ k : ℝ)
    (θ η v : E) (h : N → ℝ) (hq : q ≠ 0) (hσ : σ ≠ 0)
    (hk : k = q^2/(Fintype.card N : ℝ)) (hε : ε ≠ 0) :
    differential (fun j : S × N => g j.1 j.2) q ε σ θ η v 0 0
      (fun j => if j.1 = s then k/ε*(h j.2-inner ℝ (g j.1 j.2) v/q) else 0) =
    k/σ*(∑ i, h i*Real.sin (inner ℝ (g s i) (η-θ)/σ)) +
    q/σ*inner ℝ
      (Real.exp (-‖(σ⁻¹:ℝ) • (η-θ)‖^2/2) • ((σ⁻¹:ℝ) • (η-θ)) -
       ((Fintype.card N : ℝ)⁻¹) • ∑ i, Real.sin (inner ℝ (g s i) (η-θ)/σ) • g s i) v +
    ε/σ^2*(∑ j : S × N, inner ℝ (g j.1 j.2) v*Real.sin (inner ℝ (g j.1 j.2) (η-θ)/σ)) := by
  have hn : ‖(σ⁻¹:ℝ) • (η-θ)‖^2 = ‖η-θ‖^2/σ^2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow]; ring
  have he : -(‖η-θ‖^2/σ^2)/2 = -‖η-θ‖^2/(2*σ^2) := by ring
  simp only [differential, Pi.zero_apply, mul_zero, zero_mul, add_zero,
    sub_zero, zero_add, one_mul, Finset.sum_add_distrib]
  have hd : (∑ j : S × N, (if j.1 = s then k/ε*(h j.2-inner ℝ (g j.1 j.2) v/q) else 0) *
      Real.sin (inner ℝ (g j.1 j.2) (η-θ)/σ)) =
      k/ε*∑ i, (h i-inner ℝ (g s i) v/q)*Real.sin (inner ℝ (g s i) (η-θ)/σ) := by
    simp only [Fintype.sum_prod_type, ite_mul, zero_mul]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  rw [hd]
  simp only [inner_sub_left, real_inner_smul_left, sum_inner, hn, he]
  simp only [sub_mul, Finset.sum_sub_distrib, div_mul_eq_mul_div,
    ← Finset.sum_div]
  have hs : (∑ i, Real.sin (inner ℝ (g s i) (η-θ)/σ)*inner ℝ (g s i) v) =
      ∑ i, inner ℝ (g s i) v*Real.sin (inner ℝ (g s i) (η-θ)/σ) := by
    apply Finset.sum_congr rfl; intros; ring
  rw [hs, hk]
  field_simp
  ring

lemma active_bound (g : S → N → E) (s : S) {q ε σ k γ G : ℝ}
    (θ η v : E) (h : N → ℝ) (hq : 0 < q) (hε : 0 < ε) (hσ : 0 < σ)
    (hk : k = q^2/(Fintype.card N : ℝ)) (hg : ∀ s i, ‖g s i‖ ≤ G)
    (hf : ‖Real.exp (-‖(σ⁻¹:ℝ) • (η-θ)‖^2/2) • ((σ⁻¹:ℝ) • (η-θ)) -
       ((Fintype.card N : ℝ)⁻¹) • ∑ i, Real.sin (inner ℝ (g s i) (η-θ)/σ) • g s i‖ ≤ γ) :
    |differential (fun j : S × N => g j.1 j.2) q ε σ θ η v 0 0
      (fun j => if j.1 = s then k/ε*(h j.2-inner ℝ (g j.1 j.2) v/q) else 0)| ≤
      k/σ*(∑ i, |h i|) + q*γ/σ*‖v‖ +
        ε/σ^2*((Fintype.card S : ℝ)*(Fintype.card N : ℝ)*G)*‖v‖ := by
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  rw [active_cancellation g s q ε σ k θ η v h hq.ne' hσ.ne' hk hε.ne']
  have hsum : |∑ i, h i*Real.sin (inner ℝ (g s i) (η-θ)/σ)| ≤ ∑ i, |h i| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  have hfour := (abs_real_inner_le_norm _ v).trans (mul_le_mul_of_nonneg_right hf (norm_nonneg v))
  have hglobal : |∑ j : S × N, inner ℝ (g j.1 j.2) v*Real.sin (inner ℝ (g j.1 j.2) (η-θ)/σ)| ≤
      (Fintype.card S : ℝ)*(Fintype.card N : ℝ)*G*‖v‖ := by
    calc
      _ ≤ ∑ j : S × N, |inner ℝ (g j.1 j.2) v*Real.sin (inner ℝ (g j.1 j.2) (η-θ)/σ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : S × N, G*‖v‖ := by
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul]
        exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)).trans
          ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hg j.1 j.2) (norm_nonneg v)))
      _ = _ := by simp [Fintype.card_prod]; ring
  calc
    _ ≤ |k/σ*(∑ i, h i*Real.sin (inner ℝ (g s i) (η-θ)/σ))| +
        |q/σ*inner ℝ (Real.exp (-‖(σ⁻¹:ℝ) • (η-θ)‖^2/2) • ((σ⁻¹:ℝ) • (η-θ)) -
       ((Fintype.card N : ℝ)⁻¹) • ∑ i, Real.sin (inner ℝ (g s i) (η-θ)/σ) • g s i) v| +
       |ε/σ^2*(∑ j : S × N, inner ℝ (g j.1 j.2) v*Real.sin (inner ℝ (g j.1 j.2) (η-θ)/σ))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ k/σ*(∑ i, |h i|) + q/σ*(γ*‖v‖) +
        ε/σ^2*((Fintype.card S : ℝ)*(Fintype.card N : ℝ)*G*‖v‖) := by
      simp only [abs_mul, abs_of_nonneg (div_nonneg hk0 hσ.le),
        abs_of_pos (div_pos hq hσ), abs_of_pos (div_pos hε (sq_pos_of_pos hσ))]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hsum (div_nonneg hk0 hσ.le))
        (mul_le_mul_of_nonneg_left hfour (div_nonneg hq.le hσ.le)))
        (mul_le_mul_of_nonneg_left hglobal (div_nonneg hε.le (sq_nonneg σ)))
    _ = _ := by ring

end UniformSparsestCut.Profile

namespace UniformSparsestCut.Profile
variable {E : Type u6} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type u7} [Fintype ι]

def kernel (g : ι → E) (q ε a b : ℝ) (θ η : E) (α β : ι → ℝ) : ℝ :=
  ∫ σ in a..b, pairing g q ε σ θ η α β

lemma pairing_continuousOn (g : ι → E) (q ε : ℝ) (θ η : E) (α β : ι → ℝ)
    {a b : ℝ} (ha : 0 < a) : ContinuousOn (fun σ => pairing g q ε σ θ η α β) (Icc a b) := by
  have hn : ∀ σ ∈ Icc a b, σ ≠ 0 := fun σ h => (ha.trans_le h.1).ne'
  have hnp : ∀ σ ∈ Icc a b, 2*σ^2 ≠ 0 := fun σ h => mul_ne_zero (by norm_num) (pow_ne_zero _ (hn σ h))
  unfold pairing
  refine (continuousOn_const.mul (Real.continuous_exp.comp_continuousOn
    (continuousOn_const.div (by fun_prop) hnp))).add ?_
  apply (continuousOn_const.div continuousOn_id hn).mul
  apply continuousOn_finsetSum
  intro i _
  have hc := continuousOn_const.div continuousOn_id hn (f := fun _ : ℝ => inner ℝ (g i) (η-θ))
  exact (continuousOn_const.mul (Real.continuous_cos.comp_continuousOn hc)).add
    (continuousOn_const.mul (Real.continuous_sin.comp_continuousOn hc))

lemma pairing_integrable (g : ι → E) (q ε : ℝ) (θ η : E) (α β : ι → ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun σ => pairing g q ε σ θ η α β) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact pairing_continuousOn g q ε θ η α β ha

lemma pairing_correction (g : ι → E) {q ε σ : ℝ} (hε : 0 ≤ ε) (hσ : 0 < σ)
    (θ η : E) (α β : ι → ℝ) :
    |pairing g q ε σ θ η α β - pairing g q ε σ θ η 0 0| ≤
      ε/σ*∑ i, (|α i| * |β i|+|α i|+|β i|) := by
  have he : pairing g q ε σ θ η α β - pairing g q ε σ θ η 0 0 =
      ε/σ*∑ i, (α i*β i*Real.cos (inner ℝ (g i) (η-θ)/σ) +
        α i*Real.sin (inner ℝ (g i) (η-θ)/σ)-β i*Real.sin (inner ℝ (g i) (η-θ)/σ)) := by
    unfold pairing
    simp only [Pi.zero_apply, mul_zero, add_zero, zero_mul, sub_zero, one_mul]
    rw [show ∀ c d e : ℝ, (c+d)-(c+e)=d-e by intros; ring, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1; apply Finset.sum_congr rfl; intro i _; ring
  rw [he, abs_mul, abs_of_nonneg (div_nonneg hε hσ.le)]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hε hσ.le)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  calc
    _ ≤ |α i*β i*Real.cos (inner ℝ (g i) (η-θ)/σ)| +
        |α i*Real.sin (inner ℝ (g i) (η-θ)/σ)|+|β i*Real.sin (inner ℝ (g i) (η-θ)/σ)| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [abs_mul]
      exact add_le_add (add_le_add
        (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.abs_cos_le_one _))
        (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)))
        (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))

lemma kernel_correction (g : ι → E) {q ε a b A : ℝ}
    (hε : 0 ≤ ε) (ha : 0 < a) (hab : a ≤ b) (hA : 0 ≤ A)
    (θ η : E) (α β : ι → ℝ) (hα : ∀ i, |α i| ≤ A) (hβ : ∀ i, |β i| ≤ A) :
    |kernel g q ε a b θ η α β - kernel g q ε a b θ η 0 0| ≤
      ε*(Fintype.card ι : ℝ)*(A^2+2*A)*Real.log (b/a) := by
  have hip := pairing_integrable g q ε θ η α β ha hab
  have hiz := pairing_integrable g q ε θ η 0 0 ha hab
  have hiinv : IntervalIntegrable (fun σ : ℝ => σ⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact continuousOn_id.inv₀ (fun σ h => (ha.trans_le h.1).ne')
  have hi := hiinv.const_mul (ε*(Fintype.card ι : ℝ)*(A^2+2*A))
  unfold kernel
  rw [← intervalIntegral.integral_sub hip hiz]
  calc
    _ ≤ ∫ σ in a..b, |pairing g q ε σ θ η α β-pairing g q ε σ θ η 0 0| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ σ in a..b, ε*(Fintype.card ι : ℝ)*(A^2+2*A)*σ⁻¹ := by
      apply intervalIntegral.integral_mono_on hab (hip.sub hiz).abs hi
      intro σ hσ
      have hp := ha.trans_le hσ.1
      have hs : (∑ i, (|α i| * |β i|+|α i|+|β i|)) ≤ (Fintype.card ι : ℝ)*(A^2+2*A) := by
        calc
          _ ≤ ∑ _i : ι, (A^2+2*A) := by
            apply Finset.sum_le_sum; intro i _
            have hm := mul_le_mul (hα i) (hβ i) (abs_nonneg _) hA
            nlinarith [hα i, hβ i]
          _ = _ := by simp; ring
      calc
        _ ≤ ε/σ*∑ i, (|α i| * |β i|+|α i|+|β i|) := pairing_correction g hε hp θ η α β
        _ ≤ ε/σ*((Fintype.card ι : ℝ)*(A^2+2*A)) := mul_le_mul_of_nonneg_left hs (div_nonneg hε hp.le)
        _ = _ := by ring
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha (ha.trans_le hab)]

lemma integral_inv_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ σ in a..b, (σ^2)⁻¹) = a⁻¹-b⁻¹ := by
  have hd (σ : ℝ) (hσ : σ ∈ Icc a b) : HasDerivAt (fun σ : ℝ => -σ⁻¹) ((σ^2)⁻¹) σ := by
    convert ((hasDerivAt_id σ).inv (ha.trans_le hσ.1).ne').neg using 1 <;> try rfl
    simp; ring
  have hi : IntervalIntegrable (fun σ : ℝ => (σ^2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact (continuousOn_id.pow 2).inv₀ (fun σ h => pow_ne_zero _ (ha.trans_le h.1).ne')
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun σ hσ => hd σ (by simpa only [uIcc_of_le hab] using hσ)) hi
  convert h using 1 ; ring

lemma kernel_segment_bound (g : ι → E) {q ε a b C D : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hD : 0 ≤ D) (θ η v : E) (α β δ : ι → ℝ)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ σ ∈ Icc a b,
      |differential g q ε σ (θ+t • v) η v (fun i => α i+t*δ i) β δ| ≤ C/σ+D/σ^2) :
    |kernel g q ε a b (θ+v) η (fun i => α i+δ i) β-kernel g q ε a b θ η α β| ≤
      C*Real.log (b/a)+D/a := by
  have hip := pairing_integrable g q ε (θ+v) η (fun i => α i+δ i) β ha hab
  have hiz := pairing_integrable g q ε θ η α β ha hab
  have hii : IntervalIntegrable (fun σ : ℝ => σ⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact continuousOn_id.inv₀ (fun σ h => (ha.trans_le h.1).ne')
  have hiis : IntervalIntegrable (fun σ : ℝ => (σ^2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact (continuousOn_id.pow 2).inv₀ (fun σ h => pow_ne_zero _ (ha.trans_le h.1).ne')
  have hi := (hii.const_mul C).add (hiis.const_mul D)
  have hbound (σ : ℝ) (hσ : σ ∈ Icc a b) :
      |pairing g q ε σ (θ+v) η (fun i => α i+δ i) β-pairing g q ε σ θ η α β| ≤ C/σ+D/σ^2 := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun t ht => (pairing_hasDeriv g q ε σ θ η v α β δ t).hasDerivWithinAt)
      (fun t ht => by simpa only [Real.norm_eq_abs] using hd t ⟨ht.1, ht.2.le⟩ σ hσ)
    simpa only [one_smul, one_mul, zero_smul, add_zero, zero_mul, Real.norm_eq_abs] using h
  unfold kernel
  rw [← intervalIntegral.integral_sub hip hiz]
  calc
    _ ≤ ∫ σ in a..b, |pairing g q ε σ (θ+v) η (fun i => α i+δ i) β-pairing g q ε σ θ η α β| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ σ in a..b, C*σ⁻¹+D*(σ^2)⁻¹ := by
      apply intervalIntegral.integral_mono_on hab (hip.sub hiz).abs hi
      intro σ hσ; simpa only [div_eq_mul_inv] using hbound σ hσ
    _ = C*Real.log (b/a)+D*(a⁻¹-b⁻¹) := by
      rw [intervalIntegral.integral_add (hii.const_mul C) (hiis.const_mul D),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_inv_of_pos ha (ha.trans_le hab), integral_inv_sq ha hab]
    _ ≤ _ := by
      simp only [div_eq_mul_inv]
      have := mul_nonneg hD (inv_nonneg.mpr (ha.trans_le hab).le)
      nlinarith

end UniformSparsestCut.Profile

end

end OAI
