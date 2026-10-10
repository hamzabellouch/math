import OAI.MathematicalPhysics.Heisenberg.StateCompactness

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators
open Filter Topology Metric
open scoped NNReal
open scoped NNReal

open scoped ComplexConjugate Topology
namespace GibbsStrip
variable {E : Type*} [CStarAlgebra E]

local instance : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℂ E

def evolve (K : E) (z : ℂ) (A : E) : E :=
  NormedSpace.exp ((Complex.I*z) • K) * A * NormedSpace.exp ((-(Complex.I*z)) • K)

lemma exp_scalar_add (K : E) (z w : ℂ) :
    NormedSpace.exp ((z+w) • K) = NormedSpace.exp (z • K) * NormedSpace.exp (w • K) := by
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute ((Commute.refl K).smul_left z |>.smul_right w)

lemma evolve_add (K : E) (z w : ℂ) (A : E) :
    evolve K (z+w) A = evolve K z (evolve K w A) := by
  unfold evolve
  rw [mul_add,exp_scalar_add]
  have he : -(Complex.I*z+Complex.I*w) = -(Complex.I*w) + -(Complex.I*z) := by ring
  rw [he,exp_scalar_add]
  simp only [mul_assoc]

lemma evolve_differentiable (K A : E) : Differentiable ℂ (fun z => evolve K z A) := by
  have h (c : ℂ) : Differentiable ℂ (fun z : ℂ => NormedSpace.exp ((c*z) • K)) := by
    have hh : Differentiable ℂ (fun z : ℂ => NormedSpace.exp (z • K)) :=
      fun z => (hasDerivAt_exp_smul_const K z).differentiableAt
    exact hh.comp ((differentiable_const c).mul differentiable_id)
  unfold evolve
  have hh := ((h Complex.I).mul_const A).mul (h (-Complex.I))
  change Differentiable ℂ (fun z => NormedSpace.exp ((Complex.I*z) • K) * A *
    NormedSpace.exp (((-Complex.I)*z) • K)) at hh
  simpa only [neg_mul] using hh

lemma real_evolve_norm {K : E} (hK : IsSelfAdjoint K) (t : ℝ) (A : E) :
    ‖evolve K (t : ℂ) A‖ = ‖A‖ := by
  have h (t : ℝ) : NormedSpace.exp ((Complex.I*(t:ℂ)) • K) ∈ unitary E := by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    apply IsSelfAdjoint.smul_mem_skewAdjoint _ hK
    change star (Complex.I*(t:ℂ)) = -(Complex.I*(t:ℂ))
    simp
  have hn : NormedSpace.exp ((-(Complex.I*(t:ℂ))) • K) ∈ unitary E := by
    convert h (-t) using 1; simp
  rw [evolve,CStarRing.norm_mul_mem_unitary _ hn,CStarRing.norm_mem_unitary_mul _ (h t)]

lemma imaginary_evolve (K : E) (β : ℝ) (A : E) :
    evolve K (Complex.I * β) A =
      NormedSpace.exp ((-β : ℂ) • K) * A * NormedSpace.exp ((β : ℂ) • K) := by
  simp [evolve,← mul_assoc]

lemma exp_cancel_left (K : E) (z : ℂ) :
    NormedSpace.exp (z • K) * NormedSpace.exp ((-z) • K) = 1 := by
  rw [← exp_scalar_add]
  simp

lemma exp_cancel_right (K : E) (z : ℂ) :
    NormedSpace.exp ((-z) • K) * NormedSpace.exp (z • K) = 1 := by
  rw [← exp_scalar_add]
  simp

lemma gibbs_upper_boundary (τ : E →L[ℂ] ℂ)
    (hτ : ∀ A B, τ (A*B) = τ (B*A)) (K : E) (β t : ℝ) (c : ℂ) (A B : E) :
    c * τ (NormedSpace.exp ((-β : ℂ) • K) * (A * evolve K ((t:ℂ)+Complex.I*β) B)) =
      c * τ (NormedSpace.exp ((-β : ℂ) • K) * (evolve K (t:ℂ) B * A)) := by
  rw [add_comm (t:ℂ),evolve_add,imaginary_evolve]
  congr 1
  let D := NormedSpace.exp ((-β : ℂ) • K)
  let D' := NormedSpace.exp ((β : ℂ) • K)
  let X := evolve K (t:ℂ) B
  change τ (D*(A*(D*X*D'))) = τ (D*(X*A))
  calc
    _ = τ ((D*(A*(D*X)))*D') := by simp only [mul_assoc]
    _ = τ (D'*(D*(A*(D*X)))) := hτ _ _
    _ = τ (A*(D*X)) := by
      rw [← mul_assoc D' D,show D'*D = 1 from exp_cancel_left K (β:ℂ),one_mul]
    _ = τ ((D*X)*A) := hτ _ _
    _ = _ := by rw [mul_assoc]

lemma strip_evolve_bounded {K : E} (hK : IsSelfAdjoint K) (A : E) (β : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, 0 ≤ z.im → z.im ≤ β → ‖evolve K z A‖ ≤ M := by
  have hc : Continuous (fun u : ℝ => ‖evolve K (Complex.I*(u:ℂ)) A‖) :=
    ((evolve_differentiable K A).continuous.comp
      (continuous_const.mul Complex.continuous_ofReal)).norm
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image (hc.continuousOn (s:=Set.Icc 0 β))
  refine ⟨max M 0,le_max_right _ _,fun z hz0 hzβ => ?_⟩
  have hz : z = (z.re:ℂ)+Complex.I*(z.im:ℂ) := by
    apply Complex.ext <;> simp
  rw [hz,evolve_add,real_evolve_norm hK]
  exact (hM ⟨z.im,⟨hz0,hzβ⟩,rfl⟩).trans (le_max_left _ _)

end GibbsStrip

open Set Filter Complex
open scoped Topology

namespace HeisenbergStrip

def openStrip (β : ℝ) : Set ℂ := Complex.im ⁻¹' Ioo 0 β
def closedStrip (β : ℝ) : Set ℂ := Complex.im ⁻¹' Icc 0 β

theorem closure_openStrip {β : ℝ} (hβ : 0 < β) :
    closure (openStrip β) = closedStrip β := by
  simp only [openStrip, closedStrip, Complex.closure_preimage_im, closure_Ioo hβ.ne]

theorem isOpen_openStrip (β : ℝ) : IsOpen (openStrip β) :=
  isOpen_Ioo.preimage Complex.continuous_im

theorem bounded_strip_max {β C : ℝ} (hβ : 0 < β) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (openStrip β))
    (hbounded : ∃ M : ℝ, ∀ z ∈ closedStrip β, ‖f z‖ ≤ M)
    (hzero : ∀ z : ℂ, z.im = 0 → ‖f z‖ ≤ C)
    (htop : ∀ z : ℂ, z.im = β → ‖f z‖ ≤ C)
    {z : ℂ} (hz : z ∈ closedStrip β) : ‖f z‖ ≤ C := by
  apply PhragmenLindelof.horizontal_strip hf ?_ hzero htop hz.1 hz.2
  refine ⟨0, by simpa using div_pos Real.pi_pos hβ, 0, ?_⟩
  obtain ⟨M, hM⟩ := hbounded
  apply Asymptotics.IsBigO.of_bound M
  simp only [Filter.eventually_inf_principal]
  exact Filter.Eventually.of_forall (fun w hw => by
    simpa using hM w ⟨hw.1.le, hw.2.le⟩)

def gaussian (z : ℂ) : ℂ := Complex.exp (-(z * z))

theorem gaussian_differentiable : Differentiable ℂ gaussian :=
  Complex.differentiable_exp.comp (differentiable_id.mul differentiable_id).neg

theorem norm_gaussian (z : ℂ) : ‖gaussian z‖ = Real.exp (-z.re ^ 2 + z.im ^ 2) := by
  rw [gaussian, Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.mul_re]
  ring

theorem norm_gaussian_le {β : ℝ} {z : ℂ} (hz : z ∈ closedStrip β) :
    ‖gaussian z‖ ≤ Real.exp (β ^ 2) := by
  rw [norm_gaussian]
  apply Real.exp_le_exp.mpr
  have := sq_le_sq₀ hz.1 (hz.1.trans hz.2)
  nlinarith [sq_nonneg z.re, this.mpr hz.2]

theorem norm_gaussian_tail {β R : ℝ} (hR : 0 ≤ R) {z : ℂ}
    (hz : z ∈ closedStrip β) (hreal : R ≤ |z.re|) :
    ‖gaussian z‖ ≤ Real.exp (-(R ^ 2) + β ^ 2) := by
  rw [norm_gaussian]
  apply Real.exp_le_exp.mpr
  have hi := (sq_le_sq₀ hz.1 (hz.1.trans hz.2)).mpr hz.2
  have hr := (sq_le_sq₀ hR (abs_nonneg z.re)).mpr hreal
  rw [sq_abs] at hr
  linarith

def BoundaryCauchy (β : ℝ) (F : ℕ → ℂ → ℂ) : Prop :=
  ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ z : ℂ,
      (z.im = 0 ∨ z.im = β) → |z.re| ≤ R → ‖F m z - F n z‖ < ε

theorem boundary_mem_closedStrip {β : ℝ} (hβ : 0 ≤ β) {z : ℂ}
    (hz : z.im = 0 ∨ z.im = β) : z ∈ closedStrip β := by
  rcases hz with hz | hz <;> exact ⟨by linarith, by linarith⟩

theorem gaussian_uniformCauchy {β C : ℝ} (hβ : 0 < β) (_hC : 0 ≤ C)
    {F : ℕ → ℂ → ℂ} (hd : ∀ n, DiffContOnCl ℂ (F n) (openStrip β))
    (hbound : ∀ n z, z ∈ closedStrip β → ‖F n z‖ ≤ C)
    (hcauchy : BoundaryCauchy β F) :
    UniformCauchySeqOn (fun n z => gaussian z * F n z) atTop (closedStrip β) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have ht : Tendsto (fun R : ℝ => Real.exp (-(R ^ 2) + β ^ 2) * (2 * C))
      atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))).mul_const
        (Real.exp (β ^ 2))
    simpa only [Real.exp_add, zero_mul, mul_assoc, Function.comp_apply] using h.mul_const (2 * C)
  obtain ⟨R, hR, htail⟩ := ((Filter.eventually_ge_atTop (1 : ℝ)).and
    (ht.eventually_lt_const (by linarith : 0 < ε / 2))).exists
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have he : 0 < Real.exp (β ^ 2) := Real.exp_pos _
  obtain ⟨N, hN⟩ := hcauchy R hRpos (ε / (2 * Real.exp (β ^ 2)))
    (div_pos hε (mul_pos (by norm_num) he))
  refine ⟨N, ?_⟩
  intro m hm n hn z hz
  have hdiff (w : ℂ) (hw : w ∈ closedStrip β) : ‖F m w - F n w‖ ≤ 2 * C :=
    (norm_sub_le _ _).trans (by linarith [hbound m w hw, hbound n w hw])
  have hboundDiff : ∃ M : ℝ, ∀ w ∈ closedStrip β,
      ‖gaussian w * F m w - gaussian w * F n w‖ ≤ M := by
    refine ⟨Real.exp (β ^ 2) * (2 * C), ?_⟩
    intro w hw
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (norm_gaussian_le hw) (hdiff w hw) (norm_nonneg _) he.le
  have hedge (w : ℂ) (hw : w.im = 0 ∨ w.im = β) :
      ‖gaussian w * F m w - gaussian w * F n w‖ ≤ ε / 2 := by
    have hwS := boundary_mem_closedStrip hβ.le hw
    rw [← mul_sub, norm_mul]
    by_cases hwr : |w.re| ≤ R
    · apply le_of_lt
      calc
        ‖gaussian w‖ * ‖F m w - F n w‖ ≤
            Real.exp (β ^ 2) * ‖F m w - F n w‖ :=
          mul_le_mul_of_nonneg_right (norm_gaussian_le hwS) (norm_nonneg _)
        _ < Real.exp (β ^ 2) * (ε / (2 * Real.exp (β ^ 2))) :=
          mul_lt_mul_of_pos_left (hN m hm n hn w hw hwr) he
        _ = ε / 2 := by field_simp
    · exact (mul_le_mul (norm_gaussian_tail hRpos.le hwS (not_le.mp hwr).le)
        (hdiff w hwS) (norm_nonneg _) (Real.exp_pos _).le).trans htail.le
  have hmax := bounded_strip_max hβ
    ((gaussian_differentiable.diffContOnCl.smul (hd m)).sub
      (gaussian_differentiable.diffContOnCl.smul (hd n))) hboundDiff
    (fun w hw => hedge w (Or.inl hw)) (fun w hw => hedge w (Or.inr hw)) hz
  rw [dist_eq_norm]
  exact hmax.trans_lt (by linarith)

theorem strip_limit_of_boundaryCauchy {β C : ℝ} (hβ : 0 < β) (hC : 0 ≤ C)
    {F : ℕ → ℂ → ℂ} (hd : ∀ n, DiffContOnCl ℂ (F n) (openStrip β))
    (hbound : ∀ n z, z ∈ closedStrip β → ‖F n z‖ ≤ C)
    (hcauchy : BoundaryCauchy β F) :
    ∃ f : ℂ → ℂ, TendstoLocallyUniformlyOn F f atTop (closedStrip β) ∧
      DiffContOnCl ℂ f (openStrip β) ∧ ∀ z ∈ closedStrip β, ‖f z‖ ≤ C := by
  classical
  have hgC := gaussian_uniformCauchy hβ hC hd hbound hcauchy
  have hex (z : ℂ) : ∃ w : ℂ, z ∈ closedStrip β →
      Tendsto (fun n => gaussian z * F n z) atTop (𝓝 w) := by
    by_cases hz : z ∈ closedStrip β
    · obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete (hgC.cauchySeq hz)
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => (hz h).elim⟩
  choose g hg using hex
  have hgu : TendstoUniformlyOn (fun n z => gaussian z * F n z) g atTop
      (closedStrip β) := hgC.tendstoUniformlyOn_of_tendsto hg
  have hgc : ContinuousOn g (closedStrip β) := by
    apply hgu.continuousOn
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro n
    exact gaussian_differentiable.continuous.continuousOn.mul
      (by simpa only [closure_openStrip hβ] using (hd n).continuousOn)
  let inverseGaussian : ℂ → ℂ := fun z => Complex.exp (z * z)
  have hic : Continuous inverseGaussian :=
    Complex.continuous_exp.comp (continuous_id.mul continuous_id)
  have hiu : TendstoUniformlyOn (fun _ : ℕ => inverseGaussian)
      inverseGaussian atTop (closedStrip β) := by
    rw [Metric.tendstoUniformlyOn_iff]
    exact fun ε hε => Filter.Eventually.of_forall (fun _ _ _ => by simpa)
  have hloc := hiu.tendstoLocallyUniformlyOn.mul₀ hgu.tendstoLocallyUniformlyOn
    hic.continuousOn hgc
  have hFi (n : ℕ) (z : ℂ) :
      inverseGaussian z * (gaussian z * F n z) = F n z := by
    dsimp only [inverseGaussian, gaussian]
    rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  have hlocF : TendstoLocallyUniformlyOn F (fun z => inverseGaussian z * g z)
      atTop (closedStrip β) := hloc.congr (fun n z _ => hFi n z)
  refine ⟨fun z => inverseGaussian z * g z, hlocF, ⟨?_, ?_⟩, ?_⟩
  · exact (hlocF.mono (fun _ hz => ⟨hz.1.le, hz.2.le⟩)).differentiableOn
      (Filter.Eventually.of_forall (fun n => (hd n).differentiableOn))
      (isOpen_openStrip β)
  · rw [closure_openStrip hβ]
    exact hic.continuousOn.mul hgc
  · intro z hz
    exact le_of_tendsto ((hlocF.tendsto_at hz).norm)
      (Filter.Eventually.of_forall (fun n => hbound n z hz))

theorem boundaryCauchy_of_locallyUniform {β : ℝ} {F : ℕ → ℂ → ℂ}
    {f₀ fβ : ℝ → ℂ}
    (h₀ : TendstoLocallyUniformly (fun n (t : ℝ) => F n (t : ℂ)) f₀ atTop)
    (hβ : TendstoLocallyUniformly (fun n (t : ℝ) => F n ((t : ℂ) + Complex.I * β))
      fβ atTop) : BoundaryCauchy β F := by
  intro R _ ε hε
  have hu₀ := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_Icc : IsCompact (Icc (-R) R))).mp h₀.tendstoLocallyUniformlyOn
  have huβ := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_Icc : IsCompact (Icc (-R) R))).mp hβ.tendstoLocallyUniformlyOn
  obtain ⟨N₀, hN₀⟩ := Metric.uniformCauchySeqOn_iff.mp hu₀.uniformCauchySeqOn ε hε
  obtain ⟨Nβ, hNβ⟩ := Metric.uniformCauchySeqOn_iff.mp huβ.uniformCauchySeqOn ε hε
  refine ⟨max N₀ Nβ, ?_⟩
  intro m hm n hn z hz hr
  have hr' : z.re ∈ Icc (-R) R := abs_le.mp hr
  rcases hz with hz | hz
  · have heq : (z.re : ℂ) = z := by
      apply Complex.ext <;> simp [hz]
    simpa only [heq, dist_eq_norm] using
      hN₀ m ((le_max_left _ _).trans hm) n ((le_max_left _ _).trans hn) z.re hr'
  · have heq : (z.re : ℂ) + Complex.I * β = z := by
      apply Complex.ext <;> simp [hz]
    simpa only [heq, dist_eq_norm] using
      hNβ m ((le_max_right _ _).trans hm) n ((le_max_right _ _).trans hn) z.re hr'

theorem bounded_strip_limit {β C : ℝ} (hβ : 0 < β) (hC : 0 ≤ C)
    {F : ℕ → ℂ → ℂ} {f₀ fβ : ℝ → ℂ}
    (hd : ∀ n, DiffContOnCl ℂ (F n) (openStrip β))
    (hbounded : ∀ n, ∃ M : ℝ, ∀ z ∈ closedStrip β, ‖F n z‖ ≤ M)
    (hzero : ∀ n (t : ℝ), ‖F n (t : ℂ)‖ ≤ C)
    (htop : ∀ n (t : ℝ), ‖F n ((t : ℂ) + Complex.I * β)‖ ≤ C)
    (hconv₀ : TendstoLocallyUniformly (fun n (t : ℝ) => F n (t : ℂ)) f₀ atTop)
    (hconvβ : TendstoLocallyUniformly
      (fun n (t : ℝ) => F n ((t : ℂ) + Complex.I * β)) fβ atTop) :
    ∃ f : ℂ → ℂ, TendstoLocallyUniformlyOn F f atTop (closedStrip β) ∧
      DiffContOnCl ℂ f (openStrip β) ∧
      (∀ z ∈ closedStrip β, ‖f z‖ ≤ C) ∧
      (∀ t : ℝ, f (t : ℂ) = f₀ t) ∧
      (∀ t : ℝ, f ((t : ℂ) + Complex.I * β) = fβ t) := by
  have hb (n : ℕ) (z : ℂ) (hz : z ∈ closedStrip β) : ‖F n z‖ ≤ C := by
    apply bounded_strip_max hβ (hd n) (hbounded n) ?_ ?_ hz
    · intro w hw
      have heq : (w.re : ℂ) = w := by apply Complex.ext <;> simp [hw]
      simpa only [heq] using hzero n w.re
    · intro w hw
      have heq : (w.re : ℂ) + Complex.I * β = w := by
        apply Complex.ext <;> simp [hw]
      simpa only [heq] using htop n w.re
  obtain ⟨f, hf, hfd, hfb⟩ := strip_limit_of_boundaryCauchy hβ hC hd hb
    (boundaryCauchy_of_locallyUniform hconv₀ hconvβ)
  refine ⟨f, hf, hfd, hfb, ?_, ?_⟩
  · intro t
    have ht : (t : ℂ) ∈ closedStrip β := by
      constructor <;> simp [hβ.le]
    exact tendsto_nhds_unique (hf.tendsto_at ht) (hconv₀.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ t))
  · intro t
    have ht : (t : ℂ) + Complex.I * β ∈ closedStrip β := by
      constructor <;> simp [hβ.le]
    exact tendsto_nhds_unique (hf.tendsto_at ht) (hconvβ.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ t))

end HeisenbergStrip
end

end OAI
