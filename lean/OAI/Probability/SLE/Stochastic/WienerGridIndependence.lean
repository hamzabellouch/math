import OAI.Probability.SLE.Stochastic.WienerGrid

namespace OAI

/-! The Brownian interpolation residual is independent of the finite
grid. Only covariances of the three evaluations in each residual enter. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma brownian_affine_residual_covariance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (a b t s : ℝ≥0) (c : ℝ) (hat : a ≤ t) (htb : t ≤ b)
    (hs : s ≤ a ∨ b ≤ s) (hc : (1-c)*(a:ℝ)+c*(b:ℝ)=t) :
    cov[B s,fun ω => B t ω-((1-c)*B a ω+c*B b ω);P]=0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm u := (hB.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
  have hz : MemLp (fun ω => (1-c)*B a ω+c*B b ω) 2 P :=
    ((hm a).const_mul (1-c)).add ((hm b).const_mul c)
  have hadd : cov[B s,fun ω => (1-c)*B a ω+c*B b ω;P] =
      cov[B s,fun ω => (1-c)*B a ω;P]+cov[B s,fun ω => c*B b ω;P] :=
    covariance_add_right (hm s) ((hm a).const_mul (1-c)) ((hm b).const_mul c)
  rw [covariance_fun_sub_right (hm s) (hm t) hz,
    hadd,
    covariance_const_mul_right,covariance_const_mul_right,
    hB.covariance_eval,hB.covariance_eval,hB.covariance_eval]
  rcases hs with hs | hs
  · rw [min_eq_left (hs.trans hat),min_eq_left hs,min_eq_left (hs.trans (hat.trans htb))]
    ring
  · rw [min_eq_right (htb.trans hs),min_eq_right ((hat.trans htb).trans hs),min_eq_right hs]
    linarith

def wienerGridResidual {Ω : Type*} (n : ℕ) (B : ℝ≥0 → Ω → ℝ)
    (t : unitInterval) (ω : Ω) : ℝ :=
  B ⟨t,t.2.1⟩ ω-wienerGridInterp n (fun s => B s ω) t

lemma wienerGrid_joint_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (n : ℕ) :
    IsGaussianProcess (Sum.elim (fun i : Fin (n+3) => B (wienerGridTime n i))
      (wienerGridResidual n B)) P := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  rintro (i | t)
  · exact ⟨{wienerGridTime n i},
      { toFun := fun x => x ⟨wienerGridTime n i,by simp⟩
        map_add' := by simp
        map_smul' := by simp },by simp⟩
  · let a := wienerGridTime n (wienerGridCell n t)
    let b := wienerGridTime n (wienerGridCell n t+1)
    let u : ℝ≥0 := ⟨t,t.2.1⟩
    let c := wienerGridWeight n t
    refine ⟨{u,a,b},
      { toFun := fun x => x ⟨u,by simp⟩-
          ((1-c)*x ⟨a,by simp⟩+c*x ⟨b,by simp⟩)
        map_add' := ?_
        map_smul' := ?_ },?_⟩
    · intro x y
      simp only [Pi.add_apply]
      ring
    · intro d x
      simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
      ring
    · intro ω
      rfl

lemma wienerGrid_residual_covariance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (n : ℕ)
    (i : Fin (n+3)) (t : unitInterval) :
    cov[B (wienerGridTime n i),wienerGridResidual n B t;P]=0 := by
  have hb := wienerGrid_bracket n t
  have hs : wienerGridTime n i ≤ wienerGridTime n (wienerGridCell n t) ∨
      wienerGridTime n (wienerGridCell n t+1) ≤ wienerGridTime n i := by
    by_cases h : (i:ℕ) ≤ wienerGridCell n t
    · exact Or.inl (wienerGridTime_mono n h)
    · exact Or.inr (wienerGridTime_mono n (by omega))
  exact brownian_affine_residual_covariance hB _ _ _ _ _ hb.1 hb.2 hs
    (wienerGrid_affine n t)

lemma wienerGrid_residual_independent
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (n : ℕ) :
    IndepFun (fun ω (i : Fin (n+3)) => B (wienerGridTime n i) ω)
      (fun ω t => wienerGridResidual n B t ω) P := by
  apply (wienerGrid_joint_gaussian hB n).indepFun_of_covariance_eq_zero
  · intro i
    exact hB.aemeasurable _
  · intro t
    exact (hB.aemeasurable _).sub
      (((hB.aemeasurable _).const_mul _).add ((hB.aemeasurable _).const_mul _))
  · exact wienerGrid_residual_covariance hB n

end SLEExactGauge

end

end OAI
