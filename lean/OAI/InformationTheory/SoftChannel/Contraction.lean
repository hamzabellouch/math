import OAI.InformationTheory.SoftChannel.Comparison

namespace OAI

section

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace LeanBlast.CourtadeKumar

def IsClosedSoft {n : ℕ} (g : Cube n → ℝ) : Prop := ∀ x, g x ∈ Icc (-1) 1

lemma closed_information_mem {n : ℕ} (g : Cube n → ℝ) (hg : IsClosedSoft g) :
    informationDeficit g ∈ Icc 0 ell := by
  constructor
  · rw [informationDeficit_eq_average_psi]
    exact sub_nonneg.mpr (convexOn_cubeAverage_le psi convexOn_psi g hg)
  · have he : 0 ≤ entropyAverage g := cubeAverage_nonneg (fun x => entropy_nonneg (hg x))
    unfold informationDeficit
    linarith [entropy_le_ell (cubeAverage g)]

lemma soft_noise_interior {n : ℕ} (g : Cube n → ℝ) (hg : IsClosedSoft g)
    (hl : ∃ x, -1 < g x) (hu : ∃ x, g x < 1)
    {ρ : ℝ} (hρ : ρ ∈ Ico 0 1) : IsInterior (noiseOperator ρ g) := by
  intro x
  constructor
  · simpa only [noiseOperator_const] using
      noiseOperator_strict_mono hρ.1 hρ.2 (fun y => (hg y).1) hl x
  · simpa only [noiseOperator_const] using
      noiseOperator_strict_mono hρ.1 hρ.2 (fun y => (hg y).2) hu x

lemma soft_flow_interior {n : ℕ} (g : Cube n → ℝ) (hg : IsClosedSoft g)
    (hl : ∃ x, -1 < g x) (hu : ∃ x, g x < 1)
    {t : ℝ} (ht : 0 < t) : IsInterior (noiseFlow g t) :=
  soft_noise_interior g hg hl hu ⟨(Real.exp_pos _).le,Real.exp_lt_one_iff.mpr (by linarith)⟩

lemma soft_model_domain {a t : ℝ} (ha : a ∈ Icc 0 1) (ht : 0 < t) :
    Real.exp (-t)*a ∈ Ioo (-1) 1 := by
  have he := Real.exp_pos (-t)
  have he1 : Real.exp (-t)<1 := Real.exp_lt_one_iff.mpr (by linarith)
  constructor
  · nlinarith [mul_nonneg he.le ha.1]
  · exact (mul_le_of_le_one_right he.le ha.2).trans_lt he1

lemma hasDerivAt_soft_model {a t : ℝ} (ha : a ∈ Icc 0 1) (ht : 0 < t) :
    HasDerivAt (fun s => psi (Real.exp (-s)*a))
      (-r (psi (Real.exp (-t)*a))) t := by
  have hd := soft_model_domain ha ht
  have h := (hasDerivAt_psi hd).comp t (((hasDerivAt_id t).neg.exp).mul_const a)
  rw [r_psi hd]
  convert! h using 1; simp only [Pi.neg_apply, id_eq]; ring

theorem all_soft_flow_contraction {n : ℕ} (g : Cube n → ℝ) (hg : IsClosedSoft g)
    (hl : ∃ x, -1 < g x) (hu : ∃ x, g x < 1)
    {t : ℝ} (ht : 0 < t) :
    informationDeficit (noiseFlow g t) ≤ psi (Real.exp (-t)*psiInv (informationDeficit g)) := by
  have hI := closed_information_mem g hg
  have ha := psiInv_mem_Icc hI
  have hderiv : ∀ s, 0 < s → psi (Real.exp (-s)*psiInv (informationDeficit g)) ≤
      informationDeficit (noiseFlow g s) →
      -dissipation (noiseFlow g s) ≤ -r (psi (Real.exp (-s)*psiInv (informationDeficit g))) := by
    intro s hs hcomp
    have hinterior := soft_flow_interior g hg hl hu hs
    have hr := monotoneOn_r
      ⟨psi_nonneg _,psi_lt_ell (soft_model_domain ha hs)⟩ hinterior.information_mem hcomp
    exact neg_le_neg (hr.trans (all_soft_sharp_production _ hinterior))
  have hf0 : Tendsto (fun s => informationDeficit (noiseFlow g s)) (𝓝[>] 0) (𝓝 (informationDeficit g)) := by
    simpa only [noiseFlow_zero] using
      ((continuous_informationDeficit_noiseFlow g).continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hmodel : Continuous (fun s : ℝ => psi (Real.exp (-s)*psiInv (informationDeficit g))) :=
    continuous_psi.comp ((Real.continuous_exp.comp continuous_neg).mul continuous_const)
  have hg0 : Tendsto (fun s : ℝ => psi (Real.exp (-s)*psiInv (informationDeficit g)))
      (𝓝[>] 0) (𝓝 (informationDeficit g)) := by
    simpa only [neg_zero,Real.exp_zero,one_mul,psi_psiInv_Icc hI] using
      (hmodel.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_deriv_le_on_above_of_tendsto
    (fun s hs => hasDerivAt_informationDeficit_noiseFlow_of_isInterior g s (soft_flow_interior g hg hl hu hs))
    (fun s hs => hasDerivAt_soft_model ha hs) hderiv hf0 hg0 t ht

theorem all_soft_nonnegative_contraction {n : ℕ} (g : Cube n → ℝ) (hg : IsClosedSoft g)
    {ρ : ℝ} (hρ : ρ ∈ Icc 0 1) :
    informationDeficit (noiseOperator ρ g) ≤ psi (ρ*psiInv (informationDeficit g)) := by
  by_cases h0 : ρ=0
  · simp [h0]
  by_cases h1 : ρ=1
  · have hnoise : noiseOperator 1 g=g := funext (noiseOperator_one g)
    rw [h1,hnoise,one_mul,psi_psiInv_Icc (closed_information_mem g hg)]
  have hr0 : 0 < ρ := lt_of_le_of_ne hρ.1 (Ne.symm h0)
  have hr1 : ρ < 1 := lt_of_le_of_ne hρ.2 h1
  by_cases hl : ∃ x, -1 < g x
  · by_cases hu : ∃ x, g x < 1
    · have ht : 0 < -Real.log ρ := neg_pos.mpr (Real.log_neg hr0 hr1)
      have h := all_soft_flow_contraction g hg hl hu ht
      simpa only [noiseFlow,neg_neg,Real.exp_log hr0] using h
    · have hc : g=fun _ => 1 := by
        funext x
        exact le_antisymm (hg x).2 (not_lt.mp (fun hx => hu ⟨x,hx⟩))
      simp only [hc,informationDeficit_noise_const,informationDeficit_const,psiInv_zero,mul_zero,psi_zero,le_refl]
  · have hc : g=fun _ => -1 := by
      funext x
      exact le_antisymm (not_lt.mp (fun hx => hl ⟨x,hx⟩)) (hg x).1
    simp only [hc,informationDeficit_noise_const,informationDeficit_const,psiInv_zero,mul_zero,psi_zero,le_refl]

def antipodeEquiv (n : ℕ) : Cube n ≃ Cube n where
  toFun x i := !(x i)
  invFun x i := !(x i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

lemma cubeAverage_antipode {n : ℕ} (g : Cube n → ℝ) :
    cubeAverage (fun x => g (antipodeEquiv n x))=cubeAverage g := by
  unfold cubeAverage
  rw [(antipodeEquiv n).sum_comp g]

lemma information_antipode {n : ℕ} (g : Cube n → ℝ) :
    informationDeficit (fun x => g (antipodeEquiv n x))=informationDeficit g := by
  simp only [informationDeficit,entropyAverage,cubeAverage_antipode]
  rw [cubeAverage_antipode (fun x => entropy (g x))]

lemma kernel_negative_correlation {n : ℕ} (ρ : ℝ) (x y : Cube n) :
    noiseKernel (-ρ) x y=noiseKernel ρ (antipodeEquiv n x) y := by
  unfold noiseKernel
  apply Finset.prod_congr rfl
  intro i _
  change (if x i=y i then _ else _)=(if (!(x i))=y i then _ else _)
  cases x i <;> cases y i <;> simp <;> ring

lemma information_negative_correlation {n : ℕ} (g : Cube n → ℝ) (ρ : ℝ) :
    informationDeficit (noiseOperator (-ρ) g)=informationDeficit (noiseOperator ρ g) := by
  have he : noiseOperator (-ρ) g=fun x => noiseOperator ρ g (antipodeEquiv n x) := by
    funext x
    simp only [noiseOperator,kernel_negative_correlation]
  rw [he,information_antipode]

theorem all_soft_contraction {n : ℕ} (g : Cube n → ℝ) (hg : IsClosedSoft g)
    {ρ : ℝ} (hρ : ρ ∈ Icc (-1) 1) :
    informationDeficit (noiseOperator ρ g) ≤ psi (|ρ| *psiInv (informationDeficit g)) := by
  have ha : |ρ| ∈ Icc 0 1 := ⟨abs_nonneg _,abs_le.mpr hρ⟩
  have h := all_soft_nonnegative_contraction g hg ha
  by_cases hpos : 0 ≤ ρ
  · simpa only [abs_of_nonneg hpos] using h
  · rw [abs_of_neg (lt_of_not_ge hpos),information_negative_correlation] at h
    simpa only [abs_of_neg (lt_of_not_ge hpos)] using h

end LeanBlast.CourtadeKumar
end
end

end OAI
