import Mathlib
import OAI.Analysis.Conductivity.Flux.CompactBoxDivergence

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma cubePartial_smooth {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (v : Box3) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (cubePartial f v) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma cubePartial_add {f g : Box3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (v p : Box3) : cubePartial (fun x => f x+g x) v p=cubePartial f v p+cubePartial g v p := by
  simp only [cubePartial,fderiv_fun_add (hf p) (hg p),add_apply]

lemma cubePartial_sub {f g : Box3 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (v p : Box3) : cubePartial (fun x => f x-g x) v p=cubePartial f v p-cubePartial g v p := by
  simp only [cubePartial,fderiv_fun_sub (hf p) (hg p),sub_apply]

lemma cubePartial_neg {f : Box3 → ℝ} (v p : Box3) :
    cubePartial (fun x => -f x) v p= -cubePartial f v p := by
  simp only [cubePartial,fderiv_fun_neg,neg_apply]

lemma cubePartial_commute {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (v w p : Box3) :
    cubePartial (cubePartial f v) w p=cubePartial (cubePartial f w) v p := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (show ((2 : ℕ∞) : WithTop ℕ∞)≤↑(⊤ : ℕ∞) from WithTop.coe_le_coe.mpr le_top)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf2.fderiv_right (show (1 : WithTop ℕ∞)+1≤2 by norm_num)).contDiffAt.differentiableAt (by norm_num)
  unfold cubePartial
  rw [fderiv_clm_apply hd (differentiableAt_const _),fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using hf2.contDiffAt.isSymmSndFDerivAt (by simp) w v

lemma cubePartial_compact {f : Box3 → ℝ} (hf : HasCompactSupport f) (v : Box3) :
    HasCompactSupport (cubePartial f v) := hf.fderiv_apply ℝ v

lemma cube_integration_by_parts {f g : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (hs : HasCompactSupport g) (v : Box3) :
    (∫ p, f p*cubePartial g v p)= -(∫ p, cubePartial f v p*g p) := by
  let : (volume : Measure Box3).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (ℝ×ℝ)) (volume : Measure ℝ)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (((continuous_cubePartial hf v).mul hg.continuous).integrable_of_hasCompactSupport hs.mul_left)
    ((hf.continuous.mul (continuous_cubePartial hg v)).integrable_of_hasCompactSupport (μ := volume)
      (cubePartial_compact hs v).mul_left)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hs.mul_left)
    (fun p _ => hf.differentiable (by simp) p) (fun p _ => hg.differentiable (by simp) p)

lemma compact_divergence {r : Box3 → ℝ} (hr : ContDiff ℝ (↑(⊤ : ℕ∞)) r)
    (hs : HasCompactSupport r) (hz : (∫ p,r p)=0) :
    ∃ F₁ F₂ F₃ : Box3 → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) F₁ ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) F₂ ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) F₃ ∧
      HasCompactSupport F₁ ∧ HasCompactSupport F₂ ∧ HasCompactSupport F₃ ∧
      (∀ p, cubePartial F₁ ((1,0),0) p+cubePartial F₂ ((0,1),0) p+
        cubePartial F₃ ((0,0),1) p=r p) := by
  obtain ⟨R,hR⟩ := hs.isBounded.subset_ball (0:Box3)
  let M := max R 1
  have hM : 0<M := lt_of_lt_of_le zero_lt_one (le_max_right ..)
  have hsub : tsupport r⊆(Ioo (-M) M ×ˢ Ioo (-M) M) ×ˢ Ioo (-M) M := by
    intro p hp
    have hh : ‖p‖<M := lt_of_lt_of_le (by simpa using hR hp) (le_max_left ..)
    simp only [Prod.norm_def,Real.norm_eq_abs,max_lt_iff] at hh
    exact ⟨⟨abs_lt.mp hh.1.1,abs_lt.mp hh.1.2⟩,abs_lt.mp hh.2⟩
  obtain ⟨F₁,F₂,F₃,h₁,h₂,h₃,hs₁,hs₂,hs₃,hd,_⟩ :=
    compact_box_divergence (a := fun _ => -M) (b := fun _ => M)
      (fun _ => by linarith) hr hs hsub hz
  exact ⟨F₁,F₂,F₃,h₁,h₂,h₃,hs₁,hs₂,hs₃,hd⟩

lemma cubePartial_fst_fst (v p : Box3) : cubePartial (fun x => x.1.1) v p=v.1.1 := by
  have hh : HasFDerivAt (fun x : Box3 => x.1.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) ℝ)) p :=
    hasFDerivAt_fst.comp p hasFDerivAt_fst
  rw [cubePartial,hh.fderiv]; rfl

lemma cubePartial_snd_fst (v p : Box3) : cubePartial (fun x => x.1.2) v p=v.1.2 := by
  have hh : HasFDerivAt (fun x : Box3 => x.1.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) ℝ)) p :=
    hasFDerivAt_snd.comp p hasFDerivAt_fst
  rw [cubePartial,hh.fderiv]; rfl

lemma cube_coordinate_divergence_moment {F₁ F₂ F₃ r : Box3 → ℝ}
    (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₁) (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₂)
    (h₃ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₃)
    (hs₁ : HasCompactSupport F₁) (hs₂ : HasCompactSupport F₂) (hs₃ : HasCompactSupport F₃)
    (hd : ∀ p, cubePartial F₁ ((1,0),0) p+cubePartial F₂ ((0,1),0) p+
      cubePartial F₃ ((0,0),1) p=r p)
    {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    (∫ p,f p*r p)= -(∫ p,cubePartial f ((1,0),0) p*F₁ p)-
      (∫ p,cubePartial f ((0,1),0) p*F₂ p)-(∫ p,cubePartial f ((0,0),1) p*F₃ p) := by
  have he : (fun p => f p*r p)=(fun p => f p*cubePartial F₁ ((1,0),0) p+
      f p*cubePartial F₂ ((0,1),0) p+f p*cubePartial F₃ ((0,0),1) p) := by
    funext p; rw [←hd p]; ring
  have hi₁ : Integrable (fun p => f p*cubePartial F₁ ((1,0),0) p) := (hf.continuous.mul (continuous_cubePartial h₁ ((1,0),0))).integrable_of_hasCompactSupport (μ := volume)
    (cubePartial_compact hs₁ _).mul_left
  have hi₂ : Integrable (fun p => f p*cubePartial F₂ ((0,1),0) p) := (hf.continuous.mul (continuous_cubePartial h₂ ((0,1),0))).integrable_of_hasCompactSupport (μ := volume)
    (cubePartial_compact hs₂ _).mul_left
  have hi₃ : Integrable (fun p => f p*cubePartial F₃ ((0,0),1) p) := (hf.continuous.mul (continuous_cubePartial h₃ ((0,0),1))).integrable_of_hasCompactSupport (μ := volume)
    (cubePartial_compact hs₃ _).mul_left
  have hi₁₂ : Integrable (fun p => f p*cubePartial F₁ ((1,0),0) p+f p*cubePartial F₂ ((0,1),0) p) := hi₁.add hi₂
  rw [he,integral_add hi₁₂ hi₃,integral_add hi₁ hi₂,
    cube_integration_by_parts hf h₁ hs₁,cube_integration_by_parts hf h₂ hs₂,
    cube_integration_by_parts hf h₃ hs₃]
  ring

theorem compact_regular_coordinate_correction {r₁ r₂ : Box3 → ℝ}
    (hr₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₁) (hr₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) r₂)
    (hs₁ : HasCompactSupport r₁) (hs₂ : HasCompactSupport r₂)
    (hz₁ : (∫ p,r₁ p)=0) (hz₂ : (∫ p,r₂ p)=0)
    (ht : (∫ p,p.1.2*r₁ p-p.1.1*r₂ p)=0) :
    ∃ H : Fin 3 → Fin 3 → Box3 → ℝ,
      (∀ i j, ContDiff ℝ (↑(⊤ : ℕ∞)) (H i j)) ∧
      (∀ i j, HasCompactSupport (H i j)) ∧
      (∀ i j p,H i j p=H j i p) ∧
      (∀ p,cubePartial (H 0 0) ((1,0),0) p+cubePartial (H 1 0) ((0,1),0) p+
        cubePartial (H 2 0) ((0,0),1) p=r₁ p) ∧
      (∀ p,cubePartial (H 0 1) ((1,0),0) p+cubePartial (H 1 1) ((0,1),0) p+
        cubePartial (H 2 1) ((0,0),1) p=r₂ p) := by
  obtain ⟨F₁,F₂,F₃,hF₁,hF₂,hF₃,hsF₁,hsF₂,hsF₃,hdF⟩ := compact_divergence hr₁ hs₁ hz₁
  obtain ⟨G₁,G₂,G₃,hG₁,hG₂,hG₃,hsG₁,hsG₂,hsG₃,hdG⟩ := compact_divergence hr₂ hs₂ hz₂
  have hf₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun p : Box3 => p.1.1) := contDiff_fst.comp contDiff_fst
  have hf₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun p : Box3 => p.1.2) := contDiff_snd.comp contDiff_fst
  have hIF := cube_coordinate_divergence_moment hF₁ hF₂ hF₃ hsF₁ hsF₂ hsF₃ hdF hf₂
  have hIG := cube_coordinate_divergence_moment hG₁ hG₂ hG₃ hsG₁ hsG₂ hsG₃ hdG hf₁
  simp only [cubePartial_fst_fst,cubePartial_snd_fst,zero_mul,one_mul,integral_zero,neg_zero,
    sub_zero,zero_sub] at hIF hIG
  have hi₁ : Integrable (fun p : Box3 => p.1.2*r₁ p) := (hf₂.continuous.mul hr₁.continuous).integrable_of_hasCompactSupport (μ := volume) hs₁.mul_left
  have hi₂ : Integrable (fun p : Box3 => p.1.1*r₂ p) := (hf₁.continuous.mul hr₂.continuous).integrable_of_hasCompactSupport (μ := volume) hs₂.mul_left
  have hzq : (∫ p,F₂ p-G₁ p)=0 := by
    rw [integral_sub (hF₂.continuous.integrable_of_hasCompactSupport hsF₂)
      (hG₁.continuous.integrable_of_hasCompactSupport hsG₁)]
    rw [integral_sub hi₁ hi₂,hIF,hIG] at ht
    linarith
  obtain ⟨h₁,h₂,h₃,hh₁,hh₂,hh₃,hsh₁,hsh₂,hsh₃,hdh⟩ :=
    compact_divergence (hF₂.sub hG₁) (hsF₂.sub hsG₁) hzq
  let A := fun p => F₁ p+cubePartial h₁ ((0,1),0) p
  let B := fun p => G₁ p+cubePartial h₂ ((0,1),0) p
  let C := fun p => F₃ p+cubePartial h₃ ((0,1),0) p
  let D := fun p => G₂ p-cubePartial h₂ ((1,0),0) p
  let H : Fin 3 → Fin 3 → Box3 → ℝ := ![![A,B,C],![B,D,G₃],![C,G₃,fun _ => 0]]
  have hA := hF₁.add (cubePartial_smooth hh₁ ((0,1),0))
  have hB := hG₁.add (cubePartial_smooth hh₂ ((0,1),0))
  have hC := hF₃.add (cubePartial_smooth hh₃ ((0,1),0))
  have hD := hG₂.sub (cubePartial_smooth hh₂ ((1,0),0))
  have hsA := hsF₁.add (cubePartial_compact hsh₁ ((0,1),0))
  have hsB := hsG₁.add (cubePartial_compact hsh₂ ((0,1),0))
  have hsC := hsF₃.add (cubePartial_compact hsh₃ ((0,1),0))
  have hsD := hsG₂.sub (cubePartial_compact hsh₂ ((1,0),0))
  have hB' : B=(fun p => F₂ p-cubePartial h₁ ((1,0),0) p-cubePartial h₃ ((0,0),1) p) := by
    funext p
    change G₁ p+cubePartial h₂ ((0,1),0) p=_
    linarith [hdh p]
  refine ⟨H,?_,?_,?_,?_,?_⟩
  · intro i j; fin_cases i <;> fin_cases j
    all_goals first | exact hA | exact hB | exact hC | exact hD | exact hG₃ | exact contDiff_const
  · intro i j; fin_cases i <;> fin_cases j
    all_goals first | exact hsA | exact hsB | exact hsC | exact hsD | exact hsG₃ | exact HasCompactSupport.zero
  · intro i j p; fin_cases i <;> fin_cases j <;> rfl
  · intro p
    change cubePartial A ((1,0),0) p+cubePartial B ((0,1),0) p+cubePartial C ((0,0),1) p=r₁ p
    rw [hB']
    change cubePartial (fun p => F₁ p+cubePartial h₁ ((0,1),0) p) ((1,0),0) p+
      cubePartial (fun p => F₂ p-cubePartial h₁ ((1,0),0) p-cubePartial h₃ ((0,0),1) p) ((0,1),0) p+
      cubePartial (fun p => F₃ p+cubePartial h₃ ((0,1),0) p) ((0,0),1) p=r₁ p
    rw [cubePartial_add (hF₁.differentiable (by simp)) ((cubePartial_smooth hh₁ _).differentiable (by simp)),
      cubePartial_sub ((hF₂.sub (cubePartial_smooth hh₁ _)).differentiable (by simp))
        ((cubePartial_smooth hh₃ _).differentiable (by simp)),
      cubePartial_sub (hF₂.differentiable (by simp)) ((cubePartial_smooth hh₁ _).differentiable (by simp)),
      cubePartial_add (hF₃.differentiable (by simp)) ((cubePartial_smooth hh₃ _).differentiable (by simp)),
      cubePartial_commute hh₁ ((0,1),0) ((1,0),0),cubePartial_commute hh₃ ((0,1),0) ((0,0),1)]
    linarith [hdF p]
  · intro p
    change cubePartial B ((1,0),0) p+cubePartial D ((0,1),0) p+cubePartial G₃ ((0,0),1) p=r₂ p
    change cubePartial (fun p => G₁ p+cubePartial h₂ ((0,1),0) p) ((1,0),0) p+
      cubePartial (fun p => G₂ p-cubePartial h₂ ((1,0),0) p) ((0,1),0) p+
      cubePartial G₃ ((0,0),1) p=r₂ p
    rw [cubePartial_add (hG₁.differentiable (by simp)) ((cubePartial_smooth hh₂ _).differentiable (by simp)),
      cubePartial_sub (hG₂.differentiable (by simp)) ((cubePartial_smooth hh₂ _).differentiable (by simp)),
      cubePartial_commute hh₂ ((0,1),0) ((1,0),0)]
    linarith [hdG p]

end ScalarConductivity

end

end OAI
