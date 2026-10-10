import Mathlib
import OAI.Probability.Ballisticity.Entropy.StoppedWindowEntropy
import OAI.Probability.Ballisticity.Entropy.EntropyVariational

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal
namespace DirectionalTransience.Entropy
variable {X : Type*} [MeasurableSpace X]

lemma finite_kl_of_integrable_poslog (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hac : μ≪ν)
    (hF : Integrable (fun x => Real.log (max 1 ((μ.rnDeriv ν x).toReal))) μ) :
    klDiv μ ν≠∞ := by
  let g : X → ℝ := fun x => (μ.rnDeriv ν x).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  have hg0 (x : X) : 0≤g x := ENNReal.toReal_nonneg
  let F : X → ℝ := fun x => Real.log (max 1 (g x))
  have hF0 (x : X) : 0≤F x := Real.log_nonneg (le_max_left _ _)
  have hp : Integrable (fun x => g x*F x) ν := (integrable_toReal_rnDeriv_mul_iff hac).mpr hF
  have hl : Integrable (fun x => g x*Real.log (g x)) ν := by
    apply (hp.add (integrable_const 1)).mono' (hg.mul hg.log).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      change |g x*Real.log (g x)|≤g x*F x+1
      apply abs_le.mpr
      constructor
      · have hlow : -1≤g x*Real.log (g x) := by
          by_cases hx : g x=0
          · simp [hx]
          have h := mul_le_mul_of_nonneg_left (Real.neg_inv_le_log (hg0 x)) (hg0 x)
          rw [mul_neg,mul_inv_cancel₀ hx] at h
          exact h
        have hn := mul_nonneg (hg0 x) (hF0 x)
        linarith
      · by_cases hx : g x=0
        · simp [hx]
        have h := mul_le_mul_of_nonneg_left
          (Real.log_le_log (lt_of_le_of_ne (hg0 x) (Ne.symm hx)) (le_max_right 1 (g x))) (hg0 x)
        change g x*Real.log (g x)≤g x*F x at h
        linarith
  exact klDiv_ne_top hac ((integrable_rnDeriv_mul_log_iff hac).mp hl)

lemma finite_kl_of_domination (Q μ ν : Measure X) [IsProbabilityMeasure Q]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hkl : klDiv μ ν≠∞)
    (K : ℝ) (hK : 0≤K) (hdom : Q≤ENNReal.ofReal K • μ) : klDiv Q ν≠∞ := by
  have hac : Q≪ν := (Measure.absolutelyContinuous_of_le hdom).trans
    (Measure.smul_absolutelyContinuous.trans (klDiv_ne_top_iff.mp hkl).1)
  let g : X → ℝ := fun x => (Q.rnDeriv ν x).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv Q ν).ennreal_toReal
  have hg0 (x : X) : 0≤g x := ENNReal.toReal_nonneg
  have hgi : Integrable g ν := by
    simpa only [mul_one] using
      (integrable_toReal_rnDeriv_mul_iff hac (f := fun _ => (1:ℝ))).mpr (integrable_const 1)
  have hg1 : (∫ x, g x ∂ν)=1 := by
    simpa only [mul_one,integral_const,probReal_univ,one_smul] using
      (integral_toReal_rnDeriv_mul hac (f := fun _ => (1:ℝ)))
  apply finite_kl_of_integrable_poslog Q ν hac
  let F := fun x => Real.log (max 1 (g x))
  have hF : Measurable F := (measurable_const.max hg).log
  have hF0 (x : X) : 0≤F x := Real.log_nonneg (le_max_left _ _)
  apply integrable_of_bounded_truncated_integrals Q F hF hF0 (K*((klDiv μ ν).toReal+1))
  intro n
  let Fn : X → ℝ := fun x => min (n:ℝ) (F x)
  have hFn : Measurable Fn := measurable_const.min hF
  have hBn : ∃ B : ℝ, ∀ x, |Fn x|≤B := ⟨n,fun x => by
    rw [abs_of_nonneg (le_min (Nat.cast_nonneg _) (hF0 x))]
    exact min_le_left _ _⟩
  have hi : Integrable Fn μ := integrable_of_bounded hFn hBn
  have he : Integrable (fun x => Real.exp (Fn x)) ν := exp_integrable_of_bounded hFn hBn
  have htest := entropy_exp_test_le μ ν hkl Fn hi he
  have he₂ : (∫ x, Real.exp (Fn x) ∂ν)≤2 := by
    have hb := integral_mono he ((integrable_const 1).add hgi) (fun x => by
      calc Real.exp (Fn x)≤Real.exp (F x) := Real.exp_le_exp.mpr (min_le_right _ _)
        _ = max 1 (g x) := Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
        _ ≤ 1+g x := max_le (by linarith [hg0 x]) (by linarith))
    simpa only [Pi.add_apply,integral_add (integrable_const 1) hgi,integral_const,
      probReal_univ,one_smul,hg1,one_add_one_eq_two] using hb
  have hd := integral_mono_measure hdom
    (ae_of_all _ fun x => le_min (Nat.cast_nonneg n) (hF0 x))
    (hi.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure,ENNReal.toReal_ofReal hK,smul_eq_mul] at hd
  exact hd.trans (mul_le_mul_of_nonneg_left (by linarith) hK)

end DirectionalTransience.Entropy

end

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace DirectionalTransience.StoppedWindow
variable {X A B F G : Type*} [MeasurableSpace X] [MeasurableSpace A]
  [MeasurableSpace B] [MeasurableSpace F] [MeasurableSpace G]

lemma sample_data_map (μ : Measure X) [IsFiniteMeasure μ]
    (g : X → A) (hg : Measurable g) (f : X → F) (hf : Measurable f)
    (K : Kernel A B) [IsMarkovKernel K] :
    (μ.compProd (K.comap g hg)).map (fun p => ((g p.1,p.2),f p.1)) =
      (((Kernel.id.prod K) ∥ₖ Kernel.id) ∘ₘ (μ.map (fun x => (g x,f x)))) := by
  apply Measure.ext_of_lintegral
  intro h hh
  have hw : Measurable (fun p : X × B => ((g p.1,p.2),f p.1)) :=
    ((hg.comp measurable_fst).prodMk measurable_snd).prodMk (hf.comp measurable_fst)
  have hk : Measurable (fun z : A × F => ∫⁻ y, h y ∂((Kernel.id.prod K) ∥ₖ Kernel.id) z) :=
    hh.lintegral_kernel
  rw [lintegral_map hh hw,Measure.lintegral_compProd (show Measurable (fun p : X × B => h ((g p.1,p.2),f p.1)) from hh.comp hw),
    Measure.lintegral_bind (Kernel.aemeasurable _) hh.aemeasurable,
    lintegral_map hk (hg.prodMk hf)]
  apply lintegral_congr
  intro x
  rw [Kernel.lintegral_parallelComp _ hh]
  simp_rw [Kernel.id_apply]
  simp only [Kernel.comap_apply]
  have he (p : A × B) : (∫⁻ z : F, h (p,z) ∂Measure.dirac (f x))=h (p,f x) :=
    lintegral_dirac' _ (hh.comp measurable_prodMk_left)
  simp_rw [he]
  simpa only [Kernel.id,id_eq,Function.comp_def] using (Kernel.lintegral_deterministic_prod
    (f:=id) measurable_id K (g x) (hh.comp measurable_prodMk_right)).symm

noncomputable def selectedKernel (K : Kernel A B) (u : B × F → G)
    (_ : Measurable u) : Kernel (A × F) ((A × B) × G) :=
  (((Kernel.id.prod K) ∥ₖ Kernel.id)).map (fun p => (p.1,u (p.1.2,p.2)))
instance selectedKernel_markov (K : Kernel A B) [IsMarkovKernel K]
    (u : B × F → G) (hu : Measurable u) : IsMarkovKernel (selectedKernel K u hu) := by
  unfold selectedKernel
  apply Kernel.IsMarkovKernel.map
  exact measurable_fst.prodMk (hu.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

lemma selectedKernel_lintegral (K : Kernel A B) [IsMarkovKernel K]
    (u : B × F → G) (hu : Measurable u) (h : (A × B) × G → ℝ≥0∞)
    (hh : Measurable h) (a : A) (f : F) :
    (∫⁻ q, h q ∂selectedKernel K u hu (a,f)) = ∫⁻ b, h ((a,b),u (b,f)) ∂K a := by
  have hp : Measurable (fun p : (A × B) × F => (p.1,u (p.1.2,p.2))) :=
    measurable_fst.prodMk (hu.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  rw [selectedKernel,Kernel.map_apply _ hp,lintegral_map hh hp,
    Kernel.lintegral_parallelComp _ (show Measurable (fun p : (A × B) × F => h (p.1,u (p.1.2,p.2))) from hh.comp hp)]
  simp_rw [Kernel.id_apply]
  have he (p : A × B) : (∫⁻ z : F, h (p,u (p.2,z)) ∂Measure.dirac f)=h (p,u (p.2,f)) :=
    lintegral_dirac' _ (hh.comp (measurable_const.prodMk
      (hu.comp (measurable_const.prodMk measurable_id))))
  simp_rw [he]
  exact Kernel.lintegral_deterministic_prod measurable_id K a
    (hh.comp (measurable_id.prodMk (hu.comp (measurable_snd.prodMk measurable_const))))

lemma selected_reference (δ : Measure A) [IsFiniteMeasure δ]
    (R : Kernel A F) [IsMarkovKernel R] (K : Kernel A B) [IsMarkovKernel K]
    (P : Measure G) [IsProbabilityMeasure P] (u : B × F → G) (hu : Measurable u)
    (hP : ∀ a b, (R a).map (fun f => u (b,f))=P) :
    selectedKernel K u hu ∘ₘ δ.compProd R=(δ.compProd K).prod P := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hh.aemeasurable,
    Measure.lintegral_compProd hh.lintegral_kernel,
    lintegral_prod _ hh.aemeasurable,
    Measure.lintegral_compProd hh.lintegral_prod_right']
  apply lintegral_congr
  intro a
  simp_rw [selectedKernel_lintegral K u hu h hh]
  have hm : Measurable (fun p : F × B => h ((a,p.2),u (p.2,p.1))) :=
    hh.comp ((measurable_const.prodMk measurable_snd).prodMk (hu.comp measurable_swap))
  rw [←lintegral_prod _ hm.aemeasurable,lintegral_prod_symm _ hm.aemeasurable]
  apply lintegral_congr
  intro b
  rw [←hP a b]
  exact (lintegral_map (show Measurable (fun y : G => h ((a,b),y)) from hh.comp measurable_prodMk_left)
    (show Measurable (fun f : F => u (b,f)) from hu.comp measurable_prodMk_left)).symm

lemma selected_kl_finite [StandardBorelSpace G] [Nonempty G]
    (Q : Measure (A × F)) [IsProbabilityMeasure Q]
    (δ : Measure A) [IsProbabilityMeasure δ]
    (R : Kernel A F) [IsMarkovKernel R] (K : Kernel A B) [IsMarkovKernel K]
    (P : Measure G) [IsProbabilityMeasure P] (u : B × F → G) (hu : Measurable u)
    (hP : ∀ a b, (R a).map (fun f => u (b,f))=P)
    (hkl : klDiv Q (δ.compProd R)≠∞) :
    let W := selectedKernel K u hu ∘ₘ Q
    klDiv W (W.fst.prod P)≠∞ := by
  have h := klDiv_comp_right_le Q (δ.compProd R) (selectedKernel K u hu)
  rw [selected_reference δ R K P u hu hP] at h
  have hf := ne_top_of_le_ne_top hkl h
  rw [fresh_prod_chain] at hf
  exact (ENNReal.add_ne_top.mp hf).2

end DirectionalTransience.StoppedWindow

end

end OAI
