import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactRegularCorrection
import OAI.Analysis.Conductivity.Flux.CompactInteriorDivergence
import OAI.Analysis.Conductivity.Variational.FiniteMomentTransfer

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma exists_unit_global_interval_bump {a b : ℝ} (hab : a<b) :
    ∃ η : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) η ∧ HasCompactSupport η ∧
      tsupport η⊆Ioo a b ∧ (∫ t,η t)=1 := by
  obtain ⟨η,hη,hs,hv,hi⟩ := exists_unit_interval_bump hab
  refine ⟨η,hη,hs,hv,?_⟩
  rw [intervalIntegral.integral_of_le hab.le] at hi
  have he : (∫ t in Ioc a b,η t)=(∫ t,η t) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    exact image_eq_zero_of_notMem_tsupport (fun hh => ht ⟨(hv hh).1,(hv hh).2.le⟩)
  rwa [he] at hi

lemma exists_unit_box_bump {a b : Fin 3 → ℝ} (hab : ∀ i,a i<b i) :
    ∃ K : Box3 → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) K ∧ HasCompactSupport K ∧
      tsupport K⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) ∧
      (∫ p,K p)=1 := by
  obtain ⟨η₁,h₁,hs₁,hv₁,hi₁⟩ := exists_unit_global_interval_bump (hab 0)
  obtain ⟨η₂,h₂,hs₂,hv₂,hi₂⟩ := exists_unit_global_interval_bump (hab 1)
  obtain ⟨η₃,h₃,hs₃,hv₃,hi₃⟩ := exists_unit_global_interval_bump (hab 2)
  let K : Box3 → ℝ := fun p => (η₁ p.1.1*η₂ p.1.2)*η₃ p.2
  have hK : ContDiff ℝ (↑(⊤ : ℕ∞)) K :=
    ((h₁.comp (contDiff_fst.comp contDiff_fst)).mul
      (h₂.comp (contDiff_snd.comp contDiff_fst))).mul (h₃.comp contDiff_snd)
  have hsK : HasCompactSupport K := by
    apply HasCompactSupport.of_support_subset_isCompact ((hs₁.prod hs₂).prod hs₃)
    intro p hp
    have hh := mul_ne_zero_iff.mp hp
    have hh' := mul_ne_zero_iff.mp hh.1
    exact ⟨⟨subset_tsupport η₁ hh'.1,subset_tsupport η₂ hh'.2⟩,subset_tsupport η₃ hh.2⟩
  have htK : tsupport K⊆(tsupport η₁ ×ˢ tsupport η₂) ×ˢ tsupport η₃ := by
    apply closure_minimal _ ((hs₁.isClosed.prod hs₂.isClosed).prod hs₃.isClosed)
    intro p hp
    have hh := mul_ne_zero_iff.mp hp
    have hh' := mul_ne_zero_iff.mp hh.1
    exact ⟨⟨subset_tsupport η₁ hh'.1,subset_tsupport η₂ hh'.2⟩,subset_tsupport η₃ hh.2⟩
  refine ⟨K,hK,hsK,htK.trans (prod_mono (prod_mono hv₁ hv₂) hv₃),?_⟩
  change (∫ p : (ℝ×ℝ)×ℝ,(η₁ p.1.1*η₂ p.1.2)*η₃ p.2)=1
  rw [Measure.volume_eq_prod,integral_prod_mul (fun p : ℝ×ℝ => η₁ p.1*η₂ p.2) η₃,
    Measure.volume_eq_prod,integral_prod_mul η₁ η₂,hi₁,hi₂,hi₃]
  norm_num

lemma cubePartial_integral_zero {K : Box3 → ℝ}
    (hK : ContDiff ℝ (↑(⊤ : ℕ∞)) K) (hs : HasCompactSupport K) (v : Box3) :
    (∫ p,cubePartial K v p)=0 := by
  have hh := cube_integration_by_parts (f := fun _ => (1:ℝ)) contDiff_const hK hs v
  simpa [cubePartial] using hh

theorem box_moment_right_inverse {a b : Fin 3 → ℝ} (hab : ∀ i,a i<b i)
    (m : Fin 3 → ℝ) :
    ∃ r₁ r₂ : Box3 → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) r₁ ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) r₂ ∧
      HasCompactSupport r₁ ∧ HasCompactSupport r₂ ∧
      tsupport r₁⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) ∧
      tsupport r₂⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) ∧
      (∫ p,r₁ p)=m 0 ∧ (∫ p,r₂ p)=m 1 ∧
      (∫ p,p.1.2*r₁ p-p.1.1*r₂ p)=m 2 := by
  obtain ⟨K,hK,hs,hv,hi⟩ := exists_unit_box_bump hab
  let D := cubePartial K ((0,1),0)
  let c := m 0*(∫ p : Box3,p.1.2*K p)-m 1*(∫ p : Box3,p.1.1*K p)-m 2
  let r₁ := fun p => m 0*K p+c*D p
  let r₂ := fun p => m 1*K p
  have hD : ContDiff ℝ (↑(⊤ : ℕ∞)) D := cubePartial_smooth hK _
  have hsD : HasCompactSupport D := cubePartial_compact hs _
  have hvD : tsupport D⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) :=
    (cubePartial_tsupport _).trans hv
  have iK : Integrable K := hK.continuous.integrable_of_hasCompactSupport hs
  have iD : Integrable D := hD.continuous.integrable_of_hasCompactSupport hsD
  have hDz : (∫ p,D p)=0 := cubePartial_integral_zero hK hs _
  have hf₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun p : Box3 => p.1.1) := contDiff_fst.comp contDiff_fst
  have hf₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun p : Box3 => p.1.2) := contDiff_snd.comp contDiff_fst
  have hDm : (∫ p : Box3,p.1.2*D p)= -1 := by
    have hh := cube_integration_by_parts hf₂ hK hs ((0,1),0)
    simpa only [cubePartial_snd_fst,one_mul,hi] using hh
  have iK₁ : Integrable (fun p : Box3 => p.1.1*K p) :=
    (hf₁.continuous.mul hK.continuous).integrable_of_hasCompactSupport hs.mul_left
  have iK₂ : Integrable (fun p : Box3 => p.1.2*K p) :=
    (hf₂.continuous.mul hK.continuous).integrable_of_hasCompactSupport hs.mul_left
  have iD₂ : Integrable (fun p : Box3 => p.1.2*D p) :=
    (hf₂.continuous.mul hD.continuous).integrable_of_hasCompactSupport hsD.mul_left
  refine ⟨r₁,r₂,(contDiff_const.mul hK).add (contDiff_const.mul hD),
    contDiff_const.mul hK,(hs.mul_left).add hsD.mul_left,hs.mul_left,?_,?_,?_,?_,?_⟩
  · exact (tsupport_add _ _).trans (union_subset
      (tsupport_mul_subset_right.trans hv) (tsupport_mul_subset_right.trans hvD))
  · exact tsupport_mul_subset_right.trans hv
  · dsimp only [r₁]
    rw [integral_add (iK.const_mul _) (iD.const_mul _),integral_const_mul,integral_const_mul,hi,hDz]
    ring
  · dsimp only [r₂]
    rw [integral_const_mul,hi,mul_one]
  · have he : (fun p : Box3 => p.1.2*r₁ p-p.1.1*r₂ p)=
        (fun p => m 0*(p.1.2*K p)+c*(p.1.2*D p)-m 1*(p.1.1*K p)) := by
      funext p; dsimp only [r₁,r₂]; ring
    have iKD : Integrable (fun p : Box3 => m 0*(p.1.2*K p)+c*(p.1.2*D p)) :=
      (iK₂.const_mul _).add (iD₂.const_mul _)
    rw [he,integral_sub iKD (iK₁.const_mul _),
      integral_add (iK₂.const_mul _) (iD₂.const_mul _),integral_const_mul,integral_const_mul,
      integral_const_mul,hDm]
    dsimp only [c]
    ring

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory

theorem box_moment_bounded_right_inverse {a b : Fin 3 → ℝ} (hab : ∀ i,a i<b i) :
    ∃ g : Fin 3 → Fin 2 → Box3 → ℝ,
      (∀ i j,ContDiff ℝ (↑(⊤ : ℕ∞)) (g i j)) ∧
      (∀ i j,HasCompactSupport (g i j)) ∧
      (∀ i j,tsupport (g i j)⊆(Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2)) ∧
      (∀ m : Fin 3 → ℝ,
        (∫ p,∑ i,m i*g i 0 p)=m 0 ∧
        (∫ p,∑ i,m i*g i 1 p)=m 1 ∧
        (∫ p,p.1.2*(∑ i,m i*g i 0 p)-p.1.1*(∑ i,m i*g i 1 p))=m 2) ∧
      (∀ j n,∃ B : ℝ,0<B ∧ ∀ (m : Fin 3 → ℝ) (p : Box3),
        ‖iteratedFDeriv ℝ n (fun p => ∑ i,m i*g i j p) p‖≤B*‖m‖) := by
  choose g₀ g₁ hg₀ hg₁ hs₀ hs₁ hv₀ hv₁ hi₀ hi₁ hit using
    fun i : Fin 3 => box_moment_right_inverse hab (Pi.single i 1)
  let g : Fin 3 → Fin 2 → Box3 → ℝ := fun i => ![g₀ i,g₁ i]
  have hg (i : Fin 3) (j : Fin 2) : ContDiff ℝ (↑(⊤ : ℕ∞)) (g i j) := by
    fin_cases j
    · exact hg₀ i
    · exact hg₁ i
  have hs (i : Fin 3) (j : Fin 2) : HasCompactSupport (g i j) := by
    fin_cases j
    · exact hs₀ i
    · exact hs₁ i
  have hv (i : Fin 3) (j : Fin 2) : tsupport (g i j)⊆
      (Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2) := by
    fin_cases j
    · exact hv₀ i
    · exact hv₁ i
  have hm (i : Fin 3) (j : Fin 2) : (∫ p,g i j p)=(Pi.single i (1 : ℝ) : Fin 3 → ℝ) (j.castLE (by decide : 2≤3)) := by
    fin_cases j
    · exact hi₀ i
    · exact hi₁ i
  have hmt (i : Fin 3) : (∫ p : Box3,p.1.2*g i 0 p-p.1.1*g i 1 p)= (Pi.single i (1 : ℝ) : Fin 3 → ℝ) 2 := hit i
  have hI (i : Fin 3) (j : Fin 2) : Integrable (g i j) :=
    (hg i j).continuous.integrable_of_hasCompactSupport (hs i j)
  refine ⟨g,hg,hs,hv,?_,?_⟩
  · intro m
    have hh (j : Fin 2) : (∫ p,∑ i,m i*g i j p)=m (j.castLE (by decide : 2≤3)) := by
      rw [integral_finsetSum _ (fun i _ => (hI i j).const_mul (m i))]
      simp_rw [integral_const_mul,hm]
      simp [Pi.single_apply]
    refine ⟨hh 0,hh 1,?_⟩
    have hU : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun p : Box3 => p.1.1) := contDiff_fst.comp contDiff_fst
    have hV : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun p : Box3 => p.1.2) := contDiff_snd.comp contDiff_fst
    have htI (i : Fin 3) : Integrable (fun p : Box3 => p.1.2*g i 0 p-p.1.1*g i 1 p) :=
      ((hV.continuous.mul (hg i 0).continuous).integrable_of_hasCompactSupport (hs i 0).mul_left).sub
        ((hU.continuous.mul (hg i 1).continuous).integrable_of_hasCompactSupport (hs i 1).mul_left)
    have he : (fun p : Box3 => p.1.2*(∑ i,m i*g i 0 p)-p.1.1*(∑ i,m i*g i 1 p))=
        (fun p => ∑ i,m i*(p.1.2*g i 0 p-p.1.1*g i 1 p)) := by
      funext p
      simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he,integral_finsetSum _ (fun i _ => (htI i).const_mul (m i))]
    simp_rw [integral_const_mul,hmt]
    simp [Pi.single_apply]
  · intro j n
    obtain ⟨B,hB,hbound⟩ := fixed_smooth_tests_bound (fun i => g i j)
      (fun i => hg i j) (fun i => hs i j) n
    refine ⟨B,hB,?_⟩
    intro m p
    simpa only [smul_eq_mul] using hbound m ‖m‖ (norm_nonneg _) (norm_le_pi_norm m) p

end ScalarConductivity

end

end OAI
