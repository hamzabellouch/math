import Mathlib
import OAI.Analysis.Conductivity.Geometry.BoxCoordinateBridge
import OAI.Analysis.Conductivity.Geometry.BoxMomentRightInverse
import OAI.Analysis.Conductivity.Sources.LocalRegular

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma localPiolaSource_torque (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : DifferentiableOn ℝ X X.source) (hXi : DifferentiableOn ℝ X.symm X.target)
    (r₁ r₂ : Coord3 → ℝ) (h₁ : Function.support r₁⊆X.source)
    (h₂ : Function.support r₂⊆X.source) :
    (∫ y,(X.symm y) 1*localPiolaSource X r₁ y-
      (X.symm y) 0*localPiolaSource X r₂ y)=
      (∫ x,x 1*r₁ x-x 0*r₂ x) := by
  let r : Coord3 → ℝ := fun x => x 1*r₁ x-x 0*r₂ x
  have hs : Function.support r⊆X.source := by
    intro x hx
    by_contra hn
    have hz₁ : r₁ x=0 := Function.notMem_support.mp (fun hh => hn (h₁ hh))
    have hz₂ : r₂ x=0 := Function.notMem_support.mp (fun hh => hn (h₂ hh))
    exact hx (by simp only [r,hz₁,hz₂,mul_zero,sub_self])
  have hp := localPiolaSource_pairing volume X hX
    (fun _ hx => local_fderiv_det_ne_zero X hX hXi hx) r hs (fun _ => 1)
  simp only [one_mul] at hp
  rw [←hp]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases ht : y∈X.target
  · simp only [localPiolaSource,ite_eq_left ht,r]
    ring
  · simp only [localPiolaSource,ite_eq_right ht,mul_zero,sub_self]

theorem physical_overlap_moment_inverse
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    {a b : Fin 3 → ℝ} (hab : ∀ i,a i<b i)
    (hbox : boxCoordinates ⁻¹' ((Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2))⊆X.source)
    (m : Fin 3 → ℝ) :
    ∃ R₁ R₂ : Coord3 → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) R₁ ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) R₂ ∧
      HasCompactSupport R₁ ∧ HasCompactSupport R₂ ∧
      tsupport R₁⊆X.target ∧ tsupport R₂⊆X.target ∧
      (∫ y,R₁ y)=m 0 ∧ (∫ y,R₂ y)=m 1 ∧
      (∫ y,(X.symm y) 1*R₁ y-(X.symm y) 0*R₂ y)=m 2 := by
  obtain ⟨r₁,r₂,hr₁,hr₂,hc₁,hc₂,hs₁,hs₂,hm₁,hm₂,hmt⟩ := box_moment_right_inverse hab m
  let p₁ : Coord3 → ℝ := r₁∘boxCoordinates
  let p₂ : Coord3 → ℝ := r₂∘boxCoordinates
  have hp₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) p₁ := hr₁.comp boxCoordinates.contDiff
  have hp₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) p₂ := hr₂.comp boxCoordinates.contDiff
  have hpc₁ : HasCompactSupport p₁ := hc₁.comp_homeomorph boxCoordinates.toHomeomorph
  have hpc₂ : HasCompactSupport p₂ := hc₂.comp_homeomorph boxCoordinates.toHomeomorph
  have hps₁ : tsupport p₁⊆X.source :=
    ((tsupport_comp_subset_preimage r₁ boxCoordinates.continuous).trans (preimage_mono hs₁)).trans hbox
  have hps₂ : tsupport p₂⊆X.source :=
    ((tsupport_comp_subset_preimage r₂ boxCoordinates.continuous).trans (preimage_mono hs₂)).trans hbox
  have hd := hX.differentiableOn (by simp)
  have hdi := hXi.differentiableOn (by simp)
  have hdet : ∀ x∈X.source,(fderiv ℝ X x).det≠0 :=
    fun _ hx => local_fderiv_det_ne_zero X hd hdi hx
  refine ⟨localPiolaSource X p₁,localPiolaSource X p₂,
    localPiolaSource_smooth X hX hXi p₁ hp₁ hpc₁ hps₁,
    localPiolaSource_smooth X hX hXi p₂ hp₂ hpc₂ hps₂,
    (localPiolaSource_compact X p₁ hpc₁ hps₁).1,
    (localPiolaSource_compact X p₂ hpc₂ hps₂).1,
    (localPiolaSource_compact X p₁ hpc₁ hps₁).2,
    (localPiolaSource_compact X p₂ hpc₂ hps₂).2,?_,?_,?_⟩
  · have h := localPiolaSource_pairing volume X hd hdet p₁ (subset_tsupport p₁ |>.trans hps₁) (fun _ => 1)
    simp only [one_mul] at h
    rw [h]
    exact (boxCoordinates_integral r₁).trans hm₁
  · have h := localPiolaSource_pairing volume X hd hdet p₂ (subset_tsupport p₂ |>.trans hps₂) (fun _ => 1)
    simp only [one_mul] at h
    rw [h]
    exact (boxCoordinates_integral r₂).trans hm₂
  · rw [localPiolaSource_torque X hd hdi p₁ p₂
      (subset_tsupport p₁ |>.trans hps₁) (subset_tsupport p₂ |>.trans hps₂)]
    exact (boxCoordinates_integral (fun p => p.1.2*r₁ p-p.1.1*r₂ p)).trans hmt

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory

theorem physical_overlap_bounded_moment_inverse
    (X : OpenPartialHomeomorph Coord3 Coord3)
    (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    {a b : Fin 3 → ℝ} (hab : ∀ i,a i<b i)
    (hbox : boxCoordinates ⁻¹' ((Ioo (a 0) (b 0) ×ˢ Ioo (a 1) (b 1)) ×ˢ Ioo (a 2) (b 2))⊆X.source) :
    ∃ g : Fin 3 → Fin 2 → Coord3 → ℝ,
      (∀ i j,ContDiff ℝ (↑(⊤ : ℕ∞)) (g i j)) ∧
      (∀ i j,HasCompactSupport (g i j)) ∧
      (∀ i j,tsupport (g i j)⊆X.target) ∧
      (∀ m : Fin 3 → ℝ,
        (∫ p,∑ i,m i*g i 0 p)=m 0 ∧
        (∫ p,∑ i,m i*g i 1 p)=m 1 ∧
        (∫ p,(X.symm p) 1*(∑ i,m i*g i 0 p)-(X.symm p) 0*(∑ i,m i*g i 1 p))=m 2) ∧
      (∀ j n,∃ B : ℝ,0<B ∧ ∀ (m : Fin 3 → ℝ) (p : Coord3),
        ‖iteratedFDeriv ℝ n (fun p => ∑ i,m i*g i j p) p‖≤B*‖m‖) := by
  choose g₀ g₁ hg₀ hg₁ hs₀ hs₁ hv₀ hv₁ hi₀ hi₁ hit using
    fun i : Fin 3 => physical_overlap_moment_inverse X hX hXi hab hbox (Pi.single i 1)
  let g : Fin 3 → Fin 2 → Coord3 → ℝ := fun i => ![g₀ i,g₁ i]
  have hg (i : Fin 3) (j : Fin 2) : ContDiff ℝ (↑(⊤ : ℕ∞)) (g i j) := by
    fin_cases j
    · exact hg₀ i
    · exact hg₁ i
  have hs (i : Fin 3) (j : Fin 2) : HasCompactSupport (g i j) := by
    fin_cases j
    · exact hs₀ i
    · exact hs₁ i
  have hv (i : Fin 3) (j : Fin 2) : tsupport (g i j)⊆
      X.target := by
    fin_cases j
    · exact hv₀ i
    · exact hv₁ i
  have hm (i : Fin 3) (j : Fin 2) : (∫ p,g i j p)=(Pi.single i (1 : ℝ) : Fin 3 → ℝ) (j.castLE (by decide : 2≤3)) := by
    fin_cases j
    · exact hi₀ i
    · exact hi₁ i
  have hmt (i : Fin 3) : (∫ p : Coord3,(X.symm p) 1*g i 0 p-(X.symm p) 0*g i 1 p)= (Pi.single i (1 : ℝ) : Fin 3 → ℝ) 2 := hit i
  have hI (i : Fin 3) (j : Fin 2) : Integrable (g i j) :=
    (hg i j).continuous.integrable_of_hasCompactSupport (hs i j)
  refine ⟨g,hg,hs,hv,?_,?_⟩
  · intro m
    have hh (j : Fin 2) : (∫ p,∑ i,m i*g i j p)=m (j.castLE (by decide : 2≤3)) := by
      rw [integral_finsetSum _ (fun i _ => (hI i j).const_mul (m i))]
      simp_rw [integral_const_mul,hm]
      simp [Pi.single_apply]
    refine ⟨hh 0,hh 1,?_⟩
    have hprod (i : Fin 3) (j : Fin 2) (k : Fin 3) :
        ContDiff ℝ (↑(⊤ : ℕ∞)) (fun p : Coord3 => (X.symm p) k*g i j p) := by
      apply contDiff_of_contDiffOn_tsupport X.open_target _
        (tsupport_mul_subset_right.trans (hv i j))
      apply X.open_target.contDiffOn_iff.mpr
      intro p hp
      exact (((ContinuousLinearMap.proj k : Coord3 →L[ℝ] ℝ).contDiff.contDiffAt).comp p
        (hXi.contDiffAt (X.open_target.mem_nhds hp))).mul (hg i j).contDiffAt
    have htI (i : Fin 3) : Integrable (fun p : Coord3 => (X.symm p) 1*g i 0 p-(X.symm p) 0*g i 1 p) :=
      ((hprod i 0 1).continuous.integrable_of_hasCompactSupport (hs i 0).mul_left).sub
        ((hprod i 1 0).continuous.integrable_of_hasCompactSupport (hs i 1).mul_left)
    have he : (fun p : Coord3 => (X.symm p) 1*(∑ i,m i*g i 0 p)-(X.symm p) 0*(∑ i,m i*g i 1 p))=
        (fun p => ∑ i,m i*((X.symm p) 1*g i 0 p-(X.symm p) 0*g i 1 p)) := by
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
