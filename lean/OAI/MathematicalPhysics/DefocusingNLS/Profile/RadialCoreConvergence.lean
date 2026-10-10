import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialLimitUniqueness

namespace OAI

/-! Full C1 convergence of the actual inner amplitudes from uniqueness of all subsequential limits. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_coupled_C1_core_convergence (R l b : ℝ)
    (hRlow : (3+7/10000 : ℝ) ≤ R) (hRu : R ≤ (10/3 : ℝ))
    (hl : (3 : ℝ) ≤ l) (hlR : l ≤ R) (hlwidth : R-l ≤ (1/1000 : ℝ))
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000))
    (F G : ℝ → ℂ) (hFc : Continuous F) (hGc : Continuous G)
    (hFI : ∀ r ∈ Icc l R, F r=1+∫ t in l..r, G t)
    (hGI : ∀ r ∈ Icc l R, G r=∫ t in l..r,
      -radialFreeCoefficient t*G t-(b : ℂ)*F t)
    (hB : ∀ r ∈ Icc l R, ‖F r‖ ≤ 2 ∧ ‖G r‖ ≤ 2) (hmod1 : ‖F R‖ < 1)
    (P : ℕ → RadialInnerData) (hR : ∀ n, (P n).R=R) (H : ℕ → ℝ → ℝ)
    (hH : ∀ n, RadialInnerOutputSpec (P n).p R (P n).lo (P n).c (P n).b (H n) (H n))
    (hp : Tendsto (fun n => (P n).p) atTop atTop)
    (hcT : Tendsto (fun n => (P n).c) atTop (𝓝 6))
    (hbT : Tendsto (fun n => (P n).b) atTop (𝓝 b))
    (hloT : Tendsto (fun n => (P n).lo) atTop (𝓝 ‖F R‖)) :
    ∃ A D : ℝ → ℝ, Continuous A ∧ Continuous D ∧
      TendstoUniformlyOn H A atTop (Icc 0 R) ∧
      TendstoUniformlyOn (fun n => deriv (H n)) D atTop (Icc 0 R) ∧
      EqOn A (fun _ => 1) (Icc 0 l) ∧ D l=0 ∧
      EqOn A (fun r => ‖F r‖) (Icc l R) := by
  obtain ⟨A,D,hA,hD,φ,hφ,hTA,hTD,hcore,hDl,htail⟩ :=
    radial_coupled_identified_subsequence R l b hRlow hRu hl hlR hlwidth hb F G hFc hGc hFI hGI hB hmod1
      P hR H hH hp hcT hbT hloT
  have hAD : ∀ r ∈ Ioo 0 R, HasDerivAt A (D r) r := by
    intro r hr
    exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo (hTD.mono Ioo_subset_Icc_self)
      (Eventually.of_forall (fun n t _ => ((hH (φ n)).1 t).hasDerivAt))
      (fun t ht => hTA.tendsto_at ⟨ht.1.le,ht.2.le⟩) hr
  have hsub : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ,
      TendstoUniformlyOn (fun n => H (ns (ms n))) A atTop (Icc 0 R) ∧
      TendstoUniformlyOn (fun n => deriv (H (ns (ms n)))) D atTop (Icc 0 R) := by
    intro ns hns
    obtain ⟨A',D',hA',hD',ψ,hψ,hTA',hTD',hcore',_,htail'⟩ :=
      radial_coupled_identified_subsequence R l b hRlow hRu hl hlR hlwidth hb F G hFc hGc hFI hGI hB hmod1
        (fun n => P (ns n)) (fun n => hR (ns n)) (fun n => H (ns n)) (fun n => hH (ns n))
        (hp.comp hns) (hcT.comp hns) (hbT.comp hns) (hloT.comp hns)
    have hAA : EqOn A' A (Icc 0 R) := by
      intro r hr
      by_cases hrl : r ≤ l
      · exact (hcore' ⟨hr.1,hrl⟩).trans (hcore ⟨hr.1,hrl⟩).symm
      · exact (htail' ⟨(not_le.mp hrl).le,hr.2⟩).trans (htail ⟨(not_le.mp hrl).le,hr.2⟩).symm
    have hA'D' : ∀ r ∈ Ioo 0 R, HasDerivAt A' (D' r) r := by
      intro r hr
      exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo (hTD'.mono Ioo_subset_Icc_self)
        (Eventually.of_forall (fun n t _ => ((hH (ns (ψ n))).1 t).hasDerivAt))
        (fun t ht => hTA'.tendsto_at ⟨ht.1.le,ht.2.le⟩) hr
    have hDD := radial_derivative_limit_unique R (by linarith) A' A D' D hD' hD hAA hA'D' hAD
    exact ⟨ψ,hTA'.congr_right hAA,hTD'.congr_right hDD⟩
  refine ⟨A,D,hA,hD,?_,?_,hcore,hDl,htail⟩
  · exact radial_uniform_limit_of_subsequences H A (fun ns hns => by
      obtain ⟨ms,hms,_⟩ := hsub ns hns
      exact ⟨ms,hms⟩)
  · exact radial_uniform_limit_of_subsequences (fun n => deriv (H n)) D (fun ns hns => by
      obtain ⟨ms,_,hms⟩ := hsub ns hns
      exact ⟨ms,hms⟩)

end DefocusingNLS

end OAI
