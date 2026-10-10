import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.OriginalDistanceMonotoneLimit
import OAI.MeasureTheory.FalconerCompletion.Estimates.OriginalMassRestoration
import OAI.MeasureTheory.FalconerCompletion.Measures.CompletionPolynomialSubpower
import OAI.MeasureTheory.FalconerCompletion.Shells.ApproximatingDistanceShellDecay

namespace OAI

/-! Measures and the conditional distance-set completion. -/

section

namespace CurrentFalconer.AssemblyCompletion
open Set Metric MeasureTheory Filter
open GraphLiteralSupport.CurrentFalconer.TreeND
open scoped ENNReal ContDiff Topology

theorem normalized_starting_pair_completion
    (n : ℕ) (hn : 1≤n) (E E₁ E₂ : Set (Space n))
    (hE : IsCompact E) (hE₁ : IsCompact E₁) (hE₂ : IsCompact E₂)
    (hs₁ : E₁⊆E) (hs₂ : E₂⊆E)
    (μ ν : Measure (Space n)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ E₁ᶜ=0) (hν : ν E₂ᶜ=0)
    (hroot : ∀ x∈E₁∪E₂, ∀ i, 0≤x i ∧ x i<1)
    (δ D : ℝ) (hδ : 0<δ) (hD : 0<D)
    (hsep : ∀ x∈E₁, ∀ y∈E₂, δ≤dist x y ∧ dist x y≤D)
    (w₀ : Space n) (hw₀ : ‖w₀‖=1)
    (hpatch : ∀ x∈E₁, ∀ y∈E₂, ‖direction x y-w₀‖≤1/100)
    (chi C : ℝ) (hchi : 0<chi) (hC : 0≤C)
    (hball₁ : ∀ x : Space n, ∀ r>0, μ (ball x r)≤ENNReal.ofReal (C*r^((n+1:ℝ)/2+chi)))
    (hball₂ : ∀ x : Space n, ∀ r>0, ν (ball x r)≤ENNReal.ofReal (C*r^((n+1:ℝ)/2+chi)))
    (hfilters : StartingPairFilters n μ ν E₁ E₂) :
    (∃ α : Measure ℝ, IsFiniteMeasure α ∧ 0<α univ ∧ α≪volume ∧ α (originalDistances E)ᶜ=0) ∧
      0<volume (originalDistances E)
 := by
  classical
  let Ctest : ℝ := 1000*(n+2:ℝ)
  obtain ⟨beta,hbeta,hbetaMax,kap,hkap,hkapMax,sig,hsig,hsigMax,hmargin,
    omega,gamma,homega,homegaMax,hgamma,hshell⟩ :=
      actual_approximating_distance_shell_decay hn Ctest chi hchi
  obtain ⟨omega₀,homega₀,hfilters⟩ := hfilters
  let omega' := min (omega/2) (omega₀/2)
  have homega' : 0<omega' := lt_min (half_pos homega) (half_pos homega₀)
  have homega'₀ : omega'<omega₀ := (min_le_right _ _).trans_lt (by linarith)
  have homega'le : omega'≤omega := (min_le_left _ _).trans (by linarith)
  obtain ⟨I,X,Y,A,K,hA,hmeas,hXY,hdisj,hcard,hmono,hpos,hcaps⟩ :=
    hfilters omega' homega' homega'₀
  let Γ := fun N => productFilter (I N) (X N) (Y N)
  have hΓmeas : ∀ N, MeasurableSet (Γ N) := fun N => productFilter_measurable _ _ _ (hmeas N)
  have hΓsub : ∀ N, Γ N⊆E₁×ˢ E₂ := fun N => productFilter_subset _ _ _ _ _ (hXY N)
  have hEroot₁ : E₁⊆treeCell [] :=
    fun x hx => root_of_coordinates (hroot x (Or.inl hx))
  have hEroot₂ : E₂⊆treeCell [] :=
    fun x hx => root_of_coordinates (hroot x (Or.inr hx))
  have hμroot : μ (treeCell [])ᶜ=0 := measure_mono_null (compl_subset_compl.mpr hEroot₁) hμ
  have hνroot : ν (treeCell [])ᶜ=0 := measure_mono_null (compl_subset_compl.mpr hEroot₂) hν
  obtain ⟨H,hH,hreg⟩ := assembly_profile_regularization_uniform (n+1) hsig
  obtain ⟨Kμ,hregμ⟩ := hreg μ hμroot ((n+1:ℝ)/2+chi) C hC hball₁
  obtain ⟨Kν,hregν⟩ := hreg ν hνroot ((n+1:ℝ)/2+chi) C hC hball₂
  obtain ⟨Kret,hret⟩ := actual_original_mass_restoration n hn sig hsig
  obtain ⟨c,Cbad,hc,hCbad,Kbad,hgood⟩ := hcaps sig hsig
  obtain ⟨Ψ,hΨ,hΨsupp,hΨpos,hΨone⟩ := shell_cutoff_exists
  obtain ⟨ψ,hψ,hψnorm,hψpatch⟩ := direction_cutoff_exists w₀ hw₀
  obtain ⟨Kshell,hshell⟩ := hshell Ψ hΨ hΨsupp hΨpos hΨone ψ hψ hψnorm δ D A hδ hD hA
  obtain ⟨η,Aerr,hη,hAerr,hdecay⟩ := completionError_decay n (2*H+1) sig c Cbad δ hsig hc hCbad hδ
  obtain ⟨hfinite,hαmono,hlim,hfiniteinf,hposinf,hcarry,hcarryinf,hcompact⟩ :=
    AssemblyLimit.original_distance_monotone_limit (n+1) (by omega) E E₁ E₂ hE hE₁ hE₂
      hs₁ hs₂ μ ν hμ hν δ D hδ hD hsep Γ hΓmeas hΓsub hmono hpos
  let α : ℕ → FiniteMeasure ℝ := fun N => ⟨AssemblyLimit.filteredDistanceMeasure μ ν (Γ N),hfinite N⟩
  let αinf : FiniteMeasure ℝ := ⟨AssemblyLimit.filteredDistanceMeasure μ ν (⋂ N, Γ N),hfiniteinf⟩
  have hac : (αinf:Measure ℝ)≪volume := by
    apply completion_of_eventual_positive_approximants α αinf hαmono hlim η gamma Aerr (2*A^2)
      hη hgamma hAerr (by positivity)
    filter_upwards [eventually_ge_atTop Kμ,eventually_ge_atTop Kν,eventually_ge_atTop Kret,
      eventually_ge_atTop Kbad,eventually_ge_atTop Kshell,eventually_ge_atTop K,hdecay] with
        N hNμ hNν hNret hNbad hNshell hNK hNdecay
    obtain ⟨hNpos,hBpos,hcountμ,hdiscardμ,hprofμ⟩ := hregμ N hNμ
    obtain ⟨_,_,hcountν,hdiscardν,hprofν⟩ := hregν N hNν
    let F := actualAssemblyClassFamily μ N (N/H) chi sig (fun T hT => (hprofμ T hT).2)
    let G := actualAssemblyClassFamily ν N (N/H) chi sig (fun T hT => (hprofν T hT).2)
    obtain ⟨good,hgoodMeas,hgoodSub,hbad,hcap₁,hcap₂⟩ := hgood N hNbad
    let τ := assemblyTau F G kap Ctest beta (I N) (X N) (Y N)
    have hΓroot : Γ N⊆treeCell [] ×ˢ treeCell [] :=
      (hΓsub N).trans (prod_mono hEroot₁ hEroot₂)
    have hsepΓ : ∀ z∈Γ N, δ≤dist z.1 z.2 :=
      fun z hz => (hsep z.1 (hΓsub N hz).1 z.2 (hΓsub N hz).2).1
    have hrest := hret N hNret μ ν (N/H) chi F G kap beta hkap hbeta
      (Γ N) good (hΓmeas N) hgoodMeas hgoodSub hΓroot δ hδ hsepΓ hcap₁ hcap₂
    have hτle : τ≤(α N:Measure ℝ) := hrest.1
    have : IsFiniteMeasure τ := isFiniteMeasure_of_le (α N:Measure ℝ) hτle
    refine ⟨⟨τ,inferInstance⟩,hτle,?_,?_⟩
    · have hcntF : (Fintype.card (assemblyRetainedIndex μ N (N/H) sig):ℝ)≤completionPoly n (2*H+1) N := by
        rw [assemblyRetainedIndex_card]
        simpa only [completionPoly,Nat.add_assoc,Nat.reduceAdd] using (Nat.cast_le (α:=ℝ)).mpr hcountμ
      have hcntG : (Fintype.card (assemblyRetainedIndex ν N (N/H) sig):ℝ)≤completionPoly n (2*H+1) N := by
        rw [assemblyRetainedIndex_card]
        simpa only [completionPoly,Nat.add_assoc,Nat.reduceAdd] using (Nat.cast_le (α:=ℝ)).mpr hcountν
      have hdiscF : μ (⋃ i,F.domain i)ᶜ≤ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ))+
          ENNReal.ofReal (completionPoly n (2*H+1) N)*ENNReal.ofReal (((2:ℝ)^N)^(-sig)) := by
        rw [actualAssemblyClassFamily_union]
        simpa only [completionPoly,ENNReal.ofReal_natCast,Nat.add_assoc,Nat.reduceAdd] using hdiscardμ
      have hdiscG : ν (⋃ i,G.domain i)ᶜ≤ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ))+
          ENNReal.ofReal (completionPoly n (2*H+1) N)*ENNReal.ofReal (((2:ℝ)^N)^(-sig)) := by
        rw [actualAssemblyClassFamily_union]
        simpa only [completionPoly,ENNReal.ofReal_natCast,Nat.add_assoc,Nat.reduceAdd] using hdiscardν
      exact hrest.2.trans ((restoration_scalar_bound sig c Cbad δ hCbad hδ _ _ _ _ _
        hcntF hcntG hdiscF hdiscG hbad).trans (ENNReal.ofReal_le_ofReal hNdecay))
    · have hcountI : ((I N).card:ℝ)≤A*((2:ℝ)^N)^(2*(n+1:ℝ)*omega) := by
        apply (hcard N hNK).trans
        gcongr
        · exact one_le_pow₀ (by norm_num : (1:ℝ)≤2)
      have hh := hshell N hNshell μ ν (N/H) F G (I N) (X N) (Y N) (hmeas N)
        (fun l hl => ⟨(hXY N l hl).1.trans hEroot₁,(hXY N l hl).2.trans hEroot₂⟩)
        (fun l hl x hx y hy => hsep x ((hXY N l hl).1 hx) y ((hXY N l hl).2 hy))
        (fun l hl x hx y hy => hψpatch (direction x y) (hpatch x ((hXY N l hl).1 hx) y ((hXY N l hl).2 hy)))
        (hdisj N) hcountI
      have hpow : ((2:ℝ)^N)^(-gamma)=(2:ℝ)^(-gamma*(N:ℝ)) := by
        rw [←Real.rpow_natCast (2:ℝ) N,←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
        congr 1
        ring
      rw [hpow] at hh
      exact hh
  have hcar : (αinf:Measure ℝ) (originalDistances E)ᶜ=0 := hcarryinf
  refine ⟨⟨(αinf:Measure ℝ),inferInstance,hposinf,hac,hcar⟩,?_⟩
  by_contra hnot
  have hz : volume (originalDistances E)=0 := le_antisymm (le_of_not_gt hnot) bot_le
  have hnull : (αinf:Measure ℝ) (originalDistances E)=0 := hac hz
  have hu := measure_union_le (μ:=(αinf:Measure ℝ)) (originalDistances E) (originalDistances E)ᶜ
  rw [union_compl_self,hnull,hcar,zero_add] at hu
  exact hposinf.not_ge hu

end CurrentFalconer.AssemblyCompletion
end

end OAI
