import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphFixedAngularBudget

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer.TreeND
open Set MeasureTheory Attempt4FullFar
open scoped ComplexConjugate RealInnerProductSpace ContDiff
variable {d : ℕ}

lemma graph_const_one_jet (j : ℕ) (w : EuclideanSpace ℝ (Fin d)) :
    ‖iteratedFDeriv ℝ j (fun _ : EuclideanSpace ℝ (Fin d) => (1:ℂ)) w‖ ≤ 1 := by
  rcases j with _ | j
  · simp
  · simp [iteratedFDeriv_succ_const]

theorem graph_direct_nonedge_decay {sig c₀ : ℝ} (hsig : 0 < sig) (hc₀ : 0 < c₀) (T : ℝ) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (a p : ℕ) (v L : ℝ), (p:ℝ)-a ≤ v-p+2*sig*N → L ≤ v-p+2*sig*N → 0 ≤ v-p →
    let R := (2:ℝ)^N
    let δ := min c₀ (((2:ℝ)^((p:ℝ)-a))⁻¹*R^(10*sig))
    let τ := (2:ℝ)^(-(p:ℝ))*R^(30*sig)
    let S := R^sig*max 1 ((2:ℝ)^L*R^(-50*sig))
    ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin d))), ∀ [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
    ∀ (X Y : CellPath d) (row col : CellPath d × CellPath d)
      (M₁ M₂ H K B : ℝ) (Ψ : ℝ → ℝ)
      (b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ) (k₁ k₂ : Fin d → ℤ),
    X ∈ dyadicPaths a → Y ∈ dyadicPaths a →
    row ∈ (graphChildren ρ a p X).product (graphChildren κ a p Y) →
    col ∈ (graphChildren ρ a p X).product (graphChildren κ a p Y) →
    0 ≤ M₁ → 0 ≤ M₂ → 0 ≤ H →
    (graphCellLaw ρ (treeCell row.1) M₁).real univ ≤ H →
    (graphCellLaw ρ (treeCell col.1) M₁).real univ ≤ H →
    (graphCellLaw κ (treeCell row.2) M₂).real univ ≤ H →
    (graphCellLaw κ (treeCell col.2) M₂).real univ ≤ H →
    k₁ ∈ sphereCapGridND d δ → k₂ ∈ sphereCapGridND d δ →
    ContDiff ℝ ∞ Ψ → tsupport Ψ ⊆ Icc (1/4:ℝ) 4 →
    (∫ u : ℝ, ‖(Ψ u:ℂ)‖) ≤ K →
    (∀ u, ‖iteratedDeriv m (fun u => (Ψ u:ℂ)) u‖ ≤ K) → 0 ≤ K →
    GraphSymbolJet b m S B → GraphSymbolJet c m S B →
    ¬retainedHGraph (eligibleCells ρ a p X (tensorCapND δ k₁) b)
      (eligibleCells κ a p Y (tensorCapND δ k₂) c)
      (sphereCapCenterND δ k₁) (sphereCapCenterND δ k₂) τ row col →
    ‖graphDirectCellTerm ρ κ M₁ M₂ b c Ψ v δ k₁ k₂ row col‖ ≤ C*K*B^4*H^4*R^(-T)*(2:ℝ)^v := by
  obtain ⟨m,C,hC,N₀,hdec⟩ := graph_cap_four_decay d hsig hc₀
    (by positivity : (0:ℝ) ≤ 2*(d+1:ℝ)) T
  refine ⟨m,C,hC,N₀,?_⟩
  intro N hN a p v L hh hL hv R δ τ S ρ κ _ _ X Y row col M₁ M₂ H K B Ψ b c k₁ k₂
    hX hY hr hc hM₁ hM₂ hH hP hP' hQ hQ' hk₁ hk₂ hΨ hsΨ hK hdΨ hK0 hb hcj hne
  by_cases hin : row ∈ (eligibleCells ρ a p X (tensorCapND δ k₁) b).product
       (eligibleCells κ a p Y (tensorCapND δ k₂) c) ∧
      col ∈ (eligibleCells ρ a p X (tensorCapND δ k₁) b).product
       (eligibleCells κ a p Y (tensorCapND δ k₂) c)
  · have hn : ¬retainedCenterTests (sphereCapCenterND δ k₁) (sphereCapCenterND δ k₂)
        (treeCenter row.1) (treeCenter row.2) (treeCenter col.1) (treeCenter col.2) τ :=
      fun h => hne ⟨hin.1,hin.2,h⟩
    have hn' : ¬(‖(treeCenter row.1-treeCenter col.1)-inner ℝ (treeCenter row.1-treeCenter col.1)
          (sphereCapCenterND δ k₁) • sphereCapCenterND δ k₁‖ ≤ τ ∧
        ‖(treeCenter row.2-treeCenter col.2)-inner ℝ (treeCenter row.2-treeCenter col.2)
          (sphereCapCenterND δ k₂) • sphereCapCenterND δ k₂‖ ≤ τ ∧
        |inner ℝ (sphereCapCenterND δ k₁) (treeCenter row.1-treeCenter col.1)+
          inner ℝ (sphereCapCenterND δ k₂) (treeCenter row.2-treeCenter col.2)| ≤ τ) := by
      simpa only [retainedCenterTests,graphPerpND,real_inner_comm] using hn
    have hr' := Finset.mem_product.mp hr
    have hc' := Finset.mem_product.mp hc
    have hgeo : ∀ᵐ z ∂((graphCellLaw ρ (treeCell row.1) M₁).prod (graphCellLaw ρ (treeCell col.1) M₁)).prod
        ((graphCellLaw κ (treeCell row.2) M₂).prod (graphCellLaw κ (treeCell col.2) M₂)),
      ‖z.1.1-z.1.2‖ ≤ 2*(d+1:ℝ)*(2:ℝ)^(-(a:ℝ)) ∧
      ‖z.2.1-z.2.2‖ ≤ 2*(d+1:ℝ)*(2:ℝ)^(-(a:ℝ)) ∧
      ‖(z.1.1-z.1.2)-(treeCenter row.1-treeCenter col.1)‖ ≤ 2*(d+1:ℝ)*(2:ℝ)^(-(p:ℝ)) ∧
      ‖(z.2.1-z.2.2)-(treeCenter row.2-treeCenter col.2)‖ ≤ 2*(d+1:ℝ)*(2:ℝ)^(-(p:ℝ)) := by
      filter_upwards [graphCellLaw_four_ae ρ ρ κ κ (treeCell row.1) (treeCell col.1) (treeCell row.2) (treeCell col.2)
        M₁ M₁ M₂ M₂ (measurableSet_treeCell row.1)
        (measurableSet_treeCell col.1) (measurableSet_treeCell row.2) (measurableSet_treeCell col.2)] with z hz
      refine ⟨?_,?_,graphChildren_center_error hr'.1 hc'.1 hz.1 hz.2.1,
        graphChildren_center_error hr'.2 hc'.2 hz.2.2.1 hz.2.2.2⟩
      · exact (graphChildren_direct_size hX hr'.1 hc'.1 hz.1 hz.2.1).trans (by nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (-(a:ℝ))])
      · exact (graphChildren_direct_size hY hr'.2 hc'.2 hz.2.2.1 hz.2.2.2).trans (by nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (-(a:ℝ))])
    have hsΨ' : tsupport (fun u => (Ψ u:ℂ)) ⊆ Icc (1/4:ℝ) 4 := by
      have he : tsupport (fun u => (Ψ u:ℂ)) = tsupport Ψ := by
        change closure (Function.support _) = closure (Function.support _)
        congr 1
        ext u
        simp only [Function.mem_support,ne_eq,Complex.ofReal_eq_zero]
      rwa [he]
    have h := hdec N hN a p v L hh hL hv
      (graphCellLaw ρ (treeCell row.1) M₁) (graphCellLaw ρ (treeCell col.1) M₁)
      (graphCellLaw κ (treeCell row.2) M₂) (graphCellLaw κ (treeCell col.2) M₂)
      (fun u => (Ψ u:ℂ)) K B 1 k₁ k₂ (treeCenter row.1-treeCenter col.1)
      (treeCenter row.2-treeCenter col.2) (fun _ => 1) (fun _ => 1) b b c c
      hk₁ hk₂ (Complex.ofRealCLM.contDiff.comp hΨ) hsΨ' hK hdΨ hK0 (by norm_num)
      contDiff_const contDiff_const (fun j _ w _ => graph_const_one_jet j w)
      (fun j _ w _ => graph_const_one_jet j w) hb hb hcj hcj hgeo hn'
    simp only [graphCellLaw_transform _ _ hM₁,graphCellLaw_transform _ _ hM₂] at h
    rw [←graphDirectCellTerm_eq] at h
    simp only [one_pow,mul_one] at h
    have hmass : (((graphCellLaw ρ (treeCell row.1) M₁).prod (graphCellLaw ρ (treeCell col.1) M₁)).prod
        ((graphCellLaw κ (treeCell row.2) M₂).prod (graphCellLaw κ (treeCell col.2) M₂))).real univ ≤ H^4 := by
      simp only [Measure.real,←Set.univ_prod_univ,Measure.prod_prod,ENNReal.toReal_mul]
      calc
        _ ≤ (H*H)*(H*H) := mul_le_mul (mul_le_mul hP hP' measureReal_nonneg hH)
          (mul_le_mul hQ hQ' measureReal_nonneg hH) (by positivity) (by positivity)
        _ = H^4 := by ring
    calc
      _ ≤ _ := h
      _ ≤ C*K*B^4*R^(-T)*(2:ℝ)^v*H^4 := mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := by ring
  · rw [graph_direct_ineligible_zero ρ κ hr hc M₁ M₂ hb hcj Ψ v δ k₁ k₂ hin,norm_zero]
    positivity

end CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer.TreeND
open Set MeasureTheory Attempt4FullFar
open scoped ComplexConjugate RealInnerProductSpace ContDiff
variable {d : ℕ}

theorem graph_crossed_nonedge_decay {sig c₀ G : ℝ} (hsig : 0 < sig) (hc₀ : 0 < c₀) (hG : 0 ≤ G) (T : ℝ) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (a p : ℕ) (v L : ℝ), (p:ℝ)-a ≤ v-p+2*sig*N → L ≤ v-p+2*sig*N → 0 ≤ v-p →
    let R := (2:ℝ)^N
    let δ := min c₀ (((2:ℝ)^((p:ℝ)-a))⁻¹*R^(10*sig))
    let τ := (2:ℝ)^(-(p:ℝ))*R^(30*sig)
    let S := R^sig*max 1 ((2:ℝ)^L*R^(-50*sig))
    ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin d))), ∀ [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
    ∀ (X Y : CellPath d) (row col : CellPath d × CellPath d)
      (M₁ M₂ H K B P : ℝ) (Ψ : ℝ → ℝ) (ψ : EuclideanSpace ℝ (Fin d) → ℂ)
      (b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ) (k₁ k₂ : Fin d → ℤ),
    X ∈ dyadicPaths a → Y ∈ dyadicPaths a →
    ‖treeCenter X-treeCenter Y‖ ≤ G*(2:ℝ)^(-(a:ℝ)) →
    row ∈ (graphChildren ρ a p X).product (graphChildren κ a p Y) →
    col ∈ (graphChildren ρ a p X).product (graphChildren κ a p Y) →
    0 ≤ M₁ → 0 ≤ M₂ → 0 ≤ H →
    (graphCellLaw ρ (treeCell row.1) M₁).real univ ≤ H →
    (graphCellLaw ρ (treeCell col.1) M₁).real univ ≤ H →
    (graphCellLaw κ (treeCell row.2) M₂).real univ ≤ H →
    (graphCellLaw κ (treeCell col.2) M₂).real univ ≤ H →
    k₁ ∈ sphereCapGridND d δ → k₂ ∈ sphereCapGridND d δ →
    ContDiff ℝ ∞ Ψ → tsupport Ψ ⊆ Icc (1/4:ℝ) 4 →
    (∫ u : ℝ, ‖(Ψ u:ℂ)‖) ≤ K →
    (∀ u, ‖iteratedDeriv m (fun u => (Ψ u:ℂ)) u‖ ≤ K) → 0 ≤ K →
    0 ≤ P → ContDiff ℝ ∞ ψ →
    (∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j ψ w‖ ≤ P) →
    GraphSymbolJet b m S B → GraphSymbolJet c m S B →
    ¬retainedHFGraph (eligibleCells ρ a p X (tensorCapND δ k₁) b)
      (eligibleCells ρ a p X (tensorCapND δ k₂) b)
      (eligibleCells κ a p Y (tensorCapND δ k₁) c)
      (eligibleCells κ a p Y (tensorCapND δ k₂) c)
      (sphereCapCenterND δ k₁) (sphereCapCenterND δ k₂) τ row col →
    ‖graphCrossedCellTerm ρ κ M₁ M₂ b c Ψ ψ v δ k₁ k₂ row col‖ ≤ C*K*P^2*B^4*H^4*R^(-T)*(2:ℝ)^v := by
  obtain ⟨m,C,hC,N₀,hdec⟩ := graph_cap_four_decay d hsig hc₀
    (by positivity : (0:ℝ) ≤ 2*(d+1:ℝ)+G) T
  refine ⟨m,C,hC,N₀,?_⟩
  intro N hN a p v L hh hL hv R δ τ S ρ κ _ _ X Y row col M₁ M₂ H K B P Ψ ψ b c k₁ k₂
    hX hY hcenters hr hc hM₁ hM₂ hH hP hP' hQ hQ' hk₁ hk₂ hΨ hsΨ hK hdΨ hK0 hP0 hψ hdψ hb hcj hne
  by_cases hin : row ∈ (eligibleCells ρ a p X (tensorCapND δ k₁) b).product
       (eligibleCells κ a p Y (tensorCapND δ k₂) c) ∧
      col ∈ (eligibleCells ρ a p X (tensorCapND δ k₂) b).product
       (eligibleCells κ a p Y (tensorCapND δ k₁) c)
  · have hn : ¬retainedCenterTests (sphereCapCenterND δ k₁) (sphereCapCenterND δ k₂)
        (treeCenter row.1) (treeCenter row.2) (treeCenter col.2) (treeCenter col.1) τ :=
      fun h => hne ⟨hin.1,hin.2,h⟩
    have hn' : ¬(‖(treeCenter row.1-treeCenter col.2)-inner ℝ (treeCenter row.1-treeCenter col.2)
          (sphereCapCenterND δ k₁) • sphereCapCenterND δ k₁‖ ≤ τ ∧
        ‖(treeCenter row.2-treeCenter col.1)-inner ℝ (treeCenter row.2-treeCenter col.1)
          (sphereCapCenterND δ k₂) • sphereCapCenterND δ k₂‖ ≤ τ ∧
        |inner ℝ (sphereCapCenterND δ k₁) (treeCenter row.1-treeCenter col.2)+
          inner ℝ (sphereCapCenterND δ k₂) (treeCenter row.2-treeCenter col.1)| ≤ τ) := by
      simpa only [retainedCenterTests,graphPerpND,real_inner_comm] using hn
    have hr' := Finset.mem_product.mp hr
    have hc' := Finset.mem_product.mp hc
    have hgeo : ∀ᵐ z ∂((graphCellLaw ρ (treeCell row.1) M₁).prod (graphCellLaw κ (treeCell col.2) M₂)).prod
        ((graphCellLaw κ (treeCell row.2) M₂).prod (graphCellLaw ρ (treeCell col.1) M₁)),
      ‖z.1.1-z.1.2‖ ≤ (2*(d+1:ℝ)+G)*(2:ℝ)^(-(a:ℝ)) ∧
      ‖z.2.1-z.2.2‖ ≤ (2*(d+1:ℝ)+G)*(2:ℝ)^(-(a:ℝ)) ∧
      ‖(z.1.1-z.1.2)-(treeCenter row.1-treeCenter col.2)‖ ≤ (2*(d+1:ℝ)+G)*(2:ℝ)^(-(p:ℝ)) ∧
      ‖(z.2.1-z.2.2)-(treeCenter row.2-treeCenter col.1)‖ ≤ (2*(d+1:ℝ)+G)*(2:ℝ)^(-(p:ℝ)) := by
      filter_upwards [graphCellLaw_four_ae ρ κ κ ρ (treeCell row.1) (treeCell col.2) (treeCell row.2) (treeCell col.1)
        M₁ M₂ M₂ M₁ (measurableSet_treeCell row.1)
        (measurableSet_treeCell col.2) (measurableSet_treeCell row.2) (measurableSet_treeCell col.1)] with z hz
      have hrev : ‖treeCenter Y-treeCenter X‖ ≤ G*(2:ℝ)^(-(a:ℝ)) := by rwa [norm_sub_rev]
      refine ⟨graphChildren_cross_size hX hY hr'.1 hc'.2 hcenters hz.1 hz.2.1,
        graphChildren_cross_size hY hX hr'.2 hc'.1 hrev hz.2.2.1 hz.2.2.2,?_,?_⟩
      · exact (graphChildren_center_error hr'.1 hc'.2 hz.1 hz.2.1).trans
          (by nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (-(p:ℝ))])
      · exact (graphChildren_center_error hr'.2 hc'.1 hz.2.2.1 hz.2.2.2).trans
          (by nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (-(p:ℝ))])
    have hsΨ' : tsupport (fun u => (Ψ u:ℂ)) ⊆ Icc (1/4:ℝ) 4 := by
      have he : tsupport (fun u => (Ψ u:ℂ)) = tsupport Ψ := by
        change closure (Function.support _) = closure (Function.support _)
        congr 1
        ext u
        simp only [Function.mem_support,ne_eq,Complex.ofReal_eq_zero]
      rwa [he]
    have h := hdec N hN a p v L hh hL hv
      (graphCellLaw ρ (treeCell row.1) M₁) (graphCellLaw κ (treeCell col.2) M₂)
      (graphCellLaw κ (treeCell row.2) M₂) (graphCellLaw ρ (treeCell col.1) M₁)
      (fun u => (Ψ u:ℂ)) K B P k₁ k₂ (treeCenter row.1-treeCenter col.2)
      (treeCenter row.2-treeCenter col.1) ψ (fun w => conj (ψ w)) b c c b
      hk₁ hk₂ (Complex.ofRealCLM.contDiff.comp hΨ) hsΨ' hK hdΨ hK0 hP0
      hψ (Complex.conjCLE.contDiff.comp hψ) hdψ (by
        intro j hj w hw
        change ‖iteratedFDeriv ℝ j (Complex.conjLIE ∘ ψ) w‖ ≤ P
        rw [Complex.conjLIE.norm_iteratedFDeriv_comp_left ψ w j]
        exact hdψ j hj w hw) hb hcj hcj hb hgeo hn'
    simp only [graphCellLaw_transform _ _ hM₁,graphCellLaw_transform _ _ hM₂] at h
    rw [←graphCrossedCellTerm_eq] at h
    have hmass : (((graphCellLaw ρ (treeCell row.1) M₁).prod (graphCellLaw κ (treeCell col.2) M₂)).prod
        ((graphCellLaw κ (treeCell row.2) M₂).prod (graphCellLaw ρ (treeCell col.1) M₁))).real univ ≤ H^4 := by
      simp only [Measure.real,←Set.univ_prod_univ,Measure.prod_prod,ENNReal.toReal_mul]
      calc
        _ ≤ (H*H)*(H*H) := mul_le_mul (mul_le_mul hP hQ' measureReal_nonneg hH)
          (mul_le_mul hQ hP' measureReal_nonneg hH) (by positivity) (by positivity)
        _ = H^4 := by ring
    calc
      _ ≤ _ := h
      _ ≤ C*K*P^2*B^4*R^(-T)*(2:ℝ)^v*H^4 := mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := by ring
  · rw [graph_crossed_ineligible_zero ρ κ hr hc M₁ M₂ hb hcj Ψ ψ v δ k₁ k₂ hin,norm_zero]
    positivity

end CurrentFalconer.TreeND
end
end

end OAI
