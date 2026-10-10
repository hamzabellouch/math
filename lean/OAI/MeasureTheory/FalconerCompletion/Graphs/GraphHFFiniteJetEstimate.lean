import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphCapScaleInvCrude

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer Attempt4FullFar Attempt4Near
open scoped ComplexConjugate RealInnerProductSpace ContDiff
variable {d : ℕ}
theorem graph_HF_finite_jet_estimate {sig c₀ Ggeom : ℝ}
    (hsig : 0 < sig) (hc₀ : 0 < c₀) (hcsmall : (d+1:ℝ)*c₀ ≤ 1/2) (hGgeom : 0 ≤ Ggeom) (T : ℝ) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) (B₀ : ℕ) (s₁ s₂ : ℝ) (m₁ m₂ : ℝ → ℝ),
    RegularizedProfileData ρ N B₀ s₁ sig m₁ → RegularizedProfileData κ N B₀ s₂ sig m₂ →
    ∀ (a p : ℕ) (v L Ctest K B Pcut : ℝ) (J i₁ i₂ g₁ g₂ : ℕ)
      (X Y : CellPath d) (Ψ : ℝ → ℝ) (ψ : EuclideanSpace ℝ (Fin d) → ℂ)
      (b c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ),
    a < p → (p:ℝ) ≤ v → v ≤ N →
    (p:ℝ)-a ≤ v-p+2*sig*N → L ≤ v-p+2*sig*N → 10*sig*N ≤ v-p →
    a ≤ g₁ → a ≤ g₂ → g₁ < p → g₂ < p →
    (g₁:ℝ) ≤ (a:ℝ)+2*sig*N → (g₂:ℝ) ≤ (a:ℝ)+2*sig*N →
    0 < J → i₁ ≤ J → i₂ ≤ J →
    X ∈ dyadicPaths a → Y ∈ dyadicPaths a → 0 < ρ (treeCell X) → 0 < κ (treeCell Y) →
    ‖treeCenter X-treeCenter Y‖ ≤ Ggeom*(2:ℝ)^(-(a:ℝ)) →
    ContDiff ℝ ∞ Ψ → tsupport Ψ ⊆ Icc (1/4:ℝ) 4 → (∀ r, 0 ≤ Ψ r) →
    (∫ u : ℝ, ‖(Ψ u:ℂ)‖) ≤ K → (∀ u, ‖iteratedDeriv m (fun u => (Ψ u:ℂ)) u‖ ≤ K) → 0 ≤ K →
    let R := (2:ℝ)^N
    let A₁ := adjustedProfile (d:=d) m₁ N
    let A₂ := adjustedProfile (d:=d) m₂ N
    let S := R^sig*max 1 ((2:ℝ)^L*R^(-50*sig))
    GraphSymbolJet b m S B → GraphSymbolJet c m S B →
    0 ≤ Pcut → ContDiff ℝ ∞ ψ → (∀ w, ‖w‖=1 → ‖ψ w‖ ≤ 1) →
    (∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j ψ w‖ ≤ Pcut) →
    ImposesParallelTest ρ g₁ p (testWidth N J i₁ p sig) (R^(height A₁ g₁ p+Ctest*sig)) b →
    ImposesParallelTest κ g₂ p (testWidth N J i₂ p sig) (R^(height A₂ g₂ p+Ctest*sig)) c →
    sourceAngularHFND d (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))) a v Ψ ψ
      (fun z => sourceAngularTransformND ρ (treeCell X) (R^(-m₁ a)) b z.1 z.2)
      (fun z => sourceAngularTransformND κ (treeCell Y) (R^(-m₂ a)) c z.1 z.2) ≤
    R^(-((A₁ p-A₁ a)+(A₂ p-A₂ a))+min (height A₁ a p) (height A₂ a p)+(Ctest+36*(d:ℝ)+5)*sig)*
      graphSourceChildMax ρ κ a p v X Y (R^(-m₁ p)) (R^(-m₂ p)) Ψ b c + C*K*Pcut^2*B^4*R^(-T) := by
  classical
  obtain ⟨m,C,hC,N₁,hdec⟩ := graph_crossed_nonedge_decay (d:=d) hsig hc₀ hGgeom (T+15*(d:ℝ))
  obtain ⟨N₂,hdeg⟩ := source_graph_cap_degrees (d:=d) hsig hc₀
  refine ⟨m,((9*(c₀⁻¹+1))^d)^2*C,by positivity,max 1 (max N₁ N₂),?_⟩
  intro N hN ρ κ B₀ s₁ s₂ m₁ m₂ hρ hκ a p v L Ctest K B Pcut J i₁ i₂ g₁ g₂ X Y Ψ ψ b c
    hap hpv hvN hh hL hgap hag₁ hag₂ hg₁ hg₂ hga₁ hga₂ hJ hi₁ hi₂ hX hY hoccX hoccY hcenters
    hΨ hsΨ hΨ0 hK hdΨ hK0 R A₁ A₂ S hb hc hPcut hψ hψ1 hdψ ht₁ ht₂
  let := hρ.probability
  let := hκ.probability
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left _ _) hN)
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hpN : p ≤ N := by exact_mod_cast hpv.trans hvN
  have haN := hap.le.trans hpN
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRp : 0 < R := by positivity
  have hc₀1 : c₀ ≤ 1 := by nlinarith [show (0:ℝ) ≤ d by positivity]
  let A := graphChildren ρ a p X
  let Z := graphChildren κ a p Y
  let δ := graphCapScale N a p c₀ sig
  let τ := graphTolerance N p sig
  let Caps := (sphereCapGridND d δ).product (sphereCapGridND d δ)
  let G := fun k : (Fin d → ℤ)×(Fin d → ℤ) =>
    retainedHFGraph (eligibleCells ρ a p X (tensorCapND δ k.1) b)
      (eligibleCells ρ a p X (tensorCapND δ k.2) b)
      (eligibleCells κ a p Y (tensorCapND δ k.1) c)
      (eligibleCells κ a p Y (tensorCapND δ k.2) c)
      (sphereCapCenterND δ k.1) (sphereCapCenterND δ k.2) τ
  let η := fun k : (Fin d → ℤ)×(Fin d → ℤ) => fun z : EuclideanSpace ℝ (Fin d)×EuclideanSpace ℝ (Fin d) =>
    tensorCapND δ k.1 z.1*tensorCapND δ k.2 z.2
  let U := fun (P : CellPath d) (z : ℝ × EuclideanSpace ℝ (Fin d)) => sourceAngularTransformND ρ (treeCell P) (R^(-m₁ p)) b z.1 z.2
  let W := fun (Q : CellPath d) (z : ℝ × EuclideanSpace ℝ (Fin d)) => sourceAngularTransformND κ (treeCell Q) (R^(-m₂ p)) c z.1 z.2
  let lam₁ := R^(-m₁ p)/R^(-m₁ a)
  let lam₂ := R^(-m₂ p)/R^(-m₂ a)
  let D := R^(min (height A₁ a p) (height A₂ a p)+(Ctest+32*(d:ℝ)+1)*sig)
  let ε := C*K*Pcut^2*B^4*(R^d)^4*R^(-(T+15*(d:ℝ)))*(2:ℝ)^v
  have hAB : (A.product Z).Nonempty := Finset.nonempty_product.mpr
    ⟨graphChildren_nonempty ρ hap.le hX hoccX,graphChildren_nonempty κ hap.le hY hoccY⟩
  have hlabels : (A.card:ℝ)*Z.card ≤ R^((A₁ p-A₁ a)+(A₂ p-A₂ a)+(d:ℝ)*((p:ℝ)-a)/(N:ℝ)+4*(d+1:ℝ)*sig) := by
    have h := graphChildren_pair_profile_card ρ κ hap.le hX hY hRp
      (fun P hP => hρ.graph_child_lower hpN hP) (fun Q hQ => hκ.graph_child_lower hpN hQ)
      (hρ.graph_parent_upper haN hX hoccX) (hκ.graph_parent_upper haN hY hoccY)
    rw [graph_profile_label_exponent (d:=d) m₁ m₂ N a p ((d+1:ℝ)*sig)] at h
    convert h using 1
    congr 1
    dsimp only [A₁,A₂]
    ring
  have hdegree := hdeg N hNN₂ ρ κ A₁ A₂ Ctest J i₁ i₂ a g₁ g₂ p X Y A Z b c
    hag₁ hag₂ hg₁.le hg₂.le hga₁ hga₂ hJ hi₁ hi₂ ht₁ ht₂
  have hiΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v)) :=
    (hΨ.continuous.integrable_of_hasCompactSupport
      (IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport Ψ) hsΨ)).comp_div (by positivity)
  have hbounds₁ : ∀ P ∈ A, ∀ r, ∀ᵐ w ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d)),
      ‖U P (r,w)‖ ≤ |(R^(-m₁ p))⁻¹| * ρ.real (treeCell P)*B := by
    intro P _ r
    filter_upwards [canonicalSphereMeasureND_ae_norm (d:=d)] with w hw
    exact sourceAngularTransformND_norm_le _ _ _ _ _ _ (fun x => hb.norm_le x w hw)
  have hbounds₂ : ∀ Q ∈ Z, ∀ r, ∀ᵐ w ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d)),
      ‖W Q (r,w)‖ ≤ |(R^(-m₂ p))⁻¹| * κ.real (treeCell Q)*B := by
    intro Q _ r
    filter_upwards [canonicalSphereMeasureND_ae_norm (d:=d)] with w hw
    exact sourceAngularTransformND_norm_le _ _ _ _ _ _ (fun x => hc.norm_le x w hw)
  have hne : ∀ k ∈ Caps, ∀ row ∈ A.product Z, ∀ col ∈ A.product Z, ¬G k row col →
      ‖graphCrossedCellTerm ρ κ (R^(-m₁ p)) (R^(-m₂ p)) b c Ψ ψ v δ k.1 k.2 row col‖ ≤ ε := by
    intro k hk row hr col hcol hn
    have hk' := Finset.mem_product.mp hk
    have hd := hdec N hNN₁ a p v L hh hL (sub_nonneg.mpr hpv) ρ κ X Y row col
      (R^(-m₁ p)) (R^(-m₂ p)) (R^d) K B Pcut Ψ ψ b c k.1 k.2 hX hY hcenters hr hcol
      (by positivity) (by positivity) (by positivity)
      (graphCellLaw_mass_crude ρ hR (hρ.profile_le_dim hNpos hpN) _)
      (graphCellLaw_mass_crude ρ hR (hρ.profile_le_dim hNpos hpN) _)
      (graphCellLaw_mass_crude κ hR (hκ.profile_le_dim hNpos hpN) _)
      (graphCellLaw_mass_crude κ hR (hκ.profile_le_dim hNpos hpN) _)
    rw [←graphCapScale_eq] at hd
    exact hd hk'.1 hk'.2 hΨ hsΨ hK hdΨ hK0 hPcut hψ hdψ hb hc hn
  have hmain := graphFiniteHFND_to_child_max d a p v lam₁ lam₂ hNpos
    (A₁ p-A₁ a) (A₂ p-A₂ a)
    (min (height A₁ a p) (height A₂ a p)+(Ctest+32*(d:ℝ)+1)*sig) (4*(d+1:ℝ)*sig) 1
    (graph_profile_ratio (d:=d) hNpos m₁ a p) (graph_profile_ratio (d:=d) hNpos m₂ a p)
    (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))) A Z Caps hAB hlabels G η
    (graph_pair_partition_ae hc₀ hcsmall) U W
    (fun P _ => sourceAngularTransformND_measurable _ _ _ hb.measurable)
    (fun Q _ => sourceAngularTransformND_measurable _ _ _ hc.measurable)
    (fun P => |(R^(-m₁ p))⁻¹| * ρ.real (treeCell P)*B)
    (fun Q => |(R^(-m₂ p))⁻¹| * κ.real (treeCell Q)*B) hbounds₁ hbounds₂ (D:=D) (by positivity)
    (by simp only [one_mul]; exact le_rfl)
    (fun k hk row _ => ((hdegree k hk).1 row).2)
    (fun k hk col _ => ((hdegree k hk).2 col).2) hiΨ hΨ0 hψ.continuous.measurable (by
      filter_upwards [canonicalSphereMeasureND_ae_norm (d:=d)] with w hw
      exact hψ1 w hw)
    (fun k _ row _ col _ => by
      simpa only [η,U,W,Complex.ofReal_mul] using
        graph_crossed_cell_integrable ρ κ (R^(-m₁ p)) (R^(-m₂ p)) hb hc v hiΨ
          ψ hψ.continuous.measurable (by norm_num : (0:ℝ) ≤ 1) hψ1 δ k.1 k.2 row col)
    (show 0 ≤ ε by positivity) (by
      intro k hk row hr col hc hn
      simpa only [graphCrossedCellTerm,η,U,W,Complex.ofReal_mul] using hne k hk row hr col hc hn)
  rw [←graph_children_HF_split ρ κ hap.le hX hY hb hc (R^(-m₁ a)) (R^(-m₂ a))
    (by positivity : R^(-m₁ p) ≠ 0) (by positivity : R^(-m₂ p) ≠ 0) v Ψ ψ] at hmain
  have hid : graphSourceChildMax ρ κ a p v X Y (R^(-m₁ p)) (R^(-m₂ p)) Ψ b c =
      graphChildMaxND d (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d))) p v Ψ A Z hAB U W := by
    unfold graphSourceChildMax
    split_ifs with hx
    · rfl
    · exact (hx hAB).elim
  rw [←hid,one_mul] at hmain
  have hexp : -((A₁ p-A₁ a)+(A₂ p-A₂ a))+
      (min (height A₁ a p) (height A₂ a p)+(Ctest+32*(d:ℝ)+1)*sig)+4*(d+1:ℝ)*sig =
      -((A₁ p-A₁ a)+(A₂ p-A₂ a))+min (height A₁ a p) (height A₂ a p)+(Ctest+36*(d:ℝ)+5)*sig := by ring
  rw [hexp] at hmain
  apply hmain.trans
  apply add_le_add le_rfl
  have herr := graph_source_error_sum (T:=T) ρ κ hρ hκ hNpos haN hpN hvN
    hc₀ hc₀1 hsig.le (by positivity : 0 ≤ C*K*Pcut^2*B^4) X Y
  convert herr using 1
  ring

end CurrentFalconer.TreeND
end
end

end OAI
