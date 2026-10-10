import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.BranchCost2
import OAI.Analysis.BiholderTransport.Regularity.Reversal
import OAI.Analysis.BiholderTransport.Coordinates.NormalEikonal

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section SplitSelection
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma reverseRay_fraction_endpoint (z : TangentBundle 𝓘(ℝ,Model n) M) (t : ℝ) :
    riemannianExp (reverseRay z).1 ((1-t) • (reverseRay z).2)=
      riemannianExp z.1 (t • z.2) := by
  rw [riemannianExp_smul,riemannianExp_smul]
  change (sprayFlow (1-t) (tangentScale (-1) (sprayFlow 1 z))).1=(sprayFlow t z).1
  rw [sprayFlow_scale,←sprayFlow_add]
  change (sprayFlow ((-1:ℝ)*(1-t)+1) z).1=(sprayFlow t z).1
  rw [show (-1:ℝ)*(1-t)+1=t by ring]

lemma minimizing_reversed_split_action {y : M} {r : TangentSpace 𝓘(ℝ,Model n) y}
    (hr : r∈minimizingVectors y) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    cost (riemannianExp y r) (riemannianExp y ((1-t) • r))/t+
      cost (riemannianExp y ((1-t) • r)) y/(1-t)=cost (riemannianExp y r) y := by
  have H := splitNormalAction_contact hr (show 0<1-t by linarith) (show 1-t<1 by linarith)
  dsimp only [splitNormalAction,normalCost] at H
  rw [riemannianExp_zero,sub_sub_cancel] at H
  unfold cost at H ⊢
  rw [dist_comm (riemannianExp y r),dist_comm _ y,dist_comm (riemannianExp y r) y]
  linarith

lemma exists_split_minimizing_selection {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    ∃ a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x,
      a 0=p ∧ ContDiffAt ℝ ∞ a 0 ∧
      ∀ᶠ u in 𝓝 0, splitNormalAction x t p (u,a u)=normalCost x p u := by
  let : Nonempty M := ⟨x⟩
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  let R := reverseRay z
  have hR : R.2∈injectivityDomain R.1 := reverseRay_injectivityDomain hp
  obtain ⟨q,hq0,hq,hqr,_⟩ := exists_normal_eikonal_log hR (reverseRay_endpoint z)
  have hprefix := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors x hp) ht ht1
  obtain ⟨κ,hκ0,hκ,hκright⟩ := exists_normal_local_inverse_at hprefix
  let J : X → M := fun u => riemannianExp R.1 ((1-t) • q u)
  have hJ0 : J 0=riemannianExp x (t • p) := by
    dsimp only [J]
    rw [hq0]
    exact reverseRay_fraction_endpoint z t
  have hJ : ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,Model n) ∞ J 0 :=
    (contMDiff_riemannianExp_fiber R.1 _).comp 0 (hq.const_smul (1-t)).contMDiffAt
  let a : X → X := fun u => t⁻¹ • κ (J u)
  have ha : ContDiffAt ℝ ∞ a 0 := by
    apply ContDiffAt.const_smul
    apply ContMDiffAt.contDiffAt
    apply ContMDiffAt.comp 0 _ hJ
    rwa [hJ0]
  have ha0 : a 0=p := by
    dsimp only [a]
    rw [hJ0,hκ0,←mul_smul,inv_mul_cancel₀ ht.ne',one_smul]
  have hright : ∀ᶠ u in 𝓝 0, riemannianExp x (t • a u)=J u := by
    have H := hJ.continuousAt.eventually (by simpa only [hJ0] using hκright)
    filter_upwards [H] with u hu
    simpa only [a,←mul_smul,mul_inv_cancel₀ ht.ne',one_smul] using hu
  have hqI : ∀ᶠ u in 𝓝 0, q u∈injectivityDomain R.1 :=
    hq.continuousAt.preimage_mem_nhds ((isOpen_injectivityDomain R.1).mem_nhds (hq0.symm ▸ hR))
  refine ⟨a,ha0,ha,?_⟩
  filter_upwards [hright,hqr,hqI] with u hu hv hw
  have HE : R.1=riemannianExp x p := by
    change (sprayFlow 1 z).1=riemannianExp x p
    exact (riemannianExp_eq_sprayFlow x p).symm
  dsimp only [splitNormalAction,normalCost]
  rw [hu,←hv,←HE]
  exact minimizing_reversed_split_action (injectivityDomain_subset_minimizingVectors R.1 hw) ht ht1

end SplitSelection
end WeakMTWTransport

end

end

end

end OAI
