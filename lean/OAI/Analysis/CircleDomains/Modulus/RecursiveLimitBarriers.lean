import OAI.Analysis.CircleDomains.Modulus.CompactBarrierData
import OAI.Analysis.CircleDomains.Modulus.SavedModelBarriers
import OAI.Analysis.CircleDomains.Topology.RecursiveCircleModels

namespace OAI

/-! Diagonal selection of actual finite-model barriers around a matched
limit end. The only small-energy data used are the saved recursive pairs. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem saved_model_barrier_of_le (harea : ExteriorCoefficientAreaTheorem) (s k : ℕ)
    (hk : s+1 ≤ k) (M : CompactScalarCircleModel G (states k).family.test) :
    let S := ((states s).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε s).saved
    ∀ l : Fin S.count,
      ∃ (v : EuclideanPlane → ℝ) (W : DeGiorgi.MemW1pWitness 2 v univ),
        Continuous v ∧ tsupport v ⊆ ball 0 (65*a) ∧
        (∀ x, v x ∈ Icc (0 : ℝ) 1) ∧
        (∀ z ∈ range (S.curve l), v (complexPlaneCoordinates.symm (M.function z)) = 1) ∧
        (∫ x, ‖W.weakGrad x‖^2) < (1/((s:ℝ)+1))^2 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hk
  exact saved_model_barrier hsupply hsard hsch hG hinf hTD ha hBa hε T harea s r M

 theorem saved_barrier_around_matched_end
    (harea : ExteriorCoefficientAreaTheorem) (hconn : IsConnected G)
    (M : ∀ n, CompactScalarCircleModel G (states n).family.test)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {F : ℂ → ℂ}
    (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
    (hlim : TendstoLocallyUniformlyOn (fun n => (M (σ n)).function) F atTop
      {z : ℂ | (z : Sphere) ∈ G})
    (Hn Jn : ℕ → ℂ ≃ₜ ℂ)
    (hnest : Antitone (fun n => closedTerminalCap (Hn n)))
    (hfrontG : ∀ n, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (Hn n)) ⊆ G)
    (hboundary : ∀ n, extendAtInfinity F '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (Hn n))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (Jn n)))
    {q : Sphere} (hq : q ∈ Gᶜ) (hend : (⋂ n, closedTerminalCap (Hn n)) = {q})
    {K : Set ℂ} (hK : IsCompact K)
    (hKend : ((↑) : ℂ → Sphere) '' K ⊆ ⋂ n, closedTerminalCap (Jn n)) (s : ℕ) :
    Nonempty (CompactBarrierData (complexPlaneCoordinates.symm '' K) (65*a) (1/((s:ℝ)+1))) := by
  let S := ((states s).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε s).saved
  obtain ⟨z,rfl⟩ := OnePoint.ne_infty_iff_exists.mp (show q ≠ OnePoint.infty from
    fun he => hq (he ▸ hinf))
  obtain ⟨l,hl⟩ := mem_iUnion.mp (S.cover hq)
  obtain ⟨J,Jm,w,hwG,hwJ,hγ,hfront,hfrontm,hγlim,hwlim,hwm,hside⟩ :=
    exists_anchored_curve_images hsch hG hconn.isPreconnected hinf
      (fun n => (M (σ n)).function) F (fun n => (M (σ n)).conformal) hF hlim
      (S.jordan l) (S.curve l) (S.regular l).2.1.continuous (S.regular l).2.1.injective
      (S.regular l).2.2.1.symm (fun t => (S.regular l).2.2.2 _ (mem_range_self t))
  have hKJ : K ⊆ jordanInterior J := by
    have ht := matched_end_subset_retained_side hF.bijOn.injOn (S.jordan l) J Hn Jn
      hnest hfrontG hboundary hside hend (mem_image_of_mem _ hl)
    intro x hx
    exact OnePoint.coe_injective.mem_set_image.mp (ht (hKend (mem_image_of_mem _ hx)))
  apply exists_compact_barrier_of_curve_images hK J Jm (F ∘ S.curve l)
    (fun n => (M (σ n)).function ∘ S.curve l) hγ hfront hfrontm hγlim hwJ hwlim hwm hKJ
  filter_upwards [hσ.tendsto_atTop.eventually_ge_atTop (s+1)] with n hn
  obtain ⟨v,W,hv,hs,_hu,hone,hE⟩ := saved_model_barrier_of_le
    hsupply hsard hsch hG hinf hTD ha hBa hε T harea s (σ n) hn (M (σ n)) l
  exact ⟨v,W,hv,hs,(fun t => hone _ (mem_range_self t)),hE⟩

end AppendingSequence
end CircleDomainRigidity

end

end OAI
