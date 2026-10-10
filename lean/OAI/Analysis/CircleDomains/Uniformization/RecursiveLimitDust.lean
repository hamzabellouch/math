import OAI.Analysis.CircleDomains.Modulus.RecursiveLimitBarriers
import OAI.Analysis.CircleDomains.Modulus.ComponentBarriers

namespace OAI

/-! Every complementary component of the actual recursive conformal limit
is a point. Matched ends and the saved finite-stage barriers supply all
geometric and energy data. -/
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

 theorem recursive_limit_component_singleton
    (harea : ExteriorCoefficientAreaTheorem) (hconn : IsConnected G)
    (M : ∀ n, CompactScalarCircleModel G (states n).family.test)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {F : ℂ → ℂ}
    (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
    (hlim : TendstoLocallyUniformlyOn (fun n => (M (σ n)).function) F atTop
      {z : ℂ | (z : Sphere) ∈ G})
    {p : Sphere} (hp : p ∈ (extendAtInfinity F '' G)ᶜ) :
    connectedComponentIn (extendAtInfinity F '' G)ᶜ p = {p} := by
  let f := extendAtInfinity F
  let E := connectedComponentIn (f '' G)ᶜ p
  have hV : IsOpen (f '' G) := hF.1.isOpen_image hG hG Subset.rfl
  have hEinfty : OnePoint.infty ∉ E := by
    intro h
    exact connectedComponentIn_subset _ _ h ⟨OnePoint.infty,hinf,rfl⟩
  have hEc : IsCompact E :=
    (IsComplementaryComponent.isCompact_isConnected ⟨p,hp,rfl⟩ hV).1
  have hEconn : IsConnected E := isConnected_connectedComponentIn_iff.mpr hp
  obtain ⟨hK,hKconn⟩ := planarPart_isCompact_isConnected hEc hEconn hEinfty
  let K := planarPart E
  have hphysc : IsCompact (complexPlaneCoordinates.symm '' K) :=
    hK.image complexPlaneCoordinates.symm.continuous
  have hphysconn : IsConnected (complexPlaneCoordinates.symm '' K) :=
    hKconn.image _ complexPlaneCoordinates.symm.continuous.continuousOn
  obtain ⟨C,J,hstrict,hcover,hd,he,hboundary,hside⟩ := exists_matched_jordan_exhaustion
    hsard hsch hG hconn hinf hF.1 hF.bijOn.injOn rfl
  obtain ⟨b,q,hq,hsource,htarget,hnest⟩ := corresponding_source_end_of_target hG
    hF.1 hF.bijOn.injOn C J hstrict hcover hd he hboundary hside hp
  have hsourcenest : Antitone (fun n => closedTerminalCap ((C n).disk (b n))) := by
    apply antitone_nat_of_succ_le
    intro n
    exact (hnest n).trans (image_mono subset_closure)
  have hfrontG (n : ℕ) : ((↑) : ℂ → Sphere) ''
      frontier (jordanInterior ((C n).disk (b n))) ⊆ G :=
    (C n).boundary_subset_domain (b n)
  have hqsingle : connectedComponentIn Gᶜ q = {q} :=
    (hTD _ (connectedComponentIn_subset _ _) isPreconnected_connectedComponentIn).eq_singleton_of_mem
      (mem_connectedComponentIn hq)
  have hsource' : (⋂ n, closedTerminalCap ((C n).disk (b n))) = {q} :=
    hsource.symm.trans hqsingle
  have hKend : ((↑) : ℂ → Sphere) '' K ⊆ ⋂ n, closedTerminalCap (J n (b n)) := by
    rintro _ ⟨z,hz,rfl⟩
    exact htarget ▸ hz
  have hdata (s : ℕ) : Nonempty (CompactBarrierData (complexPlaneCoordinates.symm '' K)
      (65*a) (1/((s:ℝ)+1))) := saved_barrier_around_matched_end
    hsupply hsard hsch hG hinf hTD ha hBa hε T harea hconn M hσ hF hlim
    (fun n => (C n).disk (b n)) (fun n => J n (b n)) hsourcenest hfrontG
    (fun n => hboundary n (b n)) hq hsource' hK hKend s
  have hsub := compact_barrier_data_subsingleton hphysc hphysconn
    (show (0:ℝ) < 65*a by positivity) (fun s => Classical.choice (hdata s))
  have hKsub : K.Subsingleton := by
    intro z hz w hw
    apply complexPlaneCoordinates.symm.injective
    exact hsub (mem_image_of_mem _ hz) (mem_image_of_mem _ hw)
  have hEsub : E.Subsingleton := by
    intro z hz w hw
    obtain ⟨z',rfl⟩ := OnePoint.ne_infty_iff_exists.mp (fun he => hEinfty (he ▸ hz))
    obtain ⟨w',rfl⟩ := OnePoint.ne_infty_iff_exists.mp (fun he => hEinfty (he ▸ hw))
    exact congrArg ((↑) : ℂ → Sphere) (hKsub hz hw)
  exact hEsub.eq_singleton_of_mem (mem_connectedComponentIn hp)

 theorem recursive_limit_complement_totallyDisconnected
    (harea : ExteriorCoefficientAreaTheorem) (hconn : IsConnected G)
    (M : ∀ n, CompactScalarCircleModel G (states n).family.test)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {F : ℂ → ℂ}
    (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
    (hlim : TendstoLocallyUniformlyOn (fun n => (M (σ n)).function) F atTop
      {z : ℂ | (z : Sphere) ∈ G}) :
    IsTotallyDisconnected (extendAtInfinity F '' G)ᶜ := by
  intro S hS hSc x hx y hy
  have hp := recursive_limit_component_singleton hsupply hsard hsch hG hinf hTD
    ha hBa hε T harea hconn M hσ hF hlim (hS hx)
  have hm := hSc.subset_connectedComponentIn hx hS hy
  exact (show y = x by simpa only [hp,mem_singleton_iff] using hm).symm

end AppendingSequence
end CircleDomainRigidity

end

end OAI
