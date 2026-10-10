import OAI.Analysis.CircleDomains.Uniformization.InjectivePhaseLimit
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation

namespace OAI

/-! Compact source subsets have uniformly thick images under the actual
reflected phase maps. Hurwitz excludes an omitted point converging to
an interior value of a nonconstant limit. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {m:ℕ} {C:FiniteJordanConfiguration (Fin (m+1))} {i:Fin (m+1)}

lemma PhaseCollar.uniform_image_neighborhood (P:PhaseCollar C i) {K:Set ℂ}
    (hK:IsCompact K) (hKU:K⊆symmetricCircleAnnulus P.radius) :
    ∃ε:ℝ,0<ε ∧ ∀n z,z∈K → ball (P.reflected n z) ε⊆P.reflected n '' symmetricCircleAnnulus P.radius := by
  classical
  by_contra hn
  push Not at hn
  have hex (k:ℕ) : ∃n z y,z∈K ∧ dist y (P.reflected n z)<1/((k:ℝ)+1) ∧
      ∀w∈symmetricCircleAnnulus P.radius,P.reflected n w≠y := by
    obtain ⟨n,z,hz,hy⟩ := hn (1/((k:ℝ)+1)) (by positivity)
    obtain ⟨y,hy,hno⟩ := not_subset.mp hy
    exact ⟨n,z,y,hz,hy,fun w hw he => hno ⟨w,hw,he⟩⟩
  choose n z y hz hsmall hmiss using hex
  have hzero : Tendsto (fun k => dist (y k) (P.reflected (n k) (z k))) atTop (𝓝 (0:ℝ)) :=
    squeeze_zero (fun _ => dist_nonneg) (fun k => (hsmall k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨z₀,hz₀,a,ha,hzlim⟩ := hK.tendsto_subseq hz
  obtain ⟨b,F,G,hb,hF,_,hd,_,_,_,hi⟩ := P.exists_joint_limit (fun k => n (a k))
  have hpt : Tendsto (fun k => z (a (b k))) atTop
      (𝓝[symmetricCircleAnnulus P.radius] z₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzlim.comp hb.tendsto_atTop,
      Eventually.of_forall (fun k => hKU (hz (a (b k))))⟩
  have heval := hF.tendsto_comp
    ((hd z₀ (hKU hz₀)).differentiableAt
      ((isOpen_symmetricCircleAnnulus P.radius).mem_nhds (hKU hz₀))).continuousAt.continuousWithinAt
    (hKU hz₀) hpt
  have hy : Tendsto (fun k => y (a (b k))) atTop (𝓝 (F z₀)) := by
    apply heval.congr_dist
    have ht := hzero.comp (ha.comp hb).tendsto_atTop
    change Tendsto (fun k => dist (y (a (b k)))
      (P.reflected (n (a (b k))) (z (a (b k))))) atTop (𝓝 (0:ℝ)) at ht
    exact ht.congr' (Eventually.of_forall (fun k => dist_comm _ _))
  have homit := omitted_point_limit hurwitzZeroFreeLimit (isOpen_symmetricCircleAnnulus P.radius)
    (isConnected_symmetricCircleAnnulus P.radius_gt)
    (Eventually.of_forall (fun k => ⟨P.reflected_holomorphic (n (a (b k))),hmiss (a (b k))⟩))
    hF hy (not_constant_of_injective_outer_annulus P.radius_gt hi)
  exact homit z₀ (hKU hz₀) rfl

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
