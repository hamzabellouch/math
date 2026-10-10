import OAI.Analysis.CircleDomains.Sobolev.HolomorphicInjOnDerivative
import OAI.Analysis.CircleDomains.Topology.SymmetricAnnulusConnected

namespace OAI

/-! An injective analytic collar with exact circle preimage maps its
entire middle circle onto the target circle. -/
open Set Function Filter Metric Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma analytic_circle_image_eq {U:Set ℂ} {F:ℂ→ℂ} {a:ℂ} {r:ℝ}
    (hU:IsOpen U) (hu:sphere (0:ℂ) 1⊆U)
    (hd:DifferentiableOn ℂ F U) (hi:InjOn F U) (hr:0≤r)
    (hb:∀z∈U,‖F z-a‖=r ↔ ‖z‖=1) : F '' sphere (0:ℂ) 1=sphere a r := by
  let S := sphere a r
  let K := F '' sphere (0:ℂ) 1
  have hKS : K⊆S := by
    rintro _ ⟨z,hz,rfl⟩
    exact mem_sphere_iff_norm.mpr ((hb z (hu hz)).mpr (mem_sphere_zero_iff_norm.mp hz))
  have hKc : IsCompact K := (isCompact_sphere (0:ℂ) 1).image_of_continuousOn
    (hd.continuousOn.mono hu)
  have hopen : IsOpen (F '' U) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨z,hz,rfl⟩
    rw [←holomorphicInjOn_map_nhds hU hd hi hz]
    exact image_mem_map (hU.mem_nhds hz)
  have he : ((↑):S→ℂ) ⁻¹' K=((↑):S→ℂ) ⁻¹' (F '' U) := by
    ext y
    constructor
    · intro hy
      exact image_mono hu hy
    · rintro ⟨z,hz,he⟩
      refine ⟨z,?_,he⟩
      apply mem_sphere_zero_iff_norm.mpr
      apply (hb z hz).mp
      rw [he]
      exact mem_sphere_iff_norm.mp y.property
  have hopenK : IsOpen (((↑):S→ℂ) ⁻¹' K) := by
    rw [he]
    exact hopen.preimage continuous_subtype_val
  have hclosedK : IsClosed (((↑):S→ℂ) ⁻¹' K) :=
    hKc.isClosed.preimage continuous_subtype_val
  have hconn : IsConnected S :=
    isConnected_sphere (by rw [Complex.rank_real_complex];norm_num) a hr
  have : PreconnectedSpace S := Subtype.preconnectedSpace hconn.isPreconnected
  have hn : ((((↑):S→ℂ) ⁻¹' K):Set S).Nonempty := by
    have hz : (1:ℂ)∈sphere (0:ℂ) 1 := by simp
    have hk : F 1∈K := mem_image_of_mem F hz
    exact ⟨⟨F 1,hKS hk⟩,hk⟩
  have hall : (((↑):S→ℂ) ⁻¹' K)=univ :=
    (IsClopen.eq_univ ⟨hclosedK,hopenK⟩ hn)
  apply Subset.antisymm hKS
  intro y hy
  have : (⟨y,hy⟩:S)∈(((↑):S→ℂ) ⁻¹' K) := by rw [hall];trivial
  exact this

end CircleDomainRigidity

end

end OAI
