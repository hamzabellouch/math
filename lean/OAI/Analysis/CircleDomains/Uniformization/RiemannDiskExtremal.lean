import OAI.Analysis.CircleDomains.Uniformization.RiemannDiskSeed
import OAI.Analysis.CircleDomains.Uniformization.MontelProof
import OAI.Analysis.CircleDomains.Uniformization.HurwitzUnivalentProof
import Mathlib.Topology.Order.IsLUB

namespace OAI

/-! The normalized derivative extremum is attained by an actual univalent
map, using the already proved normal-family and Hurwitz theorems. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_extremal_normalized_disk_embedding {U : Set ℂ}
    (hU : IsOpen U) (hc : IsConnected U) {a : ℂ} (ha : a ∈ U)
    (hseed : ∃ f : ℂ → ℂ, NormalizedDiskEmbedding U a f ∧ deriv f a ≠ 0) :
    ∃ f : ℂ → ℂ, NormalizedDiskEmbedding U a f ∧ deriv f a ≠ 0 ∧
      ∀ g : ℂ → ℂ, NormalizedDiskEmbedding U a g → ‖deriv g a‖≤‖deriv f a‖ := by
  let S : Set ℝ := {t | ∃ f : ℂ → ℂ, NormalizedDiskEmbedding U a f ∧ ‖deriv f a‖=t}
  obtain ⟨f₀,h₀,hd₀⟩ := hseed
  have hS : S.Nonempty := ⟨‖deriv f₀ a‖,f₀,h₀,rfl⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU a ha
  have hbound : BddAbove S := by
    refine ⟨1/r,?_⟩
    rintro t ⟨f,hf,rfl⟩
    exact normalized_disk_derivative_bound hf hr hball
  have hpos : 0<sSup S := lt_of_lt_of_le (norm_pos_iff.mpr hd₀)
    (le_csSup hbound ⟨f₀,h₀,rfl⟩)
  obtain ⟨u,_hu,hu,huS⟩ := exists_seq_tendsto_sSup hS hbound
  choose F hF hderiv using huS
  obtain ⟨s,f,hs,hlim⟩ := montelExhaustion (fun _ => U) F (fun _ => hU)
    monotone_const (fun n => (hF n).holomorphic) (by
      intro K _hK hKU
      refine ⟨1,?_⟩
      intro n z _hz hzU
      exact (mem_ball_zero_iff.mp ((hF n).mapsTo hzU)).le)
  simp only [iUnion_const] at hlim
  have hhol : DifferentiableOn ℂ f U := hlim.differentiableOn
    (Eventually.of_forall (fun n => (hF (s n)).holomorphic)) hU
  have hderivlim := (hlim.deriv
    (Eventually.of_forall (fun n => (hF (s n)).holomorphic)) hU).tendsto_at ha
  have hext : ‖deriv f a‖=sSup S := by
    apply tendsto_nhds_unique hderivlim.norm
    have hseq : (fun n => ‖deriv (F (s n)) a‖) = u ∘ s := by
      funext n
      exact hderiv (s n)
    change Tendsto (fun n => ‖deriv (F (s n)) a‖) atTop (𝓝 (sSup S))
    rw [hseq]
    exact hu.comp hs.tendsto_atTop
  have hdn : deriv f a ≠ 0 := norm_pos_iff.mp (by rw [hext]; exact hpos)
  have hnotconst : ¬∃ c : ℂ, ∀ z ∈ U, f z=c := by
    rintro ⟨c,hc⟩
    have he : f =ᶠ[𝓝 a] (fun _ => c) := by
      filter_upwards [hU.mem_nhds ha] with z hz
      exact hc z hz
    exact hdn (by rw [he.deriv_eq,deriv_const])
  have hfa : f a=0 := by
    have h := hlim.tendsto_at ha
    have he : (fun n => F (s n) a) = (fun _ => (0:ℂ)) := by
      funext n
      exact (hF (s n)).at_base
    rw [he] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hnorm (z : ℂ) (hz : z ∈ U) : ‖f z‖≤1 := by
    apply le_of_tendsto (hlim.tendsto_at hz).norm
    exact Eventually.of_forall (fun n => (mem_ball_zero_iff.mp ((hF (s n)).mapsTo hz)).le)
  have hmap : MapsTo f U (ball 0 1) := by
    intro z hz
    apply mem_ball_zero_iff.mpr
    by_contra hh
    have he : ‖f z‖=1 := le_antisymm (hnorm z hz) (le_of_not_gt hh)
    have hm : IsMaxOn (norm ∘ f) U z := fun w hw => (hnorm w hw).trans he.ge
    have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
      hc.isPreconnected hU hhol hz hm
    have heq := hconst ha
    rw [hfa] at heq
    change (0 : ℂ)=f z at heq
    have hhzero : ‖f z‖=0 := by rw [← heq]; simp
    linarith
  refine ⟨f,⟨hhol,?_,hmap,hfa⟩,hdn,?_⟩
  · exact hurwitzUnivalentLimit U (fun n => F (s n)) f hU hc
      (Eventually.of_forall (fun n => ⟨(hF (s n)).holomorphic,(hF (s n)).injective⟩))
      hlim hnotconst
  · intro g hg
    rw [hext]
    exact le_csSup hbound ⟨g,hg,rfl⟩

end CircleDomainRigidity

end

end OAI
