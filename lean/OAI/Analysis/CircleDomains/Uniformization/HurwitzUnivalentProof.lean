import OAI.Analysis.CircleDomains.Uniformization.HurwitzZeroFreeProof
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

namespace OAI

/-! Discharge injective-limit Hurwitz using the proved zero-free theorem
on a disk avoiding the other preimage and the analytic identity principle. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem hurwitzUnivalentLimit : HurwitzUnivalentLimit := by
  intro D F f hD hconn hF hlim hnonconstant
  have hd : DifferentiableOn ℂ f D := hlim.differentiableOn (hF.mono (fun _ h => h.1)) hD
  have ha := hd.analyticOnNhd hD
  intro x hx y hy heq
  by_contra hxy
  have hop : IsOpen (D ∩ {y}ᶜ) := hD.inter isClosed_singleton.isOpen_compl
  have hx' : x ∈ D ∩ {y}ᶜ := ⟨hx,hxy⟩
  obtain ⟨r,hr,hrD⟩ := Metric.isOpen_iff.mp hop x hx'
  have hbD : ball x r ⊆ D := fun z hz => (hrD hz).1
  have hseq : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (fun z => F n z-F n y) (ball x r) ∧
        ∀ z ∈ ball x r, F n z-F n y ≠ 0 := by
    filter_upwards [hF] with n hn
    refine ⟨(hn.1.mono hbD).sub_const (F n y),?_⟩
    intro z hz he
    have hh : z = y := hn.2 (hbD hz) hy (sub_eq_zero.mp he)
    exact (hrD hz).2 hh
  have hconst : TendstoLocallyUniformlyOn (fun n (_ : ℂ) => F n y)
      (fun _ => f y) atTop (ball x r) :=
    ((hlim.tendsto_at hy).tendstoUniformlyOn_const (ball x r)).tendstoLocallyUniformlyOn
  have hsub : TendstoLocallyUniformlyOn (fun n z => F n z-F n y)
      (fun z => f z-f y) atTop (ball x r) := (hlim.mono hbD).sub hconst
  rcases hurwitzZeroFreeLimit (ball x r) (fun n z => F n z-F n y)
    (fun z => f z-f y) isOpen_ball (Metric.isConnected_ball hr) hseq hsub with hz | hn
  · have hzero : (fun z => f z-f y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [ball_mem_nhds x hr] with z hzr
      exact hz z hzr
    have hall := (ha.sub analyticOnNhd_const).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hconn.isPreconnected hx hzero
    exact hnonconstant ⟨f y,fun z hz => sub_eq_zero.mp (hall hz)⟩
  · exact hn x (mem_ball_self hr) (sub_eq_zero.mpr heq)

end CircleDomainRigidity

end

end OAI
