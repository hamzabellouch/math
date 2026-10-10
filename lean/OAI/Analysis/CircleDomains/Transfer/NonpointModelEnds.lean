import OAI.Analysis.CircleDomains.Transfer.ModelProjectionFibers
import OAI.Analysis.CircleDomains.Topology.BoundedRoundDisks
import OAI.Analysis.CircleDomains.Topology.ComponentTopology

namespace OAI

/-! The actual model has only countably many nonpoint source ends. Its
nontrivial target components are deformed positive-radius round disks,
so every such component has nonempty interior. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem nonpoint_component_interior (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) {p : Sphere} (hp : p ∉ extendAtInfinity M.function '' G)
    (hnt : (connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p).Nontrivial) :
    (interior (connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p)).Nonempty := by
  let Ω := extendAtInfinity M.function '' G
  let e := M.deformation.onePointCongr
  have he : e '' M.roundDomain = Ω := M.image_eq.symm
  have hec : e '' M.roundDomainᶜ = Ωᶜ := by rw [e.image_compl, he]
  have hq : e.symm p ∈ M.roundDomainᶜ := by
    intro hh
    apply hp
    change p ∈ Ω
    rw [← he]
    exact ⟨_, hh, e.apply_symm_apply _⟩
  let K := connectedComponentIn M.roundDomainᶜ (e.symm p)
  have hKi : e '' K = connectedComponentIn Ωᶜ p := by
    simpa only [hec, e.apply_symm_apply] using e.image_connectedComponentIn hq
  rcases M.round_circle.2.2 (e.symm p) hq with hsingle | hround
  · obtain ⟨a, ha⟩ := hsingle
    change K = {a} at ha
    have hh : (connectedComponentIn Ωᶜ p).Subsingleton := by
      rw [← hKi, ha, image_singleton]
      exact subsingleton_singleton
    exact (hnt.not_subsingleton hh).elim
  · change IsRoundClosedDisk K at hround
    have hiΩ : OnePoint.infty ∈ Ω := ⟨_, hinf, rfl⟩
    have hiround : OnePoint.infty ∈ M.roundDomain := by
      rw [← he] at hiΩ
      obtain ⟨a, ha, hai⟩ := hiΩ
      have haInf : a = OnePoint.infty := by
        apply e.injective
        exact hai
      rwa [haInf] at ha
    have hiK : OnePoint.infty ∉ K := by
      intro hh
      exact (connectedComponentIn_subset _ _ hh) hiround
    obtain ⟨c, r, hr, hK⟩ := isRoundClosedDisk_eq_euclidean hround hiK
    let V := e '' (((↑) : ℂ → Sphere) '' Metric.ball c r)
    have hV : IsOpen V := e.isOpenMap _ (OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball)
    have hsub : V ⊆ connectedComponentIn Ωᶜ p := by
      rw [← hKi, hK]
      exact image_mono (image_mono Metric.ball_subset_closedBall)
    exact ⟨e (c : Sphere), interior_maximal hsub hV
      ⟨(c : Sphere), ⟨c, Metric.mem_ball_self hr, rfl⟩, rfl⟩⟩

 theorem countable_nonpoint_source_ends (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ) :
    {q : Sphere | q ∈ Gᶜ ∧ (M.projection ⁻¹' {q}).Nontrivial}.Countable := by
  classical
  let Ω := extendAtInfinity M.function '' G
  let value : Set Sphere → Sphere := fun K =>
    if h : K.Nonempty then M.projection h.choose else OnePoint.infty
  apply ((countable_complementaryComponents_with_interior Ω).image value).mono
  intro q hq
  obtain ⟨p, hp⟩ := hq.2.nonempty
  have hpq : M.projection p = q := hp
  have hpOut : p ∉ Ω := by
    rintro ⟨x, hx, rfl⟩
    exact hq.1 (by rw [← hpq, M.projection_inverse x hx]; exact hx)
  let K := connectedComponentIn Ωᶜ p
  have hK : K.Nonempty := ⟨p, mem_connectedComponentIn hpOut⟩
  have hfiber : M.projection ⁻¹' {q} = K := by
    rw [← hpq]
    exact M.projection_fiber hsard hsch hG hconn hinf hTD hpOut
  have hnt : K.Nontrivial := hfiber ▸ hq.2
  refine ⟨K, ⟨⟨p, hpOut, rfl⟩, M.nonpoint_component_interior hinf hpOut hnt⟩, ?_⟩
  change (if h : K.Nonempty then M.projection h.choose else OnePoint.infty) = q
  rw [dite_eq_left hK]
  have hh : hK.choose ∈ M.projection ⁻¹' {q} := hfiber.symm ▸ hK.choose_spec
  exact hh

 theorem exists_enumerated_source_ends (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hne : {q : ℂ | (q : Sphere) ∉ G}.Nonempty) :
    ∃ b : ℕ → ℂ, (∀ n, (b n : Sphere) ∉ G) ∧
      ∀ q : ℂ, (q : Sphere) ∉ G → (M.projection ⁻¹' {(q : Sphere)}).Nontrivial →
        ∃ n, b n = q := by
  let S := {q : ℂ | (q : Sphere) ∉ G ∧ (M.projection ⁻¹' {(q : Sphere)}).Nontrivial}
  have hS : S.Countable := by
    apply ((M.countable_nonpoint_source_ends hsard hsch hG hconn hinf hTD).image finiteCoord).mono
    intro q hq
    exact ⟨(q : Sphere), hq, finiteCoord_coe q⟩
  obtain ⟨q₀, hq₀⟩ := hne
  let b := enumerateCountable hS q₀
  refine ⟨b, ?_, ?_⟩
  · intro n
    have hb := range_enumerateCountable_subset hS q₀ (mem_range_self n)
    rcases hb with he | he
    · simpa only [b, he, mem_ofPred_eq] using hq₀
    · exact he.1
  · intro q hq hnt
    exact subset_range_enumerate hS q₀ ⟨hq, hnt⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
