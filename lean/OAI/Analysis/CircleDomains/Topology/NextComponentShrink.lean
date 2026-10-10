import OAI.Analysis.CircleDomains.Topology.ControlledComponentShrink
import OAI.Analysis.CircleDomains.Topology.HomeomorphComponentTransport

namespace OAI

/-! Initial and successor stages for component shrinking. Every stage
is an actual plane homeomorphism; the successor controls both maps and
the quotient-valued inverse observations. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

def ComponentImageSmall {Y : Type*} [PseudoMetricSpace Y]
    (F : Set ℂ) (p : ℂ → Y) (H : ℂ ≃ₜ ℂ) (r : ℝ) : Prop :=
  ∀ x ∈ H '' F, ∀ y ∈ connectedComponentIn (H '' F) x, dist (p y) (p x)<r

lemma componentImageSmall_of_shrink {Y : Type*} [PseudoMetricSpace Y]
    {F : Set ℂ} (p : ℂ → Y) (H : ℂ ≃ₜ ℂ) {r : ℝ}
    (h : ∀ x ∈ F, ∀ y ∈ connectedComponentIn F x,
      ∀ z ∈ connectedComponentIn F x, dist (p (H y)) (p (H z))<r) :
    ComponentImageSmall F p H r := by
  intro x hx y hy
  obtain ⟨a,ha,rfl⟩ := hx
  rw [← homeomorph_image_componentIn H ha] at hy
  obtain ⟨b,hb,rfl⟩ := hy
  exact h a ha b hb a (mem_connectedComponentIn ha)

lemma exists_initial_component_shrinker
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {Y : Type*} [PseudoMetricSpace Y]
    {F : Set ℂ} (hF : IsCompact F) (hFc : IsConnected Fᶜ)
    (p : ℂ → Y) (hp : Continuous p) {r : ℝ} (hr : 0<r) :
    ∃ H : ℂ ≃ₜ ℂ, ComponentImageSmall F p H r := by
  obtain ⟨n,H,hcover,hd,hcurves⟩ := exists_componentwise_jordan_cover hsard hsch hF hFc
    (fun _ => univ) (fun _ => isOpen_univ) (fun _ => subset_univ _)
  obtain ⟨T,_,_,hsmall⟩ := exists_finite_jordan_mapped_shrink H hF hd hcover
    (fun i => (hcurves i).1.symm) p hp hr
  exact ⟨T,componentImageSmall_of_shrink p T hsmall⟩

lemma exists_next_component_shrinker
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {Y Z : Type*} [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    {F : Set ℂ} (hF : IsCompact F) (hFc : IsConnected Fᶜ)
    (p : ℂ → Y) (q : ℂ → Z) (hp : Continuous p) (hq : Continuous q)
    (hconstant : ∀ x ∈ F, ∀ y ∈ connectedComponentIn F x, q y=q x)
    (H : ℂ ≃ₜ ℂ) {δ η ε : ℝ} (hδ : 0<δ) (hη : 0<η) (hε : 0<ε)
    (hsmall : ComponentImageSmall F p H (δ/2)) :
    ∃ K : ℂ ≃ₜ ℂ, ComponentImageSmall F p K ε ∧
      (∀ x, dist (p (K x)) (p (H x))<δ) ∧
      ∀ x, dist (q (K.symm x)) (q (H.symm x))<η := by
  have hHF : IsCompact (H '' F) := hF.image H.continuous
  have hHFc : IsConnected (H '' F)ᶜ := by
    rw [← H.image_compl]
    exact hFc.image H H.continuous.continuousOn
  obtain ⟨T,_B,_hB,_hfix,hpbound,hqbound,hnew⟩ := exists_controlled_component_shrink
    hsard hsch hHF hHFc p (q ∘ H.symm) hp (hq.comp H.symm.continuous)
    hδ hη hε hsmall (component_constant_transport H q hconstant)
  refine ⟨H.trans T,?_,?_,?_⟩
  · have he : (H.trans T) '' F = T '' (H '' F) := by
      rw [image_image]
      rfl
    change ∀ x ∈ (H.trans T) '' F,
      ∀ y ∈ connectedComponentIn ((H.trans T) '' F) x, dist (p y) (p x)<ε
    rw [he]
    exact componentImageSmall_of_shrink p T hnew
  · intro x
    exact hpbound (H x)
  · intro x
    exact hqbound x

end CircleDomainRigidity

end

end OAI
