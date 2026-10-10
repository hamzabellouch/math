import OAI.Geometry.SurfaceImmersion.Primitive.ActualSupportedSurfaceLoop

namespace OAI

/-! The preferred frame and its domain are fixed before prescribing the
transverse turn size in the actual supported loop construction. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame PhaseGeometry SurfaceJetCoordinates

theorem actual_supported_surface_loop_fixed_frame {F n : Base → Vec} {a : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (ha : ContDiff ℝ ∞ a)
    {T U K P : Set Base} (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
    (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ F p))
    (hN : ∀ p ∈ U, coordDeriv dx F p ⬝ᵥ n p = 0 ∧ coordDeriv dy F p ⬝ᵥ n p = 0 ∧
      n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < coordinateMetricHessian (inducedCoordinateMetric F) Prod.fst p dy dy)
    (haT : ∀ p ∈ T, 0 ≤ a p)
    (hboundary : ∀ p ∈ T, a p = 0 → realSecondForm F dy dy p ≠ 0 ∧
      normalize (realSecondForm F dy dy p) ≠ -n p)
    (hK : IsCompact K) (hKT : K ⊆ T) (haK : ∀ p ∈ K, 0 < a p)
    (hP : P.Finite) (hPK : P ⊆ K)
    (hlocal : ∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
        fderiv ℝ f p (0,1) ≠ 0) :
    ∃ Ω : TopologicalSpace.Opens GeometricJet, CollarVelocity.jetSection F '' T ⊆ Ω ∧
      (Ω : Set GeometricJet) ⊆ supportedJetDomain U n a ∧
      ∃ e₁ e₂ : GeometricJet → Vec,
        ContDiffOn ℝ ∞ e₁ Ω ∧ ContDiffOn ℝ ∞ e₂ Ω ∧
        (∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
          j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0) ∧
      ∀ turn : ℝ, ∃ Z : TopologicalSpace.Opens GeometricJet,
        CollarVelocity.jetSection F '' T ⊆ Z ∧ (Z : Set GeometricJet) ⊆ Ω ∧
      ∃ l : Loop (jetDomain Z),
        (∀ J, l.amplitude J = a (decode J).1) ∧
        (∃ W : Set GeometricJet, IsOpen W ∧
          CollarVelocity.jetSection F '' {p ∈ T | a p = 0} ⊆ W ∧
          ∀ J, decode J ∈ W → a (decode J).1 = 0 → ∀ t, l.velocity (J,t) = normal J) ∧
        ∃ α : GeometricJet × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
          (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
          (∀ J t, l.velocity (J,t) = velocityRadius (normal J) (a (decode J).1) •
            direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t))) ∧
          ∃ τ : Base → ℝ,
            (∀ x ∈ K, ∀ θ ∈ Ico (0 : ℝ) 1,
              deriv (fun t => α (CollarVelocity.jetSection F x,t)) θ = 0 ↔ θ = 0 ∨ θ = τ x) ∧
            ∀ x ∈ K,
              turn < fderiv ℝ (fun y => α (CollarVelocity.jetSection F y,0)) x dy ∧
              turn < fderiv ℝ (fun y => α (CollarVelocity.jetSection F y,τ x)) x dy := by
  let C₀ : Set Base := {p ∈ T | a p = 0}
  have hC : IsCompact C₀ := hT.inter_right (isClosed_eq ha.continuous continuous_const)
  have hCU : C₀ ⊆ U := fun _ hp => hTU hp.1
  obtain ⟨W,hW,hCW,hWΩ,e₁,e₂,he₁,he₂,hframe,hcollar⟩ := exists_preferred_jet_frame
    hF hU hn hC hCU hI hN hHess (fun p hp => hboundary p hp.1 hp.2)
  let Ω := supportedJetDomain U n a
  have hΩ : IsOpen Ω := supportedJetDomain_open hU hn ha
  let L := CollarVelocity.jetSection F '' T
  let Cj := CollarVelocity.jetSection F '' C₀
  have hL : IsCompact L := hT.image (CollarVelocity.jetSection_smooth hF).continuous
  have hCj : IsCompact Cj := hC.image (CollarVelocity.jetSection_smooth hF).continuous
  have hLΩ : L ⊆ Ω := by
    rintro _ ⟨p,hp,rfl⟩
    exact actual_jet_mem_supported_domain hF (hTU hp) (hI p (hTU hp))
      (hN p (hTU hp)) (hHess p (hTU hp)) (fun h => (hboundary p hp h).1)
  obtain ⟨O,hO,hKO,_,hOpos⟩ := CollarVelocity.compact_open_thickening hK
    (isOpen_lt continuous_const ha.continuous) haK
  let V : Set GeometricJet := W ∩ ((Prod.fst ⁻¹' closure O)ᶜ ∩ Ω)
  have hV : IsOpen V := hW.inter ((isClosed_closure.preimage continuous_fst).isOpen_compl.inter hΩ)
  have hCV : Cj ⊆ V := by
    rintro _ ⟨p,hp,rfl⟩
    refine ⟨hCW (mem_image_of_mem _ hp),?_,hLΩ (mem_image_of_mem _ hp.1)⟩
    change p ∉ closure O
    intro hx
    have := hOpos hx
    change 0 < a p at this
    rw [hp.2] at this
    exact lt_irrefl _ this
  have hAmp : ∀ j ∈ L \ Cj, 0 < a j.1 := by
    rintro j ⟨⟨p,hp,rfl⟩,hj⟩
    apply lt_of_le_of_ne (haT p hp)
    intro hz
    exact hj (mem_image_of_mem _ ⟨hp,hz.symm⟩)
  have hCL : Cj ⊆ L := image_mono (fun _ hp => hp.1)
  have hKL : MapsTo (CollarVelocity.jetSection F) K L :=
    fun _ hx => mem_image_of_mem _ (hKT hx)
  have hVΩ : V ⊆ Ω := fun _ hj => hj.2.2
  have he1 : ContDiffOn ℝ ∞ e₁ Ω := he₁.mono (fun _ hj => hj.1)
  have he2 : ContDiffOn ℝ ∞ e₂ Ω := he₂.mono (fun _ hj => hj.1)
  have hfr := fun j (hj : j ∈ Ω) => hframe j hj.1
  refine ⟨⟨Ω,hΩ⟩,hLΩ,Subset.rfl,e₁,e₂,he1,he2,hfr,?_⟩
  intro turn
  obtain ⟨Z,hLZ,hZΩ,l,hl,hzero,α,hα,hper,hvel,τ,hturn,hlarge⟩ := constructed_surface_loop
    hF hCj hK hL hCL hKL hO hKO
    (fun j hj hjo => hj.2.1 (subset_closure hjo))
    hV hΩ hCV hVΩ hLΩ hP hPK hlocal he1 he2
    (ha.comp contDiff_fst).contDiffOn
    (fun j hj => preferredJetDomain_velocity_gram hj.1) hfr
    (fun j hj => hcollar j hj.1) (fun j hj => hj.2) hAmp turn
  refine ⟨Z,hLZ,hZΩ,l,hl,?_,α,hα,hper,hvel,τ,hturn,hlarge⟩
  obtain ⟨W',hW',hCW',_,hzero'⟩ := hzero
  exact ⟨W',hW',hCW',hzero'⟩

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
