import OAI.Geometry.SurfaceImmersion.Whitney.CalibratedCollarFamily
import OAI.Geometry.SurfaceImmersion.Primitive.ConstructedSurfaceLoop

namespace OAI

/-! Supported analytic loops with a small-angle collar fixed before the
interior compact set and its large turn derivative are selected. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates SurfaceJetCoordinates
open VelocityFrame NormalFrame TransverseSmallFunction

theorem constructed_surface_collar_family {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {C₀ L U Ω : Set CollarVelocity.JetBase}
    (hC₀ : IsCompact C₀) (hL : IsCompact L) (hCL : C₀ ⊆ L)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hCU : C₀ ⊆ U) (hUΩ : U ⊆ Ω) (hLΩ : L ⊆ Ω)
    {e₁ e₂ : CollarVelocity.JetBase → Vec} {a : CollarVelocity.JetBase → ℝ}
    (he₁ : ContDiffOn ℝ ∞ e₁ Ω) (he₂ : ContDiffOn ℝ ∞ e₂ Ω)
    (ha : ContDiffOn ℝ ∞ a Ω) (hD : ∀ j ∈ Ω, gramDet (j.2 1) (j.2 4) ≠ 0)
    (hframe : ∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
      j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0)
    (hcollar : ∀ j ∈ U, jetNormal j ≠ 0 ∧ e₁ j = normalize (jetNormal j))
    (hn : ∀ j ∈ Ω, jetNormal j ≠ 0 ∨ a j ≠ 0)
    (hap : ∀ j ∈ L \ C₀, 0 < a j) (haC : ∀ j ∈ C₀, a j = 0) :
    ∃ W : Set CollarVelocity.JetBase, IsOpen W ∧ C₀ ⊆ W ∧ W ⊆ U ∧
      ∀ ε : ℝ, 0 < ε → ∃ V : Set CollarVelocity.JetBase, IsOpen V ∧ C₀ ⊆ V ∧ V ⊆ W ∧
      ∀ (K O P : Set SmallModes.Base), IsCompact K → MapsTo (CollarVelocity.jetSection F) K L →
        IsOpen O → K ⊆ O → (∀ j ∈ C₀, j.1 ∉ closure O) → P.Finite → P ⊆ K →
        (∀ p ∈ K \ P, ∃ N : Set SmallModes.Base, IsOpen N ∧ p ∈ N ∧
          ∃ f : SmallModes.Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
            fderiv ℝ f p (0,1) ≠ 0) →
      ∀ T : ℝ, ∃ Z : TopologicalSpace.Opens CollarVelocity.JetBase,
        L ⊆ Z ∧ (Z : Set CollarVelocity.JetBase) ⊆ Ω ∧
        ∃ l : Loop (jetDomain Z), (∀ J, l.amplitude J = a (decode J)) ∧
          (∃ W' : Set CollarVelocity.JetBase, IsOpen W' ∧ C₀ ⊆ W' ∧ W' ⊆ W ∧
            ∀ J, decode J ∈ W' → a (decode J) = 0 → ∀ t, l.velocity (J,t) = normal J) ∧
          ∃ α : CollarVelocity.JetBase × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
            (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
            (∀ J t, l.velocity (J,t) = velocityRadius (normal J) (a (decode J)) •
              direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t))) ∧
            (∀ j ∈ V, ∀ t, |α (j,t)| < ε) ∧
            ∃ τ : SmallModes.Base → ℝ,
              (∀ x ∈ K, ∀ θ ∈ Ico (0 : ℝ) 1,
                deriv (fun t => α (CollarVelocity.jetSection F x,t)) θ = 0 ↔ θ = 0 ∨ θ = τ x) ∧
              ∀ x ∈ K, T < fderiv ℝ (fun y => α (CollarVelocity.jetSection F y,0)) x (0,1) ∧
                T < fderiv ℝ (fun y => α (CollarVelocity.jetSection F y,τ x)) x (0,1) := by
  let R := fun j => velocityRadius (jetNormal j) (a j)
  let u := fun j => jetNormal j ⬝ᵥ e₁ j
  let w := fun j => jetNormal j ⬝ᵥ e₂ j
  have hv := jetNormal_smooth hD
  have hR := velocityRadius_smoothOn hv ha hn
  have hRp : ∀ j ∈ Ω, 0 < R j := fun j hj => velocityRadius_pos (hn j hj)
  have hvperp (j : CollarVelocity.JetBase) (hj : j ∈ Ω) :
      j.2 1 ⬝ᵥ jetNormal j = 0 ∧ j.2 4 ⬝ᵥ jetNormal j = 0 :=
    realNormalPart_perp _ _ _ (hD j hj)
  have hreconstruct (j : CollarVelocity.JetBase) (hj : j ∈ Ω) :
      planeLift (e₁ j) (e₂ j) (VelocityFrame.planeCoordinates (e₁ j) (e₂ j) (jetNormal j)) = jetNormal j := by
    obtain ⟨h1,h2,h12,hy1,hc1,hy2,hc2⟩ := hframe j hj
    exact plane_coordinates_reconstruct (hD j hj) h1 h2 h12 hy1 hy2 hc1 hc2
      (hvperp j hj).1 (hvperp j hj).2
  have hquad (j : CollarVelocity.JetBase) (hj : j ∈ Ω) :
      R j^2 = u j^2+w j^2+a j^2 := by
    obtain ⟨h1,h2,h12,hy1,hc1,hy2,hc2⟩ := hframe j hj
    have hlen := plane_coordinates_length (hD j hj) h1 h2 h12 hy1 hy2 hc1 hc2
      (hvperp j hj).1 (hvperp j hj).2
    change velocityRadius (jetNormal j) (a j)^2 = _
    rw [velocityRadius_sq,← hlen]
  have huc (j : CollarVelocity.JetBase) (hj : j ∈ U) : 0 < u j ∧ w j = 0 :=
    collar_coordinates (hcollar j hj).1 (hcollar j hj).2 (hframe j (hUΩ hj)).2.2.1
  obtain ⟨W,hW,hCW,hWU,hfamily⟩ := CollarVelocity.calibrated_jet_collar_family hF hC₀ hL hCL
    hU hΩ hCU hUΩ hLΩ hR (dot_smoothOn hv he₁) (dot_smoothOn hv he₂) ha hRp hquad
    (fun j hj => (huc j hj).1) (fun j hj => (huc j hj).2) hap haC
  refine ⟨W,hW,hCW,hWU,?_⟩
  intro ε hε
  obtain ⟨V,hV,hCV,hVW,hfamily'⟩ := hfamily ε hε
  refine ⟨V,hV,hCV,hVW,?_⟩
  intro K O P hK hKL hO hKO hCO hP hPK hlocal T
  obtain ⟨Z,hZ,hLZ,hZΩ,α,hα,hper,hmean,hsmall,hzero,τ,hturn,hlarge⟩ :=
    hfamily' K O P hK hKL hO hKO hCO hP hPK hlocal T
  let V₀ : CollarVelocity.JetBase × ℝ → Vec := fun z =>
    R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)
  have hVs : ContDiffOn ℝ ∞ V₀ (Z ×ˢ univ) :=
    ((hR.mono hZΩ).comp contDiffOn_fst (fun z hz => hz.1)).smul
      ((hα.cos.smul ((he₁.mono hZΩ).comp contDiffOn_fst (fun z hz => hz.1))).add
        (hα.sin.smul ((he₂.mono hZΩ).comp contDiffOn_fst (fun z hz => hz.1))))
  have hVy : ∀ j ∈ Z, ∀ t, j.2 1 ⬝ᵥ V₀ (j,t) = 0 := by
    intro j hj t
    simp [V₀,direction,dotProduct_smul,dotProduct_add,(hframe j (hZΩ hj)).2.2.2.1,
      (hframe j (hZΩ hj)).2.2.2.2.2.1]
  have hVc : ∀ j ∈ Z, ∀ t, j.2 4 ⬝ᵥ V₀ (j,t) = 0 := by
    intro j hj t
    simp [V₀,direction,dotProduct_smul,dotProduct_add,(hframe j (hZΩ hj)).2.2.2.2.1,
      (hframe j (hZΩ hj)).2.2.2.2.2.2]
  have hlen : ∀ j ∈ Z, ∀ t, V₀ (j,t) ⬝ᵥ V₀ (j,t) = jetNormal j ⬝ᵥ jetNormal j + a j^2 := by
    intro j hj t
    obtain ⟨h1,h2,h12,_,_,_,_⟩ := hframe j (hZΩ hj)
    exact (planeLift_scaled_length (p := ![Real.cos (α (j,t)),Real.sin (α (j,t))])
      h1 h2 h12 (Real.cos_sq_add_sin_sq (α (j,t))) (R j)).trans (velocityRadius_sq _ _)
  have hmean' : ∀ j ∈ Z, (∫ t in 0..1, V₀ (j,t)) = jetNormal j := by
    intro j hj
    have hp : Continuous (fun t => ![Real.cos (α (j,t)),Real.sin (α (j,t))]) := by
      apply continuous_pi
      intro i
      fin_cases i
      · exact Real.continuous_cos.comp (LocalPeriodicCalculus.smooth_slice hZ hα hj).continuous
      · exact Real.continuous_sin.comp (LocalPeriodicCalculus.smooth_slice hZ hα hj).continuous
    exact (planeLift_mean (e₁ j) (e₂ j) (R j) hp (hmean j hj)).trans
      (scaled_coordinates_reconstruct (hRp j (hZΩ hj)).ne' (hreconstruct j (hZΩ hj)))
  let Z' : TopologicalSpace.Opens CollarVelocity.JetBase := ⟨Z,hZ⟩
  have hVp : ∀ j ∈ Z, Function.Periodic (fun t => V₀ (j,t)) 1 := by
    intro j hj
    have he : (fun t => V₀ (j,t)) =
        (fun θ => R j • direction (e₁ j) (e₂ j) θ) ∘ (fun t => α (j,t)) := rfl
    rw [he]
    exact (hper j hj).comp _
  let l : Loop (jetDomain Z') := Loop.ofGeometric (ha.mono hZΩ) hVs
    hVp (fun j hj => hD j (hZΩ hj))
    (fun j hj => hn j (hZΩ hj)) hVy hVc hlen hmean'
  refine ⟨Z',hLZ,hZΩ,l,(fun _ => rfl),?_,α,hα,hper,(fun _ _ => rfl),hsmall,τ,hturn,hlarge⟩
  obtain ⟨W',hW',hCW',hW'W,hzero'⟩ := hzero
  refine ⟨W',hW',hCW',hW'W,?_⟩
  intro J hJ haz t
  change R (decode J) • direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t)) = _
  rw [hzero' (decode J) hJ haz t]
  simp only [direction,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,add_zero]
  change velocityRadius (jetNormal (decode J)) (a (decode J)) • e₁ (decode J) = _
  rw [haz,(hcollar (decode J) (hWU (hW'W hJ))).2]
  change velocityRadius (jetNormal (decode J)) 0 • normalize (jetNormal (decode J)) =
    jetNormal (decode J)
  simpa only [velocityRadius,zero_pow (by decide : 2 ≠ 0),add_zero] using
    norm_smul_normalize (hcollar (decode J) (hWU (hW'W hJ))).1

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
