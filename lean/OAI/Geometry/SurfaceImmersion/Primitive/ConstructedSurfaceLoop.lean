import OAI.Geometry.SurfaceImmersion.Primitive.JetLoopPullback

namespace OAI

/-! Construct the analytic surface-loop input from the geometric frame and
the controlled angle; no periodic velocity family is assumed here. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates SurfaceJetCoordinates
open VelocityFrame NormalFrame TransverseSmallFunction

def jetNormal (j : CollarVelocity.JetBase) : Vec :=
  realNormalPart (j.2 1) (j.2 4) (j.2 0)

lemma jetSlot_smooth (i : Fin 5) :
    ContDiff ℝ ∞ (fun j : CollarVelocity.JetBase => j.2 i) :=
  (ContinuousLinearMap.proj i : RealTwoJet →L[ℝ] Vec).contDiff.comp contDiff_snd

lemma jetNormal_smooth {Ω : Set CollarVelocity.JetBase}
    (hD : ∀ j ∈ Ω, gramDet (j.2 1) (j.2 4) ≠ 0) :
    ContDiffOn ℝ ∞ jetNormal Ω := by
  intro j hj
  exact (contDiffAt_realNormalPart (jetSlot_smooth 1).contDiffAt
    (jetSlot_smooth 4).contDiffAt (jetSlot_smooth 0).contDiffAt (hD j hj)).contDiffWithinAt

theorem constructed_surface_loop {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {K O P : Set SmallModes.Base} {C₀ L U Ω : Set CollarVelocity.JetBase}
    (hC₀ : IsCompact C₀) (hK : IsCompact K) (hL : IsCompact L)
    (hCL : C₀ ⊆ L) (hKL : MapsTo (CollarVelocity.jetSection F) K L)
    (hO : IsOpen O) (hKO : K ⊆ O) (hOU : ∀ j ∈ U, j.1 ∉ O)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hCU : C₀ ⊆ U) (hUΩ : U ⊆ Ω) (hLΩ : L ⊆ Ω)
    (hP : P.Finite) (hPK : P ⊆ K)
    (hlocal : ∀ p ∈ K \ P, ∃ N : Set SmallModes.Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : SmallModes.Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
        fderiv ℝ f p (0, 1) ≠ 0)
    {e₁ e₂ : CollarVelocity.JetBase → Vec} {a : CollarVelocity.JetBase → ℝ}
    (he₁ : ContDiffOn ℝ ∞ e₁ Ω) (he₂ : ContDiffOn ℝ ∞ e₂ Ω)
    (ha : ContDiffOn ℝ ∞ a Ω) (hD : ∀ j ∈ Ω, gramDet (j.2 1) (j.2 4) ≠ 0)
    (hframe : ∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
      j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0)
    (hcollar : ∀ j ∈ U, jetNormal j ≠ 0 ∧ e₁ j = normalize (jetNormal j))
    (hn : ∀ j ∈ Ω, jetNormal j ≠ 0 ∨ a j ≠ 0)
    (hap : ∀ j ∈ L \ C₀, 0 < a j) (T : ℝ) :
    ∃ Z : TopologicalSpace.Opens CollarVelocity.JetBase, L ⊆ Z ∧ (Z : Set _) ⊆ Ω ∧
      ∃ l : Loop (jetDomain Z), (∀ J, l.amplitude J = a (decode J)) ∧
        (∃ W : Set CollarVelocity.JetBase, IsOpen W ∧ C₀ ⊆ W ∧ W ⊆ U ∧
          ∀ J, decode J ∈ W → a (decode J) = 0 → ∀ t, l.velocity (J, t) = normal J) ∧
        ∃ α : CollarVelocity.JetBase × ℝ → ℝ,
          ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
          (∀ j ∈ Z, Function.Periodic (fun t => α (j, t)) 1) ∧
          (∀ J t, l.velocity (J, t) = velocityRadius (normal J) (a (decode J)) •
            direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J, t))) ∧
          ∃ τ : SmallModes.Base → ℝ,
            (∀ x ∈ K, ∀ θ ∈ Ico (0 : ℝ) 1,
              deriv (fun t => α (CollarVelocity.jetSection F x, t)) θ = 0 ↔
                θ = 0 ∨ θ = τ x) ∧
            ∀ x ∈ K,
              T < fderiv ℝ (fun y => α (CollarVelocity.jetSection F y, 0)) x (0, 1) ∧
              T < fderiv ℝ (fun y => α (CollarVelocity.jetSection F y, τ x)) x (0, 1) := by
  obtain ⟨Z, hZ, hLZ, hZΩ, α, hα, hper, V, hVs, hV, hm, hlen, _,
    ⟨W, hW, hCW, hWU, hzero⟩, τ, hturn, hlarge⟩ := geometric_jet_velocity (X := fun j => j.2 0) (Y := fun j => j.2 1)
      (C := fun j => j.2 4) (v := jetNormal) hF
      hC₀ hK hL hCL hKL hO hKO hOU hU hΩ hCU hUΩ hLΩ hP hPK hlocal
      (jetNormal_smooth hD) he₁ he₂ ha hD hframe (fun _ _ => rfl) hcollar hn hap T
  have hVp : ∀ j ∈ Z, Function.Periodic (fun t => V (j, t)) 1 := by
    intro j hj
    have he : (fun t => V (j, t)) =
        (fun θ => velocityRadius (jetNormal j) (a j) • direction (e₁ j) (e₂ j) θ) ∘
          (fun t => α (j, t)) := funext (fun t => hV (j, t))
    rw [he]
    exact (hper j hj).comp _
  have hVy : ∀ j ∈ Z, ∀ t, j.2 1 ⬝ᵥ V (j, t) = 0 := by
    intro j hj t
    rw [hV (j, t), dotProduct_smul]
    simp [direction, dotProduct_add, dotProduct_smul, (hframe j (hZΩ hj)).2.2.2.1,
      (hframe j (hZΩ hj)).2.2.2.2.2.1]
  have hVc : ∀ j ∈ Z, ∀ t, j.2 4 ⬝ᵥ V (j, t) = 0 := by
    intro j hj t
    rw [hV (j, t), dotProduct_smul]
    simp [direction, dotProduct_add, dotProduct_smul, (hframe j (hZΩ hj)).2.2.2.2.1,
      (hframe j (hZΩ hj)).2.2.2.2.2.2]
  let Z' : TopologicalSpace.Opens CollarVelocity.JetBase := ⟨Z, hZ⟩
  let l : Loop (jetDomain Z') := Loop.ofGeometric (ha.mono hZΩ) hVs hVp
    (fun j hj => hD j (hZΩ hj)) (fun j hj => hn j (hZΩ hj)) hVy hVc hlen hm
  refine ⟨Z', hLZ, hZΩ, l, (fun _ => rfl), ⟨W, hW, hCW, hWU, ?_⟩,
    α, hα, hper, ?_, τ, hturn, hlarge⟩
  · intro J hJ haz t
    exact hzero (decode J) hJ haz t
  · intro J t
    exact hV (decode J, t)

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
