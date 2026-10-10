import OAI.Geometry.SurfaceImmersion.Primitive.LoopDensityLinear

namespace OAI

/-! Extract mass one and the vector mean from the three augmented moments. -/
noncomputable section

namespace ClosedSurfaceR4.LoopDensity

theorem mass_and_mean {ρ : ℝ → ℝ} {p : ℝ → Plane} {c : Plane}
    (hρ : Continuous ρ) (hp : Continuous p)
    (hm : (∫ t in 0..1, ρ t • augment (p t)) = augment c) :
    (∫ t in 0..1, ρ t) = 1 ∧ (∫ t in 0..1, ρ t • p t) = c := by
  have hi : IntervalIntegrable (fun t => ρ t • augment (p t)) MeasureTheory.volume 0 1 :=
    (hρ.smul (augment_continuous.comp hp)).intervalIntegrable 0 1
  have hpi : IntervalIntegrable (fun t => ρ t • p t) MeasureTheory.volume 0 1 :=
    (hρ.smul hp).intervalIntegrable 0 1
  have hcoord (i : Fin 3) :
      (∫ t in 0..1, (ρ t • augment (p t)) i) = (augment c) i := by
    have he := congrArg (fun x : Moments => x i) hm
    have hev : (∫ t in 0..1, ρ t • augment (p t)) i =
        ∫ t in 0..1, (ρ t • augment (p t)) i :=
      ((ContinuousLinearMap.proj i : Moments →L[ℝ] ℝ).intervalIntegral_comp_comm hi).symm
    rwa [hev] at he
  constructor
  · simpa [augment] using hcoord 0
  · ext i
    have hev : (∫ t in 0..1, ρ t • p t) i = ∫ t in 0..1, (ρ t • p t) i :=
      ((ContinuousLinearMap.proj i : Plane →L[ℝ] ℝ).intervalIntegral_comp_comm hpi).symm
    rw [hev]
    fin_cases i
    · simpa [augment] using hcoord 1
    · simpa [augment] using hcoord 2

end ClosedSurfaceR4.LoopDensity

end

end OAI
