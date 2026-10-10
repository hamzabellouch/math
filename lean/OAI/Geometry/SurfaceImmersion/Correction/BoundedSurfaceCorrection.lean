import OAI.Geometry.SurfaceImmersion.Primitive.SurfaceVelocityIdentities
import OAI.Geometry.SurfaceImmersion.Geometry.BoundedCoefficientRecursion
import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicGlobalization

namespace OAI

/-! Apply the finite periodic correction to the actual geometric second-jet
family, including global smooth extension and its uniform scale bound. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion
open CovarianceCorrector WeightedEstimates
local notation "ι" => JetVelocityCoordinates.toEuclidean

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

def yData (J : LowJet) : Euclidean := ι (slot 2 J)
def cData (J : LowJet) : Euclidean := ι (slot 6 J)
def xData (J : LowJet) : Euclidean := ι (tangent J)

def coefficientExpressions (n : ℕ) : ℕ → VectorExpression :=
  MetricPolynomial.coefficients yData cData xData l.euclideanVelocity l.q 0 1 n

lemma yData_smooth : ContDiffOn ℝ ∞ yData O :=
  (JetVelocityCoordinates.toEuclidean.contDiff.comp (slot_smooth 2)).contDiffOn

lemma cData_smooth : ContDiffOn ℝ ∞ cData O :=
  (JetVelocityCoordinates.toEuclidean.contDiff.comp (slot_smooth 6)).contDiffOn

include l in
lemma xData_smooth : ContDiffOn ℝ ∞ xData O :=
  JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn l.smoothTangent

/-- The loss exponent is fixed by the geometric loop and finite depth,
before choosing a slow map or a differentiation order. The same coefficients
have cancellation, support, polynomial representation, and the scale bound. -/
theorem bounded_surface_correction {S : TopologicalSpace.Opens JetPolynomial.Base}
    {K : Set LowJet} (hK : IsCompact K) (hKO : K ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ) :
    ∃ d : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (hGK : MapsTo (lowJet G) S K),
      let g := l.geometry G hG (fun _ hp => hKO (hGK hp))
      ∀ A : Set JetPolynomial.Base, IsClosed A → A ⊆ S →
        (∀ p ∈ S, p ∉ A → ∀ t, l.velocity (lowJet G p, t) = normal (lowJet G p)) →
      ∃ U : ℕ → Family S Euclidean,
        U 0 = g.initial ∧ (∀ i p, p ∈ S → average ((U i).val p) = 0) ∧
        (∀ i, ContDiff ℝ ∞ (fun z : JetPolynomial.Base × ℝ => (U i).val z.1 (z.2 : Period))) ∧
        (∀ i p, p ∉ A → (U i).val p = 0) ∧
        (g.yyCoefficient U 1).fluct = 0 ∧
        (∀ r, 1 ≤ r → r ≤ n →
          (g.xxCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.xyCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.yyCoefficient U (r + 1)).fluct = 0) ∧
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) ∧
        ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
          WeightedBound S s (m + (2 * n + 2)) B (lowJet G) →
          WeightedBound S z m (D * z / s ^ d)
            (fun p => finiteAnsatz (fun q => ι (G q)) U ℓ (n + 1) z p - ι (G p)) := by
  obtain ⟨d, hd⟩ := exists_bounded_coefficients (S := S) O.isOpen hK hKO 0 1 n ℓ
    yData_smooth cData_smooth (xData_smooth l) l.euclideanVelocity_smooth
    (fun J hJ => by rw [yData, cData, gram_toEuclidean]; exact l.gram_ne J hJ)
    l.smoothQ (fun _ hJ => l.q_pos hJ) (fun _ hJ => l.euclideanVelocity_length hJ)
  refine ⟨d, ?_⟩
  intro m B hB
  obtain ⟨D, hD, hcoeff⟩ := hd m B hB
  refine ⟨D, hD, ?_⟩
  intro G hG hGK g A hA hAS hz
  obtain ⟨U, hinit, hmean, hy, hsupport, hc, hrep, hb⟩ := hcoeff G g hG hGK
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ hp => l.geometry_velocity hG (fun _ hp => hKO (hGK hp)) hp) (fun _ _ => rfl)
  have hzero : ∀ i p, p ∈ S → p ∉ A → (U i).val p = 0 := by
    intro i p hp hpA
    exact hsupport ((S : Set JetPolynomial.Base) ∩ Aᶜ)
      (S.isOpen.inter hA.isOpen_compl) inter_subset_left
      (fun q hq => l.geometry_initial_zero hG (fun _ hp => hKO (hGK hp)) hq.1 (hz q hq.1 hq.2))
      i p ⟨hp, hpA⟩
  refine ⟨U, hinit, hmean, ?_, ?_, hy, hc, hrep, ?_⟩
  · exact fun i => (U i).smooth_global hA hAS (hzero i)
  · intro i p hp
    by_cases hpS : p ∈ S
    · exact hzero i p hpS hp
    · exact (U i).outside hpS
  · intro s z hz hzs hs1 hbound
    exact hb s z hz hzs hs1 hbound (fun q => ι (G q))

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
