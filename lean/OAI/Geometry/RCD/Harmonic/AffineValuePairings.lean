import OAI.Geometry.RCD.Metric.InnerBallValueMoments
import OAI.Geometry.RCD.Coordinates.NormalizedPairing
import OAI.Geometry.RCD.Harmonic.LocalL2Restriction
import OAI.Geometry.RCD.Harmonic.EuclideanHarmonicModel

namespace OAI

/-! # Exact value representatives for all affine-family Hilbert pairings -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace
noncomputable section
namespace RegularPointCoordinates

/-- The target, constant and coordinate values in the same order as the Hilbert family. -/
def affineValueFamily {X : Type*} {n : ℕ} (w : X → ℝ) (V : X → Euclidean n) :
    Option (Option (Fin n)) → X → ℝ :=
  affineMomentFamily n w (fun _ => 1) (fun j x => V x j)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

private theorem affineValueFamily_representatives (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (w : SobolevSpace μ hQ)
    (V : X → Euclidean n) (s : Set X) (hfin : μ s≠⊤)
    (hV : ∀ j, SobolevSpace.toLp μ hQ (u j)=ᵐ[μ.restrict s] fun x => V x j) :
    ∀ i, affineMomentFamily n (SobolevSpace.restrictLp μ hQ s w)
      (restrictedOne μ s hfin) (fun j => SobolevSpace.restrictLp μ hQ s (u j)) i =ᵐ[μ.restrict s]
      affineValueFamily (SobolevSpace.toLp μ hQ w) V i := by
  intro i
  rcases i with _ | (_ | j)
  · exact SobolevSpace.restrictLp_coe μ hQ s w
  · exact restrictedOne_coe μ s hfin
  · exact (SobolevSpace.restrictLp_coe μ hQ s (u j)).trans (hV j)

theorem affineValueFamily_memLp (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (w : SobolevSpace μ hQ)
    (V : X → Euclidean n) (s : Set X) (hfin : μ s≠⊤)
    (hV : ∀ j, SobolevSpace.toLp μ hQ (u j)=ᵐ[μ.restrict s] fun x => V x j) (i) :
    MemLp (affineValueFamily (SobolevSpace.toLp μ hQ w) V i) 2 (μ.restrict s) :=
  (memLp_congr_ae (affineValueFamily_representatives μ hQ u w V s hfin hV i)).mp (Lp.memLp _)

theorem localAffineMomentFamily_pairing (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (w : SobolevSpace μ hQ)
    (V : X → Euclidean n) (s : Set X) (hfin : μ s≠⊤)
    (hV : ∀ j, SobolevSpace.toLp μ hQ (u j)=ᵐ[μ.restrict s] fun x => V x j) (i j) :
    ⟪localAffineMomentFamily μ hQ u w s hfin i,localAffineMomentFamily μ hQ u w s hfin j⟫_ℝ=
      (μ.real s)⁻¹*∫ x in s,
        affineValueFamily (SobolevSpace.toLp μ hQ w) V i x*
        affineValueFamily (SobolevSpace.toLp μ hQ w) V j x ∂μ := by
  let U := affineMomentFamily n (SobolevSpace.restrictLp μ hQ s w)
    (restrictedOne μ s hfin) (fun j => SobolevSpace.restrictLp μ hQ s (u j))
  have he (a) : normalizeLocalL2 μ s hfin (U a)=localAffineMomentFamily μ hQ u w s hfin a := by
    rcases a with _ | (_ | j) <;> rfl
  rw [← he i,← he j]
  exact normalized_inner_of_representatives μ s hfin (U i) (U j) _ _
    (affineValueFamily_representatives μ hQ u w V s hfin hV i)
    (affineValueFamily_representatives μ hQ u w V s hfin hV j)

/-- The affine moment family is already meaningful before harmonicity of the limit is identified. -/
def euclideanValueMoments {n : ℕ} {S : ℝ} (g : Euclidean n → ℝ)
    (hg : MemLp g 2 (volume.restrict (ball 0 S))) {ρ : ℝ} (hρS : ρ≤S) :
    Option (Option (Fin n)) → Lp ℝ 2 (volume.restrict (ball (0:Euclidean n) ρ)) :=
  affineMomentFamily n
    (normalizeLocalL2 volume (ball 0 ρ) measure_ball_ne_top
      ((hg.mono_measure (Measure.restrict_mono_set volume (ball_subset_ball hρS))).toLp g))
    (normalizeLocalL2 volume (ball 0 ρ) measure_ball_ne_top
      (restrictedOne volume (ball 0 ρ) measure_ball_ne_top))
    (fun j => normalizeLocalL2 volume (ball 0 ρ) measure_ball_ne_top (euclideanCoordinateLp n ρ j))

theorem euclideanValueMoments_pairing {n : ℕ} {S ρ : ℝ}
    (g : Euclidean n → ℝ) (hg : MemLp g 2 (volume.restrict (ball 0 S)))
    (hρS : ρ≤S) (i j) :
    ⟪euclideanValueMoments g hg hρS i,euclideanValueMoments g hg hρS j⟫_ℝ=
      (volume.real (ball (0:Euclidean n) ρ))⁻¹*
        ∫ z in ball 0 ρ, affineValueFamily g id i z*affineValueFamily g id j z := by
  let gLp := (hg.mono_measure (Measure.restrict_mono_set volume (ball_subset_ball hρS))).toLp g
  let U := affineMomentFamily n gLp
    (restrictedOne volume (ball 0 ρ) measure_ball_ne_top) (euclideanCoordinateLp n ρ)
  have he (a) : normalizeLocalL2 volume (ball 0 ρ) measure_ball_ne_top (U a)=
      euclideanValueMoments g hg hρS a := by
    rcases a with _ | (_ | j) <;> rfl
  have hU (a) : U a=ᵐ[volume.restrict (ball 0 ρ)] affineValueFamily g id a := by
    rcases a with _ | (_ | j)
    · exact (hg.mono_measure (Measure.restrict_mono_set volume (ball_subset_ball hρS))).coeFn_toLp
    · exact restrictedOne_coe volume (ball 0 ρ) measure_ball_ne_top
    · exact euclideanCoordinateLp_coe n ρ j
  rw [← he i,← he j]
  exact normalized_inner_of_representatives volume (ball 0 ρ) measure_ball_ne_top
    (U i) (U j) _ _ (hU i) (hU j)

theorem EuclideanHarmonicModel.moments_pairing {n : ℕ} {S ρ : ℝ}
    (model : EuclideanHarmonicModel n S) (hρS : ρ≤S) (i j) :
    ⟪model.moments hρS i,model.moments hρS j⟫_ℝ=
      (volume.real (ball (0:Euclidean n) ρ))⁻¹*
        ∫ z in ball 0 ρ, affineValueFamily model.value id i z*affineValueFamily model.value id j z :=
  euclideanValueMoments_pairing model.value model.memLp hρS i j

end RegularPointCoordinates

end

end OAI
