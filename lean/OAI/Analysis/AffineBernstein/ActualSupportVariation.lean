import Mathlib
import OAI.Analysis.AffineBernstein.ParametricBasis
import OAI.Analysis.AffineBernstein.SupportVariationJets

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/- Every actual smooth compact flat support variation is stationary. Its
homogeneous lifting, compact support, conormal and transverse fields are
constructed explicitly rather than supplied as stationarity hypotheses. -/
theorem affineMaximal_compact_flat_support_variation {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (q₀ : S × E) (d : E) (hd : inner ℝ q₀.2 d = 1)
    (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
    (hJ : ∀ v, inner ℝ (J v).2 d = 0)
    (C : (S × E) →L[ℝ] Space n) (hC : ∀ x, C (J x) = x)
    (b : Module.Basis (Fin n ⊕ Unit) ℝ (S × E))
    {x₀ : Space n} (hx₀ : (q₀+J x₀).1 ∈ B) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let ℓ := InnerProductSpace.toDual ℝ E d
    ∃ W : Set (Space n), IsOpen W ∧ x₀ ∈ W ∧ W ⊆ {x | (q₀+J x).1 ∈ B} ∧
      ∀ (K : Set (Space n)), IsCompact K → K ⊆ W →
      ∀ (η : Space n → ℝ), ContDiff ℝ ∞ η → tsupport η ⊆ K →
      let G := flatSupportVariation ℓ q₀ C η
      let Z := supportGradient G
      HasDerivAt (fun t : ℝ => ∫ x in K, parametricAreaDensity b
        (fun y => supportParam (fun q => Y q+t • Z q) (q₀+J y))
        (supportConormal (fun q => H q+t*G q) (q₀+J x)) (0,-d) x) 0 0 := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let ℓ := InnerProductSpace.toDual ℝ E d
  have hℓ : ℓ q₀.2 = 1 := by simpa [ℓ,real_inner_comm] using hd
  have hℓJ (x : Space n) : ℓ (J x).2 = 0 := by simpa [ℓ,real_inner_comm] using hJ x
  obtain ⟨W,hW,hxW,hWU,hstat⟩ := affineMaximal_flatSupport_local_stationary hΩ hcv hu hp hm
    a L hB hK hzero q₀ d hd J hi hJ b hx₀
  change ∃ W, _
  refine ⟨W,hW,hxW,hWU,?_⟩
  intro K hKc hKW η hη hηK
  let G := flatSupportVariation ℓ q₀ C η
  let Z := supportGradient G
  let V := fun x : Space n => ((0 : S),Z (q₀+J x))
  let ν := fun t : ℝ => fun x : Space n => supportConormal (fun q => H q+t*G q) (q₀+J x)
  have hq (x : Space n) : inner ℝ (q₀+J x).2 d = 1 := by simp [inner_add_left,hd,hJ]
  have hne (x : Space n) : (q₀+J x).2 ≠ 0 := by
    intro hz
    simpa [hz] using hq x
  have hℓne (x : Space n) : ℓ (q₀+J x).2 ≠ 0 := by simp [hℓ,hℓJ]
  have hj (x : Space n) (hx : x ∈ W) :=
    affineEpigraph_support_jets hΩ hcv hu hp a L hB hK hzero (hWU hx) (hne x)
  have hG (x : Space n) : ContDiffAt ℝ ∞ G (q₀+J x) :=
    contDiffAt_flatSupportVariation ℓ q₀ C hη (hℓne x)
  have hg (x : Space n) := flatSupportVariation_support_identities ℓ q₀ C hη (hℓne x)
  have hV : ContDiffOn ℝ ∞ V W :=
    (contDiff_flatSupportVelocity ℓ q₀ C J hℓ hℓJ hη).contDiffOn
  have hsV : tsupport V ⊆ K :=
    (tsupport_flatSupportVelocity_subset ℓ q₀ C J hℓ hℓJ hC η).trans hηK
  have hν (t : ℝ) (x : Space n) (hx : x ∈ W) :
      (ν t x).comp (fderiv ℝ (fun y => supportParam Y (q₀+J y)+t • V y) x) = 0 := by
    exact supportConormal_flat_variation_tangent q₀ J (hj x hx).1 (hG x)
      (hj x hx).2.1 (contDiffAt_supportGradient (hG x))
      (hj x hx).2.2.1 (hg x).1 (hj x hx).2.2.2 (hg x).2 t
  have hξ (t : ℝ) (x : Space n) (_ : x ∈ W) : ν t x (0,-d) = 1 :=
    supportConormal_flat_transverse (hq x)
  have hν0 (x : Space n) (_ : x ∈ K) : ν 0 x = supportConormal H (q₀+J x) := by
    simp [ν]
  have hcν (x : Space n) (hx : x ∈ K) :
      ContinuousAt (fun p : ℝ × Space n => ν p.1 p.2 (L.symm ((0 : Space n),1))) (0,x) := by
    have hh := supportConormal_variation_continuous (hj x (hKW hx)).1 (hG x) 0
      (L.symm ((0 : Space n),1))
    have he : ContinuousAt (fun p : ℝ × Space n => (p.1,q₀+J p.2)) (0,x) :=
      continuousAt_fst.prodMk
        (continuousAt_const.add (J.continuous.continuousAt.comp continuousAt_snd))
    exact ContinuousAt.comp (f := fun p : ℝ × Space n => (p.1,q₀+J p.2))
      (x := (0,x)) hh he
  have ht := hstat K hKc hKW V hV hsV ν (fun _ _ => (0,-d)) hν hξ hν0 hcν
  have heX (t : ℝ) : (fun y => supportParam Y (q₀+J y)+t • V y) =
      (fun y => supportParam (fun q => Y q+t • Z q) (q₀+J y)) := by
    funext y
    exact (supportParam_variation Y Z t _).symm
  change HasDerivAt (fun t : ℝ => ∫ x in K, parametricAreaDensity b
    (fun y => supportParam (fun q => Y q+t • Z q) (q₀+J y)) (ν t x) (0,-d) x) 0 0
  convert ht using 1
  funext t
  congr 1
  funext x
  rw [heX t]

end AffineBernstein
end

end OAI
