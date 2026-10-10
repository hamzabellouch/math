import Mathlib
import OAI.Analysis.AffineBernstein.FlatParametricArea
import OAI.Analysis.AffineBernstein.ActualSupportVariation
import OAI.Analysis.AffineBernstein.TubeDensityIntegralCompact

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
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- The original affine-maximal PDE gives the literal flat tube weak Euler
identity. Both Hessian blocks, the support variation and the local stationary
chart are produced from the actual affine epigraph. -/
theorem affineMaximal_flat_tube_weak_euler {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (q₀ : S × E) (hd : inner ℝ q₀.2 (bE (Sum.inr ())) = 1)
    (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
    (hJ : ∀ v, inner ℝ (J v).2 (bE (Sum.inr ())) = 0)
    (C : (S × E) →L[ℝ] Space n) (hC : ∀ x, C (J x) = x)
    (e : Fin n ≃ ι ⊕ κ)
    (hJb : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i))
    {x₀ : Space n} (hx₀ : (q₀+J x₀).1 ∈ B) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let ℓ := InnerProductSpace.toDual ℝ E (bE (Sum.inr ()))
    let δ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
    ∃ W : Set (Space n), IsOpen W ∧ x₀ ∈ W ∧ W ⊆ {x | (q₀+J x).1 ∈ B} ∧
      ∀ (K : Set (Space n)), IsCompact K → K ⊆ W →
      ∀ (η : Space n → ℝ), ContDiff ℝ ∞ η → tsupport η ⊆ K →
      let G := flatSupportVariation ℓ q₀ C η
      (∫ x in K, tubeAreaFirstVariation (tubeBaseMatrix H (q₀+J x) bS)
        (tubeBaseMatrix G (q₀+J x) bS) (tubeRadiusMatrix H (q₀+J x) bE)
        (tubeRadiusMatrix G (q₀+J x) bE) δ) = 0 := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let d := bE (Sum.inr ())
  let ℓ := InnerProductSpace.toDual ℝ E d
  let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
  let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
  let b := (bS.prod bE.toBasis).reindex eA.symm
  obtain ⟨W,hW,hxW,hWU,hstat⟩ := affineMaximal_compact_flat_support_variation hΩ hcv hu hp hm
    a L hB hK hzero q₀ d hd J hi hJ C hC b hx₀
  refine ⟨W,hW,hxW,hWU,?_⟩
  intro K hKc hKW η hη hηK
  let G := flatSupportVariation ℓ q₀ C η
  let Z := supportGradient G
  have hℓ : ℓ q₀.2 = 1 := by simpa [ℓ,real_inner_comm] using hd
  have hℓJ (x : Space n) : ℓ (J x).2 = 0 := by simpa [ℓ,real_inner_comm] using hJ x
  have hq (x : Space n) : inner ℝ (q₀+J x).2 d = 1 := by simp [inner_add_left,hd,hJ,d]
  have hne (x : Space n) : (q₀+J x).2 ≠ 0 := by
    intro hz
    simpa [hz] using hq x
  have hℓne (x : Space n) : ℓ (q₀+J x).2 ≠ 0 := by simp [hℓ,hℓJ]
  have hj (x : Space n) (hx : x ∈ W) :=
    affineEpigraph_support_jets hΩ hcv hu hp a L hB hK hzero (hWU hx) (hne x)
  have hg (x : Space n) := flatSupportVariation_support_identities ℓ q₀ C hη (hℓne x)
  have hG (x : Space n) : ContDiffAt ℝ ∞ G (q₀+J x) :=
    contDiffAt_flatSupportVariation ℓ q₀ C hη (hℓne x)
  have hpos (x : Space n) (hx : x ∈ W) :=
    affineEpigraph_flat_tube_positive hΩ hcv hu hp a L hB hK hzero (hWU hx) (e := (q₀+J x).2) bS bE
      (by rw [hq x]; norm_num)
  have hD := hasDerivAt_integral_tubeDensity_variation (μ := volume) q₀ J hW hKc hKW
    (fun x hx => (hj x hx).1) (fun x _ => hG x) bS bE
    (fun x hx => (hpos x (hKW hx)).1) (fun x hx => (hpos x (hKW hx)).2) δ
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ x ∈ K,
      0 < (tubeBaseMatrix (fun q => H q+t*G q) (q₀+J x) bS).det ∧
      0 < (tubeRadiusMatrix (fun q => H q+t*G q) (q₀+J x) bE).det := by
    apply eventually_uniform_compact_zero (P := fun r : ℝ × Space n =>
      0 < (tubeBaseMatrix (fun q => H q+r.1*G q) (q₀+J r.2) bS).det ∧
      0 < (tubeRadiusMatrix (fun q => H q+r.1*G q) (q₀+J r.2) bE).det) hKc
    intro x hx
    obtain ⟨hb,hr⟩ := contDiffAt_tubeMatrices_variation q₀ J
      (p := (0,x)) (hj x (hKW hx)).1 (hG x) bS bE
    have hdb := ((continuousDetRows (ι := ι)).contDiff.contDiffAt.comp (0,x) hb).continuousAt
    have hdr := ((continuousDetRows (ι := κ)).contDiff.contDiffAt.comp (0,x) hr).continuousAt
    change ContinuousAt (fun p : ℝ × Space n =>
      (tubeBaseMatrix (fun q => H q+p.1*G q) (q₀+J p.2) bS).det) (0,x) at hdb
    change ContinuousAt (fun p : ℝ × Space n =>
      (tubeRadiusMatrix (fun q => H q+p.1*G q) (q₀+J p.2) bE).det) (0,x) at hdr
    exact (continuousAt_const.eventually_lt hdb (by simpa only [zero_mul,add_zero] using (hpos x (hKW hx)).1.det_pos)).and
      (continuousAt_const.eventually_lt hdr (by simpa only [zero_mul,add_zero] using (hpos x (hKW hx)).2.det_pos))
  have heq : (fun t : ℝ => ∫ x in K, parametricAreaDensity b
      (fun y => supportParam (fun q => Y q+t • Z q) (q₀+J y))
      (supportConormal (fun q => H q+t*G q) (q₀+J x)) (0,-d) x) =ᶠ[𝓝 0]
      (fun t : ℝ => ∫ x in K, tubeAreaDensity
        (tubeBaseMatrix (fun q => H q+t*G q) (q₀+J x) bS)
        (tubeRadiusMatrix (fun q => H q+t*G q) (q₀+J x) bE) δ) := by
    filter_upwards [hev] with t ht
    apply setIntegral_congr_fun hKc.measurableSet
    intro x hx
    have hHt : ContDiffAt ℝ ∞ (fun q => H q+t*G q) (q₀+J x) :=
      (hj x (hKW hx)).1.add (contDiffAt_const.mul (hG x))
    have hYt : ContDiffAt ℝ ∞ (fun q => Y q+t • Z q) (q₀+J x) :=
      (hj x (hKW hx)).2.1.add ((contDiffAt_supportGradient (hG x)).const_smul t)
    have hid := support_identities_variation (hj x (hKW hx)).1 (hG x)
      (hj x (hKW hx)).2.2.1 (hg x).1 (hj x (hKW hx)).2.2.2 (hg x).2 t
    dsimp only [b,eA,d]
    rw [parametricAreaDensity_flatSupport q₀ J hYt bS bE e hJb]
    exact flatTubeAffineAreaJet_eq hHt hYt hid.1 hid.2 bS bE (ht x hx).1 (ht x hx).2
  have hS := hstat K hKc hKW η hη hηK
  have hS' := hS.congr_of_eventuallyEq heq.symm
  exact hD.unique hS'

end AffineBernstein
end

end OAI
