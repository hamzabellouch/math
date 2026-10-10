import OAI.Analysis.AncientFlat.Profile.RadialRealCore
import OAI.Analysis.AncientFlat.Profile.RotationCore
import OAI.Analysis.AncientFlat.Evolution.OrthogonalCalculus
import OAI.Analysis.AncientFlat.Evolution.MovingUnique

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace FlatSimilarity
open FlatSymmetry
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {Af Bf : V → ℝ} {d : C₀(V,ℂ)} {u : ℝ → C₀(V,ℂ)}
omit [MeasurableSpace V] [BorelSpace V] in
lemma MovesClassically.rotated (hu : MovesClassically Af Bf d u)
    (hAf : Radial Af) (hBf : Radial Bf) (R : V ≃ₗᵢ[ℝ] V) :
    MovesClassically Af Bf (rotate R d) (fun t => rotate R (u t)) := by
  let : NormedAddCommGroup (V →ᵇ ℂ) := inferInstance
  let : NormedSpace ℝ (V →ᵇ ℂ) := inferInstance
  refine ⟨congrArg (rotate R) hu.1,?_,?_,?_,?_⟩
  · exact (rotate R).continuous.comp_continuousOn hu.2.1
  · intro t ht
    exact (hu.2.2.1 t ht).comp R.toContinuousLinearEquiv.contDiff
  · intro t ht
    exact bounded_jets_rotate R _ (hu.2.2.1 t ht) (hu.2.2.2.1 t ht)
  · intro t ht
    obtain ⟨p,hp,hpe⟩ := hu.2.2.2.2 t ht
    let Q : (V →ᵇ ℂ) →L[ℝ] (V →ᵇ ℂ) := BoundedContinuousFunction.compContinuousCLM ℂ ℝ (rotMap R)
    refine ⟨Q p,?_,fun x => ?_⟩
    · convert Q.hasFDerivAt.comp_hasDerivAt t hp using 1
      rfl
    · change p (R x)=-((Real.exp (-t)/16*Af (Real.exp (t/4) • x) : ℝ) : ℂ)*
          Δ (Δ (fun y => u t (R y))) x-(1/2+(Bf (Real.exp (t/4) • x) : ℂ))*u t (R x)
      rw [hpe, bilaplacian_rotate R _ (hu.2.2.1 t ht)]
      rw [←R.map_smul, hAf R, hBf R]
omit [MeasurableSpace V] [BorelSpace V] in
lemma MovesClassically.conjugate (hu : MovesClassically Af Bf d u) :
    MovesClassically Af Bf (star d) (fun t => star (u t)) := by
  let : NormedAddCommGroup (V →ᵇ ℂ) := inferInstance
  let : NormedSpace ℝ (V →ᵇ ℂ) := inferInstance
  refine ⟨congrArg Star.star hu.1,?_,?_,?_,?_⟩
  · exact continuous_star.comp_continuousOn hu.2.1
  · intro t ht
    exact Complex.conjCLE.contDiff.comp (hu.2.2.1 t ht)
  · intro t ht
    exact bounded_jets_star _ (hu.2.2.2.1 t ht)
  · intro t ht
    obtain ⟨p,hp,hpe⟩ := hu.2.2.2.2 t ht
    let Q : (V →ᵇ ℂ) →L[ℝ] (V →ᵇ ℂ) := Complex.conjCLE.toContinuousLinearMap.compLeftContinuousBounded V
    refine ⟨Q p,?_,fun x => ?_⟩
    · convert Q.hasFDerivAt.comp_hasDerivAt t hp using 1
      rfl
    · change star (p x)=-((Real.exp (-t)/16*Af (Real.exp (t/4) • x) : ℝ) : ℂ)*
          Δ (Δ (fun y => star (u t y))) x-(1/2+(Bf (Real.exp (t/4) • x) : ℂ))*star (u t x)
      rw [hpe,bilaplacian_star]
      simp only [star_sub,star_mul,star_neg,star_add,star_div₀,star_one,Complex.star_def,Complex.conj_ofReal, map_ofNat]
      ring
lemma MovesClassically.radial {c : ℝ} (h : SymbolBounds c Af Bf)
    (hu : MovesClassically Af Bf d u) (hAf : Radial Af) (hBf : Radial Bf)
    (hd : Radial (d : V → ℂ)) : ∀ t ∈ Icc (0:ℝ) 1, Radial (u t : V → ℂ) := by
  intro t ht R x
  have hd' : rotate R d=d := by ext y; exact hd R y
  have hrot := hu.rotated hAf hBf R
  rw [hd'] at hrot
  exact congrArg (fun f : C₀(V,ℂ) => f x) (hrot.unique h hu t ht)
lemma MovesClassically.realValued {c : ℝ} (h : SymbolBounds c Af Bf)
    (hu : MovesClassically Af Bf d u) (hd : RealValued (d : V → ℂ)) :
    ∀ t ∈ Icc (0:ℝ) 1, RealValued (u t : V → ℂ) := by
  intro t ht x
  have hd' : star d=d := by ext y; exact hd y
  have hs := hu.conjugate
  rw [hd'] at hs
  exact congrArg (fun f : C₀(V,ℂ) => f x) (hs.unique h hu t ht)
end FlatSimilarity

end

end OAI
