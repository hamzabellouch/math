import OAI.Geometry.RCD.Sobolev.FiniteEnergyRepresentatives

namespace OAI

/-! # Pointwise coordinate forms for pairs of Sobolev linear families -/

open Set Filter MeasureTheory
open scoped BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem localGamma_finset_sum_left {ι : Type*} (s : Finset ι)
    (u : ι → SobolevSpace μ hQ) (g : SobolevSpace μ hQ) :
    localGamma μ hQ (∑ i ∈ s, u i) g =ᵐ[μ]
      fun x => ∑ i ∈ s, localGamma μ hQ (u i) g x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty,zero_smul,zero_mul] using
      localGamma_smul_left μ hQ 0 (0 : SobolevSpace μ hQ) g
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [localGamma_add_left μ hQ (u i) (∑ j ∈ s, u j) g,ih] with x hx hy
    exact hx.trans (congrArg (fun z => localGamma μ hQ (u i) g x+z) hy)

theorem localGamma_finset_sum_right {ι : Type*} (s : Finset ι)
    (f : SobolevSpace μ hQ) (u : ι → SobolevSpace μ hQ) :
    localGamma μ hQ f (∑ i ∈ s, u i) =ᵐ[μ]
      fun x => ∑ i ∈ s, localGamma μ hQ f (u i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty,zero_smul,zero_mul] using
      localGamma_smul_right μ hQ 0 f (0 : SobolevSpace μ hQ)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [localGamma_add_right μ hQ f (u i) (∑ j ∈ s, u j),ih] with x hx hy
    exact hx.trans (congrArg (fun z => localGamma μ hQ f (u i) x+z) hy)

variable {m : ℕ}

def gammaCoordinateForm (U V : Euclidean m →L[ℝ] SobolevSpace μ hQ) (x : X) :
    Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] ℝ :=
  coordinateBilinear (fun i j =>
    localGamma μ hQ (U (EuclideanSpace.single i 1)) (V (EuclideanSpace.single j 1)) x)

/-- Two different Sobolev linear families have one finite coordinate
bilinear form, representing every fixed pair of gradient directions. -/
theorem gammaCoordinateForm_rep (U V : Euclidean m →L[ℝ] SobolevSpace μ hQ)
    (a b : Euclidean m) :
    localGamma μ hQ (U a) (V b) =ᵐ[μ] fun x => gammaCoordinateForm μ hQ U V x a b := by
  classical
  let e (i : Fin m) : Euclidean m := EuclideanSpace.single i 1
  have hU : U a=∑ i : Fin m, a i • U (e i) := by
    have hh := congrArg (fun T : Euclidean m →L[ℝ] SobolevSpace μ hQ => T a)
      (sobolevColumnMap_of_linear μ hQ U)
    rw [sobolevColumnMap_apply] at hh
    exact hh.symm
  have hV : V b=∑ j : Fin m, b j • V (e j) := by
    have hh := congrArg (fun T : Euclidean m →L[ℝ] SobolevSpace μ hQ => T b)
      (sobolevColumnMap_of_linear μ hQ V)
    rw [sobolevColumnMap_apply] at hh
    exact hh.symm
  have hleft := localGamma_finset_sum_left μ hQ Finset.univ (fun i => a i • U (e i))
    (∑ j, b j • V (e j))
  have hright (i : Fin m) := localGamma_finset_sum_right μ hQ Finset.univ
    (a i • U (e i)) (fun j => b j • V (e j))
  have hscalar (i j : Fin m) : localGamma μ hQ (a i • U (e i)) (b j • V (e j)) =ᵐ[μ]
      fun x => (a i*b j)*localGamma μ hQ (U (e i)) (V (e j)) x := by
    filter_upwards [localGamma_smul_left μ hQ (a i) (U (e i)) (b j • V (e j)),
      localGamma_smul_right μ hQ (b j) (U (e i)) (V (e j))] with x hx hy
    rw [hx,hy]
    ring
  rw [hU,hV]
  filter_upwards [hleft,ae_all_iff.mpr hright,
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (hscalar i))] with x hl hr hs
  rw [hl]
  simp only [gammaCoordinateForm,coordinateBilinear_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hr i]
  exact Finset.sum_congr rfl (fun j _ => hs i j)

end RegularPointCoordinates

end

end OAI
