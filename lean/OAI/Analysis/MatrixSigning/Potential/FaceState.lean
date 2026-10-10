import Mathlib
import OAI.Analysis.MatrixSigning.Potential.RationalBasis
import OAI.Analysis.MatrixSigning.Potential.MovementBudget
import OAI.Analysis.MatrixSigning.Optimization.RealExtendCube

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
noncomputable section
open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d N : ℕ}

def faceState (base : Fin N → ℚ) : Fin (activeIndices base).length → ℚ :=
  fun j => base (activeIndex base j)

def activePotential (coords : Fin N → Fin d × Fin d → ℚ) (base : Fin N → ℚ)
    (ν lam : ℚ) : Coordinates (activeIndices base).length → ℝ :=
  facePotential ((ν/(d:ℚ):ℚ):ℝ) (lam:ℝ)
    (fixedPart (activeIndex base) (fun i => (base i:ℝ)) (rationalAtoms coords))
    (fun j => rationalAtoms coords (activeIndex base j))

lemma variance_le_one (A : Fin N → H d) {ν : ℚ} (hν1 : ν ≤ 1)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ (ν:ℝ) • (Hermitian.one : H d)) :
    (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ (Hermitian.one : H d) := by
  calc
    _ ≤ (ν:ℝ) • (Hermitian.one : H d) := hvar
    _ ≤ (1:ℝ) • (Hermitian.one : H d) := scalar_one_mono (by exact_mod_cast hν1)
    _ = _ := one_smul ℝ _

lemma epsilon_spec [NeZero d] {ν : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
    0 < ν/(d:ℚ) ∧ ν/(d:ℚ) ≤ 1 ∧ ν/(d:ℚ)*(d:ℚ) ≤ 1 := by
  have hd : (0:ℚ) < d := by exact_mod_cast NeZero.pos d
  have hd1 : (1:ℚ) ≤ d := by exact_mod_cast NeZero.pos d
  refine ⟨div_pos hν hd,(div_le_one hd).mpr (hν1.trans hd1),?_⟩
  simpa only [div_mul_cancel₀ _ hd.ne'] using hν1

lemma activeQuery_correct [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (base : Fin N → ℚ) (y : Fin (activeIndices base).length → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam error : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 ≤ lam)
    (he : 0 < error) (he1 : error ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hb : ∀ i,|base i| ≤ 1) (hy : ∀ j,|y j| ≤ 1) :
    |(faceQuery coords base y ν lam error:ℝ)-activePotential coords base ν lam (pointCast y)| ≤ (error:ℝ) := by
  have hh := faceQuery_correct coords base y hA htr hν hν1 hlam he he1 hvar hb hy
  simp only [activePotential,facePotential,penalty,pointCast,Rat.cast_div,Rat.cast_natCast]
  exact hh

lemma activePotential_regular [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (base : Fin N → ℚ) (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam σ : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hσ : 0 < σ)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hb : ∀ i,|base i| ≤ 1)
    (hx : ∀ i,|faceState base i| ≤ 1-σ)
    {r : ℝ} (hr : 0 ≤ r) (hrσ : r ≤ (σ:ℝ)/2)
    (y : Coordinates (activeIndices base).length) (hy : ‖y-pointCast (faceState base)‖ ≤ r) :
    ContDiffAt ℝ 3 (activePotential coords base ν lam) y ∧
      ∀ u,‖u‖ ≤ 1 →
        |iteratedDeriv 2 (fun t : ℝ => activePotential coords base ν lam (y+t • u)) 0| ≤
          (curveBudget d (activeIndices base).length (ν/(d:ℚ)) σ lam:ℝ) ∧
        |iteratedDeriv 3 (fun t : ℝ => activePotential coords base ν lam (y+t • u)) 0| ≤
          (curveBudget d (activeIndices base).length (ν/(d:ℚ)) σ lam:ℝ) := by
  have hep := epsilon_spec (d:=d) hν hν1
  have hbr : Cube (fun i => (base i:ℝ)) := fun i => (show |(base i:ℝ)| ≤ 1 by exact_mod_cast hb i)
  have hxr : ∀ i,|pointCast (faceState base) i| ≤ 1-(σ:ℝ) := fun i => (show |(faceState base i:ℝ)| ≤ 1-(σ:ℝ) by exact_mod_cast hx i)
  have hystrip := strip_nearby (pointCast (faceState base)) y hr hxr hy hrσ
  have hh := face_smooth_and_derivatives (ε:=((ν/(d:ℚ):ℚ):ℝ)) (σ:=(σ:ℝ)) (activeIndex base) (activeIndex_injective base)
    (fun i => (base i:ℝ)) (rationalAtoms coords) hA htr (variance_le_one _ hν1 hvar)
    hbr (real_active_outside_endpoint base hb) (by exact_mod_cast hep.1)
    (by exact_mod_cast hep.2.2) (by exact_mod_cast hσ) y hystrip (lam:=(lam:ℝ))
  refine ⟨hh.1.of_le (by decide),?_⟩
  simpa only [activePotential,curveBudget_cast] using hh.2

lemma nearby_rational_cube (x y : Fin N → ℚ) {σ r : ℚ} (hr : 0 ≤ r)
    (hx : ∀ i,|x i| ≤ 1-σ) (hy : ‖pointCast y-pointCast x‖ ≤ (r:ℝ)) (hrσ : r ≤ σ) :
    ∀ i,|y i| ≤ 1 := by
  intro i
  have hc := (pi_norm_le_iff_of_nonneg (show (0:ℝ) ≤ r by exact_mod_cast hr)).mp hy i
  change ‖(y i:ℝ)-(x i:ℝ)‖ ≤ (r:ℝ) at hc
  rw [Real.norm_eq_abs] at hc
  have hx' : |(x i:ℝ)| ≤ 1-(σ:ℝ) := by exact_mod_cast hx i
  have hr' : (r:ℝ) ≤ (σ:ℝ) := by exact_mod_cast hrσ
  have htri := abs_sub_le (y i:ℝ) (x i:ℝ) 0
  simp only [sub_zero] at htri
  have hh : |(y i:ℝ)| ≤ 1 := by linarith
  exact_mod_cast hh

end
end CurrentKS.RationalFace

end OAI
