import Mathlib
import OAI.Analysis.MatrixSigning.Potential.NormPotential
import OAI.Analysis.MatrixSigning.Optimization.Transition
import OAI.Analysis.MatrixSigning.Optimization.UpperIndex
import OAI.Analysis.MatrixSigning.Potential.PenaltyParameter

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.RationalFace

section
open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference CurrentKS.Descent
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

theorem rationalRun_spec [NeZero d] [NeZero N] (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hA0 : ∀ i,rationalAtoms coords i≠0)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hlamhi : (lam:ℝ) ≤ Real.sqrt (ν:ℝ)/(100*N))
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d)) :
    (∀ i,|rationalRun coords ν lam i|=1) ∧
      operatorNorm (S (rationalAtoms coords) (pointCast (rationalRun coords ν lam))) ≤
        (3931/100:ℝ)*Real.sqrt (ν:ℝ) := by
  let P := StripCube (N:=N) (lam^2/ν)
  let f := fullPotential coords ν lam
  let step := transition coords ν lam
  let x₀ : Fin N → ℚ := freezeAll (lam^2/ν) 0
  let k := fuel (uniformDrop d N ν lam)
  have hp : ∀ x y,P x → step x=some y → P y := by
    intro x y hx hs
    exact (transition_spec coords hA hA0 hrank htr hν hν1 hlam hlam1 hvar x y hx hs).1
  have hd : ∀ x y,P x → step x=some y → f y ≤ f x-(uniformDrop d N ν lam:ℝ) := by
    intro x y hx hs
    exact (transition_spec coords hA hA0 hrank htr hν hν1 hlam hlam1 hvar x y hx hs).2
  have hrq := uniformDrop_pos (N:=N) (d:=d) hν hlam
  have hrr : (0:ℝ) < uniformDrop d N ν lam := by exact_mod_cast hrq
  have he := epsilon_spec (d:=d) hν hν1
  have hε : (0:ℝ) < ((ν/(d:ℚ):ℚ):ℝ) := by exact_mod_cast he.1
  have hεd : ((ν/(d:ℚ):ℚ):ℝ)*(d:ℝ) ≤ 1 := by exact_mod_cast he.2.2
  have hnorm (x : Fin N → ℚ) (hx : P x) :
      operatorNorm (S (rationalAtoms coords) (pointCast x)) ≤ f x := by
    apply norm_le_potential (rationalAtoms coords) hA htr hε hεd
      (by exact_mod_cast hlam.le) (by exact_mod_cast hν1) hvar
    intro i
    change |(x i:ℝ)| ≤ 1
    exact_mod_cast hx.1 i
  have hnon : ∀ x,P x → 0 ≤ f x := by
    intro x hx
    exact (operatorNorm_nonneg _).trans (hnorm x hx)
  have hzero : ∀ i : Fin N, |(0:Fin N → ℚ) i| ≤ 1 := by intro i;norm_num
  have hx₀ : P x₀ := freezeAll_stripCube _ _ hzero
  have hi : f x₀ ≤ (3931/100:ℝ)*Real.sqrt (ν:ℝ) := by
    have hh := potential_zero_le (rationalAtoms coords) (by exact_mod_cast hν) hlamhi hvar
    have hf := fullPotential_freeze coords hA htr hν hν1 hlam.le hvar (0:Fin N → ℚ) hzero
    apply hf.trans
    have hz : pointCast (0:Fin N → ℚ)=0 := by ext i; simp [pointCast]
    change fullPotential coords ν lam 0 ≤ _
    unfold fullPotential
    rw [hz]
    simpa only [Rat.cast_div,Rat.cast_natCast] using hh
  have hi100 : f x₀ ≤ 100 := by
    have hs : Real.sqrt (ν:ℝ) ≤ 1 := (Real.sqrt_le_one).mpr (by exact_mod_cast hν1)
    linarith
  have hk : f x₀ < (k:ℝ)*(uniformDrop d N ν lam:ℝ) :=
    lt_of_le_of_lt hi100 (fuel_spec hrq)
  have ht : step (run step k x₀)=none := run_terminates step P f hrr hnon hp hd k x₀ hx₀ hk
  have hxf : P (run step k x₀) := run_invariant step P hp k x₀ hx₀
  have hv : f (run step k x₀) ≤ f x₀ := run_value_le step P f hp
    (fun x y hx hs => (hd x y hx hs).trans (sub_le_self _ hrr.le)) k x₀ hx₀
  exact ⟨terminal_vertex coords ν lam _ hxf.1 ht,(hnorm _ hxf).trans (hv.trans hi)⟩

lemma scalar_coefficient40 {v w : ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hvw : v ≤ (1001/1000:ℝ)*w) :
    (3931/100:ℝ)*Real.sqrt v ≤ 40*Real.sqrt w := by
  have hv2 := Real.sq_sqrt hv
  have hw2 := Real.sq_sqrt hw
  have hs : 0 ≤ Real.sqrt w := Real.sqrt_nonneg _
  nlinarith [Real.sqrt_nonneg v,
    sq_nonneg (40*Real.sqrt w-(3931/100:ℝ)*Real.sqrt v)]

end

open CurrentKS.RationalSDP CurrentKS.Schedule

variable {d N : ℕ}

def normalizedRun (coords : Fin N → Fin d × Fin d → ℚ) : Fin N → ℚ :=
  let ν := varianceQuery coords
  rationalRun coords ν (penaltyParameter N ν)

open CurrentKS.Hermitian CurrentKS.State CurrentKS.Difference
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

theorem normalizedRun_spec [NeZero d] [NeZero N]
    (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hA0 : ∀ i,rationalAtoms coords i≠0)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1) :
    (∀ i,|normalizedRun coords i|=1) ∧
      operatorNorm (S (rationalAtoms coords) (pointCast (normalizedRun coords))) ≤
        40*Real.sqrt (operatorNorm (varianceH (rationalAtoms coords))) := by
  let ν := varianceQuery coords
  let lam := penaltyParameter N ν
  have hν := varianceQuery_spec coords hA hrank htr
  have hlam := penaltyParameter_pos_le (NeZero.pos N) hν.1 hν.2.1
  have hi := penaltyParameter_interval (NeZero.pos N) hν.1 hν.2.1
  have hvar : varianceH (rationalAtoms coords) ≤ (ν:ℝ) • (Hermitian.one : H d) :=
    (le_operatorNorm_smul_one _).trans (scalar_one_mono hν.2.2.1)
  have hh := rationalRun_spec coords hA hA0 hrank htr hν.1 hν.2.1
    hlam.1 hlam.2 hi.2 hvar
  exact ⟨hh.1,hh.2.trans (scalar_coefficient40 (by exact_mod_cast hν.1.le)
    (operatorNorm_nonneg _) hν.2.2.2)⟩

end CurrentKS.RationalFace

open Matrix

end

end OAI
