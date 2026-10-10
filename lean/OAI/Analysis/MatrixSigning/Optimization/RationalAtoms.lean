import Mathlib
import OAI.Analysis.MatrixSigning.Potential.ParameterCube
import OAI.Analysis.MatrixSigning.Optimization.ValueObjectiveCoeffs

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.RationalSDP
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational CurrentKS.State
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

def rationalAtoms (coords : Fin N → Fin d × Fin d → ℚ) (i : Fin N) : H d :=
  assemble (WithLp.toLp 2 fun j => (coords i j:ℝ))

lemma complexSum_rationalAtoms (coords : Fin N → Fin d × Fin d → ℚ) (x : Fin N → ℚ) :
    complexSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ)) =
      ((S (rationalAtoms coords) (fun i => (x i:ℝ))) : Mat d) := by
  simp only [complexSum,S,Submodule.coe_sum,Submodule.coe_smul_of_tower,
    rationalAtoms,assemble]

lemma complexEta_rationalAtoms (coords : Fin N → Fin d × Fin d → ℚ) (θ : Fin N → ℚ)
    (Z : H d) :
    complexEta (fun i j => (coords i j:ℝ)) (fun i => (θ i:ℝ)) Z =
      ((etaTheta 384 (rationalAtoms coords) (fun i => (θ i:ℝ))) Z : Mat d) := by
  rw [etaTheta_apply]
  simp only [complexEta,Submodule.coe_sum,Submodule.coe_smul_of_tower,rationalAtoms,assemble]
  rfl

lemma valuePencil_feasible (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (ε : ℚ) (v : EuclideanSpace ℝ (Fin (valueDimension d))) :
    v ∈ (valuePencil coords x θ ε).feasible ↔
      unpackValue v ∈ valueSpectrahedron (ε:ℝ)
        (S (rationalAtoms coords) (fun i => (x i:ℝ)))
        (etaTheta 384 (rationalAtoms coords) (fun i => (θ i:ℝ))) := by
  change ((valuePencil coords x θ ε).realEval v).PosSemidef ↔ _
  rw [valuePencil_psd,complexSum_rationalAtoms]
  exact complexValueProgram_iff _ _ _ _ (complexEta_rationalAtoms coords θ) (unpackValue v)

lemma valuePencil_ball (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (hA : ∀ i,rationalAtoms coords i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν : ℝ} (hν : ν ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    (hx : Cube (fun i => (x i:ℝ))) (hθ : ParameterCube (fun i => (θ i:ℝ)))
    {ε : ℚ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Metric.closedBall (packValue (50,(1/20:ℝ) • (Hermitian.one : H d),
      (1/20:ℝ) • (Hermitian.one : H d))) (valueInnerRadius d:ℝ) ⊆
      (valuePencil coords x θ ε).feasible := by
  intro v hv
  apply (valuePencil_feasible coords x θ ε v).mpr
  apply value_center_coordinate_ball _ _ (etaTheta_positive (by norm_num) _ hθ) _ _ _ hε hε1 v hv
  · exact (etaTheta_one_bound (by norm_num) _ hvar hθ).trans
      (scalar_one_mono (by linarith : 384*ν≤384))
  · convert (S_bounds _ hA htr hx).1 using 1
    exact neg_one_smul ℝ (Hermitian.one : H d)
  · simpa only [one_smul] using (S_bounds _ hA htr hx).2

lemma valueOuterRadius_le {ε : ℚ} (hε : 0 < ε) : 100 ≤ valueOuterRadius d ε := by
  have hm : (0:ℚ) ≤ 400/ε*((d:ℚ)+1) := by positivity
  have hd : (0:ℚ) ≤ valueDimension d := Nat.cast_nonneg _
  unfold valueOuterRadius
  nlinarith

lemma valueLipschitz_le {ε : ℚ} (hε : 0 ≤ ε) : 1 ≤ valueLipschitz d ε := by
  have hm : (0:ℚ) ≤ 2*ε*d := by positivity
  have hd : (0:ℚ) ≤ valueDimension d := Nat.cast_nonneg _
  unfold valueLipschitz
  nlinarith


def valueQueryPoint (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (ν δ : ℚ) : Fin (valueDimension d) → ℚ :=
  let ε := ν/d
  let L := valueLipschitz d ε
  let R := valueOuterRadius d ε
  let r := valueInnerRadius d
  (valuePencil coords x θ ε).optimize (valueObjectiveCoeffs d ε) δ
    (nearRadius δ L R r) R 100 (optimizeFuel δ 100)

def valueQuery (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ) (ν δ : ℚ) : ℚ :=
  valueObjective d (ν/d) (valueQueryPoint coords x θ ν δ)

lemma valueQueryPoint_correct [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (hA : ∀ i,rationalAtoms coords i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν δ : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hx : Cube (fun i => (x i:ℝ))) (hθ : ParameterCube (fun i => (θ i:ℝ))) :
    let ε : ℚ := ν/d
    let y := valueQueryPoint coords x θ ν δ
    realVector y ∈ (valuePencil coords x θ ε).feasible ∧
      |(valueQuery coords x θ ν δ:ℝ)-value (ε:ℝ)
        (S (rationalAtoms coords) (fun i => (x i:ℝ)))
        (etaTheta 384 (rationalAtoms coords) (fun i => (θ i:ℝ)))| ≤ 2*(δ:ℝ) := by
  let ε : ℚ := ν/d
  let A := rationalAtoms coords
  let xr : Coordinates N := fun i => (x i:ℝ)
  let θr : Coordinates N := fun i => (θ i:ℝ)
  have hd : (0:ℚ) < d := by exact_mod_cast NeZero.pos d
  have hd1 : (1:ℚ) ≤ d := by exact_mod_cast NeZero.pos d
  have hε : 0 < ε := div_pos hν hd
  have hε1 : ε ≤ 1 := (div_le_one hd).mpr (hν1.trans hd1)
  have hεr : (ε:ℝ) = (ν:ℝ)/d := by simp [ε]
  have hpos := etaTheta_positive (show (0:ℝ)≤384 by norm_num) A hθ
  obtain ⟨z,hz,hz100,hzmin⟩ := etaTheta_minimizer A hA htr (by exact_mod_cast hν)
    (by exact_mod_cast hν1) hvar xr θr hx hθ
  rw [← hεr] at hz100 hzmin
  have hSl : -(100:ℝ) • (Hermitian.one : H d) ≤ S A xr := by
    have hb := (S_bounds A hA htr hx).1
    exact (show -(100:ℝ) • (Hermitian.one : H d) ≤ -(Hermitian.one : H d) by
      calc
        (-100:ℝ) • (Hermitian.one : H d) ≤ (-1:ℝ) • Hermitian.one :=
          scalar_one_mono (by norm_num)
        _ = -Hermitian.one := neg_one_smul ℝ (Hermitian.one : H d)).trans hb
  have hSu : S A xr ≤ (100:ℝ) • (Hermitian.one : H d) := by
    exact (S_bounds A hA htr hx).2.trans (by
      simpa only [one_smul] using scalar_one_mono (d := d) (show (1:ℝ)≤100 by norm_num))
  have hbz := sublevel_oracleBox (S A xr) (etaTheta 384 A θr) hpos
    (by exact_mod_cast hε) hSl hSu z hz hz100
  have hzK : packValue z ∈ (valuePencil coords x θ ε).feasible := by
    rw [valuePencil_feasible,unpack_packValue]
    exact (mem_valueSpectrahedron _ _ _ _).mpr ⟨hbz,hz⟩
  let c : Point d := (50,(1/20:ℝ) • (Hermitian.one : H d),(1/20:ℝ) • Hermitian.one)
  have hball := valuePencil_ball coords x θ hA htr (by exact_mod_cast hν1) hvar hx hθ hε hε1
  have hcK : packValue c ∈ (valuePencil coords x θ ε).feasible :=
    hball (by exact Metric.mem_closedBall_self (by exact_mod_cast (valueInnerRadius_pos (d := d)).le))
  have hbc : oracleBox (ε:ℝ) c := by
    have hh := (valuePencil_feasible coords x θ ε (packValue c)).mp hcK
    rw [unpack_packValue] at hh
    exact (mem_valueSpectrahedron _ _ _ _).mp hh |>.1
  have hsmall : δ ≤ valueLipschitz d ε*(2*valueOuterRadius d ε+valueInnerRadius d) := by
    have hl := valueLipschitz_le (d := d) hε.le
    have hr := valueOuterRadius_le (d := d) hε
    have hi := valueInnerRadius_pos (d := d)
    nlinarith
  have hzn : 0 ≤ objective (ε:ℝ) z := by
    obtain ⟨hzt,hzX,hzY⟩ := trace_bounds_of_feasible (S A xr) (etaTheta 384 A θr) hpos hz
    simp only [objective,Hermitian.realTrace_add]
    exact add_nonneg hzt (mul_nonneg (by exact_mod_cast hε.le) (add_nonneg hzX hzY))
  have hres := (valuePencil coords x θ ε).optimize_nearOptimal (valueObjectiveCoeffs d ε)
    δ (valueLipschitz d ε) (valueOuterRadius d ε) (valueInnerRadius d) 100 (packValue z) (packValue c)
    hδ (valueLipschitz_pos hε.le) (valueOuterRadius_nonneg hε) valueInnerRadius_pos valueInnerRadius_le
    (objectiveCLM_value_norm hε.le) hzK (oracleBox_norm_packValue hε z hbz)
    (oracleBox_norm_packValue hε c hbc) hball hsmall (by
      rw [objectiveCLM_value,unpack_packValue]
      exact ⟨by norm_num; linarith,hz100⟩)
  change realVector (valueQueryPoint coords x θ ν δ) ∈ (valuePencil coords x θ ε).feasible ∧
    objectiveCLM (valueObjectiveCoeffs d ε) (realVector (valueQueryPoint coords x θ ν δ)) ≤
      objectiveCLM (valueObjectiveCoeffs d ε) (packValue z)+2*(δ:ℝ) at hres
  have he : (valueQuery coords x θ ν δ:ℝ) =
      objectiveCLM (valueObjectiveCoeffs d ε) (realVector (valueQueryPoint coords x θ ν δ)) := by
    rw [objectiveCLM_apply]
    unfold valueQuery
    rw [← valueObjectiveCoeffs_dot]
    simp only [dotProduct,Rat.cast_sum,Rat.cast_mul,realVector,PiLp.toLp_apply]
    rfl
  have hmin := value_eq_of_min (ε:ℝ) (S A xr) (etaTheta 384 A θr) z hz hzmin
  have hyv := (mem_valueSpectrahedron _ _ _ _).mp
    ((valuePencil_feasible coords x θ ε _).mp hres.1) |>.2
  have hlow := value_le_feasible (ε:ℝ) (by exact_mod_cast hε.le) (S A xr)
    (etaTheta 384 A θr) hpos _ hyv
  refine ⟨hres.1,?_⟩
  change |(valueQuery coords x θ ν δ:ℝ)-value (ε:ℝ) (S A xr) (etaTheta 384 A θr)| ≤ _
  have hu := hres.2
  rw [objectiveCLM_value,objectiveCLM_value,unpack_packValue,← hmin] at hu
  rw [he,objectiveCLM_value,abs_of_nonneg (sub_nonneg.mpr hlow)]
  linarith

end CurrentKS.RationalSDP

end

end OAI
