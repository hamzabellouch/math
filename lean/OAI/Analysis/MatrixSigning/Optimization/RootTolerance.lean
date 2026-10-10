import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.RationalAtoms
import OAI.Analysis.MatrixSigning.Arithmetic.CubeInterval

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators

variable {d N : ℕ}

def rootTolerance (d N : ℕ) (lam error : ℚ) : ℚ :=
  error/(2*(38400*d+lam*N+1))

def potentialQuery (coords : Fin N → Fin d × Fin d → ℚ) (x : Fin N → ℚ)
    (ν lam error : ℚ) : ℚ :=
  let θ := fun i => CurrentKS.Scalar.approxPsi (x i) (rootTolerance d N lam error)
  valueQuery coords x θ ν (error/4)+lam*∑ i,θ i

noncomputable section
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational CurrentKS.State CurrentKS.Scalar
open Matrix Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius

lemma rootTolerance_pos {lam error : ℚ} (hlam : 0 ≤ lam) (he : 0 < error) :
    0 < rootTolerance d N lam error := by
  unfold rootTolerance
  positivity

lemma rootTolerance_bound {lam error : ℚ} (hlam : 0 ≤ lam) (he : 0 < error) :
    (38400*d+lam*N)*rootTolerance d N lam error ≤ error/2 := by
  have hD : 0 < (2*(38400*(d:ℚ)+lam*N+1)) := by positivity
  have hpos := rootTolerance_pos (d := d) (N := N) hlam he
  have hid : 2*(38400*(d:ℚ)+lam*N+1)*rootTolerance d N lam error=error := by
    unfold rootTolerance
    field_simp
  nlinarith

theorem potentialQuery_correct [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (x : Fin N → ℚ)
    (hA : ∀ i,rationalAtoms coords i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam error : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 ≤ lam)
    (he : 0 < error) (he1 : error ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hx : Cube (fun i => (x i:ℝ))) :
    |(potentialQuery coords x ν lam error:ℝ)-
      (value ((ν:ℝ)/d) (S (rationalAtoms coords) (fun i => (x i:ℝ)))
        (eta 384 (rationalAtoms coords) (fun i => (x i:ℝ)))+
        (lam:ℝ)*∑ i,psi (x i:ℝ))| ≤ (error:ℝ) := by
  let δ := rootTolerance d N lam error
  let θ := fun i => approxPsi (x i) δ
  let xr : Coordinates N := fun i => (x i:ℝ)
  let θr : Coordinates N := fun i => (θ i:ℝ)
  let A := rationalAtoms coords
  have hδ : 0 < δ := rootTolerance_pos hlam he
  have hroot (i : Fin N) := approxPsi_spec (x i) δ (hx i) hδ
  have hθ : ParameterCube θr := by
    intro i
    change 0 ≤ (approxPsi (x i) δ:ℝ) ∧ (approxPsi (x i) δ:ℝ) ≤ 1
    exact ⟨by exact_mod_cast (hroot i).1.1,by exact_mod_cast (hroot i).1.2⟩
  have hdiff : ∀ i,|θr i-psi (xr i)| ≤ (δ:ℝ) := fun i => (hroot i).2
  have hq := (valueQueryPoint_correct coords x θ hA htr hν hν1
    (by positivity : 0 < error/4) (by linarith : error/4 ≤ 1) hvar hx hθ).2
  have hp := etaTheta_value_perturbation A hA htr (ν := (ν:ℝ)) (δ := (δ:ℝ)) (lam := (lam:ℝ)) (by exact_mod_cast hν)
    (by exact_mod_cast hν1) (by exact_mod_cast hδ.le) (by exact_mod_cast hlam)
    hvar xr θr (fun i => psi (xr i)) hx hθ (parameterCube_psi hx) hdiff
  let mid : ℝ := value ((ν:ℝ)/d) (S A xr) (etaTheta 384 A θr)+(lam:ℝ)*∑ i,θr i
  have hqm : |(potentialQuery coords x ν lam error:ℝ)-mid| ≤ (error:ℝ)/2 := by
    dsimp only [potentialQuery,mid]
    push_cast
    have heq : ((ν/d:ℚ):ℝ)=(ν:ℝ)/d := by push_cast; rfl
    simp only [heq,Rat.cast_div,Rat.cast_ofNat] at hq
    convert hq using 1 <;> first | rfl | ((try dsimp [θ,θr,A,xr,δ]); ring_nf)
  have hpm : |mid-(value ((ν:ℝ)/d) (S A xr) (eta 384 A xr)+
      (lam:ℝ)*∑ i,psi (xr i))| ≤ (error:ℝ)/2 := by
    apply hp.trans
    exact_mod_cast rootTolerance_bound (d := d) (N := N) hlam he
  change |(potentialQuery coords x ν lam error:ℝ)-
    (value ((ν:ℝ)/d) (S A xr) (eta 384 A xr)+(lam:ℝ)*∑ i,psi (xr i))| ≤ _
  exact (abs_sub_le _ mid _).trans (by linarith)

end
end CurrentKS.RationalSDP

end OAI
