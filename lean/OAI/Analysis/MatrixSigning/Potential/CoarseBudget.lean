import Mathlib
import OAI.Analysis.MatrixSigning.Potential.NormCoordinate
import OAI.Analysis.MatrixSigning.Potential.ObjectiveVarsCLM
import OAI.Analysis.MatrixSigning.Potential.NormPsdScalar

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ}
private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace
private local instance : NormedAddCommGroup (Vars d) := inferInstance
private local instance : NormedSpace ℝ (Vars d) := inferInstance
private local instance : TopologicalSpace (Vars d) :=
  (inferInstance : NormedAddCommGroup (Vars d)).toUniformSpace.toTopologicalSpace
local instance : NormedAddCommGroup (H d →L[ℝ] H d) := inferInstance
local instance : NormedSpace ℝ (H d →L[ℝ] H d) := inferInstance

lemma contDiff_S (A : Fin N → H d) {n : WithTop ℕ∞} : ContDiff ℝ n (S A) := by
  apply ContDiff.sum
  intro i _
  exact (contDiff_apply ℝ ℝ i).smul contDiff_const

lemma contDiffAt_eta (c : ℝ) (A : Fin N → H d) {x : Coordinates N}
    (hx : ∀ i, |x i| < 1) {n : WithTop ℕ∞} : ContDiffAt ℝ n (eta c A) x := by
  apply ContDiffAt.sum
  intro i _
  have hp : ContDiffAt ℝ n (fun y : Coordinates N => psi (y i)) x :=
    (contDiffAt_psi (hx i)).comp x (contDiffAt_apply ℝ ℝ i x)
  have hc : ContDiffAt ℝ n (fun _ : Coordinates N => c) x := contDiffAt_const
  exact (hc.mul hp).smul (show ContDiffAt ℝ n (fun _ : Coordinates N => sandwichCLM (A i)) x from contDiffAt_const)

def coarseBudget (d N : ℕ) (ε σ : ℝ) : ℝ :=
  200+((d:ℝ)+1)+|ε|+(200/ε)*((d:ℝ)+1)+200*((d:ℝ)+1)+
    (((d:ℝ)+1)+N)+384*N*(1+800/σ^3)

lemma coarseBudget_bounds {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    1 ≤ coarseBudget d N ε σ ∧ (d:ℝ)+1 ≤ coarseBudget d N ε σ ∧
    |ε| ≤ coarseBudget d N ε σ ∧
    200+(200/ε)*((d:ℝ)+1) ≤ coarseBudget d N ε σ ∧
    200*((d:ℝ)+1) ≤ coarseBudget d N ε σ ∧
    ((d:ℝ)+1)+N ≤ coarseBudget d N ε σ ∧
    384*N*(1+800/σ^3) ≤ coarseBudget d N ε σ := by
  have hd : 0 ≤ (d:ℝ)+1 := by positivity
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hp : 0 ≤ (200/ε)*((d:ℝ)+1) := by positivity
  have hr : 0 ≤ 384*(N:ℝ)*(1+800/σ^3) := by positivity
  have he := abs_nonneg ε
  dsimp [coarseBudget]
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor <;> linarith

lemma contDiffAt_face_eta (A : Fin N → H d) (x : Coordinates N) (z : Vars d)
    (hxi : ∀ i, |x i| < 1) :
    ContDiffAt ℝ 3 (fun v : Coordinates N × Vars d => eta 384 A v.1) (x,z) := by
  exact ContDiffAt.comp (f := fun v : Coordinates N × Vars d => v.1)
    (g := eta 384 A) (x,z) (contDiffAt_eta 384 A hxi)
    (contDiffAt_fst : ContDiffAt ℝ 3 (fun v : Coordinates N × Vars d => v.1) (x,z))

lemma strip_S_jet (A : Fin N → H d) (hA : ∀ i, ‖A i‖ ≤ 1)
    (S₀ : H d) (hS₀ : ‖S₀‖ ≤ (d:ℝ)+1) (x : Coordinates N) (z : Vars d)
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2) :
    JetBound (fun v : Coordinates N × Vars d => S₀+S A v.1) (x,z)
      (coarseBudget d N ε σ) := by
  have hxi (i : Fin N) : |x i| < 1 := strip_interior hσ (hx i)
  let L : (Coordinates N × Vars d) →L[ℝ] Coordinates N := ContinuousLinearMap.fst ℝ _ _
  have hLc : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ..
  have h := (JetBound.const S₀ (x,z)).add contDiffAt_const
    ((contDiff_S A).contDiffAt.comp (x,z) contDiffAt_fst)
    (jetBound_S A hA L hLc (fun i => (hxi i).le))
  exact h.mono (by linarith [(coarseBudget_bounds (d:=d) (N:=N) hε hσ).2.2.2.2.2.1])

lemma strip_eta_jet (A : Fin N → H d) (hA : ∀ i, ‖A i‖ ≤ 1)
    (x : Coordinates N) (z : Vars d) {ε σ : ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hx : ∀ i, |x i| ≤ 1-σ/2) :
    JetBound (fun v : Coordinates N × Vars d => eta 384 A v.1) (x,z)
      (coarseBudget d N ε σ) := by
  let L : (Coordinates N × Vars d) →L[ℝ] Coordinates N := ContinuousLinearMap.fst ℝ _ _
  have hLc : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ..
  have h := jetBound_eta 384 A hA L hLc (z:=(x,z)) hσ hx
  apply h.mono
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<384)]
  nlinarith [(coarseBudget_bounds (d:=d) (N:=N) hε hσ).2.2.2.2.2.2]

lemma kkt_strip_jet (A : Fin N → H d) (hA : ∀ i,‖A i‖ ≤ 1)
    (S₀ : H d) (hS₀ : ‖S₀‖ ≤ (d:ℝ)+1) (x : Coordinates N) {ε σ : ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2)
    (z : Vars d) (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d)
    (hz : ‖z‖ ≤ 200+(200/ε)*((d:ℝ)+1))
    (hiX : ‖invH (xCoord d z)‖ ≤ 200*((d:ℝ)+1))
    (hiY : ‖invH (yCoord d z)‖ ≤ 200*((d:ℝ)+1))
    (hP : ‖mCoord d z‖ ≤ 1) (hQ : ‖nCoord d z‖ ≤ 1) :
    JetBound (fun v : Coordinates N × Vars d => kktSystem ε (S₀+S A v.1) (eta 384 A v.1) v.2)
      (x,z) (300*(coarseBudget d N ε σ)^5) := by
  obtain ⟨hb,hd,he,hzB,hiB,hSB,hηB⟩ := coarseBudget_bounds (d:=d) (N:=N) hε hσ
  let Z : (Coordinates N × Vars d) →L[ℝ] Vars d := ContinuousLinearMap.snd ℝ _ _
  have hZc : ‖Z‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ..
  exact jetBound_kktGiven Z hZc (hz.trans hzB) hb hd he hX hY
    (hiX.trans hiB) (hiY.trans hiB) hP hQ
    (contDiffAt_const.add ((contDiff_S A).contDiffAt.comp (x,z) contDiffAt_fst))
    (contDiffAt_face_eta A x z (fun i => strip_interior hσ (hx i)))
    (strip_S_jet A hA S₀ hS₀ x z hε hσ hx) (strip_eta_jet A hA x z hε hσ hx)

theorem value_strip_derivatives [NeZero d] (A : Fin N → H d)
    (_hA : ∀ i,A i ∈ psdCone d) (hAn : ∀ i,‖A i‖ ≤ 1)
    (S₀ : H d) (hS₀ : ‖S₀‖ ≤ (d:ℝ)+1) (x h : Coordinates N)
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2) (hh : ‖h‖ ≤ 1)
    (hlo : -(100:ℝ) • (Hermitian.one : H d) ≤ S₀+S A x)
    (hhi : S₀+S A x ≤ (100:ℝ) • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible (S₀+S A x) (eta 384 A x)) (hz100 : objective ε z ≤ 100)
    (hmin : ∀ w ∈ feasible (S₀+S A x) (eta 384 A x),objective ε z ≤ objective ε w) :
    let B := coarseBudget d N ε σ
    let Jb := 10^18*((d:ℝ)+1)*(1+ε⁻¹)^4
    let D := 300*B^5
    let f := fun t : ℝ => value ε (S₀+S A (x+t • h)) (eta 384 A (x+t • h))
    |iteratedDeriv 2 f 0| ≤ (1+|ε| *(2*((d:ℝ)+1)))*(Jb*D*(1+Jb*D)^2) ∧
    |iteratedDeriv 3 f 0| ≤ (1+|ε| *(2*((d:ℝ)+1)))*
      (Jb*D*((1+Jb*D)^3+3*(1+Jb*D)*(Jb*D*(1+Jb*D)^2))) := by
  have hB : 0 < coarseBudget d N ε σ :=
    lt_of_lt_of_le zero_lt_one (coarseBudget_bounds (d:=d) (N:=N) hε hσ).1
  have hxi (i : Fin N) : |x i| < 1 := strip_interior hσ (hx i)
  have hpos := eta_positive (by norm_num : (0:ℝ)≤384) A (fun i => (hxi i).le)
  obtain ⟨P,Q,J,hP,hQ,hPn,hQn,hzero,hJ,hJi,hzB,hiX,hiY⟩ :=
    bounded_optimizer_data (S₀+S A x) (eta 384 A x) hpos (eta_symmetric 384 A x) hε hlo hhi z hz hz100 hmin
  apply value_curve_derivatives ε (fun y => S₀+S A y) (eta 384 A) x h
    (contDiffAt_const.add (contDiff_S A).contDiffAt) (contDiffAt_eta 384 A hxi)
    (Filter.Eventually.of_forall (fun y => eta_symmetric 384 A y)) (pack z P Q)
    hz.1.1 hz.1.2
    hP hQ hzero J
    hJ
    (by positivity) (by positivity) hJi hh
  exact kkt_strip_jet A hAn S₀ hS₀ x hε hσ hx (pack z P Q)
    hz.1.1 hz.1.2 hzB
    hiX hiY
    hPn hQn
end
end CurrentKS.State

end OAI
