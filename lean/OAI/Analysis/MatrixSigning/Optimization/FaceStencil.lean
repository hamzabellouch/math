import Mathlib
import OAI.Analysis.MatrixSigning.Potential.C1Rational
import OAI.Analysis.MatrixSigning.Potential.Parameters2
import OAI.Analysis.MatrixSigning.Potential.FaceState

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference CurrentKS.Descent

variable {d N : ℕ}

def faceStencil (coords : Fin N → Fin d × Fin d → ℚ) (base : Fin N → ℚ) (ν lam : ℚ) :
    (Fin (activeIndices base).length → ℚ) → ℚ :=
  fun y => faceQuery coords base y ν lam (parameters d (activeIndices base).length ν lam).stencilError

def faceScore (coords : Fin N → Fin d × Fin d → ℚ) (base : Fin N → ℚ) (ν lam : ℚ) :
    (Fin (activeIndices base).length → ℚ) → ℚ :=
  fun y => faceQuery coords base y ν lam (parameters d (activeIndices base).length ν lam).selectionError

def faceCandidates (coords : Fin N → Fin d × Fin d → ℚ) (base : Fin N → ℚ) (ν lam : ℚ)
    [NeZero (activeIndices base).length] : List (Fin (activeIndices base).length → ℚ) :=
  let p := parameters d (activeIndices base).length ν lam
  allCandidates (faceStencil coords base ν lam) (faceState base) p.h p.a p.M p.s p.ρ

def faceChoice (coords : Fin N → Fin d × Fin d → ℚ) (base : Fin N → ℚ) (ν lam : ℚ)
    [NeZero (activeIndices base).length] : Fin (activeIndices base).length → ℚ :=
  select (faceScore coords base ν lam) (faceState base) (faceCandidates coords base ν lam)

noncomputable section
open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff

lemma faceCandidates_cube [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (base : Fin N → ℚ) [NeZero (activeIndices base).length]
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hx : ∀ i,|faceState base i| ≤ 1-lam^2/ν) :
    ∀ y∈faceCandidates coords base ν lam, ∀ i,|y i| ≤ 1 := by
  let p := parameters d (activeIndices base).length ν lam
  have hp : p.Valid (activeIndices base).length :=
    parameters_valid (NeZero.pos d) (NeZero.pos _) hν hν1 hlam hlam1
  exact allCandidates_cube _ _ _ _ _ _ _ p.σ hp.threshold_pos hp.threshold_le
    hp.bound_one hp.step_pos.le hp.mesh_pos hp.mesh_error
    (by linarith [hp.step_strip,hp.strip_pos]) hp.strip_pos.le hx

lemma faceStencil_correct [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (base : Fin N → ℚ) [NeZero (activeIndices base).length]
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hb : ∀ i,|base i| ≤ 1) (hx : ∀ i,|faceState base i| ≤ 1-lam^2/ν) :
    let p := parameters d (activeIndices base).length ν lam
    ∀ y,‖pointCast y-pointCast (faceState base)‖ ≤ 2*(p.h:ℝ) →
      |(faceStencil coords base ν lam y:ℝ)-activePotential coords base ν lam (pointCast y)| ≤
        (p.a:ℝ)*(p.h:ℝ)^2/(128*(activeIndices base).length) := by
  let p := parameters d (activeIndices base).length ν lam
  have hp : p.Valid (activeIndices base).length :=
    parameters_valid (NeZero.pos d) (NeZero.pos _) hν hν1 hlam hlam1
  dsimp only
  intro y hy
  have hyc := nearby_rational_cube (faceState base) y (r:=2*p.h) (σ:=p.σ)
    (by linarith [hp.stencil_pos]) hx (by simpa only [Rat.cast_mul,Rat.cast_ofNat] using hy)
    (by linarith [hp.stencil_strip,hp.strip_pos])
  have hq := activeQuery_correct coords base y hA htr hν hν1 hlam.le
    hp.stencilError_pos hp.stencilError_le hvar hb hyc
  apply hq.trans_eq
  simp only [p,parameters,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_natCast]

lemma faceCandidates_progress [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (base : Fin N → ℚ) [NeZero (activeIndices base).length]
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hA0 : ∀ i,rationalAtoms coords i≠0)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hb : ∀ i,|base i| ≤ 1) (hx : ∀ i,|faceState base i| ≤ 1-lam^2/ν) :
    let p := parameters d (activeIndices base).length ν lam
    ∃ y∈faceCandidates coords base ν lam,
      activePotential coords base ν lam (pointCast y) ≤
        activePotential coords base ν lam (pointCast (faceState base))-2*(p.a:ℝ)*(p.s:ℝ)^2 := by
  let p := parameters d (activeIndices base).length ν lam
  have hp : p.Valid (activeIndices base).length :=
    parameters_valid (NeZero.pos d) (NeZero.pos _) hν hν1 hlam hlam1
  have hepd : p.ε*(d:ℚ) ≤ 1 := (epsilon_spec (d:=d) hν hν1).2.2
  have hbr : Cube (fun i => (base i:ℝ)) := fun i => (show |(base i:ℝ)| ≤ 1 by exact_mod_cast hb i)
  have hxc : Cube (pointCast (faceState base)) := by
    intro i
    change |(base (activeIndex base i):ℝ)| ≤ 1
    exact_mod_cast hb (activeIndex base i)
  have hord := face_order_bounds (activeIndex base) (activeIndex_injective base)
    (fun i => (base i:ℝ)) (rationalAtoms coords) hA htr hbr _ hxc
  have hη := face_eta_one_bound (activeIndex base) (activeIndex_injective base)
    (fun i => (base i:ℝ)) (rationalAtoms coords) (variance_le_one _ hν1 hvar)
    hbr (real_active_outside_endpoint base hb) _ hxc
  have hregular := activePotential_regular (lam:=lam) coords base hA htr hν hν1 hp.strip_pos hvar hb hx
    (show (0:ℝ) ≤ (p.s+2*p.h:ℚ) by exact_mod_cast (show (0:ℚ) ≤ p.s+2*p.h by linarith [hp.step_pos,hp.stencil_pos]))
    (show ((p.s+2*p.h:ℚ):ℝ) ≤ (p.σ:ℝ)/2 by exact_mod_cast hp.radius)
  have hreg : ∀ y,‖y-pointCast (faceState base)‖ ≤ (p.s:ℝ)+2*(p.h:ℝ) →
      ContDiffAt ℝ 3 (activePotential coords base ν lam) y := by
    intro y hy
    exact (hregular y (by simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat] using hy)).1
  have hders : ∀ y,‖y-pointCast (faceState base)‖ ≤ (p.s:ℝ)+2*(p.h:ℝ) → ∀ u,‖u‖ ≤ 1 →
      |iteratedDeriv 2 (fun t : ℝ => activePotential coords base ν lam (y+t • u)) 0| ≤ (p.M:ℝ) ∧
      |iteratedDeriv 3 (fun t : ℝ => activePotential coords base ν lam (y+t • u)) 0| ≤ (p.M:ℝ) := by
    intro y hy
    exact (hregular y (by simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat] using hy)).2
  exact face_candidates_progress (fun j => rationalAtoms coords (activeIndex base j))
    (fixedPart (activeIndex base) (fun i => (base i:ℝ)) (rationalAtoms coords)) (faceState base)
    (faceStencil coords base ν lam) p.ε lam p.σ p.h p.a p.M p.s p.ρ
    hp.epsilon_pos hp.epsilon_le hepd hlam hp.strip_pos hx (fun j => hA _) (fun j => hA0 _)
    (fun j => hrank _) hord.1 hord.2 hη rfl hp.threshold_pos hp.threshold_le hp.bound_one
    hp.step_pos hp.step_le hp.step_strip hp.step_curvature hp.stencil_pos hp.stencil_le
    hp.stencil_curvature hp.mesh_pos hp.mesh_error hreg hders
    (faceStencil_correct coords base hA htr hν hν1 hlam hlam1 hvar hb hx)

theorem faceChoice_spec [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (base : Fin N → ℚ) [NeZero (activeIndices base).length]
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hA0 : ∀ i,rationalAtoms coords i≠0)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hb : ∀ i,|base i| ≤ 1) (hx : ∀ i,|faceState base i| ≤ 1-lam^2/ν) :
    let p := parameters d (activeIndices base).length ν lam
    (∀ i,|faceChoice coords base ν lam i| ≤ 1) ∧
      activePotential coords base ν lam (pointCast (faceChoice coords base ν lam)) ≤
        activePotential coords base ν lam (pointCast (faceState base))-
          3*((p.a:ℝ)*(p.s:ℝ)^2)/2 := by
  let p := parameters d (activeIndices base).length ν lam
  have hp : p.Valid (activeIndices base).length :=
    parameters_valid (NeZero.pos d) (NeZero.pos _) hν hν1 hlam hlam1
  have hcube : ∀ y∈faceState base::faceCandidates coords base ν lam,∀ i,|y i| ≤ 1 := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl|hy
    · exact fun i => hb (activeIndex base i)
    · exact faceCandidates_cube coords base hν hν1 hlam hlam1 hx y hy
  have herr : ∀ y∈faceState base::faceCandidates coords base ν lam,
      |(faceScore coords base ν lam y:ℝ)-activePotential coords base ν lam (pointCast y)| ≤
        ((p.a:ℝ)*(p.s:ℝ)^2)/4 := by
    intro y hy
    have hq := activeQuery_correct coords base y hA htr hν hν1 hlam.le
      hp.selectionError_pos hp.selectionError_le hvar hb (hcube y hy)
    apply hq.trans_eq
    simp only [p,parameters,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat]
  have hprog := faceCandidates_progress coords base hA hA0 hrank htr hν hν1 hlam hlam1 hvar hb hx
  refine ⟨hcube _ (select_mem _ _ _),?_⟩
  apply select_decrease (fun y => activePotential coords base ν lam (pointCast y))
    (faceScore coords base ν lam) (faceState base) (faceState base) _ herr
  obtain ⟨y,hy,hd⟩ := hprog
  refine ⟨y,List.mem_cons_of_mem _ hy,?_⟩
  nlinarith

end
end CurrentKS.RationalFace

end OAI
