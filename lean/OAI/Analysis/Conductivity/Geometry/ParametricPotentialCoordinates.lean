import Mathlib
import OAI.Analysis.Conductivity.Geometry.RegularPotentialCoordinates
import OAI.Analysis.Conductivity.Variational.ParametricDiffeomorph

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_parametric_potential_coordinates
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (p : P) (x : Coord3) (hD : Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    {U : Set (P×Coord3)} (hU : IsOpen U) (hpx : (p,x)∈U) :
    ∃ Y : OpenPartialHomeomorph (P×Coord3) (P×Coord3),
      (p,x)∈Y.source ∧ Y.source⊆U ∧
      (∀ q y,(Y (q,y)).1=q) ∧
      (∀ q y,coordinatePair (Y (q,y)).2=u (q,y)) ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) Y ∧ ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target := by
  let D := fderiv ℝ (fun y => u (p,y)) x
  obtain ⟨Q,hQ⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hD
  let L := potentialCompletionEquiv D hD
  let φ : P×Coord3 → Coord3 := fun q => L (completedPotential (fun y => u (q.1,y)) D Q q.2)
  have hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ :=
    L.contDiff.comp (((Q.contDiff.comp hu).add contDiff_snd).sub (Q.contDiff.comp (D.contDiff.comp contDiff_snd)))
  have hup : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => u (p,y)) :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  have hφd : fderiv ℝ (fun y => φ (p,y)) x=(L : Coord3 →L[ℝ] Coord3) := by
    have hh := L.hasFDerivAt.comp x (completedPotential_derivative
      ((hup.differentiable (by simp) x).hasFDerivAt) Q)
    simpa only [φ,D,Function.comp_def,ContinuousLinearMap.comp_id] using hh.fderiv
  obtain ⟨Y,hp,hsub,he,hY,hYi⟩ := exists_parametric_diffeomorph hφ p x L hφd hU hpx
  refine ⟨Y,hp,hsub,fun q y => by rw [he],?_,hY,hYi⟩
  intro q y
  rw [he]
  exact (potentialCompletionEquiv_pairing D hD _).trans
    (completedPotential_pairing (fun y => u (q,y)) D Q hQ y)

omit [FiniteDimensional ℝ P] in
lemma fiberSlice_smooth
    (Y : OpenPartialHomeomorph (P×Coord3) (P×Coord3))
    (hY : ∀ p x,(Y (p,x)).1=p)
    (hsm : ContDiff ℝ (↑(⊤:ℕ∞)) Y)
    (hinv : ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target) (p : P) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fiberSlice Y hY p) ∧
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fiberSlice Y hY p).symm (fiberSlice Y hY p).target := by
  constructor
  · exact contDiff_snd.comp (hsm.comp (contDiff_const.prodMk contDiff_id))
  · exact contDiff_snd.contDiffOn.comp
      (hinv.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hx => hx))
      (fun _ _ => mem_univ _)

end ScalarConductivity

end

end OAI
