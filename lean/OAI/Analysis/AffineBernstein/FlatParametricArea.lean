import Mathlib
import OAI.Analysis.AffineBernstein.ParametricAffineArea
import OAI.Analysis.AffineBernstein.FlatTubeArea

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma parametricAreaDensity_flatSupport {n : ℕ}
    {H : S × E → ℝ} {Y : S × E → E} (q₀ : S × E)
    (J : Space n →L[ℝ] (S × E)) {x : Space n}
    (hY : ContDiffAt ℝ ∞ Y (q₀+J x))
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (e : Fin n ≃ ι ⊕ κ)
    (hJ : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i)) :
    let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
    parametricAreaDensity ((bS.prod bE.toBasis).reindex eA.symm)
      (fun y => supportParam Y (q₀+J y)) (supportConormal H (q₀+J x))
      (0,-bE (Sum.inr ())) x = flatTubeAffineAreaJet H Y (q₀+J x) bS bE := by
  let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
  let X := fun y => supportParam Y (q₀+J y)
  let ν := supportConormal H (q₀+J x)
  have hp : ContDiffAt ℝ ∞ (supportParam Y) (q₀+J x) := contDiffAt_fst.prodMk hY
  have hf : parametricFrame X (0,-bE (Sum.inr ())) x =
      flatTubeFrame Y (q₀+J x) bS bE ∘ eA := by
    funext i
    rcases i with i | ⟨⟩
    · have hd := (hp.differentiableAt (by simp)).hasFDerivAt.comp x (J.hasFDerivAt.const_add q₀)
      change fderiv ℝ X x (coordinateVector n i) = _
      have hdf : fderiv ℝ X x = _ := hd.fderiv
      rw [hdf]
      change fderiv ℝ (supportParam Y) (q₀+J x) (J (coordinateVector n i)) = _
      rw [hJ]
      rcases hei : e i with j | j <;> simp [eA,flatTubeFrame,tubeTangent,hei]
    · rfl
  let M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := Matrix.of fun i j => ν
    (fderiv ℝ (fderiv ℝ (supportParam Y)) (q₀+J x) (tubeTangent bS bE i) (tubeTangent bS bE j))
  have hm : parametricSecondForm X ν x = M.submatrix e e := by
    ext i j
    change dirDeriv (coordinateVector n i) (dirDeriv (coordinateVector n j)
      (fun y => ν (supportParam Y (q₀+J y)))) x =
        ν (fderiv ℝ (fderiv ℝ (supportParam Y)) (q₀+J x)
          (tubeTangent bS bE (e i)) (tubeTangent bS bE (e j)))
    have hνp : ContDiffAt ℝ ∞ (fun q => ν (supportParam Y q)) (q₀+J x) :=
      ν.contDiff.contDiffAt.comp (q₀+J x) hp
    have hq : ContDiffAt ℝ ∞ (fun y => q₀+J y) x :=
      contDiffAt_const.add J.contDiff.contDiffAt
    have hh : ContDiffAt ℝ ∞ (fun y => ν (supportParam Y (q₀+J y))) x :=
      hνp.comp (f := fun y => q₀+J y) x hq
    rw [dirDeriv_eq_second hh]
    rw [second_fderiv_affine_comp J q₀ hνp]
    rw [second_fderiv_clm_comp ν hp]
    simp [hJ]
  have hn : n = Fintype.card ι+Fintype.card κ := by
    simpa using Fintype.card_congr e
  change Real.rpow _ _ * Real.rpow _ _ = _
  rw [hm,Matrix.det_submatrix_equiv_self,hf,Module.Basis.det_reindex_symm]
  simp only [flatTubeAffineAreaJet,hn,Nat.cast_add]
  rfl

end AffineBernstein
end

end OAI
