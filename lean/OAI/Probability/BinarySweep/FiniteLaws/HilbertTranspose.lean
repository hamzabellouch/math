import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.YoungTranspose
import OAI.Probability.BinarySweep.Conditional.ConditionalSpecht

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Irrep Representation

variable (μ : YoungDiagram)

lemma norm_signC (g : G μ) : ‖signC μ g‖=1 := by
  have h := congrArg Norm.norm (signC_sq μ g)
  rw [norm_mul,norm_one] at h
  nlinarith [norm_nonneg (signC μ g)]

lemma hilbert_transpose_equiv : Nonempty ((hilbertSpecht μ).Equiv
    (signTwist μ ((hilbertSpecht μ.transpose).comp (transposeCells μ).permCongrHom.toMonoidHom))) := by
  obtain ⟨f⟩ := specht_transpose_sign μ
  let E := (spechtHilbertEquiv μ).symm.trans (f.toLinearEquiv.trans (spechtHilbertEquiv μ.transpose))
  refine ⟨.mk E ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := (spechtHilbertEquiv μ).surjective v
  change spechtHilbertEquiv μ.transpose
      (f.toLinearEquiv.toFun ((spechtHilbertEquiv μ).symm.toFun
        (spechtHilbertEquiv μ (spechtRep μ g ((spechtHilbertEquiv μ).symm.toFun
          (spechtHilbertEquiv μ w)))))) =
    signC μ g • spechtHilbertEquiv μ.transpose
      (spechtRep μ.transpose ((transposeCells μ).permCongr g)
        ((spechtHilbertEquiv μ.transpose).symm.toFun
          (spechtHilbertEquiv μ.transpose (f.toLinearEquiv.toFun
            ((spechtHilbertEquiv μ).symm.toFun (spechtHilbertEquiv μ w))))))
  have hs (ν : YoungDiagram) (x : SpechtSpace ν) :
      (spechtHilbertEquiv ν).symm.toFun (spechtHilbertEquiv ν x) = x :=
    (spechtHilbertEquiv ν).symm_apply_apply x
  simp only [hs]
  have h := Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap g w
  change f.toLinearEquiv.toFun (spechtRep μ g w) = signC μ g •
    spechtRep μ.transpose ((transposeCells μ).permCongr g) (f.toLinearEquiv.toFun w) at h
  exact (congrArg (spechtHilbertEquiv μ.transpose).toFun h).trans (map_smul _ _ _)

lemma hilbert_transpose_moment (p : G μ → ℂ) (q : ℕ) :
    evenMoment q (groupAverage (hilbertSpecht μ) p) =
      evenMoment q (groupAverage (hilbertSpecht μ.transpose)
        (fun g => p ((transposeCells μ).symm.permCongr g)*signC μ.transpose g)) := by
  obtain ⟨f⟩ := hilbert_transpose_equiv μ
  rw [equivalent_evenMoment _ _ f (hilbertSpecht_unitary μ) (fun g v => by
    change ‖signC μ g • hilbertSpecht μ.transpose ((transposeCells μ).permCongr g) v‖=‖v‖
    rw [norm_smul,norm_signC,hilbertSpecht_unitary,one_mul])]
  congr 1
  unfold groupAverage
  rw [←Equiv.sum_comp (transposeCells μ).permCongr]
  apply Finset.sum_congr rfl
  intro g _
  change p g • (signC μ g • hilbertSpecht μ.transpose ((transposeCells μ).permCongr g)) = _
  dsimp only
  rw [smul_smul,transpose_sign]
  rw [show (transposeCells μ).symm.permCongr ((transposeCells μ).permCongr g)=g from
    (transposeCells μ).permCongr.symm_apply_apply g]

end BinaryCoordinateSweeps.Young
namespace BinaryCoordinateSweeps
open Young Irrep

lemma realSign_permCongr_complex {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (e : X≃Y) (g : Equiv.Perm X) :
    (realSign (e.permCongr g):ℂ)=(realSign g:ℂ) := by
  exact congrArg (fun sign : ℤˣ => (((sign : ℤ) : ℝ) : ℂ))
    (Equiv.Perm.sign_permCongr e g)

lemma conditional_transpose_moment {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (μ : YoungDiagram) (e : Cell μ ≃ FreeSlot H 0) (z : ℝ) (q : ℕ) :
    evenMoment q (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g:ℂ))) =
    evenMoment q (groupAverage ((hilbertSpecht μ.transpose).comp
      ((transposeCells μ).symm.trans e).symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g*realSign g:ℂ))) := by
  rw [groupAverage_comp_slots,groupAverage_comp_slots,hilbert_transpose_moment]
  congr 2
  funext g
  congr 1
  rw [realSign_permCongr_complex]
  change ((Equiv.Perm.sign g:ℤ):ℂ)=(((Equiv.Perm.sign g:ℤ):ℝ):ℂ)
  norm_cast

end BinaryCoordinateSweeps

end

end OAI
