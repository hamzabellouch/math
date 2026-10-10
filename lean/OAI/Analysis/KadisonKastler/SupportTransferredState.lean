import OAI.Analysis.KadisonKastler.SupportVectorTransfer
import OAI.Analysis.KadisonKastler.SupportCompressedMatrix

namespace OAI

/-! # Vector states under the support-corner transfer -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem support_transfer_vector_state (M : VonNeumannAlgebra H) (ξ : H)
    (v : Algebra M) (w : Algebra M.commutant)
    (hwq : w.val * star w.val = (vectorSupportProjection M.commutant ξ).val.val)
    (a : Algebra M) :
    inner ℂ (star (v.val * w.val) ξ) (a.val (star (v.val * w.val) ξ)) =
      inner ℂ ξ ((v.val * a.val * star v.val) ξ) := by
  have hwa : w.val * a.val = a.val * w.val :=
    (VonNeumannAlgebra.mem_commutant_iff.mp w.property a.val a.property).symm
  have hqv : (w.val * star w.val) * star v.val =
      star v.val * (w.val * star w.val) :=
    (VonNeumannAlgebra.mem_commutant_iff.mp
      (M.commutant.mul_mem w.property (M.commutant.star_mem' w.property))
      (star v.val) (M.star_mem' v.property)).symm
  have hqξ : (w.val * star w.val) ξ = ξ := by
    rw [hwq,vectorSupportProjection_apply]
  have he : w.val (a.val (star w.val (star v.val ξ))) = a.val (star v.val ξ) := by
    change (w.val * a.val * star w.val * star v.val) ξ = _
    rw [hwa]
    have he' : (a.val * w.val) * star w.val * star v.val =
        a.val * star v.val * (w.val * star w.val) := by
      calc
        _ = a.val * ((w.val * star w.val) * star v.val) := by simp only [mul_assoc]
        _ = _ := by rw [hqv]; simp only [mul_assoc]
    rw [he',mul_apply_eq_comp,hqξ]
    rfl
  rw [star_mul]
  change inner ℂ (w.val.adjoint (star v.val ξ))
    (a.val (star w.val (star v.val ξ))) = _
  rw [w.val.adjoint_inner_left,he]
  change inner ℂ (v.val.adjoint ξ) (a.val (star v.val ξ)) = _
  rw [v.val.adjoint_inner_left]
  rfl

theorem supportCompressedMatrixUnits_centralizes
    {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : MatrixUnitSystem ι (Algebra M)) (ξ : H)
    (hcentral : ∀ i j (x : Algebra M),
      inner ℂ ξ (((E.entry i j) * x).val ξ) =
        inner ℂ ξ ((x * E.entry i j).val ξ))
    (v : Algebra M) (w : Algebra M.commutant) (hv : star v * v = 1)
    (hcomm : ∀ i j, (v * star v) * E.entry i j = E.entry i j * (v * star v))
    (hwq : w.val * star w.val = (vectorSupportProjection M.commutant ξ).val.val)
    (i j : ι) (x : Algebra M) :
    let Ω := star (v.val * w.val) ξ
    let F := supportCompressedMatrixUnits E v hv hcomm
    inner ℂ Ω ((F.entry i j * x).val Ω) =
      inner ℂ Ω ((x * F.entry i j).val Ω) := by
  dsimp only
  rw [support_transfer_vector_state M ξ v w hwq,
    support_transfer_vector_state M ξ v w hwq]
  let F := supportCompressedMatrixUnits E v hv hcomm
  have hl : v * (F.entry i j * x) * star v = E.entry i j * (v * x * star v) := by
    calc
      _ = (v * F.entry i j) * x * star v := by simp only [mul_assoc]
      _ = _ := by
        rw [← supportCompressedMatrixUnits_intertwine E v hv hcomm i j]
        simp only [mul_assoc]
  have hr : v * (x * F.entry i j) * star v = (v * x * star v) * E.entry i j := by
    calc
      _ = v * x * (F.entry i j * star v) := by simp only [mul_assoc]
      _ = _ := by
        rw [← supportCompressedMatrixUnits_intertwine_star E v hv hcomm i j]
        simp only [mul_assoc]
  change inner ℂ ξ ((v * (F.entry i j * x) * star v).val ξ) =
    inner ℂ ξ ((v * (x * F.entry i j) * star v).val ξ)
  rw [hl,hr]
  exact hcentral i j (v * x * star v)

end

end KadisonKastler

end OAI
