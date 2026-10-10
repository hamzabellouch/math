import OAI.Analysis.KadisonKastler.VectorSupportProjection

namespace OAI

/-! # Full matrix units transported from a supported corner -/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

def supportCompressedMatrixUnits (E : MatrixUnitSystem ι (Algebra M))
    (v : Algebra M) (hv : star v * v = 1)
    (hcomm : ∀ i j, (v * star v) * E.entry i j = E.entry i j * (v * star v)) :
    MatrixUnitSystem ι (Algebra M) where
  entry i j := star v * E.entry i j * v
  star_entry i j := by simp only [star_mul, star_star, E.star_entry, mul_assoc]
  mul_entry i j k l := by
    have hvv : (v * star v) * v = v := by rw [mul_assoc,hv,mul_one]
    calc
      (star v * E.entry i j * v) * (star v * E.entry k l * v) =
          star v * E.entry i j * ((v * star v) * E.entry k l) * v := by
        simp only [mul_assoc]
      _ = star v * (E.entry i j * E.entry k l) * ((v * star v) * v) := by
        rw [hcomm k l]
        simp only [mul_assoc]
      _ = if j = k then star v * E.entry i l * v else 0 := by
        rw [hvv,E.mul_entry]
        split_ifs <;> simp
  total := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, E.total, mul_one,hv]

theorem supportCompressedMatrixUnits_hom (E : MatrixUnitSystem ι (Algebra M))
    (v : Algebra M) (hv : star v * v = 1)
    (hcomm : ∀ i j, (v * star v) * E.entry i j = E.entry i j * (v * star v))
    (a : Matrix ι ι ℂ) :
    (supportCompressedMatrixUnits E v hv hcomm).hom a = star v * E.hom a * v := by
  simp only [MatrixUnitSystem.hom_apply, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc]
  rfl

theorem supportCompressedMatrixUnits_concreteHom (E : MatrixUnitSystem ι (Algebra M))
    (v : Algebra M) (hv : star v * v = 1)
    (hcomm : ∀ i j, (v * star v) * E.entry i j = E.entry i j * (v * star v))
    (a : Matrix ι ι ℂ) :
    (supportCompressedMatrixUnits E v hv hcomm).concreteHom a =
      star v.val * E.concreteHom a * v.val :=
  congrArg (fun x : Algebra M => x.val) (supportCompressedMatrixUnits_hom E v hv hcomm a)

theorem supportCompressedMatrixUnits_mono
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (E : MatrixUnitSystem ι (Algebra M)) (F : MatrixUnitSystem κ (Algebra M))
    (v : Algebra M) (hv : star v * v = 1)
    (hE : ∀ i j, (v * star v) * E.entry i j = E.entry i j * (v * star v))
    (hF : ∀ i j, (v * star v) * F.entry i j = F.entry i j * (v * star v))
    (hEF : E.concreteAlgebra ≤ F.concreteAlgebra) :
    (supportCompressedMatrixUnits E v hv hE).concreteAlgebra ≤
      (supportCompressedMatrixUnits F v hv hF).concreteAlgebra := by
  rintro T ⟨a,rfl⟩
  obtain ⟨b,hb⟩ := hEF (show E.concreteHom a ∈ E.concreteAlgebra from ⟨a,rfl⟩)
  refine ⟨b, ?_⟩
  change (supportCompressedMatrixUnits F v hv hF).concreteHom b =
    (supportCompressedMatrixUnits E v hv hE).concreteHom a
  rw [supportCompressedMatrixUnits_concreteHom, supportCompressedMatrixUnits_concreteHom]
  exact congrArg (fun T : H →L[ℂ] H => star v.val * T * v.val) hb

theorem supportCompressedMatrixUnits_intertwine
    (E : MatrixUnitSystem ι (Algebra M)) (v : Algebra M) (hv : star v * v = 1)
    (hcomm : ∀ i j, (v * star v) * E.entry i j = E.entry i j * (v * star v))
    (i j : ι) :
    E.entry i j * v = v * (supportCompressedMatrixUnits E v hv hcomm).entry i j := by
  change E.entry i j * v = v * (star v * E.entry i j * v)
  calc
    _ = E.entry i j * ((v * star v) * v) := by rw [mul_assoc v (star v) v,hv,mul_one]
    _ = ((v * star v) * E.entry i j) * v := by rw [hcomm]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

theorem supportCompressedMatrixUnits_intertwine_star
    (E : MatrixUnitSystem ι (Algebra M)) (v : Algebra M) (hv : star v * v = 1)
    (hcomm : ∀ i j, (v * star v) * E.entry i j = E.entry i j * (v * star v))
    (i j : ι) :
    star v * E.entry i j = (supportCompressedMatrixUnits E v hv hcomm).entry i j * star v := by
  have h := congrArg star (supportCompressedMatrixUnits_intertwine E v hv hcomm j i)
  simpa only [star_mul,E.star_entry,
    (supportCompressedMatrixUnits E v hv hcomm).star_entry] using h

end

end KadisonKastler

end OAI
