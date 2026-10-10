import Mathlib.LinearAlgebra.Complex.Module
import OAI.Analysis.FactorGeneration.MatrixEncoding
import OAI.Analysis.FactorGeneration.MatrixSequence
import OAI.Analysis.FactorGeneration.ProjectionEncoding

namespace OAI

noncomputable section

namespace Generator

/-! One arbitrary operator and a pair of self-adjoint operators generate the same weakly closed star algebra. -/
open scoped ComplexStarModule
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local notation "Op" => H →L[ℂ] H

theorem realPart_mem (S : StarSubalgebra ℂ Op) {x : Op} (hx : x ∈ S) :
    (ℜ x : Op) ∈ S := by
  rw [realPart_apply_coe, ← Complex.coe_smul]
  exact S.smul_mem (add_mem hx (star_mem hx)) _

theorem imaginaryPart_mem (S : StarSubalgebra ℂ Op) {x : Op} (hx : x ∈ S) :
    (ℑ x : Op) ∈ S := by
  rw [imaginaryPart_apply_coe, ← Complex.coe_smul]
  exact S.smul_mem (S.smul_mem (sub_mem hx (star_mem hx)) _) _

theorem mem_iff_parts_mem (S : StarSubalgebra ℂ Op) (x : Op) :
    x ∈ S ↔ (ℜ x : Op) ∈ S ∧ (ℑ x : Op) ∈ S := by
  refine ⟨fun hx => ⟨realPart_mem S hx, imaginaryPart_mem S hx⟩, ?_⟩
  rintro ⟨hr, hi⟩
  rw [← realPart_add_I_smul_imaginaryPart x]
  exact add_mem hr (S.smul_mem hi _)

theorem wstar_singleton_eq_parts (x : Op) :
    wstar {x} = wstar {(ℜ x : Op), (ℑ x : Op)} := by
  apply le_antisymm
  · apply wstar_le (wstar_closed _)
    intro y hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    apply (mem_iff_parts_mem _ x).mpr
    exact ⟨subset_wstar _ (by simp), subset_wstar _ (by simp)⟩
  · apply wstar_le (wstar_closed _)
    intro y hy
    have hx := subset_wstar {x} (Set.mem_singleton x)
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact realPart_mem _ hx
    · rcases Set.mem_singleton_iff.mp hy with rfl
      exact imaginaryPart_mem _ hx

theorem realPart_pack {a b : Op} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    (ℜ (a + Complex.I • b) : Op) = a := by
  simp only [map_add, realPart_I_smul, hb.imaginaryPart, neg_zero, add_zero]
  exact ha.coe_realPart

theorem imaginaryPart_pack {a b : Op} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    (ℑ (a + Complex.I • b) : Op) = b := by
  simp only [map_add, ha.imaginaryPart, imaginaryPart_I_smul, zero_add]
  exact hb.coe_realPart

theorem wstar_pack {a b : Op} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    wstar {a + Complex.I • b} = wstar {a, b} := by
  rw [wstar_singleton_eq_parts, realPart_pack ha hb, imaginaryPart_pack ha hb]

/-- Exact equivalence in thm:main, without proving either side for II1 factors. -/
theorem singlyGenerated_iff_two_selfAdjoint (S : StarSubalgebra ℂ Op) :
    SinglyGenerated S ↔ ∃ a ∈ S, ∃ b ∈ S,
      IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ wstar {a, b} = S := by
  constructor
  · rintro ⟨x, hx, hgen⟩
    exact ⟨ℜ x, realPart_mem S hx, ℑ x, imaginaryPart_mem S hx,
      (ℜ x).property, (ℑ x).property, (wstar_singleton_eq_parts x).symm.trans hgen⟩
  · rintro ⟨a, ha, b, hb, hsa, hsb, hgen⟩
    exact ⟨a + Complex.I • b, add_mem ha (S.smul_mem hb _),
      (wstar_pack hsa hsb).trans hgen⟩

end

/-! Two self-adjoint generators for an actual two-by-two amplification
whose actual commutant has four self-adjoint generators. Spectral separation
is proved, and the final generation uses the surjective coefficient map. -/
open scoped BigOperators
namespace MatrixUnitSystem
open MatrixEncoding
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (E : MatrixUnitSystem (Fin 2) M.toStarSubalgebra)

def concreteCoefficientHom : Matrix (Fin 2) (Fin 2) E.commutant →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  M.toStarSubalgebra.subtype.comp E.coefficientHom

theorem coefficient_corner (a : E.commutant) :
    E.concreteCoefficientHom (corner a)=a.val.val*(E.entry 0 0).val := by
  have he : corner a=Matrix.single 0 0 a := by ext i j; fin_cases i <;> fin_cases j <;> simp [corner,Matrix.single]
  change (E.coefficientHom (corner a)).val=_
  rw [he,E.coefficientHom_single]
  rfl

theorem coefficient_diagonal (a : E.commutant) :
    E.concreteCoefficientHom (corner a+E21*corner a*E12)=a.val.val := by
  have he : corner a+E21*corner a*E12=Matrix.diagonal (fun _ : Fin 2 => a) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [corner,E21,E12,Matrix.diagonal]
  rw [he]
  change (E.coefficientEval (Matrix.diagonal (fun _ : Fin 2 => a))).val=a.val.val
  congr 1
  simp [coefficientEval,Matrix.diagonal,apply_ite,ite_mul,← Finset.mul_sum,E.total]

theorem two_generators_of_four_commutant_generators (a₁ a₂ a₃ a₄ : E.commutant)
    (h₁ : IsSelfAdjoint a₁) (h₂ : IsSelfAdjoint a₂)
    (h₃ : IsSelfAdjoint a₃) (h₄ : IsSelfAdjoint a₄)
    (hgen : wstar {a₁.val.val,a₂.val.val,a₃.val.val,a₄.val.val}=E.relativeVonNeumann.toStarSubalgebra) :
    ∃ A ∈ M,∃ B ∈ M,IsSelfAdjoint A ∧ IsSelfAdjoint B ∧ wstar {A,B}=M.toStarSubalgebra := by
  let f := E.concreteCoefficientHom
  let t := f (encodeA a₁ a₂ 0)
  let q := f E22
  let C : ℝ := 2*‖t‖+1
  let A := f (encodeA a₁ a₂ (algebraMap ℂ E.commutant (C : ℂ)))
  let B := f (encodeB a₃ a₄)
  have hA : A ∈ M := (E.coefficientHom _).property
  have hB : B ∈ M := (E.coefficientHom _).property
  have hsa : IsSelfAdjoint A :=
    (encodeA_selfAdjoint h₁ h₂ (scalar_shift_selfAdjoint C)).map f
  have hsb : IsSelfAdjoint B := (encodeB_selfAdjoint h₃ h₄).map f
  have hq : q*q=q :=
    (map_mul f E22 E22).symm.trans (congrArg f E22_idempotent)
  have hqt : Commute q t := (E22_commute_encodeA a₁ a₂).map f
  have hsplit : A=C • q+t := by
    change f _=C • f E22+f (encodeA a₁ a₂ 0)
    exact (congrArg f (encodeA_scalar_shift a₁ a₂ C)).trans
      ((map_add f _ _).trans (congrArg (fun x => x + f (encodeA a₁ a₂ 0))
        ((map_smul f (C : ℂ) E22).trans (Complex.coe_smul C (f E22)))))
  let Q := wstar {A,B}
  let S := Q.comap f
  have hAm : encodeA a₁ a₂ (algebraMap ℂ E.commutant (C : ℂ)) ∈ S := subset_wstar _ (by simp [A])
  have hBm : encodeB a₃ a₄ ∈ S := subset_wstar _ (by simp [B])
  have h22 : (E22 : Matrix (Fin 2) (Fin 2) E.commutant) ∈ S := by
    change q ∈ wstar {A,B}
    apply (wstar_mono (s := {A}) (t := {A,B}) (by simp))
    rw [hsplit]
    exact idempotent_mem_wstar_of_gap q t hq hqt C (by dsimp [C]; linarith)
  have h11 : (E11 : Matrix (Fin 2) (Fin 2) E.commutant) ∈ S := by
    have he : (1 : Matrix (Fin 2) (Fin 2) E.commutant)-E22=E11 := by rw [← complement]; abel
    rw [← he]
    exact S.sub_mem S.one_mem h22
  obtain ⟨_,h12,h21⟩ := matrix_units_mem S h11 hBm
  obtain ⟨hc₁,hc₂,hc₃,hc₄⟩ := encoded_corners_mem_scalar S (C : ℂ) h11 hAm hBm
  have hcoeff (a : E.commutant) (ha : corner a ∈ S) : a.val.val ∈ Q := by
    rw [← E.coefficient_diagonal a]
    exact S.add_mem ha (S.mul_mem (S.mul_mem h21 ha) h12)
  have hN : E.relativeVonNeumann.toStarSubalgebra ≤ Q := by
    rw [← hgen]
    exact wstar_le (wstar_closed _) (by
      rintro _ (rfl | rfl | rfl | rfl)
      · exact hcoeff a₁ hc₁
      · exact hcoeff a₂ hc₂
      · exact hcoeff a₃ hc₃
      · exact hcoeff a₄ hc₄)
  have hcorner (a : E.commutant) : corner a ∈ S := by
    change f (corner a) ∈ Q
    rw [E.coefficient_corner a]
    apply Q.mul_mem (hN ⟨a,rfl⟩)
    have hp := E.coefficient_corner (1 : E.commutant)
    have he : corner (1 : E.commutant)=E11 := rfl
    rw [he] at hp
    have hp' : f E11=(E.entry 0 0).val := by simpa using hp
    have hh : f E11 ∈ Q := h11
    rwa [hp'] at hh
  have htop : S=⊤ := eq_top_of_corner_and_units S hcorner h12 h21
  refine ⟨A,hA,B,hB,hsa,hsb,le_antisymm ?_ ?_⟩
  · exact wstar_le (Tracial.vonNeumann_wotClosed M) (by rintro _ (rfl | rfl) <;> assumption)
  · intro x hx
    obtain ⟨a,ha⟩ := E.coefficientHom_surjective 0 ⟨x,hx⟩
    have hm : a ∈ S := by rw [htop]; trivial
    change (E.coefficientHom a).val ∈ Q at hm
    rwa [ha] at hm

end MatrixUnitSystem

end Generator

end

end OAI
