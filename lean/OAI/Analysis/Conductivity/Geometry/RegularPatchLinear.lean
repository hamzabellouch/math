import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactDepthReductionTwo

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma TwoFieldRankRegular.linearCoordinates {u : Coord3 → Fin 2 → ℝ} {O : Set Coord3}
    (hO : IsOpen O) (hu : ContDiffOn ℝ (↑(⊤:ℕ∞)) u O)
    (h : TwoFieldRankRegular u O) (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) :
    TwoFieldRankRegular (fun x => Q (u (P x))) (P ⁻¹' O) := by
  rcases h with h|h|⟨κ,hκ⟩
  · left
    intro x hx
    have hd := (hu.differentiableOn (by simp) (P x) hx).differentiableAt (hO.mem_nhds hx)
    have he := Q.hasFDerivAt.comp x (hd.hasFDerivAt.comp x P.hasFDerivAt)
    change LinearIndependent ℝ (gradientColumns (fderiv ℝ (Q ∘ u ∘ P) x)).col
    rw [he.fderiv]
    apply gradientColumns_rank
    exact Q.surjective.comp ((gradientColumns_surjective _ (h (P x) hx)).comp P.surjective)
  · right; left
    obtain ⟨v,l,κ,hv,hl,hd,he⟩ := h
    refine ⟨fun x => v (P x),Q l,Q κ,?_,?_,?_,?_⟩
    · exact hv.comp P.contDiff.contDiffOn (fun _ hx => hx)
    · obtain ⟨j,hj⟩ := hl
      by_contra! hh
      have hz : Q l=0 := funext hh
      have hl0 : l=0 := Q.injective (hz.trans (map_zero Q).symm)
      exact hj (congrFun hl0 j)
    · intro x hx hz
      have hxv := (hv.differentiableOn (by simp) (P x) hx).differentiableAt (hO.mem_nhds hx)
      have hh := (hxv.hasFDerivAt.comp x P.hasFDerivAt).fderiv
      change fderiv ℝ (v ∘ P) x=0 at hz
      rw [hh] at hz
      apply hd (P x) hx
      ext y
      have h := congrArg (fun D : Coord3 →L[ℝ] ℝ => D (P.symm y)) hz
      change (fderiv ℝ v (P x)) (P (P.symm y))=0 at h
      simpa only [P.apply_symm_apply,_root_.zero_apply] using h
    · intro x hx j
      have hh : u (P x)=v (P x) • l+κ := by
        ext i
        simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using he (P x) hx i
      change Q (u (P x)) j=Q l j*v (P x)+Q κ j
      rw [hh,map_add,map_smul]
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_comm]
  · exact Or.inr (Or.inr ⟨Q κ,fun x hx => congrArg Q (hκ (P x) hx)⟩)

end ScalarConductivity

end

end OAI
