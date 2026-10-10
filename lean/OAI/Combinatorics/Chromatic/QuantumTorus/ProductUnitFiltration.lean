import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.Product
import OAI.Combinatorics.Chromatic.Shuffle.UnitalFiltration

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
lemma OnSlopeOrZero.compatible {c η : I → ℝ} {θ : ℝ} {d e : I → ℕ}
    (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e) :
    d=0 ∨ e=0 ∨ slope c η d=slope c η e := by
  rcases hd with hd|hd
  · exact Or.inl hd
  rcases he with he|he
  · exact Or.inr (Or.inl he)
  exact Or.inr (Or.inr (hd.trans he.symm))

lemma OnSlopeOrZero.add {c η : I → ℝ} (hc : ∀ i,0<c i) {θ : ℝ} {d e : I → ℕ}
    (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e) :
    OnSlopeOrZero c η θ (d+e) := by
  rcases hd with rfl|hd
  · simpa only [zero_add] using he
  rcases he with rfl|he
  · exact Or.inr (by simpa only [add_zero] using hd)
  exact Or.inr ((slope_add_same c η hc (hd.trans he.symm)).trans hd)
end ElementaryPositivity.SlopeArithmetic

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma B_zero_eq_scalar (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (f : B a μ 0) :
    ∃ r : ℚ, f=r • (1 : B a μ 0) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    refine ⟨constantCoeff f.val,?_⟩
    change quotientAlg a μ 0 f=constantCoeff f.val • (1 : B a μ 0)
    have h:=congrArg (quotientAlg a μ 0) (S_zero_eq_scalar f)
    simpa only [map_smul,map_one] using h

lemma shuffleBUnit_one_left (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d : I → ℕ) (hs : (0 : I → ℕ)=0 ∨ d=0 ∨ slope c η 0=slope c η d)
    (f : B a (slope c η) d) :
    shuffleBUnit a c η hc 0 d hs 1 f=castB a (slope c η) (zero_add d).symm f := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change shuffleBUnit a c η hc 0 d hs (quotientAlg a (slope c η) 0 1)
      (quotientAlg a (slope c η) d f)=_
    change quotientAlg a (slope c η) (0+d) (shufflePolynomial a 1 f)=_
    rw [shufflePolynomial_unit_left,←castB_mk]
    rfl

lemma shuffleBUnit_one_right (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d : I → ℕ) (hs : d=0 ∨ (0 : I → ℕ)=0 ∨ slope c η d=slope c η 0)
    (f : B a (slope c η) d) :
    shuffleBUnit a c η hc d 0 hs f 1=castB a (slope c η) (add_zero d).symm f := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change shuffleBUnit a c η hc d 0 hs (quotientAlg a (slope c η) d f)
      (quotientAlg a (slope c η) 0 1)=_
    change quotientAlg a (slope c η) (d+0) (shufflePolynomial a f 1)=_
    rw [shufflePolynomial_unit_right,←castB_mk]
    rfl

lemma shuffleBUnit_filtered_zero_left (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (hs : (0 : I → ℕ)=0 ∨ d=0 ∨ slope c η 0=slope c η d)
    (U V : ℤ) (f : B a (slope c η) 0) (g : B a (slope c η) d)
    (hf : f∈unitalSourceFiltration a c η hc θ 0 U)
    (hg : g∈unitalSourceFiltration a c η hc θ d V) :
    shuffleBUnit a c η hc 0 d hs f g∈unitalSourceFiltration a c η hc θ (0+d) (U+V) := by
  classical
  by_cases hu : U≤0
  · obtain ⟨r,rfl⟩:=B_zero_eq_scalar a (slope c η) f
    rw [map_smul,LinearMap.smul_apply,shuffleBUnit_one_left]
    exact (unitalSourceFiltration a c η hc θ (0+d) (U+V)).smul_mem r
      (unitalSourceFiltration_antitone a c η hc θ (0+d) (by omega)
        (castB_mem_unitalSourceFiltration a c η hc θ (zero_add d).symm V hg))
  · have hz : f=0 := by simpa only [unitalSourceFiltration,ite_eq_left rfl,ite_eq_right hu,ite_true,Submodule.mem_bot] using hf
    rw [hz,map_zero,LinearMap.zero_apply]
    exact Submodule.zero_mem _

lemma shuffleBUnit_filtered_zero_right (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (hs : d=0 ∨ (0 : I → ℕ)=0 ∨ slope c η d=slope c η 0)
    (U V : ℤ) (f : B a (slope c η) d) (g : B a (slope c η) 0)
    (hf : f∈unitalSourceFiltration a c η hc θ d U)
    (hg : g∈unitalSourceFiltration a c η hc θ 0 V) :
    shuffleBUnit a c η hc d 0 hs f g∈unitalSourceFiltration a c η hc θ (d+0) (U+V) := by
  classical
  by_cases hv : V≤0
  · obtain ⟨r,rfl⟩:=B_zero_eq_scalar a (slope c η) g
    rw [map_smul,shuffleBUnit_one_right]
    exact (unitalSourceFiltration a c η hc θ (d+0) (U+V)).smul_mem r
      (unitalSourceFiltration_antitone a c η hc θ (d+0) (by omega)
        (castB_mem_unitalSourceFiltration a c η hc θ (add_zero d).symm U hf))
  · have hz : g=0 := by simpa only [unitalSourceFiltration,ite_eq_left rfl,ite_eq_right hv,ite_true,Submodule.mem_bot] using hg
    rw [hz,map_zero]
    exact Submodule.zero_mem _

end ElementaryPositivity.RawShuffle

end

end OAI
