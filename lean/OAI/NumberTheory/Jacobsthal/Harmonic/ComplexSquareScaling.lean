import OAI.NumberTheory.Jacobsthal.Probability.HorizontalBoundaryMarks
import OAI.NumberTheory.Jacobsthal.Probability.RealExceptionalMarks

namespace OAI

namespace Erdos970

section

open scoped ComplexConjugate
namespace ErdosComplexCurveFactors
open ErdosCriticalGeometry

noncomputable def conjugateEquiv : MV ℂ ≃+* MV ℂ :=
  MvPolynomial.mapEquiv (Fin 2) Complex.conjAe.toRingEquiv

noncomputable def conjugate (F : MV ℂ) : MV ℂ := MvPolynomial.map (starRingEnd ℂ) F

theorem coeff_conjugate (F : MV ℂ) (m : Fin 2 →₀ ℕ) :
    (conjugate F).coeff m = conj (F.coeff m) := MvPolynomial.coeff_map _ _ _

theorem conjugate_conjugate (F : MV ℂ) : conjugate (conjugate F) = F := by
  ext m
  rw [coeff_conjugate,coeff_conjugate]
  exact star_star _

theorem conjugate_irreducible {F : MV ℂ} (hF : Irreducible F) : Irreducible (conjugate F) :=
  (MulEquiv.irreducible_iff conjugateEquiv.toMulEquiv).mpr hF

theorem conjugate_totalDegree (F : MV ℂ) : (conjugate F).totalDegree = F.totalDegree := by
  unfold conjugate MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective F Complex.conjAe.injective]

theorem eval_conjugate_real (F : MV ℂ) (x y : ℝ) :
    MvPolynomial.eval ![(x : ℂ),(y : ℂ)] (conjugate F) =
      conj (MvPolynomial.eval ![(x : ℂ),(y : ℂ)] F) := by
  have he : (starRingEnd ℂ) ∘ (![(x : ℂ),(y : ℂ)] : Fin 2 → ℂ) = ![(x : ℂ),(y : ℂ)] := by
    funext i
    fin_cases i <;> simp
  have h := MvPolynomial.map_eval (starRingEnd ℂ) ![(x : ℂ),(y : ℂ)] F
  rw [he] at h
  exact h.symm

end ErdosComplexCurveFactors

end

section

open Set
namespace ErdosAlgebraicCurve
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosLocalFiberGraphs ErdosMarkedStrips

theorem exists_algebraic_marks (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) (S : ℝ) :
    ∃ E : Finset ℝ, 0 ∈ E ∧ S ∈ E ∧ E.card ≤ 14*Q.totalDegree^2 ∧
      (∀ t ∈ E, verticalPolynomial Q t ≠ 0) ∧ RegularOff Q S E := by
  classical
  obtain ⟨B,hB,hbad⟩ := exists_bad_abscissae Q hQ hdeg
  obtain ⟨hf0,hc0⟩ := boundary_abscissae_bound Q hQ hdeg 0
  obtain ⟨hfS,hcS⟩ := boundary_abscissae_bound Q hQ hdeg S
  let E := B ∪ hf0.toFinset ∪ hfS.toFinset ∪ {0,S}
  have hBE : B ⊆ E := fun x hx => Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  have h0E : hf0.toFinset ⊆ E := fun x hx => Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
  have hSE : hfS.toFinset ⊆ E := fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hsize : E.card ≤ B.card+hf0.toFinset.card+hfS.toFinset.card+2 := by
    calc
      _ ≤ (B ∪ hf0.toFinset ∪ hfS.toFinset).card+({0,S} : Finset ℝ).card := Finset.card_union_le _ _
      _ ≤ ((B ∪ hf0.toFinset).card+hfS.toFinset.card)+2 :=
        Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_le_two)
      _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
  have h0card : hf0.toFinset.card ≤ 2*Q.totalDegree := by rwa [← ncard_eq_toFinset_card _ hf0]
  have hScard : hfS.toFinset.card ≤ 2*Q.totalDegree := by rwa [← ncard_eq_toFinset_card _ hfS]
  refine ⟨E,?_,?_,?_,(fun t _ => real_vertical_nonzero Q hQ hdeg t),?_⟩
  · exact Finset.mem_union_right _ (by simp)
  · exact Finset.mem_union_right _ (by simp)
  · have hn : 10*Q.totalDegree^2+4*Q.totalDegree+2 ≤ 14*Q.totalDegree^2 := by nlinarith
    omega
  · intro t ht
    have hnotB : t ∉ B := fun h => ht (hBE h)
    refine ⟨⟨?_,?_⟩,?_⟩
    · exact fun hz => ht (h0E (hf0.mem_toFinset.mpr hz))
    · exact fun hz => ht (hSE (hfS.mem_toFinset.mpr hz))
    · exact fun y _ hy => hbad t hnotB y hy

end ErdosAlgebraicCurve

end

section

namespace ErdosAlgebraicCurve
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosMarkedStrips

theorem absolutely_irreducible_curve_lattice_bound (Q : MV ℝ)
    (hQ : Irreducible (complexify Q)) (hdeg : 1 < Q.totalDegree)
    (S : ℝ) (hS : 0 ≤ S) :
    ((polynomialSquarePoints Q S).card : ℝ) ≤
      182*(Q.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3)) := by
  obtain ⟨E,h0,hSE,hcard,hfiber,hregular⟩ := exists_algebraic_marks Q hQ hdeg S
  have h := marked_square_cubic_bound Q S E 14 hS h0 hSE hfiber hregular hcard
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h]

end ErdosAlgebraicCurve

end

section

open Set
namespace ErdosComplexCurveFactors
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosDivisibleInflection ErdosMarkedStrips ErdosConvexGraph
attribute [local instance] Classical.propDecidable

noncomputable def complexSquarePoints (F : MV ℂ) (S : ℝ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (0 : ℤ) ⌊S⌋).product (Finset.Icc (0 : ℤ) ⌊S⌋)).filter
    (fun p => MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] F = 0)

theorem mem_complexSquarePoints (F : MV ℂ) (S : ℝ) (p : ℤ × ℤ) :
    p ∈ complexSquarePoints F S ↔ InSquare S p ∧
      MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] F = 0 := by
  simp only [complexSquarePoints,InSquare,Finset.mem_filter,Finset.product_eq_sprod,
    Finset.mem_product,Finset.mem_Icc,Int.le_floor,Int.cast_nonneg_iff]

theorem scalar_totalDegree (a : ℂ) (ha : a ≠ 0) (F : MV ℂ) :
    (MvPolynomial.C a * F).totalDegree = F.totalDegree := by
  have hs : (MvPolynomial.C a * F).support = F.support := by
    ext m
    simp only [MvPolynomial.mem_support_iff,MvPolynomial.coeff_C_mul,mul_ne_zero_iff]
    exact ⟨fun h => h.2,fun h => ⟨ha,h⟩⟩
  unfold MvPolynomial.totalDegree
  rw [hs]

theorem complexSquare_scalar (a : ℂ) (ha : a ≠ 0) (F : MV ℂ) (S : ℝ) :
    complexSquarePoints (MvPolynomial.C a * F) S = complexSquarePoints F S := by
  ext p
  simp only [mem_complexSquarePoints,map_mul,MvPolynomial.eval_C,mul_eq_zero,ha,false_or]

theorem eval_complexify_int (R : MV ℝ) (p : ℤ × ℤ) :
    MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] (complexify R) = (peval R p.1 p.2 : ℂ) := by
  simpa only [Complex.ofReal_intCast,peval_eq_eval_pair] using complexify_eval R p.1 p.2

theorem complexSquare_complexify (R : MV ℝ) (S : ℝ) :
    complexSquarePoints (complexify R) S = polynomialSquarePoints R S := by
  ext p
  simp only [mem_complexSquarePoints,mem_polynomialSquarePoints,eval_complexify_int,Complex.ofReal_eq_zero]

theorem scalar_irreducible_iff (a : ℂ) (ha : a ≠ 0) (F : MV ℂ) :
    Irreducible (MvPolynomial.C a * F) ↔ Irreducible F :=
  irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr ha).map MvPolynomial.C)

def complexIntPoint (p : ℤ × ℤ) : ℂ × ℂ := ((p.1 : ℂ),(p.2 : ℂ))

theorem complexIntPoint_injective : Function.Injective complexIntPoint := by
  intro p q hpq
  have h1 : (p.1 : ℂ) = (q.1 : ℂ) := congrArg Prod.fst hpq
  have h2 : (p.2 : ℂ) = (q.2 : ℂ) := congrArg Prod.snd hpq
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

end ErdosComplexCurveFactors

end

end Erdos970

end OAI
