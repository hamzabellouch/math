import Mathlib
import OAI.Probability.CriticalPercolation.Modular.ActionOrbitTransport

namespace OAI

section
noncomputable section
open Set
open scoped Classical BigOperators

namespace ActionOrbitTransport
variable (Λ X : Type*) [Group Λ] [MulAction Λ X]

namespace Representatives
variable (R : Representatives Λ X)

def weightedRow (w : X → ℝ) (F : X → X → ℝ) (p : R.RootedPair) : ℝ :=
  w p.1 * F p.1 p.2

lemma weightedRow_finite (w : X → ℝ) (F : X → X → ℝ)
    (hF : ∀ x, (Function.support (F x)).Finite) :
    (Function.support (weightedRow Λ X R w F)).Finite := by
  apply (Set.finite_iUnion (fun x : {x // x∈R.roots} =>
    (hF x).image (Prod.mk x))).subset
  intro p hp
  refine Set.mem_iUnion.mpr ⟨p.1,p.2,?_,rfl⟩
  intro hz
  exact hp (by simp only [weightedRow,hz,mul_zero])

lemma fiber_sum_root (hfin : ∀ x y, (stabilizerOrbit Λ X x y).Finite)
    (w : X → ℝ) (F : X → X → ℝ)
    (hF : ∀ (φ : Λ) x y, F (φ • x) (φ • y) = F x y)
    (x : {x // x∈R.roots}) (y : X) :
    (∑' p : (pairMap Λ X R) ⁻¹' {pairOrbit Λ X x y}, weightedRow Λ X R w F p) =
      w x * (suborbitCard Λ X x y : ℝ) * F x y := by
  let := (hfin x y).fintype
  rw [← (fiberEquiv Λ X R x y).symm.tsum_eq]
  have hv (z : stabilizerOrbit Λ X x y) :
      weightedRow Λ X R w F ((fiberEquiv Λ X R x y).symm z) = w x * F x y := by
    change w x * F x z = w x * F x y
    obtain ⟨φ,hx,hy⟩ := (mem_stabilizerOrbit Λ X).mp z.property
    have hh := hF φ x y
    rw [hx,hy] at hh
    rw [hh]
  simp only [hv,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hcard : Fintype.card (stabilizerOrbit Λ X x y) = suborbitCard Λ X x y := by
    rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    rfl
  rw [hcard]
  ring

lemma fiber_sum (hfin : ∀ x y, (stabilizerOrbit Λ X x y).Finite)
    (w : X → ℝ) (hw : ∀ (φ : Λ) x, w (φ • x) = w x)
    (F : X → X → ℝ) (hF : ∀ (φ : Λ) x y, F (φ • x) (φ • y) = F x y)
    (x y : X) :
    (∑' p : (pairMap Λ X R) ⁻¹' {pairOrbit Λ X x y}, weightedRow Λ X R w F p) =
      w x * (suborbitCard Λ X x y : ℝ) * F x y := by
  obtain ⟨u,hu,φ,rfl⟩ := R.cover x
  let v := φ⁻¹ • y
  have hy : φ • v = y := smul_inv_smul φ y
  have hq : pairOrbit Λ X (φ • u) y = pairOrbit Λ X u v := by
    rw [←hy,smul_pairOrbit]
  rw [hq,fiber_sum_root Λ X R hfin w F hF ⟨u,hu⟩ v]
  change w u * (suborbitCard Λ X u v : ℝ) * F u v = _
  rw [←hy,hw,smul_suborbitCard,hF]

lemma tsum_weightedRow (w : X → ℝ) (F : X → X → ℝ)
    (hF : ∀ x, (Function.support (F x)).Finite) :
    (∑' p, weightedRow Λ X R w F p) = ∑ x ∈ R.roots, w x * ∑' y, F x y := by
  have hs : Summable (weightedRow Λ X R w F) := summable_of_hasFiniteSupport (weightedRow_finite Λ X R w F hF)
  rw [hs.tsum_prod]
  simp only [weightedRow,tsum_mul_left,tsum_fintype]
  exact Finset.sum_coe_sort R.roots (fun x => w x * ∑' y, F x y)

lemma massTransport (hfin : ∀ x y, (stabilizerOrbit Λ X x y).Finite)
    (w : X → ℝ) (hw : ∀ (φ : Λ) x, w (φ • x) = w x)
    (hbal : ∀ x y, w x * (suborbitCard Λ X x y : ℝ) = w y * (suborbitCard Λ X y x : ℝ))
    (F : X → X → ℝ) (hF : ∀ (φ : Λ) x y, F (φ • x) (φ • y) = F x y)
    (hrow : ∀ x, (Function.support (F x)).Finite)
    (hcol : ∀ y, (Function.support (fun x => F x y)).Finite) :
    (∑ x ∈ R.roots, w x * ∑' y, F x y) = ∑ y ∈ R.roots, w y * ∑' x, F x y := by
  let F' := fun x y => F y x
  have hF' (φ : Λ) (x y : X) : F' (φ • x) (φ • y) = F' x y := hF φ y x
  have hs : Summable (weightedRow Λ X R w F) := summable_of_hasFiniteSupport (weightedRow_finite Λ X R w F hrow)
  have ht : Summable (weightedRow Λ X R w F') := summable_of_hasFiniteSupport (weightedRow_finite Λ X R w F' hcol)
  rw [←tsum_weightedRow Λ X R w F hrow,←tsum_weightedRow Λ X R w F' hcol]
  calc
    _ = ∑' q : PairOrbit Λ X, ∑' p : (pairMap Λ X R) ⁻¹' {q}, weightedRow Λ X R w F p :=
      (hs.hasSum.tsum_fiberwise (pairMap Λ X R)).tsum_eq.symm
    _ = ∑' q : PairOrbit Λ X, ∑' p : (pairMap Λ X R) ⁻¹' {swapPairOrbit Λ X q},
          weightedRow Λ X R w F' p := by
      apply tsum_congr
      intro q
      induction q using Quotient.inductionOn' with
      | h p =>
        change (∑' z : (pairMap Λ X R) ⁻¹' {pairOrbit Λ X p.1 p.2}, weightedRow Λ X R w F z) =
          ∑' z : (pairMap Λ X R) ⁻¹' {pairOrbit Λ X p.2 p.1}, weightedRow Λ X R w F' z
        rw [fiber_sum Λ X R hfin w hw F hF,fiber_sum Λ X R hfin w hw F' hF',hbal]
    _ = ∑' p, weightedRow Λ X R w F' p := by
      exact ((swapPairOrbit Λ X).tsum_eq (fun q =>
        ∑' p : (pairMap Λ X R) ⁻¹' {q}, weightedRow Λ X R w F' p)).trans
          (ht.hasSum.tsum_fiberwise (pairMap Λ X R)).tsum_eq

end Representatives
end ActionOrbitTransport
end
end

end OAI
