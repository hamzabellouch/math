import Mathlib
import OAI.Probability.CriticalPercolation.Modular.GraphModular
import OAI.Probability.CriticalPercolation.GraphGeometry.OrbitRepresentatives

namespace OAI

section
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

private def swapPairOrbitFn : G.PairOrbit → G.PairOrbit :=
  Quotient.map Prod.swap (by
    intro a b hab
    obtain ⟨φ,hφ⟩ := MulAction.mem_orbit_iff.mp hab
    exact MulAction.mem_orbit_iff.mpr ⟨φ,Prod.ext (congrArg Prod.snd hφ) (congrArg Prod.fst hφ)⟩)

def swapPairOrbit : G.PairOrbit ≃ G.PairOrbit where
  toFun := swapPairOrbitFn G
  invFun := swapPairOrbitFn G
  left_inv q := by induction q using Quotient.inductionOn' with | h p => rfl
  right_inv q := by induction q using Quotient.inductionOn' with | h p => rfl

@[simp] lemma swapPairOrbit_mk (x y : V) :
    G.swapPairOrbit (G.pairOrbit x y) = G.pairOrbit y x := rfl

namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

def weightedRow (w : V → ℝ) (F : V → V → ℝ) (p : R.RootedPair) : ℝ :=
  w p.1 * F p.1 p.2

lemma weightedRow_finite (w : V → ℝ) (F : V → V → ℝ)
    (hF : ∀ x, (Function.support (F x)).Finite) :
    (Function.support (weightedRow G R w F)).Finite := by
  apply (Set.finite_iUnion (fun x : {x // x∈R.roots} =>
    (hF x).image (Prod.mk x))).subset
  intro p hp
  refine Set.mem_iUnion.mpr ⟨p.1,p.2,?_,rfl⟩
  intro hz
  exact hp (by simp only [weightedRow,hz,mul_zero])

lemma fiber_sum_root (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (w : V → ℝ) (F : V → V → ℝ)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y)
    (x : {x // x∈R.roots}) (y : V) :
    (∑' p : (pairMap G R) ⁻¹' {G.pairOrbit x y}, weightedRow G R w F p) =
      w x * (G.suborbitCard x y : ℝ) * F x y := by
  let := (G.stabilizerOrbit_finite hc hl x y).fintype
  rw [← (fiberEquiv G R x y).symm.tsum_eq]
  have hv (z : G.stabilizerOrbit x y) :
      weightedRow G R w F ((fiberEquiv G R x y).symm z) = w x * F x y := by
    change w x * F x z = w x * F x y
    obtain ⟨φ,hx,hy⟩ := G.mem_stabilizerOrbit.mp z.property
    have hh := hF φ x y
    rw [hx,hy] at hh
    rw [hh]
  simp only [hv,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hcard : Fintype.card (G.stabilizerOrbit x y) = G.suborbitCard x y := by
    rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    rfl
  rw [hcard]
  ring

lemma fiber_sum (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (w : V → ℝ) (hw : ∀ (φ : G.Aut) x, w (φ.vertex x) = w x)
    (F : V → V → ℝ) (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y)
    (x y : V) :
    (∑' p : (pairMap G R) ⁻¹' {G.pairOrbit x y}, weightedRow G R w F p) =
      w x * (G.suborbitCard x y : ℝ) * F x y := by
  obtain ⟨u,hu,φ,rfl⟩ := R.cover x
  let v := φ.vertex.symm y
  have hy : φ.vertex v = y := φ.vertex.apply_symm_apply y
  have hq : G.pairOrbit (φ.vertex u) y = G.pairOrbit u v := by
    rw [←hy,Aut.pairOrbit]
  rw [hq,fiber_sum_root G R hc hl w F hF ⟨u,hu⟩ v]
  change w u * (G.suborbitCard u v : ℝ) * F u v = _
  rw [←hy,hw,Aut.suborbitCard,hF]

lemma tsum_weightedRow (w : V → ℝ) (F : V → V → ℝ)
    (hF : ∀ x, (Function.support (F x)).Finite) :
    (∑' p, weightedRow G R w F p) = ∑ x ∈ R.roots, w x * ∑' y, F x y := by
  have hs : Summable (weightedRow G R w F) := summable_of_hasFiniteSupport (weightedRow_finite G R w F hF)
  rw [hs.tsum_prod]
  simp only [weightedRow,tsum_mul_left,tsum_fintype]
  exact Finset.sum_coe_sort R.roots (fun x => w x * ∑' y, F x y)

lemma massTransport (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (w : V → ℝ) (hw : ∀ (φ : G.Aut) x, w (φ.vertex x) = w x)
    (hbal : ∀ x y, w x * (G.suborbitCard x y : ℝ) = w y * (G.suborbitCard y x : ℝ))
    (F : V → V → ℝ) (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y)
    (hrow : ∀ x, (Function.support (F x)).Finite)
    (hcol : ∀ y, (Function.support (fun x => F x y)).Finite) :
    (∑ x ∈ R.roots, w x * ∑' y, F x y) = ∑ y ∈ R.roots, w y * ∑' x, F x y := by
  let F' := fun x y => F y x
  have hF' (φ : G.Aut) (x y : V) : F' (φ.vertex x) (φ.vertex y) = F' x y := hF φ y x
  have hs : Summable (weightedRow G R w F) := summable_of_hasFiniteSupport (weightedRow_finite G R w F hrow)
  have ht : Summable (weightedRow G R w F') := summable_of_hasFiniteSupport (weightedRow_finite G R w F' hcol)
  rw [←tsum_weightedRow G R w F hrow,←tsum_weightedRow G R w F' hcol]
  calc
    _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {q}, weightedRow G R w F p :=
      (hs.hasSum.tsum_fiberwise (pairMap G R)).tsum_eq.symm
    _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {G.swapPairOrbit q},
          weightedRow G R w F' p := by
      apply tsum_congr
      intro q
      induction q using Quotient.inductionOn' with
      | h p =>
        change (∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.1 p.2}, weightedRow G R w F z) =
          ∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.2 p.1}, weightedRow G R w F' z
        rw [fiber_sum G R hc hl w hw F hF,fiber_sum G R hc hl w hw F' hF',hbal]
    _ = ∑' p, weightedRow G R w F' p := by
      exact (G.swapPairOrbit.tsum_eq (fun q =>
        ∑' p : (pairMap G R) ⁻¹' {q}, weightedRow G R w F' p)).trans
          (ht.hasSum.tsum_fiberwise (pairMap G R)).tsum_eq

end OrbitRepresentatives
end CriticalPercolation.BondGraph
end
end

end OAI
