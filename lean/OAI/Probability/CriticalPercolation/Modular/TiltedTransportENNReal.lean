import Mathlib
import OAI.Probability.CriticalPercolation.Modular.ModularClusterMass
import OAI.Probability.CriticalPercolation.GraphGeometry.OrbitRepresentatives
import OAI.Probability.CriticalPercolation.Modular.TiltedMassTransport

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

def ennRow (F : V → V → ℝ≥0∞) (p : R.RootedPair) : ℝ≥0∞ := F p.1 p.2

lemma enn_fiber_sum_root (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ≥0∞)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y)
    (x : {x // x∈R.roots}) (y : V) :
    (∑' p : (pairMap G R) ⁻¹' {G.pairOrbit x y}, ennRow G R F p) =
      (G.suborbitCard x y : ℝ≥0∞) * F x y := by
  let := (G.stabilizerOrbit_finite hc hl x y).fintype
  rw [← (fiberEquiv G R x y).symm.tsum_eq]
  have hv (z : G.stabilizerOrbit x y) :
      ennRow G R F ((fiberEquiv G R x y).symm z) = F x y := by
    change F x z = F x y
    obtain ⟨φ,hx,hy⟩ := G.mem_stabilizerOrbit.mp z.property
    have hh := hF φ x y
    rwa [hx,hy] at hh
  simp only [hv,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hcard : Fintype.card (G.stabilizerOrbit x y) = G.suborbitCard x y := by
    rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    rfl
  rw [hcard]

lemma enn_fiber_sum (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ≥0∞)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y) (x y : V) :
    (∑' p : (pairMap G R) ⁻¹' {G.pairOrbit x y}, ennRow G R F p) =
      (G.suborbitCard x y : ℝ≥0∞) * F x y := by
  obtain ⟨u,hu,φ,rfl⟩ := R.cover x
  let v := φ.vertex.symm y
  have hy : φ.vertex v = y := φ.vertex.apply_symm_apply y
  have hq : G.pairOrbit (φ.vertex u) y = G.pairOrbit u v := by
    rw [←hy,Aut.pairOrbit]
  rw [hq,enn_fiber_sum_root G R hc hl F hF ⟨u,hu⟩ v]
  change (G.suborbitCard u v : ℝ≥0∞) * F u v = _
  rw [←hy,Aut.suborbitCard,hF]

lemma tsum_ennRow (F : V → V → ℝ≥0∞) :
    (∑' p, ennRow G R F p) = ∑ x ∈ R.roots, ∑' y, F x y := by
  change (∑' p : {x // x∈R.roots} × V, F p.1 p.2) = _
  rw [ENNReal.tsum_prod (f := fun (x : {x // x∈R.roots}) y => F x y)]
  simp only [tsum_fintype]
  exact Finset.sum_coe_sort R.roots (fun x => ∑' y, F x y)

lemma tilted_massTransport_ennreal (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ≥0∞)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y) :
    (∑ x ∈ R.roots, ∑' y, F x y) =
      ∑ y ∈ R.roots, ∑' x, F x y * G.stabilizerWeight y x := by
  let F' := fun x y => F y x * G.stabilizerWeight x y
  have hF' (φ : G.Aut) (x y : V) : F' (φ.vertex x) (φ.vertex y) = F' x y := by
    simp only [F',hF,Aut.stabilizerWeight]
  have heq : (∑' p, ennRow G R F p) = (∑' p, ennRow G R F' p) := by
    calc
      _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {q}, ennRow G R F p :=
        (ENNReal.tsum_fiberwise _ _).symm
      _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {G.swapPairOrbit q},
          ennRow G R F' p := by
        apply tsum_congr
        intro q
        induction q using Quotient.inductionOn' with
        | h p =>
          change (∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.1 p.2}, ennRow G R F z) =
            ∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.2 p.1}, ennRow G R F' z
          rw [enn_fiber_sum G R hc hl F hF,enn_fiber_sum G R hc hl F' hF']
          have hbal : (G.suborbitCard p.2 p.1 : ℝ≥0∞) * G.stabilizerWeight p.2 p.1 =
              (G.suborbitCard p.1 p.2 : ℝ≥0∞) := by
            unfold stabilizerWeight
            rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg _),
              G.suborbitCard_mul_modularRatio hc hl,ENNReal.ofReal_natCast]
          simp only [F']
          rw [mul_left_comm, hbal, mul_comm]
      _ = ∑' p, ennRow G R F' p :=
        (G.swapPairOrbit.tsum_eq _).trans (ENNReal.tsum_fiberwise _ _)
  rw [tsum_ennRow G R F,tsum_ennRow G R F'] at heq
  exact heq

end OrbitRepresentatives
end CriticalPercolation.BondGraph
end
end

end OAI
