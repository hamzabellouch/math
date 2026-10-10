import OAI.Probability.DilutedSpin.ClippedProxyRate
import OAI.Probability.DilutedSpin.PhysicalReservoirIncrement
import OAI.Probability.DilutedSpin.VariationalUpper

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {N L q : ℕ} [NeZero N]

lemma energyCavityIncrement_proxy_bound (M : Model (q+1)) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) :
    |energyCavityIncrement (N := N) M.disorder.toMeasure M.field.toMeasure (weights L) M.alpha (scoreRate N)
        (clipSample C) (clipReal H) (fun i : Spec L×ℕ => prior i.1) (gridExponents L)
        (spinFactor direction anchor u)-clippedCavityProxy M C H N L u|≤
      C*|(oneNewRate M.alpha q N:ℝ)-(M.alpha*(q+1):ℝ≥0)|+4*(scoreRate N:ℝ)/(N+1)+
      C*|((M.alpha*N-reservoirRate M.alpha q N:ℝ≥0):ℝ)-(M.alpha*q:ℝ≥0)| := by
  have hs := clippedSiteInsertion_rate_bound (N := N) M hC hH u
    (oneNewRate M.alpha q N) (M.alpha*(q+1))
  have hb := clippedBondInsertion_rate_bound (N := N) M hC hH u
    (M.alpha*N-reservoirRate M.alpha q N) (M.alpha*q)
  have he : energyCavityIncrement (N := N) M.disorder.toMeasure M.field.toMeasure (weights L) M.alpha (scoreRate N)
        (clipSample C) (clipReal H) (fun i : Spec L×ℕ => prior i.1) (gridExponents L)
        (spinFactor direction anchor u)=Real.log 2+
      clippedSiteInsertion M C H N L u (oneNewRate M.alpha q N)-
      clippedBondInsertion M C H N L u (M.alpha*N-reservoirRate M.alpha q N) := by
    unfold clippedSiteInsertion clippedBondInsertion
    rw [insertionPoisson_site_energy M hC hH,insertionPoisson_bond_energy M hC hH]
    simp only [energyCavityIncrement,reservoirEnergyRoot,reservoirEnergyLaw,Nat.add_sub_cancel]
    rfl
  rw [he]
  unfold clippedCavityProxy
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
  have hx := (abs_sub
    (clippedSiteInsertion M C H N L u (oneNewRate M.alpha q N)-clippedSiteInsertion M C H N L u (M.alpha*(q+1)))
    (clippedBondInsertion M C H N L u (M.alpha*N-reservoirRate M.alpha q N)-clippedBondInsertion M C H N L u (M.alpha*q))).trans (add_le_add hs hb)
  convert hx using 1
  congr 1
  ring

end DilutedSpinGlass.UniversalDictionary

end

section
namespace DilutedSpinGlass
open Filter
open scoped Topology

/-- The upper comparison for the exact arity and first-moment hypotheses of
`main:theorem`; no bounded representative is assumed. -/
lemma pressure_le_variationalValue_exact {p N : ℕ} (M : Model p)
    (hM : Admissible M) (hN : 0<N) : pressure M N ≤ variationalValue M := by
  have hp : p=(p-1)+1 := by have := hM.arity; omega
  revert M
  rw [hp]
  intro M hM
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  exact pressure_le_variationalValue M hM

lemma variationalValue_le_functional_exact {p : ℕ} (M : Model p)
    (hM : Admissible M) (r : ℕ) (ζ : Hierarchy (r+1)) (m : Fin r → ℝ)
    (hm : Exponents m) : variationalValue M ≤ functional M r ζ m := by
  have hp : p=(p-1)+1 := by have := hM.arity; omega
  revert M
  rw [hp]
  intro M hM
  exact variationalValue_le_functional M hM r ζ m hm

end DilutedSpinGlass

end

end OAI
