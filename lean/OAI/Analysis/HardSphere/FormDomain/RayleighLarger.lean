import Mathlib
import OAI.Analysis.HardSphere.FormDomain.RmsPermuteFunBosonic
import OAI.Analysis.HardSphere.Collisions.IntegrableCompInsertNth

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Filter Set

lemma rayleigh_larger {n m : ℕ} {L : Length} {a c : ℝ} (hn : 0 < n) (hnm : n ≤ m)
    (h : ∀ u : Jet n L, u∈dirichletDomain n L a → c*(n:ℝ)*‖u.1‖^2≤energy u) :
    ∀ v : Jet m L, v∈dirichletDomain m L a → c*(m:ℝ)*‖v.1‖^2≤energy v := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m hnm ih => exact rayleigh_successor (hn.trans_le hnm) ih

lemma IsGroundVector.rayleigh_larger {n m : ℕ} {L : Length} {a : ℝ}
    {u : Jet n L} (hu : IsGroundVector n L a u) (hn : 0 < n) (hnm : n ≤ m)
    (v : Jet m L) (hv : v∈dirichletDomain m L a) :
    (energy u/(n:ℝ))*(m:ℝ)*‖v.1‖^2≤energy v := by
  apply HardSphere.rayleigh_larger hn hnm (c := energy u/(n:ℝ)) ?_ v hv
  intro w hw
  rw [div_mul_cancel₀ _ (by exact_mod_cast hn.ne')]
  exact hu.rayleigh_all w hw

lemma IsGroundVector.energy_per_particle_mono {n m : ℕ} {L : Length} {a : ℝ}
    {u : Jet n L} {v : Jet m L} (hu : IsGroundVector n L a u)
    (hv : IsGroundVector m L a v) (hn : 0 < n) (hnm : n ≤ m) :
    energy u/(n:ℝ)≤energy v/(m:ℝ) := by
  have h := hu.rayleigh_larger hn hnm v hv.1
  rw [hv.2.2.1,pow_two,mul_one,mul_one] at h
  exact (le_div_iff₀ (by exact_mod_cast hn.trans_le hnm)).mpr h

end HardSphere

end

end OAI
