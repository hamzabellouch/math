import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.EntropyHolder

namespace OAI

/-! Dimension bounds for finite-state entropy. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open Filter Topology
open Set Filter Complex Complex.HadamardThreeLines
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume
open scoped BigOperators
variable {L q : ℕ}

theorem vonNeumannEntropy_nonneg (Ω : State L q) (hΩ : ‖Ω‖=1) (X : Finset (Vertex L)) :
    0 ≤ vonNeumannEntropy Ω X := by
  apply Finset.sum_nonneg
  intro i hi
  have hp := (reducedDensity_posSemidef Ω X).eigenvalues_nonneg
  apply Real.negMulLog_nonneg (hp i)
  have h := Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset (RegionConfiguration q X))) => hp j) hi
  simpa only [marginal_eigenvalues_sum Ω hΩ X] using h

theorem vonNeumannEntropy_empty (Ω : State L q) (hΩ : ‖Ω‖=1) :
    vonNeumannEntropy Ω ∅=0 := by
  classical
  let : IsEmpty {v : Vertex L // v∈(∅ : Finset (Vertex L))} :=
    ⟨fun v => Finset.notMem_empty _ v.property⟩
  let i : RegionConfiguration q (∅ : Finset (Vertex L)) := fun v => isEmptyElim v
  have hp : (reducedDensity_isHermitian Ω ∅).eigenvalues i=1 := by
    simpa only [Fintype.sum_subsingleton _ i] using marginal_eigenvalues_sum Ω hΩ ∅
  simp only [vonNeumannEntropy,Fintype.sum_subsingleton _ i,hp,Real.negMulLog_one]

end PolynomialPEPS.Subvolume

namespace PolynomialPEPS.SubvolumeEntropy
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem sum_negMulLog_le_log_card (p : ι → ℝ) (hp : ∀ i, 0≤p i) (hs : ∑ i,p i=1) :
    ∑ i, Real.negMulLog (p i) ≤ Real.log (Fintype.card ι) := by
  classical
  let N : ℝ := Fintype.card ι
  have hN : 0<N := by
    change (0:ℝ)<(Fintype.card ι:ℝ)
    exact_mod_cast (Fintype.card_pos (α:=ι))
  have hn : N≠0 := ne_of_gt hN
  have hw : ∑ _i : ι, 1/N=1 := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; change N*(1/N)=1; field_simp
  have hj := Real.concaveOn_negMulLog.le_map_sum
    (w:=fun _i : ι => 1/N) (p:=p) (t:=Finset.univ)
    (fun i hi => le_of_lt (one_div_pos.mpr hN)) hw (fun i hi => hp i)
  simp only [smul_eq_mul,← Finset.mul_sum,hs,mul_one] at hj
  have hr : Real.negMulLog (1/N)=(1/N)*Real.log N := by
    change -(1/N)*Real.log (1/N)=(1/N)*Real.log N
    rw [Real.log_div (by norm_num) hn,Real.log_one]
    ring
  rw [hr] at hj
  exact (mul_le_mul_iff_right₀ (one_div_pos.mpr hN)).mp hj

end PolynomialPEPS.SubvolumeEntropy

namespace PolynomialPEPS.Subvolume
open scoped BigOperators
variable {L q : ℕ}

theorem vonNeumannEntropy_le_card_log (hq : 0<q) (Ω : State L q) (hΩ : ‖Ω‖=1)
    (X : Finset (Vertex L)) : vonNeumannEntropy Ω X ≤ (X.card:ℝ)*Real.log q := by
  let : Nonempty (RegionConfiguration q X) := ⟨fun _ => ⟨0,hq⟩⟩
  have h := PolynomialPEPS.SubvolumeEntropy.sum_negMulLog_le_log_card
    (reducedDensity_isHermitian Ω X).eigenvalues
    (reducedDensity_posSemidef Ω X).eigenvalues_nonneg (marginal_eigenvalues_sum Ω hΩ X)
  change vonNeumannEntropy Ω X ≤ _ at h
  simpa only [RegionConfiguration,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,
    Nat.cast_pow,Real.log_pow] using h

end PolynomialPEPS.Subvolume

end

end OAI
