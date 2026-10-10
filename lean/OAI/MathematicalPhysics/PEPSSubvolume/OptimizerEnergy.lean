import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.Marginal
import OAI.MathematicalPhysics.PEPSSubvolume.PhysicalModular

namespace OAI

/-! Quadratic crossing bounds for a global filter optimizer. -/

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
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.OptimizerEnergy
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix PolynomialPEPS.Subvolume.SpectralCurve PolynomialPEPS.Subvolume.CrossingIdentity
open PolynomialPEPS.Subvolume.PhysicalModular PolynomialPEPS.Subvolume.OptimizerMarginal PolynomialPEPS.Subvolume.ActualDiagonal
variable {L q : ℕ}

theorem filter_spectral_sum (X : Finset (Vertex L)) (F : LocalPositiveFilter q X)
    (p : ℝ) (hF : filterTracePower F p=1)
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (e : RegionConfiguration q X → ℝ) (he : ∀ i, 0 ≤ e i)
    (hrep : F.matrix = spectralHom U (fun i => (e i:ℂ))) :
    ∑ i, (e i)^p=1 := by
  unfold filterTracePower NestedFilter.tracePower at hF
  have hs' := sum_eigenvalues_spectralHom U e (spectral_positive U e he).isHermitian
    (fun t => t^p)
  have heig := F.positive.isHermitian.eigenvalues_eq_eigenvalues_iff
    (spectral_positive U e he).isHermitian
  have heq := heig.mpr (congrArg Matrix.charpoly hrep)
  rw [heq] at hF
  exact hs'.symm.trans hF

theorem spectral_real_error_le {ι : Type*} [Fintype ι]
    (X : Finset (Vertex L)) (v : State L q)
    (F : LocalPositiveFilter q X)
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (e : RegionConfiguration q X → ℝ) (he : ∀ i, 0 ≤ e i)
    (a : ℝ) (ha : 0<a) (ha' : a ≤ 1/2) (hs : ∑ i, (e i)^(2/a)=1)
    (hrep : F.matrix = spectralHom U (fun i => (e i:ℂ)))
    (hρ : reducedDensity v X = (‖v‖^2:ℂ) • spectralHom U (fun i => (((e i)^(2/a):ℝ):ℂ)))
    (H : Operator L q) (hH : H.IsHermitian)
    (A : ι → Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
    (B : ι → Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ)
    (hdecomp : H = ∑ i, tensorAcross X (A i) (B i)) :
    |(inner ℂ v (asMap H v)).re - (inner ℂ v (asMap
      (liftLocal X F.matrix * H * liftLocal X (inverseOnSupport U e)) v)).re| ≤
      8*a^2*‖v‖^2*(∑ i, ‖A i‖*‖B i‖) := by
  classical
  let R := liftLocal X F.matrix
  let D := liftLocal X (inverseOnSupport U e)
  have hR : R.IsHermitian := F.positive.isHermitian.isSelfAdjoint.map (localLiftHom X)
  have hD : D.IsHermitian := by
    have hf : IsSelfAdjoint (fun i => ((e i:ℂ)⁻¹)) := by
      rw [isSelfAdjoint_iff]
      ext i
      simp
    exact ((hf.map (spectralHom U)).map (localLiftHom X)).isHermitian
  have hb := physical_sum_error_le X v U e he a ha ha' hs hρ A B
  change ‖inner ℂ v (asMap (modularError (liftLocal X (spectralHom U (fun i => (e i:ℂ)))) D
    (∑ i, tensorAcross X (A i) (B i))) v)‖ ≤ _ at hb
  rw [← hrep,← hdecomp] at hb
  have hr := modularError_real R D H hR hD hH v
  change |(inner ℂ v (asMap H v)).re-(inner ℂ v (asMap (R*H*D) v)).re| ≤ _
  rw [abs_sub_comm,← hr]
  exact (Complex.abs_re_le_norm _).trans hb

theorem crossing_error_le {ι : Type*} [Fintype ι] (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ψ : State L q) (n : ℕ)
    (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (k : ℕ) (hk : k<n) (ha : 0<a k) (ha' : a k ≤ 1/2)
    (H : Operator L q) (hH : H.IsHermitian)
    (hHs : ∀ j, k<j → j<n → SupportedOn H (X j))
    (hc : ∀ j, j<k → Commute H (liftLocal (X j) (F j).matrix))
    (A : ι → Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ)
    (B : ι → Matrix (RegionConfiguration q (X k)ᶜ) (RegionConfiguration q (X k)ᶜ) ℂ)
    (hdecomp : H = ∑ i, tensorAcross (X k) (A i) (B i)) :
    let P := orderedPrefix (fun j => liftLocal (X j) (F j).matrix) n
    let v := asMap (L := L) (q := q) P ψ
    |(inner ℂ v (asMap H v)).re - (inner ℂ v (asMap (P*H) ψ)).re| ≤
      8*(a k)^2*‖v‖^2*(∑ i, ‖A i‖*‖B i‖) := by
  classical
  dsimp only
  let P := orderedPrefix (fun j => liftLocal (X j) (F j).matrix) n
  let v := asMap (L := L) (q := q) P ψ
  have hp : 2<2/a k := (lt_div_iff₀ ha).mpr (by linarith)
  obtain ⟨U,e,he,hrep,hρ⟩ := optimizer_marginal_spectral hq X hX a ψ n F hF k hk
    (ne_of_gt (lt_trans (by norm_num) hp))
  have hs := filter_spectral_sum (X k) (F k) (2/a k) (hF.1 ⟨k,hk⟩) U e he hrep
  have hsub := optimizer_modular_substitution hq X hX a ψ n F hF k hk hp U e he hrep hs H hHs hc
  change inner ℂ v (asMap (P*H) ψ) = inner ℂ v (asMap
    (liftLocal (X k) (F k).matrix * H * liftLocal (X k) (inverseOnSupport U e)) v) at hsub
  change |(inner ℂ v (asMap H v)).re-(inner ℂ v (asMap (P*H) ψ)).re| ≤ _
  rw [hsub]
  exact spectral_real_error_le (X k) v (F k) U e he (a k) ha ha' hs hrep hρ H hH A B hdecomp

end PolynomialPEPS.Subvolume.OptimizerEnergy

end

end OAI
