import OAI.Probability.InvariantIsing.Cavity.CavityCovariancePartitionBound
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteField
import OAI.Probability.InvariantIsing.Cavity.CavityFieldResidual

namespace OAI

/-! The covariance bound specialized to the actual finite overlap quantile.
Its weights and all positive deficit arguments follow from the quantile. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_finite_covariance_bound {ι : Type*} [Fintype ι] {d n : ℕ}
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) :
    let T := cavitySpectralMatrixPath ρ eig hρ hsum A hA
    ‖q 0 • cavitySpectralMatrixDensity ρ eig hρ hsum A hA (deficit p (q 0)) +
      (∑ i : Fin n, (cut i.succ.castSucc)⁻¹ •
        (T (deficit p (q i.castSucc)) - T (deficit p (q i.succ)))) +
      T (deficit p (q (Fin.last n)))‖ ≤ (ρ a)⁻¹ := by
  intro T
  have hd (i : Fin (n + 1)) : 0 < deficit p (q i) :=
    finite_overlap_deficit_pos p cut hfirst hlast q hq.monotone hp htop
      (hq.monotone (Fin.le_last i))
  have hb (i : Fin n) : 0 < cut i.succ.castSucc := by
    rw [← hfirst]
    exact hcut (by change 0 < i.val + 1; omega)
  have hg (i : Fin n) : deficit p (q i.castSucc) - deficit p (q i.succ) =
      cut i.succ.castSucc * (q i.succ - q i.castSucc) := by
    have hi := finite_overlap_deficit_increment p cut hcut hfirst hlast q hq hp i
      (r := q i.succ) ⟨hq.monotone (Fin.castSucc_le_succ i), le_rfl⟩
    linarith
  have ht : deficit p (q (Fin.last n)) = 1 - q (Fin.last n) :=
    deficit_eq_one_sub_of_ae_le p
      ((finite_overlap_ae_bounds p cut hfirst hlast q hq.monotone hp).mono (fun _ h => h.2))
  exact cavity_spectral_covariance_partition_bound ρ eig hρ hsum A hA a heig
    q (fun i => deficit p (q i)) (fun i => cut i.succ.castSucc) hq.monotone
    (finite_overlap_value_mem_unit p cut hcut q hp 0).1 (fun i => (hd i).le) (hd 0) hb hg ht

end InvariantIsing

end

end OAI
