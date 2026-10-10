import OAI.Probability.InvariantIsing.Cavity.CavitySpectralDensityIntegral
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteDeficit

namespace OAI

/-! Exact finite-level spectral integrals. The covariance of a shared
prefix is the canonical spectral path evaluated at its overlap value. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavity_prefix_sum_differences {n : ℕ} (f : Fin (n + 1) → ℝ)
    (l : Fin (n + 1)) :
    f 0 + (∑ i : Fin n, if (i : ℕ) + 1 ≤ (l : ℕ) then
      f i.succ - f i.castSucc else 0) = f l := by
  refine Fin.induction ?_ ?_ l
  · simp
  · intro j hj
    have hs : (∑ i : Fin n, if (i : ℕ) + 1 ≤ (j.succ : ℕ) then
        f i.succ - f i.castSucc else 0) =
        (∑ i : Fin n, if (i : ℕ) + 1 ≤ (j.castSucc : ℕ) then
          f i.succ - f i.castSucc else 0) + (f j.succ - f j.castSucc) := by
      calc
        _ = ∑ i : Fin n,
            ((if (i : ℕ) + 1 ≤ (j.castSucc : ℕ) then f i.succ - f i.castSucc else 0) +
            (if i = j then f j.succ - f j.castSucc else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hij : i = j
          · subst i
            simp
          · have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
            by_cases hlt : (i : ℕ) + 1 ≤ (j : ℕ)
            · have hlt' : (i : ℕ) + 1 ≤ (j.succ : ℕ) := by simp; omega
              simp only [hlt, hlt', Fin.val_castSucc, ite_true, hij, ite_false, add_zero]
            · have hlt' : ¬ (i : ℕ) + 1 ≤ (j.succ : ℕ) := by simp; omega
              simp only [hlt, hlt', Fin.val_castSucc, ite_false, hij, add_zero]
        _ = _ := by rw [Finset.sum_add_distrib]; simp
    rw [hs]
    linarith

variable {ι : Type*} [Fintype ι]

lemma finite_overlap_spectral_increment (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {n : ℕ} (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (a : ι) (i : Fin n) :
    (∫ r in q i.castSucc..q i.succ, spectralPathDensity rho lam hrho hsum p a r) =
      (projectedResolvent rho lam hrho hsum a (deficit p (q i.castSucc)) -
        projectedResolvent rho lam hrho hsum a (deficit p (q i.succ))) /
          cut i.castSucc.succ := by
  have hm := finite_overlap_cumulative_mass p cut hcut hfirst hlast q hq hp i.castSucc
  have hc : 0 < cut i.castSucc.succ := by
    rw [← hfirst]
    exact hcut (Fin.succ_pos _)
  have he := integral_spectralPathDensity_gap rho lam hrho hsum p a
    (hq (Fin.castSucc_lt_succ (i := i)))
    (finite_overlap_value_gap p cut hfirst hlast q hq.monotone hp i)
    (finite_overlap_deficit_pos p cut hfirst hlast q hq.monotone hp htop
      (hq.monotone (Fin.le_last _))) (by rw [hm]; exact hc.ne')
  rwa [hm] at he

theorem finite_overlap_spectral_prefix (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {n : ℕ} (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (a : ι) (l : Fin (n + 1)) :
    (∫ r in 0..q l, spectralPathDensity rho lam hrho hsum p a r) =
      q 0 * projectedResolventDerivative rho lam hrho hsum a (deficit p (q 0)) +
      ∑ i : Fin n, if (i : ℕ) + 1 ≤ (l : ℕ) then
        (projectedResolvent rho lam hrho hsum a (deficit p (q i.castSucc)) -
          projectedResolvent rho lam hrho hsum a (deficit p (q i.succ))) /
            cut i.castSucc.succ else 0 := by
  let F (j : Fin (n + 1)) := ∫ r in 0..q j, spectralPathDensity rho lam hrho hsum p a r
  have hroot : F 0 = q 0 * projectedResolventDerivative rho lam hrho hsum a
      (deficit p (q 0)) :=
    integral_spectralPathDensity_root rho lam hrho hsum p a
      (finite_overlap_value_mem_unit p cut hcut q hp 0).1
      ((finite_overlap_ae_bounds p cut hfirst hlast q hq.monotone hp).mono (fun _ h => h.1))
  have hstep (i : Fin n) : F i.succ - F i.castSucc =
      (projectedResolvent rho lam hrho hsum a (deficit p (q i.castSucc)) -
        projectedResolvent rho lam hrho hsum a (deficit p (q i.succ))) /
          cut i.castSucc.succ := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((continuous_spectralPathDensity rho lam hrho hsum p a).intervalIntegrable 0 (q i.castSucc))
      ((continuous_spectralPathDensity rho lam hrho hsum p a).intervalIntegrable
        (q i.castSucc) (q i.succ))
    have hi := finite_overlap_spectral_increment rho lam hrho hsum p cut hcut hfirst hlast
      q hq hp htop a i
    dsimp only [F]
    linarith
  have he := cavity_prefix_sum_differences F l
  rw [hroot] at he
  simp_rw [hstep] at he
  exact he.symm

theorem finite_overlap_spectral_diagonal (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {n : ℕ} (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (a : ι) :
    spectralGroupDiagonal rho lam hrho hsum p a =
      q 0 * projectedResolventDerivative rho lam hrho hsum a (deficit p (q 0)) +
      (∑ i : Fin n,
        (projectedResolvent rho lam hrho hsum a (deficit p (q i.castSucc)) -
          projectedResolvent rho lam hrho hsum a (deficit p (q i.succ))) /
            cut i.castSucc.succ) +
      projectedResolvent rho lam hrho hsum a (deficit p (q (Fin.last n))) := by
  have he := finite_overlap_spectral_prefix rho lam hrho hsum p cut hcut hfirst hlast
    q hq hp htop a (Fin.last n)
  have ht := integral_spectralPathDensity_tail rho lam hrho hsum p a htop.le
    ((finite_overlap_ae_bounds p cut hfirst hlast q hq.monotone hp).mono (fun _ h => h.2))
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((continuous_spectralPathDensity rho lam hrho hsum p a).intervalIntegrable 0 (q (Fin.last n)))
    ((continuous_spectralPathDensity rho lam hrho hsum p a).intervalIntegrable (q (Fin.last n)) 1)
  have hi (i : Fin n) : (i : ℕ) + 1 ≤ (Fin.last n : ℕ) := by simpa only [Fin.val_last] using Nat.succ_le_of_lt i.isLt
  simp only [hi, ite_true] at he
  unfold spectralGroupDiagonal
  linarith

end InvariantIsing

end

end OAI
