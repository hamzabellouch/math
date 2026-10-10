import OAI.Dynamics.ConditionalShuffle.OverlayFiber

namespace OAI

noncomputable section
open scoped Classical
namespace Revealed.Instrument
open Thorp Thorp.Conditional Thorp.Fourier Revealed.Disintegration
variable {E S G Ω R : Type} [fintype_S : Fintype S] [Fintype G] [Group G] [Fintype Ω] [nonempty_Ω : Nonempty Ω]
  [Fintype R] [nonempty_R : Nonempty R]
variable (I : Data E S G Ω)

def resampledRun (J : E → Ω → R → G) (e : E) :
    (n : ℕ) → (Fin n → Ω) → (Fin n → R) → G
  | 0, _, _ => 1
  | n+1, c, r => J (base I e n (observed I e n (Fin.init c))) (c (Fin.last n)) (r (Fin.last n)) *
      resampledRun J e n (Fin.init c) (Fin.init r)

lemma resampledRun_law (J : E → Ω → R → G)
    (hJ : ∀ e c, fairMass (J e c) = kernel I e (I.obs e c))
    (e : E) (n : ℕ) (c : Fin n → Ω) :
    fairMass (resampledRun I J e n c) = realProduct n (kernels I e n (observed I e n c)) := by
  let retained_fintype_S := fintype_S
  let retained_nonempty_Ω := nonempty_Ω
  let retained_nonempty_R := nonempty_R
  induction n with
  | zero =>
      funext g
      simp only [resampledRun, fairMass, realProduct, Fintype.card_fun,
        Fintype.card_fin, pow_zero, Nat.cast_one, div_one]
      simp [eq_comm]
  | succ n ih =>
      have hc := Thorp.FiniteLaw.conv_fairMass
        (J (base I e n (observed I e n (Fin.init c))) (c (Fin.last n)))
        (resampledRun I J e n (Fin.init c))
      change realConv _ _ = _ at hc
      rw [hJ, ih] at hc
      simp only [observed, kernels, realProduct, Fin.init_snoc, Fin.snoc_last]
      rw [hc]
      funext g
      rw [fairMass_eq_mean, fairMass_eq_mean, mean_prod, mean_function_snoc]
      rw [mean_comm]
      apply mean_congr; intro r
      apply mean_congr; intro q
      simp only [resampledRun, Fin.init_snoc, Fin.snoc_last]

lemma distance_mean (e : E) (n : ℕ) :
    distance I e n = mean (fun c : Fin n → Ω =>
      tv (realProduct n (kernels I e n (observed I e n c)))
        (fun _ => (Fintype.card G : ℝ)⁻¹)) := by
  unfold distance
  have hm := pathJoint_marginal I e n
  have hprob : fairMass (observed I e n) = weights I e n := by
    rw [← marginal_fairMass (observed I e n) (groupRun I e n)]
    exact funext hm
  rw [← hprob, fairMass_test]

lemma resampled_distance (J : E → Ω → R → G)
    (hJ : ∀ e c, fairMass (J e c) = kernel I e (I.obs e c)) (e : E) (n : ℕ) :
    mean (fun c : Fin n → Ω => tv (fairMass (resampledRun I J e n c))
      (fun _ => (Fintype.card G : ℝ)⁻¹)) = distance I e n := by
  simp_rw [resampledRun_law I J hJ, distance_mean]

end Revealed.Instrument

end

end OAI
