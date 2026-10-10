import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketDifferentiation
import OAI.Analysis.LipschitzHilbert.Packets.TopWeightedPacket

namespace OAI

/-! Fixed polynomial weights commute exactly with the actual finite
interval synthesis, without changing the analyzing coefficients. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

omit [Fintype κ] in
theorem planarPacketInterval_commonWeight
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (w : ℝ → ℝ → ℝ)
    (a b : ℕ) (x y : ℝ) :
    planarPacketInterval coeff (fun j u k t z => (w z t:ℂ)*wave j u k t z) a b x y =
      w x y • planarPacketInterval coeff wave a b x y := by
  have h := planarPacketInterval_smul coeff wave (w x y) a b x y
  convert h using 1
  ext k
  rfl

omit [Fintype κ] in
theorem planarPacketInterval_topWeighted
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
    (u r v R : ℝ) (q : ℕ) (a b : ℕ) (x y : ℝ) :
    planarPacketInterval coeff (fun j i k t z => topWeightedWave (wave j i k t) u r v R t q z)
      a b x y = (polynomialWeight u r q x*polynomialWeight v R q y) •
        planarPacketInterval coeff (fun j i k t z => wave j i k t z) a b x y := by
  simp_rw [topWeightedWave_apply]
  exact planarPacketInterval_commonWeight coeff _
    (fun x y => polynomialWeight u r q x*polynomialWeight v R q y) a b x y

theorem planarPacketInterval_topWeighted_norm
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
    (u r v R : ℝ) (q : ℕ) (a b : ℕ) (x y : ℝ) :
    ‖planarPacketInterval coeff (fun j i k t z => topWeightedWave (wave j i k t) u r v R t q z)
      a b x y‖ = (polynomialWeight u r q x*polynomialWeight v R q y) *
        ‖planarPacketInterval coeff (fun j i k t z => wave j i k t z) a b x y‖ := by
  rw [planarPacketInterval_topWeighted, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))
      (zero_le_one.trans (polynomialWeight_one_le _ _ _ _)))]

end LipschitzHilbert

end

end OAI
