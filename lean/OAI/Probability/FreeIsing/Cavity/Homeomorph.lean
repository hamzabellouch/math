import OAI.Probability.FreeIsing.Cavity.Pair
import OAI.Probability.FreeIsing.Estimates.MessageFunction

namespace OAI

noncomputable section

namespace Problem367

def cavitySiteMap (theta : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 + cavityMessage theta p.2, p.2 + cavityMessage theta p.1)

def cavityHomeomorph {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1) :
    (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun := cavitySiteMap theta
  invFun := CavityPair.solve (lipschitzWith_cavityMessage h0 h1.le) h1
  left_inv p := CavityPair.solve_eq _ _ ⟨rfl, rfl⟩
  right_inv z := Prod.ext (CavityPair.solve_spec _ _ z).1 (CavityPair.solve_spec _ _ z).2
  continuous_toFun := by
    have hψ := (lipschitzWith_cavityMessage h0 h1.le).continuous
    exact (continuous_fst.add (hψ.comp continuous_snd)).prodMk
      (continuous_snd.add (hψ.comp continuous_fst))
  continuous_invFun := CavityPair.continuous_solve _ _

def cavityFromSites {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    (z : ℝ × ℝ) : ℝ × ℝ := (cavityHomeomorph h0 h1).symm z

theorem cavityFromSites_spec {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    (z : ℝ × ℝ) :
    (cavityFromSites h0 h1 z).1 + cavityMessage theta (cavityFromSites h0 h1 z).2 = z.1 ∧
    (cavityFromSites h0 h1 z).2 + cavityMessage theta (cavityFromSites h0 h1 z).1 = z.2 :=
  CavityPair.solve_spec (lipschitzWith_cavityMessage h0 h1.le) h1 z

theorem cavityFromSites_eq {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    {z p : ℝ × ℝ}
    (hp : p.1 + cavityMessage theta p.2 = z.1 ∧
      p.2 + cavityMessage theta p.1 = z.2) : cavityFromSites h0 h1 z = p :=
  CavityPair.solve_eq (lipschitzWith_cavityMessage h0 h1.le) h1 hp

theorem continuous_cavityFromSites {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1) :
    Continuous (cavityFromSites h0 h1) := (cavityHomeomorph h0 h1).symm.continuous

theorem measurable_cavityFromSites {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1) :
    Measurable (cavityFromSites h0 h1) := (continuous_cavityFromSites h0 h1).measurable

theorem cavityFromSites_swap {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    (z : ℝ × ℝ) : cavityFromSites h0 h1 z.swap = (cavityFromSites h0 h1 z).swap :=
  CavityPair.solve_swap (lipschitzWith_cavityMessage h0 h1.le) h1 z

theorem cavityFromSites_bound {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    (z : ℝ × ℝ) :
    |(cavityFromSites h0 h1 z).1 - z.1| ≤ Real.artanh theta ∧
    |(cavityFromSites h0 h1 z).2 - z.2| ≤ Real.artanh theta := by
  have h := cavityFromSites_spec h0 h1 z
  constructor
  · rw [show (cavityFromSites h0 h1 z).1 - z.1 =
        -cavityMessage theta (cavityFromSites h0 h1 z).2 by linarith [h.1], abs_neg]
    exact cavityMessage_abs_le_artanh h0 h1 _
  · rw [show (cavityFromSites h0 h1 z).2 - z.2 =
        -cavityMessage theta (cavityFromSites h0 h1 z).1 by linarith [h.2], abs_neg]
    exact cavityMessage_abs_le_artanh h0 h1 _

theorem cavityFromSites_neg {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    (z : ℝ × ℝ) : cavityFromSites h0 h1 (-z) = -cavityFromSites h0 h1 z := by
  apply cavityFromSites_eq h0 h1
  have hs : theta ^ 2 ≤ 1 := by nlinarith
  have h := cavityFromSites_spec h0 h1 z
  change -((cavityFromSites h0 h1 z).1) +
      cavityMessage theta (-((cavityFromSites h0 h1 z).2)) = -z.1 ∧
    -((cavityFromSites h0 h1 z).2) +
      cavityMessage theta (-((cavityFromSites h0 h1 z).1)) = -z.2
  rw [cavityMessage_neg hs, cavityMessage_neg hs]
  constructor <;> linarith [h.1, h.2]

end Problem367

end

end OAI
