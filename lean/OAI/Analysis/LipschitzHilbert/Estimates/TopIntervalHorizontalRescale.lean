import OAI.Analysis.LipschitzHilbert.Estimates.TopCovariantHorizontalRescale

namespace OAI

/-! Horizontal normalization preserves the actual analyzed top interval. -/

noncomputable section
namespace LipschitzHilbert.PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem horizontalRescale_interval (P : PlanarPacketFamily N κ ι)
    (r : ℝ) (hr : 0 < r) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (a b : ℕ) (x y : ℝ) :
    planarPacketInterval ((P.horizontalRescale r hr).mainCoefficient d
      (fun z => v (z.1,r*z.2)) (fun z => g (z.1,r*z.2)))
      (fun j u k t s => (P.horizontalRescale r hr).wave j u k t s) a b x y =
    planarPacketInterval (P.mainCoefficient d v g)
      (fun j u k t s => P.wave j u k t s) a b (r*x) y := by
  have hc : (P.horizontalRescale r hr).mainCoefficient d
      (fun z => v (z.1,r*z.2)) (fun z => g (z.1,r*z.2)) = P.mainCoefficient d v g := by
    funext j u
    exact P.horizontalRescale_mainCoefficient r hr d v g j u
  rw [hc]
  rfl

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
