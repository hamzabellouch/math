import OAI.Geometry.RCD.Harmonic.QuantitativeAffineMean

namespace OAI

/-! # Affinity of normalized means from vanishing scaled second variation -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem scaled_affine_mean_limit (F H G : ℕ → ℝ → ℝ)
    (r : ℕ → ℝ) (_hr : ∀ k, 0 < r k) (M : ℝ≥0)
    (hLip : ∀ k, LipschitzOnWith M (fun t => F k t/r k) (Icc (0:ℝ) 1))
    (hH : ∀ k t, t∈Ioo (0:ℝ) 1 → DifferentiableAt ℝ (H k) t)
    (hint : ∀ k a b, 0 < a → a ≤ b → b < 1 →
      (∫ t in a..b, G k t)=deriv (H k) b-deriv (H k) a)
    (hG : ∀ a b, 0 < a → a ≤ b → b < 1 →
      TendstoUniformlyOn (fun k t => G k t/r k) (fun _ => 0) atTop (Icc a b))
    (hval : ∀ t∈Ioo (0:ℝ) 1, Tendsto (fun k => (F k t-H k t)/r k) atTop (𝓝 0))
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    Tendsto (fun k => (F k t-((1-t)*F k 0+t*F k 1))/r k) atTop (𝓝 0) := by
  let F' k t := F k t/r k
  let H' k t := H k t/r k
  have hder (k : ℕ) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
      DifferentiableAt ℝ (H' k) t := (hH k t ht).div_const (r k)
  have hint' (k : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
      (∫ t in a..b, G k t/r k)=deriv (H' k) b-deriv (H' k) a := by
    rw [intervalIntegral.integral_div,hint k a b ha hab hb]
    rw [show deriv (H' k) b=deriv (H k) b/r k from
      ((hH k b ⟨ha.trans_le hab,hb⟩).hasDerivAt.div_const (r k)).deriv,
      show deriv (H' k) a=deriv (H k) a/r k from
      ((hH k a ⟨ha,hab.trans_lt hb⟩).hasDerivAt.div_const (r k)).deriv]
    ring
  have hval' : ∀ t∈Ioo (0:ℝ) 1, Tendsto (fun k => F' k t-H' k t) atTop (𝓝 0) := by
    intro t ht
    simpa only [F',H',sub_div] using hval t ht
  have hchord : ∀ {a b x : ℝ}, 0 < a → a < b → b < 1 → x∈Icc a b →
      Tendsto (fun k => F' k x-F' k a-((F' k b-F' k a)/(b-a))*(x-a)) atTop (𝓝 0) := by
    intro a b x ha hab hb hx
    apply interior_chord_errors_transfer F' H' hval' _ ha hab hb hx
    intro a b x ha hab hb hx
    exact interior_chord_error_tendsto_zero H' (fun k t => G k t/r k)
      hder hint' hG ha hab hb hx
  have hh := endpoint_chord_error_of_interior_errors F' M hLip hchord ht
  convert hh using 1
  funext k
  dsimp only [F']
  ring

end RegularPointCoordinates

end

end OAI
