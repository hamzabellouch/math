import OAI.MeasureTheory.Falconer.Graphs.GraphZNonstationary
import OAI.MeasureTheory.Falconer.Graphs.GraphNonedgeAmplitude

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graph_z_nonedge_scale_bound {f : (Plane × ℝ) → ℂ} {C : ℝ} (n N : ℕ)
    (sig v p s : ℝ) (x y η : Plane)
    (hf : GraphDerivativeBound n f C (graphNonedgeDerivativeScale N sig (v-p)))
    (hs : tsupport f ⊆ graphAmplitudeCompact) (hC : 0 ≤ C)
    (hτ : ((2:ℝ)^v*((2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig)))/16 ≤
      |(2:ℝ)^v*inner ℝ η (graphDerivative s x y)|) :
    ‖∫ z : ℝ, Complex.exp (Complex.I*Complex.ofReal ((2:ℝ)^v*inner ℝ η (graphA z x+s • graphB z y)))*f (η,z)‖ ≤
      8*C*16^n*((2:ℝ)^N)^(-26*sig*(n:ℝ)) := by
  let τ := (2:ℝ)^v*inner ℝ η (graphDerivative s x y)
  let G := (2:ℝ)^v*((2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig))
  let E := graphNonedgeDerivativeScale N sig (v-p)
  have hG : 0 < G := by dsimp [G]; positivity
  have hE : 0 < E := by dsimp [E,graphNonedgeDerivativeScale]; positivity
  have hτpos : 0 < |τ| := (by positivity : 0 < G/16).trans_le hτ
  have hτne : τ ≠ 0 := abs_pos.mp hτpos
  have he := graph_z_nonstationary_bound n hf hs hC hE.le ((2:ℝ)^v) s x y η hτne
  have hratio : E/|τ| ≤ 16*((2:ℝ)^N)^(-26*sig) := by
    calc
      _ ≤ E/(G/16) := div_le_div_of_nonneg_left hE.le (by positivity) hτ
      _ = 16*(E/G) := by field_simp
      _ = _ := by rw [graph_nonedge_scale_gain]
  calc
    _ ≤ 8*C*E^n/|τ|^n := by simpa only [Complex.ofReal_mul] using he
    _ = 8*C*(E/|τ|)^n := by rw [div_pow]; ring
    _ ≤ 8*C*(16*((2:ℝ)^N)^(-26*sig))^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio _) (by positivity)
    _ = 8*C*16^n*((2:ℝ)^N)^(-26*sig*(n:ℝ)) := by
      rw [mul_pow,← Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ (2:ℝ)^N)]
      ring

end PlanarFalconer

end OAI
