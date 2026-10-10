import OAI.Probability.GammaPassage.ShapeDeficit
import OAI.Probability.GammaPassage.HighDensityOriented

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory
open scoped Topology

def crossingChain (initialPath : List Step) (trial connector : ℕ → List Step) : ℕ → List Step
  | 0 => initialPath ++ trial 0
  | n+1 => crossingChain initialPath trial connector n ++ (connector n ++ trial (n+1))

theorem crossingChain_endpoint (initialPath : List Step) (trial connector : ℕ → List Step)
    (a z : ℕ → Vertex) (hp : displacement initialPath = a 0)
    (ht : ∀ n, a n+displacement (trial n)=z n)
    (hc : ∀ n, z n+displacement (connector n)=a (n+1)) (n : ℕ) :
    displacement (crossingChain initialPath trial connector n)=z n := by
  induction n with
  | zero => simpa only [crossingChain,displacement_append,hp] using ht 0
  | succ n ih =>
    simp only [crossingChain,displacement_append,ih,← add_assoc,hc,ht]

theorem crossingChain_defect (w : Edge → ℝ) (b m a e : ℝ)
    (initialPath : List Step) (trial connector : ℕ → List Step) (p z : ℕ → Vertex)
    (hp : displacement initialPath=p 0)
    (ht : ∀ n, p n+displacement (trial n)=z n)
    (hc : ∀ n, z n+displacement (connector n)=p (n+1))
    (htrial : ∀ n, defect w b m a (p n) (trial n) ≤ -e)
    (hconnector : ∀ n, defect w b m a (z n) (connector n) ≤ e/2) (n : ℕ) :
    defect w b m a 0 (crossingChain initialPath trial connector n) ≤
      defect w b m a 0 initialPath-((n : ℝ)+1)*e+(n : ℝ)*e/2 := by
  induction n with
  | zero =>
    simp only [crossingChain,defect_append,zero_add,hp]
    have hh := htrial 0
    norm_num
    linarith
  | succ n ih =>
    rw [crossingChain,defect_append,crossingChain_endpoint initialPath trial connector p z hp ht hc,
      zero_add,defect_append,hc]
    have h1 := htrial (n+1)
    have h2 := hconnector n
    push_cast
    linarith

/-- A forward path from zero lies in its indexed layer, with nonnegative
coordinates bounded by the layer index. -/
theorem oriented_path_coordinates (v : ℕ → Vertex) (h0 : v 0=0)
    (hs : ∀ n, v (n+1)=v n+(1,0) ∨ v (n+1)=v n+(0,1)) (n : ℕ) :
    (v n).1+(v n).2=(n : ℤ) ∧ 0 ≤ (v n).1 ∧ 0 ≤ (v n).2 ∧ (v n).2 ≤ n := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rcases hs n with he | he <;> rw [he] <;> simp only [Prod.fst_add,Prod.snd_add] <;>
      push_cast <;> omega

/-- A crossing chain with a linear deficit contradicts the uniform shape
law when its endpoints escape with at most linear growth. -/
theorem UniformShape.no_crossing_chain (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (μ : Plane → ℝ) (hu : UniformShape w μ) (b m a e B : ℝ) (he : 0 < e) (hB : 0 < B)
    (hf : ∀ v, m*v 0+a*(v 1-b*v 0) ≤ μ v)
    (initialPath : List Step) (trial connector : ℕ → List Step) (p z : ℕ → Vertex)
    (hp : displacement initialPath=p 0)
    (ht : ∀ n, p n+displacement (trial n)=z n)
    (hc : ∀ n, z n+displacement (connector n)=p (n+1))
    (htrial : ∀ n, defect w b m a (p n) (trial n) ≤ -e)
    (hconnector : ∀ n, defect w b m a (z n) (connector n) ≤ e/2)
    (hescape : Tendsto (fun n => ‖latticeEmbed (z n)‖) atTop atTop)
    (hbound : ∀ n, ‖latticeEmbed (z n)‖ ≤ B*((n : ℝ)+1)) : False := by
  apply hu.no_linear_deficit w hw μ (fun v => m*v 0+a*(v 1-b*v 0)) hf z
    (crossingChain initialPath trial connector) (defect w b m a 0 initialPath) (e/2) B
    (by linarith) hB hescape hbound
    (crossingChain_endpoint initialPath trial connector p z hp ht hc)
  intro n
  have hh := crossingChain_defect w b m a e initialPath trial connector p z hp ht hc htrial hconnector n
  rw [defect,crossingChain_endpoint initialPath trial connector p z hp ht hc] at hh
  simp only [support,transverse] at hh
  change pathCost w 0 (crossingChain initialPath trial connector n) ≤
    m*(z n).1+a*((z n).2-b*(z n).1)+defect w b m a 0 initialPath-e/2*n
  linarith

end GammaFPP.CrossingBridge

end OAI
