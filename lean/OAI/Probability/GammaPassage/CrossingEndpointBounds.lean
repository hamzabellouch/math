import OAI.Probability.GammaPassage.CrossingChain
import OAI.Probability.GammaPassage.GoodSiteBlocks

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory
open scoped Topology

theorem crossing_endpoints_escape_linear (b σ S : ℝ) (n d : ℤ)
    (hb : |b| ≤ 1) (hσ : |σ|=1) (hS : 0 < S) (hn : 0 < n) (hd : 0 ≤ d)
    (v z : ℕ → Vertex) (hv0 : v 0=0)
    (hstep : ∀ t, v (t+1)=v t+(1,0) ∨ v (t+1)=v t+(0,1))
    (hx : ∀ t, (z t).1=blockX n d (v t)+n)
    (hr : ∀ t, |transverse b (z t)-blockY σ S (v t)| ≤ S/4) :
    Tendsto (fun t => ‖latticeEmbed (z t)‖) atTop atTop ∧
    ∀ t, ‖latticeEmbed (z t)‖ ≤ (2*((n : ℝ)+d)+3*S)*((t : ℝ)+1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
  have hcoords (t : ℕ) := oriented_path_coordinates v hv0 hstep t
  have hxt (t : ℕ) : ((z t).1 : ℝ) = (t : ℝ)*((n : ℝ)+d)+n := by
    rw [hx]
    simp only [blockX,blockLayer,Int.cast_add,Int.cast_mul]
    have hh := congrArg (fun a : ℤ => (a : ℝ)) (hcoords t).1
    push_cast at hh
    rw [hh]
  have hxpos (t : ℕ) : (t : ℝ)+1 ≤ ((z t).1 : ℝ) := by
    rw [hxt]
    nlinarith [Nat.cast_nonneg (α := ℝ) t]
  have hnlow (t : ℕ) : (t : ℝ) ≤ ‖latticeEmbed (z t)‖ := by
    have hh := plane_coordinate_le_norm (latticeEmbed (z t)) 0
    change |((z t).1 : ℝ)| ≤ _ at hh
    have hp : (0 : ℝ) ≤ (z t).1 := by linarith [Nat.cast_nonneg (α := ℝ) t,hxpos t]
    rw [abs_of_nonneg hp] at hh
    linarith [hxpos t]
  refine ⟨tendsto_atTop_mono hnlow tendsto_natCast_atTop_atTop,?_⟩
  intro t
  have hlevel : (0 : ℝ) ≤ blockLevel (v t) ∧ (blockLevel (v t) : ℝ) ≤ 2*t := by
    have hh := hcoords t
    constructor <;> dsimp [blockLevel] <;> exact_mod_cast (by omega : _)
  have hy : |blockY σ S (v t)| ≤ 2*(t : ℝ)*S := by
    unfold blockY
    rw [abs_mul,abs_mul,hσ,one_mul,abs_of_nonneg hlevel.1,abs_of_pos hS]
    exact mul_le_mul_of_nonneg_right hlevel.2 hS.le
  have hrbound : |transverse b (z t)| ≤ 2*(t : ℝ)*S+S/4 := by
    have hh := abs_add_le (transverse b (z t)-blockY σ S (v t)) (blockY σ S (v t))
    rw [sub_add_cancel] at hh
    linarith [hr t]
  have hpos : (0 : ℝ) ≤ (z t).1 := by linarith [hxpos t,Nat.cast_nonneg (α := ℝ) t]
  have hyy : |((z t).2 : ℝ)| ≤ |transverse b (z t)|+((z t).1 : ℝ) := by
    have hh := abs_add_le (transverse b (z t)) (b*((z t).1 : ℝ))
    have he : transverse b (z t)+b*((z t).1 : ℝ)=((z t).2 : ℝ) := by unfold transverse; ring
    rw [he,abs_mul,abs_of_nonneg hpos] at hh
    have hm := mul_le_mul_of_nonneg_right hb hpos
    linarith
  have hnorm := plane_norm_le_coordinates (latticeEmbed (z t))
  change ‖latticeEmbed (z t)‖ ≤ |((z t).1 : ℝ)|+|((z t).2 : ℝ)| at hnorm
  rw [abs_of_nonneg hpos] at hnorm
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  rw [hxt] at hyy hnorm
  nlinarith

end GammaFPP.CrossingBridge

end OAI
