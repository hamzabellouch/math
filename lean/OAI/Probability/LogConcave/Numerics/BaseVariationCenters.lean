import Mathlib
import OAI.Probability.LogConcave.Numerics.BaseVariation

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature
open scoped Classical

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma baseVariation_of_centers (E : MeanTree X d) (u v : X) (B : ℝ)
    (hb : ‖base E u-base E v‖≤B)
    (hc : centers (fun _ b => ‖b u-b v‖≤B) E) : BaseVariation B u v E := by
  induction E with | node k b hb' a r C ih =>
    exact ⟨hb,fun i => ih i (hc i).1 (hc i).2⟩

omit [MeasurableSpace X] in
lemma DirectCenter.variation {r T v r' : ℝ} {x Y G b : X → Point d}
    (hr : 0≤r) (hT : T≤1) (hb : DirectCenter r T v x Y G r' b) (u z : X) :
    ‖b u-b z‖≤‖x u-x z‖+r*(‖Y u-Y z‖+‖G u-G z‖) := by
  obtain ⟨ρ,hρ,θ,hθ,hr',rfl⟩ := hb
  have hρ1 : ρ≤1 := hρ.2.trans hT
  have hrρ : 0≤r*ρ := mul_nonneg hr hρ.1
  have ho : ‖oriented Y G θ u-oriented Y G θ z‖≤‖Y u-Y z‖+‖G u-G z‖ := by
    rw [show oriented Y G θ u-oriented Y G θ z=
      Real.cos θ • (Y u-Y z)+Real.sin θ • (G u-G z) by dsimp [oriented]; module]
    apply (norm_add_le _ _).trans
    simp only [norm_smul,Real.norm_eq_abs]
    nlinarith [Real.abs_cos_le_one θ,Real.abs_sin_le_one θ,norm_nonneg (Y u-Y z),norm_nonneg (G u-G z)]
  rw [show x u+(r*ρ) • oriented Y G θ u-(x z+(r*ρ) • oriented Y G θ z)=
    (x u-x z)+(r*ρ) • (oriented Y G θ u-oriented Y G θ z) by module]
  apply (norm_add_le _ _).trans
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hrρ]
  have h₁ := mul_le_mul_of_nonneg_left ho hrρ
  have h₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ1 hr)
    (show 0≤‖Y u-Y z‖+‖G u-G z‖ by positivity)
  nlinarith

lemma literalMean_variationX {r T h ψ σ v : ℝ} {n m N nc Nc : ℕ}
    (hr : 0≤r) (hT : 0<T) (hT1 : T<1) (hh : 0<h) (hv : 0≤v)
    (hψ : ∀j : Fin (m+1),|ψ*angleNodes m j|≤v) (e : ProbabilityNode T h (n+1))
    (x y Y G : Point d) :
    BaseVariation ‖x-y‖ (x,(Y,G)) (y,(Y,G)) (literalMean r T h ψ σ n m N nc Nc e) := by
  have hg := literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=N) (nc:=nc) (Nc:=Nc) hT hT1 hh hv hψ e
  apply baseVariation_of_centers
  · rw [hg.1]
    simp
  · exact centers_mono _ (fun r' b hb => by
      simpa only [Prod.fst,Prod.snd,sub_self,norm_zero,add_zero,mul_zero] using hb.variation hr hT1.le (x,(Y,G)) (y,(Y,G))) hg.2

lemma literalMean_variationY {r T h ψ σ v : ℝ} {n m N nc Nc : ℕ}
    (hr : 0≤r) (hT : 0<T) (hT1 : T<1) (hh : 0<h) (hv : 0≤v)
    (hψ : ∀j : Fin (m+1),|ψ*angleNodes m j|≤v) (e : ProbabilityNode T h (n+1))
    (x Y Z G : Point d) :
    BaseVariation (r*‖Y-Z‖) (x,(Y,G)) (x,(Z,G)) (literalMean r T h ψ σ n m N nc Nc e) := by
  have hg := literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=N) (nc:=nc) (Nc:=Nc) hT hT1 hh hv hψ e
  apply baseVariation_of_centers
  · rw [hg.1]
    simp only [sub_self,norm_zero]
    positivity
  · exact centers_mono _ (fun r' b hb => by
      simpa only [Prod.fst,Prod.snd,sub_self,norm_zero,add_zero,zero_add] using hb.variation hr hT1.le (x,(Y,G)) (x,(Z,G))) hg.2

lemma literalSample_variationX {r T h : ℝ} {n N : ℕ}
    (hr : 0≤r) (hn : 0<n) (hT : 0<T) (hT1 : T<1) (hh : 0<h)
    (e : ProbabilityNode T h n) (x y z : Point d) :
    BaseVariation ‖x-y‖ (x,z) (y,z) (literalSample r T h n N e) := by
  have hg := literalSample_geometry (d:=d) (r:=r) (N:=N) hn hT hT1 hh e
  apply baseVariation_of_centers
  · rw [hg.1]; simp
  · exact centers_mono _ (fun r' b hb => by
      simpa only [Prod.fst,Prod.snd,sub_self,norm_zero,add_zero,mul_zero] using hb.variation hr hT1.le (x,z) (y,z)) hg.2
end LogConcaveSampling.MeanTree

end

end

end OAI
