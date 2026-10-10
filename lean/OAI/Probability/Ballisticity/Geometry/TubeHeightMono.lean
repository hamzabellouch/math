import Mathlib
import OAI.Probability.Ballisticity.Geometry.CurvePolicyTubeMass
import OAI.Probability.Ballisticity.Estimates.CurveCenter

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma tubePrefix_eq_curvePrefix {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (θ z : ℝ) (H : ℕ) :
    TubePrefix ℓ f x θ z H = CurvePrefix ℓ f x (fun j => (j:ℝ)*θ) z H := rfl

lemma tubePrefix_mono_height_ae {d : ℕ} (e f : Direction d) (x : Lattice d)
    (θ z : ℝ) {H K : ℕ} (hH : 0 < H) (hHK : H ≤ K) (ω : Environment d) :
    TubePrefix (realPosition (step e)) f x θ z K ≤ᵐ[quenchedKernel (ω,x)]
      TubePrefix (realPosition (step e)) f x θ z H := by
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn
  intro hX
  rw [tubePrefix_eq_curvePrefix] at hX ⊢
  have hX := (curvePrefix_iff e f x _ z (hH.trans_le hHK) X h0 hnn).mp hX
  apply (curvePrefix_iff e f x _ z hH X h0 hnn).mpr
  refine ⟨?_,fun j hj => hX.2 j (hj.trans hHK)⟩
  have hh := hX.1
  rw [←cross_eq_hit] at hh ⊢
  exact cross_antitone _ x (by exact_mod_cast hHK) hh

lemma quenchedTube_mono_height {d : ℕ} (e f : Direction d) (x : Lattice d)
    (θ z : ℝ) {H K : ℕ} (hH : 0 < H) (hHK : H ≤ K) (ω : Environment d) :
    quenchedKernel (ω,x) (TubePrefix (realPosition (step e)) f x θ z K) ≤
      quenchedKernel (ω,x) (TubePrefix (realPosition (step e)) f x θ z H) :=
  measure_mono_ae (tubePrefix_mono_height_ae e f x θ z hH hHK ω)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma tubePrefix_mono_width {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (θ : ℝ) {z w : ℝ} (hzw : z ≤ w) (H : ℕ) :
    TubePrefix ℓ f x θ z H ⊆ TubePrefix ℓ f x θ w H := by
  intro X hX
  obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hX
  refine Set.mem_iUnion.mpr ⟨a,ha.1,?_⟩
  intro j hj
  obtain ⟨k,hk,hr,hb⟩ := ha.2 j hj
  exact ⟨k,hk,hr,hb.trans hzw⟩

lemma curvePolicy_real_tube_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (b : ℕ → ℝ) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    {H : ℕ} (hH : 0 < H) {r : ℝ} (hr : 0 < r)
    (hb : ∀ j ≤ H, |b j-(j:ℝ)*b H/H| ≤ D)
    (E : Set (Lattice d)) {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α)
    (hδ1 : δ ≤ 1) (hα1 : α ≤ 1)
    (dummy : Lattice d) (hd : signedHeight e dummy=H) (hdb : signedCoordinate f dummy=b H)
    (n : ℕ) {K : ℕ} (hK : 0 < K) (hKn : K ≤ n*H) :
    let μ := curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy
    let θ := (∫ u, signedCoordinate f u ∂μ.toMeasure)/(H:ℝ)
    (environmentLaw ν).real {ω | quenchedKernel (ω,0)
      (TubePrefix (realPosition (step e)) f 0 θ (r+2*B+D) K) < (α*δ)^n/2} ≤
      2*((n:ℝ)*(environmentLaw ν).real {ω | curveIncrement (realPosition (step e)) f 0 b B H ω Set.univ < δ} +
        (4*(n:ℝ)*(∫ u, (signedCoordinate f u-b H)^2 ∂μ.toMeasure))/r^2) := by
  dsimp only
  let μ := curvePolicy_average ν (realPosition (step e)) f b B hH E hδ hα dummy
  let m := ∫ u, signedCoordinate f u ∂μ.toMeasure
  have hm : |m-b H| ≤ B := curvePolicy_mean_bound ν e f b hB hH E hδ hα dummy hdb
  have hθ : (H:ℝ)*(m/(H:ℝ))=m := by field_simp
  have hh := curvePolicy_tube_probability ν e f b hB (add_nonneg hD hB) hH (m/H) hr
    (median_line_mean_bound b hH hB hm hb) E hδ hα hδ1 hα1 dummy hd hdb 0 n 0
    (by simp [signedHeight]) hθ
  have hl : environmentLaw ν {ω | quenchedKernel (ω,0)
      (TubePrefix (realPosition (step e)) f 0 (m/H) (r+2*B+D) K) < (α*δ)^n/2} ≤
      environmentLaw ν {ω | quenchedKernel (ω,0)
      (TubePrefix (realPosition (step e)) f 0 (m/H) (r+B+(D+B)) (n*H)) < (α*δ)^n/2} := by
    apply measure_mono
    intro ω hω
    have he : r+B+(D+B)=r+2*B+D := by ring
    rw [he]
    exact (quenchedTube_mono_height e f 0 (m/H) _ hK hKn ω).trans_lt hω
  have hV : 0 ≤ 4*(n:ℝ)*(∫ u, (signedCoordinate f u-b H)^2 ∂μ.toMeasure)/r^2 := by
    apply div_nonneg _ (sq_nonneg _)
    exact mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)
  have hrhs : 2*((n:ℝ≥0∞)*environmentLaw ν {ω | curveIncrement (realPosition (step e)) f 0 b B H ω Set.univ < δ}+
      ENNReal.ofReal (4*(n:ℝ)*(∫ u, (signedCoordinate f u-b H)^2 ∂μ.toMeasure)/r^2)) ≠ ⊤ := by
    finiteness
  have hh := ENNReal.toReal_mono hrhs (hl.trans hh)
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofNat,
    ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal hV] at hh
  exact hh

end DirectionalTransience

end

end

end OAI
