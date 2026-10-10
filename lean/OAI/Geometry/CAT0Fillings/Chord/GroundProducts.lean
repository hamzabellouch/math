import Mathlib
import OAI.Geometry.CAT0Fillings.Conformal.Closed
import OAI.Geometry.CAT0Fillings.Minimizers.CriticalEnergy
import OAI.Geometry.CAT0Fillings.Chord.GroundState

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def chordXi (o : X) (v : q.Sobolev) (κ β : ℝ) (z : ℕ × Euc (k+1)) : Euc (k+1) :=
  (κ*(q.inclusion v (q.atlasParam z))^(1+β)) • q.gradient (LipschitzWith.dist_right o) z+
    (κ*β*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β) • q.closedGradient v z

lemma closed_chord_product (hz : IsCycle T) (o : X) (v : q.Sobolev) {κ β B : ℝ}
    {f : ℝ → ℝ} (hb : 0 < β) (hB : 0 ≤ B) (hf : ContDiff ℝ 1 f)
    (hfB : ∀ t, |f t| ≤ B ∧ |deriv f t| ≤ B)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ L : q.Sobolev,
      (q.closedGradient L : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => (γ*(q.inclusion v (q.atlasParam z))^(γ-1)) • q.closedGradient v z)) :
    ∃ P : q.Sobolev,
      (q.inclusion P : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => q.inclusion v x*f (κ*dist o x*(q.inclusion v x)^β)) ∧
      (q.closedGradient P : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β) • q.closedGradient v z+
          deriv f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β) • q.chordXi o v κ β z) := by
  obtain ⟨P,hP,hDP⟩ := q.closed_conformal hz (LipschitzWith.dist_right o)
    (fun x => ⟨dist_nonneg,Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ o) (mem_univ x)⟩) (m := 0) (α := 1) (κ := κ)
    le_rfl hb hB hf hfB v hv hm hpow
  refine ⟨P,?_,?_⟩
  · simpa only [Conformal.profile,pow_zero,one_mul,Real.rpow_one] using hP
  · filter_upwards [hDP,q.atlas_preserving.quasiMeasurePreserving.ae hv,
      q.closedGradient_level_zero hz v 0] with z hD hu hzero
    rw [hD]
    split_ifs with hpos
    · dsimp only [Conformal.profileRD,Conformal.profileZD,chordXi]
      simp only [Nat.cast_zero,pow_zero,zero_mul,zero_add,one_mul,mul_one,
        Real.rpow_one,sub_self,Real.rpow_zero,
        show (1:ℝ)+β-1 = β by ring]
      module
    · have hu0 : q.inclusion v (q.atlasParam z) = 0 := le_antisymm (not_lt.mp hpos) hu
      have hD0 := hzero hu0
      simp [chordXi,hu0,hD0,Real.zero_rpow hb.ne',Real.zero_rpow (by linarith : 1+β ≠ 0)]
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry

lemma deriv_square {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (t : ℝ) :
    deriv (fun x => (f x)^2) t = 2*f t*deriv f t := by
  have h := ((hf.differentiable (by norm_num) t).hasDerivAt.pow 2).deriv
  norm_num only [show 2-1 = (1:ℕ) by rfl, pow_one, Nat.cast_ofNat] at h
  exact h

lemma deriv_square_bound {f : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hf : ContDiff ℝ 1 f)
    (hfB : ∀ t, |f t| ≤ B ∧ |deriv f t| ≤ B) :
    ∀ t, |(f t)^2| ≤ 2*B^2 ∧ |deriv (fun x => (f x)^2) t| ≤ 2*B^2 := by
  intro t
  have hder := deriv_square hf t
  constructor
  · rw [abs_pow]
    have h := pow_le_pow_left₀ (abs_nonneg (f t)) (hfB t).1 2
    nlinarith [sq_nonneg B]
  · rw [hder,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    calc
      _ ≤ 2*B*B := mul_le_mul (mul_le_mul_of_nonneg_left (hfB t).1 (by norm_num))
        (hfB t).2 (abs_nonneg _) (by positivity)
      _ = _ := by ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma chord_ground_state (hz : IsCycle T) (o : X) (v : q.Sobolev) {κ β B : ℝ}
    {f : ℝ → ℝ} (hb : 0 < β) (hB : 0 ≤ B) (hf : ContDiff ℝ 1 f)
    (hfB : ∀ t, |f t| ≤ B ∧ |deriv f t| ≤ B)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ L : q.Sobolev,
      (q.closedGradient L : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => (γ*(q.inclusion v (q.atlasParam z))^(γ-1)) • q.closedGradient v z))
    (heuler : ∀ ψ : q.Sobolev,
      4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+1:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂MassMeasure.currentMassMeasure hT)) :
    ∃ P : q.Sobolev,
      (q.inclusion P : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => q.inclusion v x*f (κ*dist o x*(q.inclusion v x)^β)) ∧
      Integrable (fun z => (deriv f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β))^2*
        ‖q.chordXi o v κ β z‖^2) q.atlasMeasure ∧
      AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) P =
        (k+1:ℝ)*(∫ x, (q.inclusion v x)^(2+4*β)*(f (κ*dist o x*(q.inclusion v x)^β))^2 ∂MassMeasure.currentMassMeasure hT)+
          4*β*(∫ z, (deriv f (κ*dist o (q.atlasParam z)*(q.inclusion v (q.atlasParam z))^β))^2*
            ‖q.chordXi o v κ β z‖^2 ∂q.atlasMeasure) := by
  obtain ⟨P,hP,hDP⟩ := q.closed_chord_product hz o v (κ := κ) hb hB hf hfB hv hm hpow
  obtain ⟨Q,hQ,hDQ⟩ := q.closed_chord_product hz o v (κ := κ) hb (show 0 ≤ 2*B^2 by positivity)
    (hf.pow 2) (deriv_square_bound hB hf hfB) hv hm hpow
  refine ⟨P,hP,?_⟩
  apply q.ground_state v P Q
    (w := fun x => f (κ*dist o x*(q.inclusion v x)^β))
    (d := fun x => deriv f (κ*dist o x*(q.inclusion v x)^β))
    (ξ := q.chordXi o v κ β) hb hv hP hQ hDP ?_ (heuler Q)
  filter_upwards [hDQ] with z hzD
  rw [hzD]
  rw [deriv_square hf]
end CAT0Fillings.ChartGeometry
end

end OAI
