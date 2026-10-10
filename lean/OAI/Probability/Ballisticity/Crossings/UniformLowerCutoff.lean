import Mathlib
import OAI.Probability.Ballisticity.Estimates.LayerPairTruthEventMono

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

def LowerEscape {d : ℕ} (ν : Measure (Row d)) (e f : Direction d) (b C q : ℝ) : Prop :=
  ∃ K : ℕ, 0 < K ∧ (K:ℝ) ≤ C*fluctuationScale
    (independentConditionedPairLaw ν (realPosition (step e)))
    (commonIncrementProcess (realPosition (step e)) f 0) b ∧
    ∀ x y : Lattice d, signedHeight e x=signedHeight e y →
      q ≤ (sharedConditionedPairLaw ν (realPosition (step e)) x y).real
        (layerPairTruthEvent (realPosition (step e)) (signedHeight e) x y
          (signedHeight e x+K) {uv | 2*b ≤ |signedCoordinate f uv.1-signedCoordinate f uv.2|})

lemma LowerEscape.mono {d : ℕ} {ν : Measure (Row d)} {e f : Direction d} {b C q C' q' : ℝ}
    (h : LowerEscape ν e f b C q) (hC : C ≤ C') (hq : q' ≤ q) :
    LowerEscape ν e f b C' q' := by
  obtain ⟨K,hK,hbound,hprob⟩ := h
  exact ⟨K,hK,hbound.trans (mul_le_mul_of_nonneg_right hC (fluctuationScale_nonneg _ _ _)),
    fun x y hxy => hq.trans (hprob x y hxy)⟩

theorem bad_radius_lower_escape_uniform {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {l ε : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) (hε : 0 < ε) :
    ∃ C q D₀ : ℝ, 0 < C ∧ 0 < q ∧ 0 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      ε ≤ fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) D*
        (independentConditionedPairLaw ν (realPosition (step e))).real
          {P | l*D < |commonIncrementProcess (realPosition (step e)) f 0 P|} →
      LowerEscape ν e f (4*D) C q := by
  let ℓ := realPosition (step e)
  let μ := independentConditionedPairLaw ν ℓ
  let S := commonIncrementProcess ℓ f 0
  let n := fluctuationScale μ S
  change ∃ C q D₀ : ℝ, 0 < C ∧ 0 < q ∧ 0 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
    ε ≤ n D*μ.real {P | l*D < |S P|} → LowerEscape ν e f (4*D) C q
  by_contra hn
  push Not at hn
  have hex (i : ℕ) : ∃ D : ℝ, (i:ℝ)+1 ≤ D ∧ ε ≤ n D*μ.real {P | l*D < |S P|} ∧
      ¬LowerEscape ν e f (4*D) ((i:ℝ)+1) (1/((i:ℝ)+1)) :=
    hn ((i:ℝ)+1) (1/((i:ℝ)+1)) ((i:ℝ)+1) (by positivity) (by positivity) (by positivity)
  choose r hr hbad hfail using hex
  have hrinf : Tendsto r atTop atTop := by
    apply tendsto_atTop_mono hr
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  obtain ⟨C,q,hC,hq,hesc⟩ := bad_radius_lower_cutoff_escape ν hue e f hef htrans r hrinf
    hl hl1 hε (Eventually.of_forall hbad)
  have hnum : ∀ᶠ i : ℕ in atTop, C ≤ (i:ℝ)+1 :=
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).eventually_ge_atTop C
  have hden : Tendsto (fun i : ℕ => 1/((i:ℝ)+1)) atTop (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).comp (tendsto_add_atTop_nat 1)
  have hsmall : ∀ᶠ i : ℕ in atTop, 1/((i:ℝ)+1) ≤ q :=
    (hden.eventually (gt_mem_nhds hq)).mono fun i hi => hi.le
  obtain ⟨i,hi,hiC,hiq⟩ := (hesc.and (hnum.and hsmall)).exists
  apply hfail i
  apply LowerEscape.mono (C := C) (q := q) _ hiC hiq
  simpa only [LowerEscape,← mul_assoc,show (2:ℝ)*4=8 by norm_num] using hi

end DirectionalTransience

end

end

end OAI
