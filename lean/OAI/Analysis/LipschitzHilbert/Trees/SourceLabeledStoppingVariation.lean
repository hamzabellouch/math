import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledVariationSplit
import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualVariation

namespace OAI

/-! The original masked physical packets, grouped by their actual stopping
levels, have the same fixed length-variation bound used in the reference
event. This includes clamped prefixes and every disjoint unary run. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem cubicVariation_cube {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) : cubicVariation F N ^ 3 = finiteCubicVariation F N := by
  rw [cubicVariation, ← Real.rpow_natCast, ← Real.rpow_mul (finiteCubicVariation_nonneg F N)]
  norm_num

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)

def physicalMaskedValue (z : ℝ×ℝ) (q : P.PacketIndex) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => P.physicalMultiplierCoefficient t b v g q.1 q.2.1 q.2.2 k*
    ((T q.1 q.2.1 q.2.2).mask L A z:ℂ)*
    (P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k z)

theorem physicalMaskedValue_length_sum (y x : ℝ) (j : Fin N) :
    (∑ q ∈ Finset.univ.filter (fun q : P.PacketIndex => q.1 = j),
      P.physicalMaskedValue alt hAlt t b v g T L A (x,y+t*x) q) =
        P.physicalMaskedBand alt hAlt t b v g T L A y j x := by
  classical
  rw [Finset.sum_filter,Fintype.sum_sigma,Finset.sum_eq_single j]
  · simp only [ite_true]
    ext k
    simp only [Fintype.sum_sigma,physicalMaskedValue,physicalMaskedBand,
      WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply]
  · intro k _ hkj
    simp only [hkj,ite_false,Finset.sum_const_zero]
  · simp

def physicalStoppingPrefix (stop : Fin N → ℕ) (z : ℝ×ℝ) : ℕ → EuclideanSpace ℂ κ :=
  packetPrefix (fun k => ∑ q ∈ Finset.univ.filter (fun q : P.PacketIndex => stop q.1 = k),
    P.physicalMaskedValue alt hAlt t b v g T L A z q)

/-- One fixed original variation controls the stopping prefix at every
angular horizon, without a factor depending on that horizon. -/
theorem physicalStoppingPrefix_variation_le (stop : Fin N → ℕ)
    (hstop : Antitone stop) (y x : ℝ) (H : ℕ) :
    finiteCubicVariation (P.physicalStoppingPrefix alt hAlt t b v g T L A stop (x,y+t*x)) H ≤
      P.physicalMaskedVariation alt hAlt t b v g T L A y x ^ 3 := by
  have h := stopping_prefix_cubic_variation (Finset.univ : Finset P.PacketIndex)
    (fun q => q.1) stop hstop (P.physicalMaskedValue alt hAlt t b v g T L A (x,y+t*x)) H
  dsimp only at h
  simp_rw [P.physicalMaskedValue_length_sum alt hAlt t b v g T L A y x] at h
  rw [physicalMaskedVariation,cubicVariation_cube]
  exact h

/-- The clamping in the stopped path theorem preserves this bound. -/
theorem physicalStoppingPrefix_clamped_variation_le (stop : Fin N → ℕ)
    (hstop : Antitone stop) (y x : ℝ) (H : ℕ) :
    finiteCubicVariation (fun k =>
      P.physicalStoppingPrefix alt hAlt t b v g T L A stop (x,y+t*x) (min k H)) (2*H) ≤
        P.physicalMaskedVariation alt hAlt t b v g T L A y x ^ 3 := by
  apply (finiteCubicVariation_comp_le _ _ (fun k => min k H)
    (fun _ _ h => min_le_min h le_rfl) (min_le_left _ _)).trans
  exact P.physicalStoppingPrefix_variation_le alt hAlt t b v g T L A stop hstop y x (2*H)

theorem physicalStoppingPrefix_good_bound (stop : Fin N → ℕ)
    (hstop : Antitone stop) (y x : ℝ) (H : ℕ) {V : ℝ}
    (hV : P.physicalMaskedVariation alt hAlt t b v g T L A y x ≤ V) :
    finiteCubicVariation (fun k =>
      P.physicalStoppingPrefix alt hAlt t b v g T L A stop (x,y+t*x) (min k H)) (2*H) ≤ V^3 := by
  exact (P.physicalStoppingPrefix_clamped_variation_le alt hAlt t b v g T L A
    stop hstop y x H).trans (pow_le_pow_left₀ (cubicVariation_nonneg _ _) hV 3)

/-- The same original reference event bounds all greedy unary segments. -/
theorem physical_unary_runs_variation_le
    {unary : ℕ → Prop} {n : ℕ → ℝ} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish)
    (S : ∀ r : R.runs, UnarySegmentPartition n r.val.1 r.val.2)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (y x : ℝ)
    (level : ℕ → ℕ) (hlevel : StrictMono level) (H : ℕ) (hend : level finish ≤ H) :
    (∑ i : UnaryRunSegment R S,
      intervalOscillation (P.physicalStoppingPrefix alt hAlt t b v g T L A stop (x,y+t*x))
        H (level i.2.val.1) (level i.2.val.2)^3) ≤
      P.physicalMaskedVariation alt hAlt t b v g T L A y x ^ 3 := by
  have h := unary_runs_stopping_oscillation_cube_sum R S (Finset.univ : Finset P.PacketIndex)
    (fun q => q.1) stop hstop (P.physicalMaskedValue alt hAlt t b v g T L A (x,y+t*x))
    level hlevel H hend
  dsimp only at h
  simp_rw [P.physicalMaskedValue_length_sum alt hAlt t b v g T L A y x] at h
  rw [physicalMaskedVariation,cubicVariation_cube]
  exact h

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
