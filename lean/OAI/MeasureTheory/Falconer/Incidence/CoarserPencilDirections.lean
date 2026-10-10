import OAI.MeasureTheory.Falconer.Incidence.GoodPencilDirections

namespace OAI

/-! Good projected directions for a packet eight times wider than its
coarse grid cells, at the actual normalized fine-point resolution. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem good_pencil_projection_directions_coarser (N : ℕ) {s t K KP : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hKP : 1 ≤ KP)
    (p : Space 2) (hp : |p 0| ≤ 1) (T : Finset (Space 2)) (hT : T.Nonempty)
    (hsep : FiniteSeparatedAt (1/(2:ℝ)^(N+3)) T) (hchart : InBoundedLineChart T)
    (hinc : ∀ l ∈ T, TubeIncident (1/(2:ℝ)^(N+3)) p l)
    (hreg : NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) s K T)
    (P : Finset (Space 2)) (hP : P.Nonempty) (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t KP P) :
    ∃ U ⊆ T, U.Nonempty ∧ (T.card:ℝ) ≤ 50*(U.card:ℝ) ∧
      FiniteSeparatedAt (1/(2:ℝ)^(N+3)) U ∧ InBoundedLineChart U ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) s (50*K) U ∧
      ∀ l ∈ U, planarProjectionEnergy N s (-l 0) P ≤
        2*projectionEnergyBudget N s t (25*K*(4:ℝ)^s) KP*(P.card:ℝ)^2 := by
  let I := T.image (fun l => l 0)
  let D := I.image Neg.neg
  have hδ : 0 < 1/(2:ℝ)^(N+3) := by positivity
  have hKI : 1 ≤ 25*K*(4:ℝ)^s := by
    have h4 : (1:ℝ) ≤ (4:ℝ)^s := Real.one_le_rpow (by norm_num) hs
    have hm := mul_le_mul hK h4 (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)
    nlinarith only [hm]
  have hscale : 1/(2:ℝ)^(N+3) ≤ 1/(2:ℝ)^N := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hDcard : D.card = I.card := Finset.card_image_of_injective _ neg_injective
  have hDbound : ∀ c ∈ D, |c| ≤ 1 := by
    intro c hc
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp ha
    simpa only [abs_neg] using (hchart l hl).1
  have hDball : ∀ u r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      scalarBallMass D u r ≤ (25*K*(4:ℝ)^s)*r^s*(D.card:ℝ) := by
    intro u r hr hr1
    change scalarBallMass (I.image Neg.neg) u r ≤ _
    rw [scalarBallMass_neg,hDcard]
    exact pencil_slope_regular hδ hs hK p hp T hsep hchart hinc hreg (-u) r (hscale.trans hr) hr1
  obtain ⟨J,hJD,hhalf,henergy⟩ := good_projection_directions N hs hst hKI hKP
    D P hP hDbound hPchart hDball hPball
  let U := T.filter (fun l => -l 0 ∈ J)
  have hUT : U ⊆ T := Finset.filter_subset _ _
  have hJU : J ⊆ U.image (fun l => -l 0) := by
    intro c hc
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (hJD hc)
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨hl,hc⟩,rfl⟩
  have hJUcard : (J.card:ℝ) ≤ (U.card:ℝ) :=
    Nat.cast_le.mpr ((Finset.card_le_card hJU).trans Finset.card_image_le)
  have hTcard := pencil_slope_card hδ p T hsep hchart hinc
  have hloss : (T.card:ℝ) ≤ 50*(U.card:ℝ) := by
    change (T.card:ℝ) ≤ 25*(I.card:ℝ) at hTcard
    rw [hDcard] at hhalf
    linarith only [hhalf,hTcard,hJUcard]
  have hUne : U.Nonempty := by
    have htpos : 0 < (T.card:ℝ) := Nat.cast_pos.mpr hT.card_pos
    apply Finset.card_pos.mp
    exact Nat.cast_pos.mp (show 0 < (U.card:ℝ) by linarith only [htpos,hloss])
  refine ⟨U,hUT,hUne,hloss,finiteSeparatedAt_subset hUT hsep,
    (fun l hl => hchart l (hUT hl)),?_,?_⟩
  · simpa only [mul_comm K 50] using normalized_finite_ball_bound_subset hδ.le
      (zero_le_one.trans hK) hUT hloss hreg
  · intro l hl
    exact henergy (-l 0) (Finset.mem_filter.mp hl).2


end Falconer

end OAI
