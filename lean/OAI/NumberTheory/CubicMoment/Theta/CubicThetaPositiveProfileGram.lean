import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveFourierMass

namespace OAI

/-! Exact finite-row Gram formula for compact Fourier sources, including
cutoffs below the injective cusp. The rows and every phase remain literal. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaFourierProfileTerm_point_continuous (h : Eisenstein)
    (r : CubicThetaBottomRow) (W : C_c(ℝ,ℂ)) :
    Continuous (fun p : CubicThetaPoint => cubicThetaFourierProfileTerm h r p.val W) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (cubicThetaFourierProfileTerm_continuousAt h r W p.property).comp
    continuous_subtype_val.continuousAt

lemma cubicThetaPositiveProfileGram_row_integrable (h k : Eisenstein)
    (W V : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0)
    (r : CubicThetaBottomRow) :
    Integrable (fun p => star (cubicThetaFourierStripSeed h W p)*
      cubicThetaFourierProfileTerm k r p.val V) cubicThetaPointMeasure :=
  cubicThetaFourierStripSeed_mul_integrable h W hε hW _
    (cubicThetaFourierProfileTerm_point_continuous k r V)

theorem cubicThetaPositiveProfileGram_unfold (h k : Eisenstein)
    (W V : C_c(ℝ,ℂ)) {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (hW : ∀ v≤ε,W v=0) (hV : ∀ v≤δ,V v=0) :
    inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW)
      (cubicThetaPositiveFourierProfileL2 k V hδ hV)=
      ∫ p,star (cubicThetaFourierStripSeed h W p)*
        cubicThetaFourierProfileSeries k p.val V ∂cubicThetaPointMeasure := by
  rw [cubicThetaPositiveFourierProfileL2,cubicThetaPositiveFourierProfileL2,
    cubicThetaSectionPairing_L2,cubicThetaPositiveFourierProfile_pairing_integral]
  rfl

theorem cubicThetaPositiveProfileGram_finite (h k : Eisenstein)
    (W V : C_c(ℝ,ℂ)) {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (hW : ∀ v≤ε,W v=0) (hV : ∀ v≤δ,V v=0) :
    ∃ S : Finset CubicThetaBottomRow,cubicThetaZeroRow∈S ∧
      inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW)
        (cubicThetaPositiveFourierProfileL2 k V hδ hV)=
        ∑ r∈S,∫ p,star (cubicThetaFourierStripSeed h W p)*
          cubicThetaFourierProfileTerm k r p.val V ∂cubicThetaPointMeasure := by
  classical
  obtain ⟨K,hK,hsub⟩ := cubicThetaFourierStripSeed_compact h W hε hW
  have hc : IsCompact (Subtype.val '' K) := hK.image continuous_subtype_val
  have hp : ∀ y∈Subtype.val '' K,0<y.2 := by
    rintro y ⟨p,_,rfl⟩
    exact p.property
  obtain ⟨S,hS⟩ := cubicThetaRows_compact_below hδ hc hp
  let T := insert cubicThetaZeroRow S
  have he (p : CubicThetaPoint) :
      star (cubicThetaFourierStripSeed h W p)*cubicThetaFourierProfileSeries k p.val V=
        ∑ r∈T,star (cubicThetaFourierStripSeed h W p)*cubicThetaFourierProfileTerm k r p.val V := by
    by_cases hz : cubicThetaFourierStripSeed h W p=0
    · simp [hz]
    · rw [←Finset.mul_sum]
      congr 1
      apply tsum_eq_sum
      intro r hr
      apply cubicThetaFourierProfileTerm_zero
      apply hV
      exact (hS p.val ⟨p,hsub hz,rfl⟩ r (fun hs => hr (Finset.mem_insert_of_mem hs))).le
  refine ⟨T,Finset.mem_insert_self _ _,?_⟩
  rw [cubicThetaPositiveProfileGram_unfold h k W V hε hδ hW hV]
  simp_rw [he]
  exact integral_finsetSum T (fun r _ => cubicThetaPositiveProfileGram_row_integrable h k W V hε hW r)

end CubicFirstMoment

end

end OAI
