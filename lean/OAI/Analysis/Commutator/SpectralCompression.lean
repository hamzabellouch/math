import Mathlib
import OAI.Analysis.Commutator.SmoothingSubsequence
import OAI.Analysis.Commutator.SpectralThresholdBounds

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma threshold_factor {B : H →L[ℂ] H} (hB : 0≤B) {r : ℝ} (hr : 0<r) :
    ∃ C : H →L[ℂ] H,C*B=threshold B r ∧ B*star C=threshold B r := by
  let E := threshold B r
  let D := B+r • (1-E)
  let U : (H →L[ℂ] H)ˣ := (threshold_completion_unit hB hr).unit
  have hu : (U:H →L[ℂ] H)=D := IsUnit.unit_spec _
  let C := (↑U⁻¹:H →L[ℂ] H)*E
  have hp : E*E=E := (threshold_projection B r).isIdempotentElem.eq
  have he : D*E=B*E := by
    dsimp only [D]
    rw [add_mul,smul_mul_assoc,sub_mul,one_mul,hp,sub_self,smul_zero,add_zero]
  have hc : C*B=E := by
    dsimp only [C]
    rw [mul_assoc,(threshold_commute (IsSelfAdjoint.of_nonneg hB) r).eq,←he,←hu,←mul_assoc,Units.inv_mul,one_mul]
  refine ⟨C,hc,?_⟩
  have hh := congrArg star hc
  simpa only [star_mul,(IsSelfAdjoint.of_nonneg hB).star_eq,
    (show star E=E from (threshold_projection B r).isSelfAdjoint.star_eq)] using hh

lemma threshold_compression_tendsto {B : H →L[ℂ] H} (hB : 0≤B) {r : ℝ} (hr : 0<r)
    (A : ℕ → H →L[ℂ] H)
    (ht : Tendsto (fun n => B*A n*B) atTop (𝓝 0)) :
    Tendsto (fun n => threshold B r*A n*threshold B r) atTop (𝓝 0) := by
  obtain ⟨C,hCB,hBC⟩ := threshold_factor hB hr
  have he (n : ℕ) : threshold B r*A n*threshold B r=C*(B*A n*B)*star C := by
    nth_rw 1 [←hCB]
    nth_rw 1 [←hBC]
    simp only [mul_assoc]
  simp_rw [he]
  simpa only [mul_zero,zero_mul] using (tendsto_const_nhds (x:=C)).mul ht |>.mul (tendsto_const_nhds (x:=star C))

lemma positive_compression_bound {A E : H →L[ℂ] H} (hA : 0≤A) (hA1 : A≤1)
    (hE : IsStarProjection E) : A≤(2:ℝ) • (E*A*E)+(2:ℝ) • (1-E) := by
  let Q := 1-E
  have hQ : IsStarProjection Q := hE.one_sub
  have hsa : IsSelfAdjoint (E-Q) := hE.isSelfAdjoint.sub hQ.isSelfAdjoint
  have hp : 0≤(E-Q)*A*(E-Q) := sandwich_nonneg hA hsa
  have hs : A≤(2:ℝ) • (E*A*E)+(2:ℝ) • (Q*A*Q) := by
    apply sub_nonneg.mp
    convert hp using 1
    dsimp only [Q]
    simp only [two_smul ℝ]
    noncomm_ring
  have hle : Q*A*Q≤Q := by
    have hh := hQ.isSelfAdjoint.conjugate_le_conjugate hA1
    simpa only [mul_one,hQ.isIdempotentElem.eq] using hh
  have htwo : (2:ℝ) • (Q*A*Q)≤(2:ℝ) • Q := by
    simpa only [two_smul ℝ] using add_le_add hle hle
  exact hs.trans (add_le_add le_rfl htwo)

end Kadison.PositiveWOT

end

end
end

end OAI
