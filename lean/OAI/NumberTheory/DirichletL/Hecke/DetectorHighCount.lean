import OAI.NumberTheory.DirichletL.Hecke.DetectorCountFromMoments
import OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountEndpoint

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeDetectorHighCount
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorRowCount

theorem high_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height : ℝ) (i : ℕ),
      1<U → 5/6≤2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type*} (F : Fiber M H Label Slot U a ε (3/2) T allowance i),
      Moments F Δ c κ C height εm →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*U^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hamp⟩ := HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hamp] with U hamp
  intro a ε T allowance Δ C height i hU ha ha' hε hεsmall hC hh hf Label Slot F moments
  have hgeom := F.lengths hU
  have hr0 : 0≤F.r := by linarith [hgeom.2.2.2.1]
  have hr2 : F.r≤2 := by linarith [hgeom.2.1]
  obtain ⟨hconst,_,_,hconstI⟩ := fiberConstant_bounds C height K₀ hC hh hK
  have hi := hamp F.rows F.family a ε (3/2) T allowance i hU (by linarith)
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff moments.inverse_raw
  have hb : (F.rows.card : ℝ)≤fiberConstant C height K₀*
      U^(max 1 ((1+5*F.r)/6)-(2*a-1)*F.r+(2*ε+εm)) := by
    apply hi.trans
    convert mul_le_mul_of_nonneg_right hconstI
      (Real.rpow_nonneg (zero_lt_one.trans hU).le
        (max 1 ((1+5*F.r)/6)-(2*a-1)*F.r+2*ε+εm)) using 1 <;> congr 2; ring
  have hout := high_bin_count hconst hU.le ha (show 2*a-1≤1 by linarith)
    (show 0≤76*ε by positivity) (show 1-76*ε≤F.r by linarith [hgeom.2.2.2.1]) hb
  convert hout using 1; congr 2; ring

end SevenEighths.HeckeDetectorHighCount

end

end OAI
