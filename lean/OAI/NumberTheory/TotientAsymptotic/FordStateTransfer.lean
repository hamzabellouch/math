import OAI.NumberTheory.TotientAsymptotic.FordBandMass
import OAI.NumberTheory.TotientAsymptotic.BandStateMass

namespace OAI

/-! A full reciprocal-mass transfer step for the actual Ford tuple family. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma ford_state_fiber_bands_eq {b k : ℕ} (hk : k ≤ b) (T : Finset (ShiftedPair b))
    (Y : ℕ → ℝ) (hUV : Y k ≤ Y (k-1)) (s : ShiftedPair b) :
    (((T.image (fun t => fordFactorState t (Y (k-1)))).filter (fun q => lowerState q (Y k)=s)).image
      (fun q => stateBand hk q (Y k) (Y (k-1))))=
    (T.filter (fun t => fordFactorState t (Y k)=s)).image (fun t => fordBand hk t Y) := by
  classical
  have hb (t : ShiftedPair b) : stateBand hk (fordFactorState t (Y (k-1))) (Y k) (Y (k-1))=
      fordBand hk t Y := stateBand_fordFactorState hk t le_rfl
  ext f
  constructor
  · intro hf
    obtain ⟨q,hq,he⟩ := Finset.mem_image.mp hf
    obtain ⟨hq,hqs⟩ := Finset.mem_filter.mp hq
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
    rw [lower_fordFactorState t hUV] at hqs
    exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,hqs⟩,(hb t).symm.trans he⟩
  · intro hf
    obtain ⟨t,ht,he⟩ := Finset.mem_image.mp hf
    obtain ⟨ht,hts⟩ := Finset.mem_filter.mp ht
    refine Finset.mem_image.mpr ⟨fordFactorState t (Y (k-1)),?_,(hb t).trans he⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨t,ht,rfl⟩,by rwa [lower_fordFactorState t hUV]⟩

lemma ford_lower_states {b : ℕ} (T : Finset (ShiftedPair b)) {U V : ℝ} (hUV : U ≤ V) :
    (T.image (fun t => fordFactorState t V)).image (fun q => lowerState q U)=
      T.image (fun t => fordFactorState t U) := by
  classical
  rw [Finset.image_image]
  congr 1
  funext t
  exact lower_fordFactorState t hUV

theorem ford_state_mass_transfer : ∃ C D₀ : ℝ,0 < C ∧ 0 < D₀ ∧
    ∀ (b k D r : ℕ) (_hk : k ≤ b) (i : Fin k),i.val+1=k →
    ∀ (y S : ℝ) (Y U : ℕ → ℝ),Real.exp 2 ≤ y → 1 ≤ B y →
    FordComparisonParameters b y S D r Y U →
    2 ≤ Y k → 1 < U (k-1) → D₀ ≤ Real.sqrt (B S*B y) →
    ∀ T : Finset (ShiftedPair b),
    (∀ t ∈ T,FordComparisonConditions b y S D r Y U t) →
    (∑ q ∈ T.image (fun t => fordFactorState t (Y (k-1))),(factorProduct q:ℝ)⁻¹) ≤
    ((C*(k:ℝ)^2*(B y)^2/(Real.log (U (k-1)))^2)*
      Real.exp (fordBandCap k y S Y*(Real.log k+1)))*
    (∑ q ∈ T.image (fun t => fordFactorState t (Y k)),(factorProduct q:ℝ)⁻¹) := by
  classical
  obtain ⟨C,D₀,hC,hD₀,hbound⟩ := ford_band_fiber_mass
  refine ⟨C,D₀,hC,hD₀,?_⟩
  intro b k D r hk i hi y S Y U hy hBy hp hYk hUi hD T hT
  have hUV := ford_cutoff_antitone hp (Nat.sub_le k 1) hk
  let Q := T.image (fun t => fordFactorState t (Y (k-1)))
  have htrunc : ∀ q ∈ Q,∀ j,partBelow (q.left j) (Y (k-1))=q.left j ∧
      partBelow (q.right j) (Y (k-1))=q.right j := by
    intro q hq j
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
    exact ⟨partBelow_nested _ le_rfl,partBelow_nested _ le_rfl⟩
  have htail : ∀ q ∈ Q,∀ j : Fin b,k ≤ j.val →
      partBetween (q.left j) (Y k) (Y (k-1))=1 ∧
      partBetween (q.right j) (Y k) (Y (k-1))=1 := by
    intro q hq j hj
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
    have hh := ford_band_tail hp (hT t ht) j hj
    exact ⟨(partBetween_below _ le_rfl).trans hh.1,(partBetween_below _ le_rfl).trans hh.2⟩
  have hmass := band_state_mass_transfer hk hUV Q htrunc htail (A:=
    (C*(k:ℝ)^2*(B y)^2/(Real.log (U (k-1)))^2)*
      Real.exp (fordBandCap k y S Y*(Real.log k+1))) (by
    intro s hs
    dsimp only [Q] at hs ⊢
    rw [ford_state_fiber_bands_eq hk T Y hUV s]
    have hs' : s ∈ T.image (fun t => fordFactorState t (Y k)) := by
      rwa [ford_lower_states T hUV] at hs
    exact hbound b k D r hk i hi y S Y U hy hBy hp hYk hUi hD T hT s hs')
  simpa only [Q,ford_lower_states T hUV] using hmass

end TotientAsymptotic

end

end OAI
