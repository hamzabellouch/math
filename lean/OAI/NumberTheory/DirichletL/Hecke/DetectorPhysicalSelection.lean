import OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalBins
import OAI.NumberTheory.DirichletL.Hecke.DetectorRelativePrime

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorPhysicalSelection
open HeckeFamily HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)

def physical {Row Slot : Type*} (row : Row→O) (W : Slot→ℝ→ℂ)
    (b w : Slot→ℝ) (z : Slot→ℂ) (U : ℝ) (u : Row) (s : Slot) : ℂ :=
  HeckePrimeRow.canonicalPrimeAmplitude M H (row u) (W s) (b s) (U^(w s)) (z s)

def weightedMean {Slot : Type*} (slots : Finset Slot) (w g : Slot→ℝ) : ℝ :=
  (∑ s∈slots,w s*g s)/(∑ s∈slots,w s)

theorem weightedMean_bounds {Slot : Type*} (slots : Finset Slot) (w g : Slot→ℝ)
    (δ : ℝ) (hw : ∀ s∈slots,0≤w s) (hL : 0<∑ s∈slots,w s)
    (hg : ∀ s∈slots,0≤g s ∧ g s≤δ/2) :
    0≤weightedMean slots w g ∧ weightedMean slots w g≤δ/2 := by
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun s hs => mul_nonneg (hw s hs) (hg s hs).1)) hL.le
  · apply (div_le_iff₀ hL).mpr
    calc
      _ ≤ ∑ s∈slots,w s*(δ/2) := Finset.sum_le_sum (fun s hs =>
        mul_le_mul_of_nonneg_left (hg s hs).2 (hw s hs))
      _ = _ := by rw [←Finset.sum_mul]; ring

omit [NeZero M] in
theorem select_physical_product {Row Slot : Type*} (rows : Finset Row) (hne : rows.Nonempty)
    (slots : Finset Slot) (row : Row→O) (W : Slot→ℝ→ℂ) (b w g : Slot→ℝ)
    (zs : Slot→ℂ) (U δ mesh binWidth z : ℝ)
    (hU : 1<U) (hδ : 0≤δ) (hmesh : 0≤mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<w s) (hwm : ∀ s∈slots,w s≤mesh)
    (hL : 0<∑ s∈slots,w s) (hz : 0≤z) (hzL : z≤∑ s∈slots,w s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      amplitude (U^(w s)) (δ/2) binWidth (physical M H row W b w zs U u s)=g s) :
    ∃ selected : Finset Slot, selected⊆slots ∧ (∀ s∈selected,0<g s) ∧
      (∑ s∈selected,w s)≤z ∧
      ∀ u∈rows, U^(2*weightedMean slots w g*z-δ*mesh)≤
        ‖∏ s∈selected,physical M H row W b w zs U u s‖^2 := by
  obtain ⟨u0,hu0⟩ := hne
  have hg (s : Slot) (hs : s∈slots) : 0≤g s ∧ g s≤δ/2 := by
    rw [←hbins u0 hu0 s hs]
    exact amplitude_bounds _ _ _ _ (by positivity)
  obtain ⟨hq,hqδ⟩ := weightedMean_bounds slots w g δ (fun s hs => (hw s hs).le) hL hg
  have hm : weightedMean slots w g*(∑ s∈slots,w s)≤∑ s∈slots,w s*g s := by
    unfold weightedMean
    rw [div_mul_cancel₀ _ hL.ne']
  obtain ⟨selected,hsub,hpositive,hlen,hspike⟩ := common_bin_selection slots w g U δ mesh binWidth
    (weightedMean slots w g) z hU hδ hmesh hbin hw hwm hg hq hqδ hz hzL hm
  exact ⟨selected,hsub,hpositive,hlen,fun u hu => hspike _ (hbins u hu)⟩

end SevenEighths.HeckeDetectorPhysicalSelection

end

end OAI
