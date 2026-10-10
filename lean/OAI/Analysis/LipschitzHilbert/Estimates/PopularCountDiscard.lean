import OAI.Analysis.LipschitzHilbert.Estimates.CountThreshold

namespace OAI

/-! The count cutoff used in concentration has the requested relative
area cost, from the actual popular witnesses and Lacey--Li input. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert

theorem popular_top_count_discard (hLL : LaceyLiInput) (a k d s H : ℝ)
    (ha : 0 ≤ a) (hd : 4 ≤ d) (hs : 0 ≤ s) (hH : 0 ≤ H) :
    ∃ Cn L0 : ℝ, 0 < Cn ∧ 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (ι : Type*) [Fintype ι] (T : ι → SlopeBox) (l r : ℝ),
      (∀ i, |(T i).slope| ≤ 1) → ∀ (u : Plane → ℝ) (K : ℝ≥0),
      LipschitzWith K u → 300*((2*K:ℝ≥0):ℝ)*(r-l) ≤ 1 →
      ∀ E : ι → Set (ℝ × ℝ), (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ (T i).radius z ≤ L^a) →
      (∀ i z, z ∈ E i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal (L^(-a)*(T i).length*(T i).width) ≤
        (volume.prod volume) (E i)) →
      ∀ (N : ℝ) (F : Set (ℝ × ℝ)), 0 < N →
      (∀ z ∈ F, z.1 ∈ Icc l r) →
      (∑ i, (T i).area) ≤ L^s*N^2*(volume.prod volume).real F →
      (volume.prod volume) (F ∩ {z | N*L^Cn < ∑ i, (T i).weight (L^k) d z}) ≤
        ENNReal.ofReal (L^(-H)*(volume.prod volume).real F) := by
  obtain ⟨C,hC,hcount⟩ := popular_top_count_powers hLL a k d ha hd
  let A := a+3*max k a
  let Cn := A+(s+H)/2+1
  have hA : 0 ≤ A := by dsimp [A]; nlinarith [le_max_right k a]
  have hCn : 0 < Cn := by dsimp [Cn]; positivity
  refine ⟨Cn,max 1 C,hCn,le_max_left _ _,?_⟩
  intro L hL ι _ T l r hslopes u K hu hlength E hE hdisj hinside hclose hsize N F hN hFstrip hS
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hCL : C ≤ L := (le_max_right _ _).trans hL
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have htail := hcount L hL1 ι T l r hslopes u K hu hlength E hE hdisj hinside hclose hsize
    (N*L^Cn) (mul_pos hN (Real.rpow_pos_of_pos hLpos _))
  apply (measure_mono (show F ∩ {z | N*L^Cn < ∑ i, (T i).weight (L^k) d z} ⊆
      {z | z.1 ∈ Icc l r} ∩ {z | N*L^Cn < ∑ i, (T i).weight (L^k) d z} from
    fun z hz => ⟨hFstrip z hz.1,hz.2⟩)).trans
  apply htail.trans
  exact ENNReal.ofReal_le_ofReal (weak_two_polynomial_threshold C L A s H N
    ((volume.prod volume).real F) (∑ i, (T i).area) hC.le hL1 hCL hN measureReal_nonneg
      (Finset.sum_nonneg fun i _ => (T i).area_pos.le) hS)

end LipschitzHilbert

end

end OAI
