import OAI.Analysis.LipschitzHilbert.Phase.SourceAngularEnvelope
import OAI.Analysis.LipschitzHilbert.Trees.SourceLengthRestriction

namespace OAI

/-! Original length restrictions and the common top mask in the actual
source analytic amplitude. Small masks retain their full gain when the
single-top bounds are summed over an eligible angular node. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

variable {ι X : Type*}

theorem sourcePacketAmplitude_smul_value {σ E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (top : σ → ι) (stop : σ → ℕ) (value : σ → E)
    (phase : ℕ → ℂ) (a : ℝ) (z : X) (level : ℕ) (cell : ℤ) (q : ℂ) :
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets top stop
      (fun p => q • value p) phase a z level cell =
      q • g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets top stop
        value phase a z level cell := by
  unfold sourcePacketAmplitude packetAmplitude sourcePacketBase
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [smul_smul]
  congr 1
  ring

/-- The bound uses the original analyzing coefficients and their interval
concentration, even after any interval of original lengths is retained. -/
theorem sourcePacketAmplitude_masked_restricted_envelope
    (grid : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i z, 0 < weight i z)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (M : ℕ) (top : ι) (htop : top ∈ tops)
    (he : grid.eligible cutoff (precision top) M) (z : X)
    (a Z : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hZ : 0 ≤ Z)
    (hz0 : ∀ j < M, 0 ≤ (phase j).re) (hz : ∀ j < M, ‖phase j‖ ≤ Z)
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (jet : Fin 3) (stop : Fin N → ℕ) (hstop : Antitone stop)
    (start : ℕ) (hstart : start ≤ M) (hmax : ∀ j, stop j ≤ M)
    (x y B C : ℝ) (hB : 0 ≤ B) (hC : 1 ≤ C) (hweight : weight top z ≤ C)
    (hinterval : ∀ l u, l ≤ u → u ≤ N →
      ‖P.rawInterval coeff jet l u x y‖ ≤ B*(weight top z)^8)
    (lower upper : ℕ) (q : ℂ) :
    ‖grid.sourcePacketAmplitude tops slope precision cutoff weight K gap Finset.univ
      (fun _ : Fin N => top) stop
      (fun j => q • P.rawBand (P.restrictCoefficient coeff lower upper) jet j x y)
      phase a z start (grid.index start (slope top))‖ ≤
      (C^8*B*(1+(a+Z*K)*(Real.log (max 1 (∑ i ∈ tops, weight i z))+1))) *
        ‖q‖*(weight top z)^4 := by
  rw [grid.sourcePacketAmplitude_smul_value, norm_smul]
  have hb := grid.sourcePacketAmplitude_fourth_envelope tops slope precision cutoff weight
    hp hw hK gap phase M top htop he z a Z ha0 ha1 hZ hz0 hz P
    (P.restrictCoefficient coeff lower upper) jet stop hstop start hstart hmax x y B C
    hB hC hweight (P.restricted_rawInterval_bound coeff lower upper jet x y
      (B*(weight top z)^8) hinterval)
  calc
    _ ≤ ‖q‖*((C^8*B*(1+(a+Z*K)*
        (Real.log (max 1 (∑ i ∈ tops, weight i z))+1)))*(weight top z)^4) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg q)
    _ = _ := by ring

/-- In particular the exponential smallness of every insignificant top
mask survives the sum, with no loss proportional to the number of tops. -/
theorem node_masked_amplitude_envelope {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (grid : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (amplitude : ι → E) (q : ι → ℂ) (level : ℕ) (cell : ℤ) (z : X)
    (A C ε : ℝ) (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hw : ∀ i ∈ grid.cellTops tops slope precision cutoff level cell, 0 ≤ weight i z)
    (hC : ∀ i ∈ grid.cellTops tops slope precision cutoff level cell, weight i z ≤ C)
    (hq : ∀ i ∈ grid.cellTops tops slope precision cutoff level cell, ‖q i‖ ≤ ε)
    (hamp : ∀ i ∈ grid.cellTops tops slope precision cutoff level cell,
      ‖amplitude i‖ ≤ A*(weight i z)^4) :
    ‖∑ i ∈ grid.cellTops tops slope precision cutoff level cell, q i • amplitude i‖ ≤
      (A*C^3)*ε*grid.mass tops slope precision cutoff weight level cell z := by
  have hb := grid.node_amplitude_fourth_envelope tops slope precision cutoff weight
    (fun i => q i • amplitude i) level cell z (ε*A) C (mul_nonneg hε hA) hw hC
    (fun i hi => by
      rw [norm_smul]
      calc
        ‖q i‖*‖amplitude i‖ ≤ ε*(A*(weight i z)^4) :=
          mul_le_mul (hq i hi) (hamp i hi) (norm_nonneg _) hε
        _ = (ε*A)*(weight i z)^4 := by ring)
  convert hb using 1; ring

end LipschitzHilbert.AngularGrid

end

end OAI
