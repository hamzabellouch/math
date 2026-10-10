import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualPolynomial
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledMainTail

namespace OAI

/-! On the actual good-reference event, the residual-square expression
has a single fixed polynomial bound. The error and main quantities are
the original physical packet sums, not abstract envelope assumptions. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physical_residual_expression_polynomial (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y x : ℝ)
    {L C R c q p r : ℝ} (hL : 6 ≤ L) (hC : 0 ≤ C) (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hCb : C ≤ L^c) (hAb : P.absoluteConstant ≤ L^q)
    (hError : P.physicalAngularError t a b v g (x,y+t*x) ≤ L^p)
    (hMain : P.physicalMainSquare t a b v g y x ≤ L^p) (hRb : R ≤ L^r) :
    3*C^2*((∑ k, P.absoluteConstant*P.physicalErrorScale t a b v g k y x)^2+
      R*∑ k, (P.absoluteConstant*P.physicalMainScale t a b v g k y x)^2) ≤
        (L^(c+q+p+r+1))^2 := by
  let E := P.physicalAngularError t a b v g (x,y+t*x)
  let S := P.physicalMainSquare t a b v g y x
  have hE : 0 ≤ E := by
    change 0 ≤ P.physicalAngularError t a b v g (x,y+t*x)
    rw [← P.sum_physicalErrorScale t a b v g y x]
    exact Finset.sum_nonneg (fun k _ => P.physicalErrorScale_nonneg t a b v g k y x)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hsumE : (∑ k, P.absoluteConstant*P.physicalErrorScale t a b v g k y x) =
      P.absoluteConstant*E := by
    rw [← Finset.mul_sum,P.sum_physicalErrorScale]
  have hsumS : (∑ k, (P.absoluteConstant*P.physicalMainScale t a b v g k y x)^2) =
      P.absoluteConstant^2*S^2 := by
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    congr 1
    exact (Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg
      (P.physicalMainScale t a b v g k y x)))).symm
  rw [hsumE,hsumS]
  calc
    _ = 3*C^2*P.absoluteConstant^2*(E^2+R*S^2) := by ring
    _ ≤ _ := residual_square_polynomial_bound hL hC P.absoluteConstant_pos.le hE hS hR hr
      hCb hAb hError hMain hRb

theorem physical_packet_residual_square_polynomial {τ : Type*}
    (horder : 6 ≤ P.order) (i : Fin 3) (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (hf : Measurable f) (hf1 : ∀ z, ‖f z‖ ≤ 1)
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → ℝ×ℝ → ℝ)
    (hp : ∀ T ∈ tops, 0 ≤ precision T) (hw : ∀ T z, 0 < weight T z)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (hz : ∀ k, 0 ≤ (phase k).re) (alpha : ℝ) (ha : 0 ≤ alpha) (z : ℝ×ℝ)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (stop : Fin N → ℕ) (mask : τ → ℂ)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (he : ∀ q ∈ packets, grid.eligible cutoff (precision (assigned q)) (stop q.1))
    (C : ℝ) (hC : 0 ≤ C) (hmask : ∀ T ∈ tops, weight T z^(-alpha)*‖mask T‖ ≤ C)
    (level : ℕ → ℕ) (hlevel : StrictMono level) (count : ℕ) (pathSlope : ℝ)
    (R : ℝ) (hR : 0 ≤ R)
    (hcard : ∀ j < count,
      ((residualLengthSet stop (level j) (level (j+1))).card:ℝ) ≤ R)
    (L c q p r : ℝ) (hL : 6 ≤ L) (hr : 0 ≤ r)
    (hCb : C ≤ L^c) (hAb : P.absoluteConstant ≤ L^q) (hRb : R ≤ L^r)
    (hError : P.physicalAngularError t a b v f z ≤ L^p)
    (hMain : P.physicalMainSquare t a b v f (z.2-t*z.1) z.1 ≤ L^p) :
    let value := P.physicalPacketValue t b v f i z
    (∑ j : Fin count, ‖grid.packetResidual packets (fun q => slope (assigned q))
      (fun q => stop q.1)
      (grid.sourcePacketBase tops slope precision cutoff weight assigned (fun q => stop q.1)
        (fun q => mask (assigned q) • value q) alpha z)
      (grid.sourceTransition tops slope precision cutoff weight K gap phase z)
      (level j.val) (level (j.val+1)) (grid.index (level j.val) pathSlope)‖^2) ≤
        (L^(c+q+p+r+1))^2 := by
  dsimp only
  have h := P.physical_packet_residual_square_sum horder i t a b hb hb1 v hv f hf hf1
    grid tops slope precision cutoff weight hp hw hK gap phase hz alpha ha z packets assigned
    stop mask hassigned he C hC hmask level hlevel count pathSlope R hR hcard
  apply h.trans
  have hpoint : (z.1,z.2-t*z.1+t*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  exact P.physical_residual_expression_polynomial t a b v f (z.2-t*z.1) z.1
    hL hC hR hr hCb hAb (by simpa only [hpoint] using hError) hMain hRb

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
