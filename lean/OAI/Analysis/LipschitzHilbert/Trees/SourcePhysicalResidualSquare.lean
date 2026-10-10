import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledCrossIdentity

namespace OAI

/-! The original masked physical residual blocks inherit the square
bound from the original analyzing/alternate-synthesis decomposition. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

/-- Actual top masks and original physical packets satisfy the marked
residual square estimate; the analyzing coefficient is unchanged. -/
theorem physical_masked_packet_residual_square_polynomial {τ : Type*}
    (horder : 6 ≤ P.order) (t a : ℝ)
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
    (stop : Fin N → ℕ) (T : τ → SlopeBox) (L A : ℝ)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (he : ∀ q ∈ packets, grid.eligible cutoff (precision (assigned q)) (stop q.1))
    (C : ℝ) (hC : 0 ≤ C) (hmask : ∀ top ∈ tops, weight top z^(-alpha)*‖((T top).mask L A z:ℂ)‖ ≤ C)
    (level : ℕ → ℕ) (hlevel : StrictMono level) (count : ℕ) (pathSlope : ℝ)
    (R : ℝ) (hR : 0 ≤ R)
    (hcard : ∀ j < count,
      ((residualLengthSet stop (level j) (level (j+1))).card:ℝ) ≤ R)
    (c q p r : ℝ) (hL : 6 ≤ L) (hr : 0 ≤ r)
    (hCb : C ≤ L^c) (hAb : P.absoluteConstant ≤ L^q) (hRb : R ≤ L^r)
    (hError : P.physicalAngularError t a b v f z ≤ L^p)
    (hMain : P.physicalMainSquare t a b v f (z.2-t*z.1) z.1 ≤ L^p) :
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
    (∑ j : Fin count, ‖grid.packetResidual packets (fun q => slope (assigned q))
      (fun q => stop q.1)
      (grid.sourcePacketBase tops slope precision cutoff weight assigned (fun q => stop q.1)
        value alpha z)
      (grid.sourceTransition tops slope precision cutoff weight K gap phase z)
      (level j.val) (level (j.val+1)) (grid.index (level j.val) pathSlope)‖^2) ≤
        (L^(c+q+p+r+1))^2 := by
  let mask := fun top => ((T top).mask L A z:ℂ)
  have hvalue : P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z =
      fun q => mask (assigned q) • P.physicalCrossPacketValue alt hAlt t b v f 0 z q := by
    funext q
    rcases q with ⟨j,⟨l,u⟩⟩
    have hpoint : (z.1,z.2-t*z.1+t*z.1) = z := by
      apply Prod.ext
      · rfl
      · dsimp
        ring
    have h := P.physicalMaskedValue_eq_cross alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A (z.2-t*z.1) z.1 ⟨j,⟨l,u⟩⟩
    rw [hpoint] at h
    rw [h]
    ext k
    simp only [mask,PiLp.smul_apply,Complex.real_smul,smul_eq_mul]
  dsimp only
  rw [hvalue]
  exact P.physical_cross_packet_residual_square_polynomial alt hAlt horder 0 t a
    b hb hb1 v hv f hf hf1 grid tops slope precision cutoff weight hp hw hK gap phase hz
    alpha ha z packets assigned stop mask hassigned he C hC hmask level hlevel count
    pathSlope R hR hcard L c q p r hL hr hCb hAb hRb hError hMain

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
