import OAI.Analysis.LipschitzHilbert.Trees.SourceBoxSupremumEnergy
import OAI.Analysis.LipschitzHilbert.Trees.SourcePlanarPolynomial
import OAI.Analysis.LipschitzHilbert.Trees.SourceCellPolynomial

namespace OAI

/-! Polynomially weighted suprema on transverse tree cells. The bound
comes from coordinate Fourier support and the strong maximal estimate. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators FourierTransform ENNReal
namespace LipschitzHilbert

/-- A pointwise weighted comparison passes to the actual packet supremum. -/
theorem packetNormSup_weighted_le {X E ι : Type*} [NormedAddCommGroup E]
    (F G : ι → X → E) (Q : Set X) (c d B : ℝ)
    (hc : 0<c) (hd : 0≤d) (hB : 0≤B)
    (hG : ∀ a x, x∈Q → ‖G a x‖≤B)
    (hFG : ∀ a x, x∈Q → c*‖F a x‖≤d*‖G a x‖) :
    c*packetNormSup F Q≤d*packetNormSup G Q := by
  have hGb := packetNormValues_bddAbove G Q B hB hG
  have hG0 := packetNormSup_nonneg G Q B hB hG
  have hs : packetNormSup F Q≤d*packetNormSup G Q/c := by
    apply packetNormSup_le F Q _ (div_nonneg (mul_nonneg hd hG0) hc.le)
    intro a x hx
    apply (le_div_iff₀ hc).mpr
    have hv : ‖G a x‖≤packetNormSup G Q :=
      le_csSup hGb (Or.inr ⟨a,x,hx,rfl⟩)
    simpa only [mul_comm c] using (hFG a x hx).trans (mul_le_mul_of_nonneg_left hv hd)
  simpa only [mul_comm c] using (le_div_iff₀ hc).mp hs

variable {J ι κ : Type*} [Fintype κ]

/-- The polynomial power on each transverse cell is paid for by the
energy of the polynomially localized packet family, uniformly in the
number of cells and packets. -/
theorem finite_weighted_box_supremum_energy
    (s : Finset J) (Kx Ky : SchwartzMap ℝ ℂ)
    (F : J → ι → SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ))
    (q : ℕ) (b W Rx Ry : ℝ) (hW : 0<W) (cx rx n : J → ℝ)
    (hrx : ∀ j∈s, 0<rx j)
    (hKx : ∀ ξ, |ξ|≤Rx → 𝓕 Kx ξ=1) (hKy : ∀ η, |η|≤Ry → 𝓕 Ky η=1)
    (hFx : ∀ j∈s, ∀ a y ξ, 𝓕 (vectorHorizontalSlice (F j a) y) ξ≠0 → |ξ|≤Rx/rx j)
    (hFy : ∀ j∈s, ∀ a x η, 𝓕 (vectorVerticalSlice (F j a) x) η≠0 → |η|≤Ry/(W/2))
    (A : J → Set (ℝ×ℝ)) (hA : ∀ j∈s, MeasurableSet (A j))
    (hAfin : ∀ j∈s, (volume.prod volume) (A j)≠∞)
    (hsub : ∀ j∈s, A j⊆coordinateBox (cx j) (b+n j*W) (rx j) (W/2))
    (hdisj : Set.Pairwise (↑s) (Disjoint on A))
    (U : ℝ×ℝ → ℝ) (hUm : Measurable U) (hU2 : MemLp U 2 (volume.prod volume))
    (B : ℝ) (hB : 0≤B) (hU0 : ∀ p, 0≤U p) (hUb : ∀ p, ‖U p‖≤B)
    (hFU : ∀ j∈s, ∀ a p, polynomialWeight b (2*W) q p.2*‖F j a p‖≤U p) :
    (∑ j∈s, (1+|n j|)^(4*q)*
      (packetNormSup (fun a z => F j a z)
        (coordinateBox (cx j) (b+n j*W) (rx j) (W/2)))^2*
          (volume.prod volume).real (A j))≤
      32^(2*q)*(147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)^2*
        (1296*∫ p, (U p)^2 ∂volume.prod volume) := by
  let G := fun j a => planarPolynomialLocalization b (2*W) q (F j a)
  let Q := fun j => coordinateBox (cx j) (b+n j*W) (rx j) (W/2)
  have hGU : ∀ j∈s, ∀ a p, ‖G j a p‖≤U p := by
    intro j hj a p
    exact (planarPolynomialLocalization_norm b (2*W) q (F j a) p).trans_le (hFU j hj a p)
  have hGb : ∀ j∈s, ∀ a p, ‖G j a p‖≤B := by
    intro j hj a p
    exact (hGU j hj a p).trans ((le_abs_self (U p)).trans (hUb p))
  have hFG : ∀ j∈s, ∀ a p, ‖F j a p‖≤‖G j a p‖ := by
    intro j hj a p
    rw [planarPolynomialLocalization_norm]
    exact le_mul_of_one_le_left (norm_nonneg _) (polynomialWeight_one_le b (2*W) q p.2)
  have hcell (j : J) (hj : j∈s) :
      (1+|n j|)^(4*q)*(packetNormSup (fun a z => F j a z) (Q j))^2≤
        32^(2*q)*(packetNormSup (fun a z => G j a z) (Q j))^2 := by
    have hpoint (a : ι) (p : ℝ×ℝ) (hp : p∈Q j) :
        (1+|n j|)^(2*q)*‖F j a p‖≤32^q*‖G j a p‖ := by
      have hy : |p.2-b-n j*W|≤W/2 := by
        simpa only [sub_add_eq_sub_sub] using hp.2
      rw [planarPolynomialLocalization_norm]
      have h := mul_le_mul_of_nonneg_right
        (transverse_cell_polynomial_weight b W (n j) p.2 q hW hy) (norm_nonneg (F j a p))
      simpa only [mul_assoc] using h
    have hs := packetNormSup_weighted_le (fun a z => F j a z) (fun a z => G j a z)
      (Q j) ((1+|n j|)^(2*q)) (32^q) B (by positivity) (by positivity) hB
      (fun a p _ => hGb j hj a p) hpoint
    have hF0 := packetNormSup_nonneg (fun a z => F j a z) (Q j) B hB
      (fun a p _ => (hFG j hj a p).trans (hGb j hj a p))
    have hs2 := pow_le_pow_left₀ (mul_nonneg (by positivity) hF0) hs 2
    simp only [mul_pow,←pow_mul] at hs2
    convert hs2 using 1 <;> congr 2 <;> omega
  have he := finite_box_supremum_energy s Kx Ky G Rx Ry cx (fun j => b+n j*W)
    rx (fun _ => W/2) hrx (fun _ _ => by positivity) hKx hKy
    (fun j hj a => planarPolynomialLocalization_horizontal_band b (2*W) q (F j a)
      (Rx/rx j) (hFx j hj a))
    (fun j hj a => planarPolynomialLocalization_vertical_band b (2*W) q (F j a)
      (Ry/(W/2)) (hFy j hj a))
    A hA hAfin hsub hdisj U hUm hU2 B hB hU0 hUb hGU
  calc
    _ ≤ ∑ j∈s, 32^(2*q)*(packetNormSup (fun a z => G j a z) (Q j))^2*
        (volume.prod volume).real (A j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (hcell j hj) (measureReal_nonneg)
    _ = 32^(2*q)*∑ j∈s, (packetNormSup (fun a z => G j a z) (Q j))^2*
        (volume.prod volume).real (A j) := by rw [Finset.mul_sum]; congr 1; ext j; ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he (by positivity : 0≤(32:ℝ)^(2*q))

end LipschitzHilbert

end

end OAI
