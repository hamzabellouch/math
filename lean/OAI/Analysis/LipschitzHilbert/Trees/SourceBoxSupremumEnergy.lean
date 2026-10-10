import OAI.Analysis.LipschitzHilbert.Trees.SourceBoxSupremum

namespace OAI

/-! The uniform cell-supremum energy estimate, derived from actual
coordinate spectra and the proved strong maximal bound. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators FourierTransform ENNReal
namespace LipschitzHilbert
open DyadicLineGrid
variable {J ι κ : Type*} [Fintype κ]

theorem finite_box_supremum_energy
    (s : Finset J) (Kx Ky : SchwartzMap ℝ ℂ)
    (F : J → ι → SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ))
    (Rx Ry : ℝ) (cx cy rx ry : J → ℝ)
    (hrx : ∀ j∈s, 0<rx j) (hry : ∀ j∈s, 0<ry j)
    (hKx : ∀ ξ, |ξ|≤Rx → 𝓕 Kx ξ=1) (hKy : ∀ η, |η|≤Ry → 𝓕 Ky η=1)
    (hFx : ∀ j∈s, ∀ a y ξ, 𝓕 (vectorHorizontalSlice (F j a) y) ξ≠0 → |ξ|≤Rx/rx j)
    (hFy : ∀ j∈s, ∀ a x η, 𝓕 (vectorVerticalSlice (F j a) x) η≠0 → |η|≤Ry/ry j)
    (A : J → Set (ℝ×ℝ)) (hA : ∀ j∈s, MeasurableSet (A j))
    (hAfin : ∀ j∈s, (volume.prod volume) (A j)≠∞)
    (hsub : ∀ j∈s, A j⊆coordinateBox (cx j) (cy j) (rx j) (ry j))
    (hdisj : Set.Pairwise (↑s) (Disjoint on A))
    (U : ℝ×ℝ → ℝ) (hUm : Measurable U) (hU2 : MemLp U 2 (volume.prod volume))
    (B : ℝ) (hB : 0≤B) (hU0 : ∀ p, 0≤U p) (hUb : ∀ p, ‖U p‖≤B)
    (hFU : ∀ j∈s, ∀ a p, ‖F j a p‖≤U p) :
    (∑ j∈s, (packetNormSup (fun a z => F j a z)
      (coordinateBox (cx j) (cy j) (rx j) (ry j)))^2*(volume.prod volume).real (A j))≤
      (147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)^2*
        (1296*∫ p, (U p)^2 ∂volume.prod volume) := by
  let C := 147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1
  have hC : 0≤C := by
    have := (schwartzEnvelopeConstant_pos Kx 1).le
    have := (schwartzEnvelopeConstant_pos Ky 1).le
    positivity
  have hG := threeStrongMaximal_energy hUm hU2
  have hpoint (j : J) (hj : j∈s) :
      ∀ᵐ z ∂volume.prod volume, z∈A j →
        ∀ a x, x∈coordinateBox (cx j) (cy j) (rx j) (ry j) →
          ‖F j a x‖≤C*threeStrongMaximal U z := by
    have h := planar_family_box_bound Kx Ky (F j) Rx Ry (cx j) (cy j) (rx j) (ry j)
      (hrx j hj) (hry j hj) hKx hKy (hFx j hj) (hFy j hj)
      U hUm hU2 B hB hU0 hUb (hFU j hj)
    filter_upwards [h] with z hz
    intro hzA
    exact hz (hsub j hj hzA)
  have hbound : ∀ j∈s, ∀ a x, x∈coordinateBox (cx j) (cy j) (rx j) (ry j) →
      ‖F j a x‖≤B := by
    intro j hj a x _
    exact (hFU j hj a x).trans ((le_abs_self (U x)).trans (hUb x))
  have h := packetNormSup_finite_energy (volume.prod volume) s
    (fun j a z => F j a z) (fun j => coordinateBox (cx j) (cy j) (rx j) (ry j))
    A hA hAfin hdisj B C hB hC hbound (threeStrongMaximal U) hG.1
    (threeStrongMaximal_nonneg U) hpoint
  exact h.trans (mul_le_mul_of_nonneg_left hG.2 (sq_nonneg C))

end LipschitzHilbert

end

end OAI
