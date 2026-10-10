import OAI.Analysis.LipschitzHilbert.Trees.SourcePlanarSynthesis
import OAI.Analysis.LipschitzHilbert.Trees.SourceWeightedTreeMaximal

namespace OAI

/-! Actual Schwartz representatives and coordinate spectra of tree
partial sums. Only packets longer than the cell scale are used. -/
noncomputable section
open FourierTransform
open scoped FourierTransform BigOperators
namespace LipschitzHilbert
variable {κ : Type} [Fintype κ]

theorem vector_horizontal_sum {J : Type*} (s : Finset J)
    (f : J → SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (y : ℝ) :
    vectorHorizontalSlice (∑ j∈s, f j) y=∑ j∈s, vectorHorizontalSlice (f j) y := by
  ext x k
  simp only [vectorHorizontalSlice_apply,sum_apply,WithLp.ofLp_sum,Finset.sum_apply]

theorem vector_vertical_sum {J : Type*} (s : Finset J)
    (f : J → SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (x : ℝ) :
    vectorVerticalSlice (∑ j∈s, f j) x=∑ j∈s, vectorVerticalSlice (f j) x := by
  ext y k
  simp only [vectorVerticalSlice_apply,sum_apply,WithLp.ofLp_sum,Finset.sum_apply]

theorem vector_sum_bands {J : Type*} (s : Finset J)
    (f : J → SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (Rx Ry : ℝ)
    (hf : ∀ j∈s,
      (∀ y ξ, 𝓕 (vectorHorizontalSlice (f j) y) ξ≠0 → |ξ|≤Rx) ∧
      (∀ x η, 𝓕 (vectorVerticalSlice (f j) x) η≠0 → |η|≤Ry)) :
    (∀ y ξ, 𝓕 (vectorHorizontalSlice (∑ j∈s, f j) y) ξ≠0 → |ξ|≤Rx) ∧
    (∀ x η, 𝓕 (vectorVerticalSlice (∑ j∈s, f j) x) η≠0 → |η|≤Ry) := by
  constructor
  · intro y ξ hne
    by_contra hn
    apply hne
    rw [vector_horizontal_sum,fourier_sum,sum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    by_contra h
    exact hn ((hf j hj).1 y ξ h)
  · intro x η hne
    by_contra hn
    apply hne
    rw [vector_vertical_sum,fourier_sum,sum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    by_contra h
    exact hn ((hf j hj).2 x η h)

namespace SourceLabeledLattice
variable {N : ℕ} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

def physicalTreePartialSchwartz (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (n : ℕ) :
    SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ) :=
  ∑ j : Fin N, if j.val<n then planarSynthesisSchwartz
    (fun a : Σ l : P.labels j, Item j l => c j a.1 a.2)
    (fun a k => P.physicalPacket t j a.1 a.2 k) else 0

@[simp] theorem physicalTreePartialSchwartz_apply (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (n : ℕ) (z : ℝ×ℝ) :
    P.physicalTreePartialSchwartz t c n z=P.physicalTreePartial t c n z := by
  unfold physicalTreePartialSchwartz physicalTreePartial packetPartialSum
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [planarSynthesisSchwartz_apply,zero_apply]

/-- Uniform coordinate cutoffs for a genuine prefix of long packets.
The cutoff is expressed at the cell scale rather than the smallest
individual packet length. -/
theorem physicalTreePartialSchwartz_bands
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (n : ℕ) (r w cStar cEta CEta Cb : ℝ)
    (hr : 0<r) (hw : 0<w) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCb : 0≤Cb)
    (hlen : ∀ j : Fin N, j.val<n → r≤P.length j)
    (hspectrum : ∀ j l u k ξ η, planarAngularFourier (P.physicalPacket 0 j l u k) (ξ,η)≠0 →
      |ξ+P.rowSlope j l*η|≤cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta)
    (hselector : ∀ j l, |P.rowSlope j l|≤Cb*w/P.length j) :
    (∀ y ξ, 𝓕 (vectorHorizontalSlice (P.physicalTreePartialSchwartz 0 c n) y) ξ≠0 →
      |ξ|≤(CEta*Cb+cStar)/(2*Real.pi*r)) ∧
    (∀ x η, 𝓕 (vectorVerticalSlice (P.physicalTreePartialSchwartz 0 c n) x) η≠0 →
      |η|≤CEta/(2*Real.pi*w)) := by
  unfold physicalTreePartialSchwartz
  apply vector_sum_bands
  intro j _
  by_cases hj : j.val<n
  · simp only [ite_eq_left hj]
    apply planarSynthesisSchwartz_coordinate_bands
    · intro a k _ y ξ hξ
      have h := (sourcePacket_coordinate_bands (P.physicalPacket 0 j a.1 a.2 k)
        (P.rowSlope j a.1) (P.length j) w cStar cEta CEta Cb
        (P.length_pos j) hw hcEta hCb (hspectrum j a.1 a.2 k) (hselector j a.1)).1 y ξ hξ
      apply h.trans
      exact div_le_div_of_nonneg_left (by positivity)
        (by positivity : 0<2*Real.pi*r)
        (mul_le_mul_of_nonneg_left (hlen j hj) (by positivity))
    · intro a k _
      exact (sourcePacket_coordinate_bands (P.physicalPacket 0 j a.1 a.2 k)
        (P.rowSlope j a.1) (P.length j) w cStar cEta CEta Cb
        (P.length_pos j) hw hcEta hCb (hspectrum j a.1 a.2 k) (hselector j a.1)).2
  · simp only [ite_eq_right hj]
    have hx (y : ℝ) : vectorHorizontalSlice (0 : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) y=0 := by
      ext x k
      rfl
    have hy (x : ℝ) : vectorVerticalSlice (0 : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) x=0 := by
      ext y k
      rfl
    simp only [hx,hy,FourierTransform.fourier_zero,zero_apply,ne_eq,not_true_eq_false,
      IsEmpty.forall_iff,and_self,forall_const]

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
