import OAI.Analysis.LipschitzHilbert.Trees.SourceDemodulatedSynthesis
import OAI.Analysis.LipschitzHilbert.Trees.SourceLongPrefixes
import OAI.Analysis.LipschitzHilbert.Trees.SourceLongCellEnergy

namespace OAI

/-! Narrow-bin reproduction for actual long intervals. The transverse
weight and all physical cells retain their original spatial width. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert
variable {κ : Type} [Fintype κ]

theorem packetNormSup_verticalDemodulation {ι : Type*} (nu : κ → ℝ)
    (F : ι → SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (Q : Set (ℝ×ℝ)) :
    packetNormSup (fun a z => verticalDemodulation nu (F a) z) Q=
      packetNormSup (fun a z => F a z) Q := by
  simp only [packetNormSup,packetNormValues,verticalDemodulation_norm]

namespace SourceLabeledLattice
variable {N : ℕ} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physicalLongIntervalSchwartz_demodulated_bands
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (lo hi : ℕ) (r w cStar CEta Cb Cv : ℝ) (nu : κ → ℝ)
    (hr : 0<r) (hw : 0<w) (hcStar : 0≤cStar) (hCEta : 0≤CEta) (hCb : 0≤Cb)
    (hspectrum : ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
      |xi+P.rowSlope j l*eta|≤cStar/P.length j ∧ |eta|≤CEta/w)
    (hslope : ∀ j l, |P.rowSlope j l|≤Cb*w/P.length j)
    (hbin : ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
      |eta-nu k|≤Cv/P.width) :
    (∀ y xi, 𝓕 (vectorHorizontalSlice
      (verticalDemodulation nu (P.physicalLongIntervalSchwartz 0 r c lo hi)) y) xi≠0 →
      |xi|≤((cStar+Cb*CEta)/r)/(2*Real.pi)) ∧
    (∀ x eta, 𝓕 (vectorVerticalSlice
      (verticalDemodulation nu (P.physicalLongIntervalSchwartz 0 r c lo hi)) x) eta≠0 →
      |eta|≤(Cv/P.width)/(2*Real.pi)) := by
  have hp (n : ℕ) := P.physicalTreePartialSchwartz_demodulated_bands c (min n (P.longPrefix r))
    r w cStar CEta Cb Cv nu hr hw hcStar hCEta hCb (by
      intro j hj
      have hl := (P.longPrefix_spec r j).mp (hj.trans_le (min_le_right _ _))
      linarith) hspectrum hslope hbin
  have hx (f g : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (y : ℝ) :
      vectorHorizontalSlice (f-g) y=vectorHorizontalSlice f y-vectorHorizontalSlice g y := by
    ext x k
    rfl
  have hy (f g : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (x : ℝ) :
      vectorVerticalSlice (f-g) x=vectorVerticalSlice f x-vectorVerticalSlice g x := by
    ext y k
    rfl
  constructor
  · intro y xi hne
    by_contra hn
    apply hne
    rw [physicalLongIntervalSchwartz,verticalDemodulation_sub,hx]
    simp only [sub_eq_add_neg,FourierTransform.fourier_add,FourierTransform.fourier_neg,add_apply,neg_apply]
    have hz (n : ℕ) : 𝓕 (vectorHorizontalSlice
        (verticalDemodulation nu (P.physicalTreePartialSchwartz 0 c (min n (P.longPrefix r)))) y) xi=0 := by
      by_contra h
      exact hn ((hp n).1 y xi h)
    rw [hz,hz,neg_zero,add_zero]
  · intro x eta hne
    by_contra hn
    apply hne
    rw [physicalLongIntervalSchwartz,verticalDemodulation_sub,hy]
    simp only [sub_eq_add_neg,FourierTransform.fourier_add,FourierTransform.fourier_neg,add_apply,neg_apply]
    have hz (n : ℕ) : 𝓕 (vectorVerticalSlice
        (verticalDemodulation nu (P.physicalTreePartialSchwartz 0 c (min n (P.longPrefix r)))) x) eta=0 := by
      by_contra h
      exact hn ((hp n).2 x eta h)
    rw [hz,hz,neg_zero,add_zero]

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
