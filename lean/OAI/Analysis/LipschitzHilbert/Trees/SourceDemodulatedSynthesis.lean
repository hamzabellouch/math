import OAI.Analysis.LipschitzHilbert.Trees.SourceDemodulatedFourier
import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeSpectrum

namespace OAI

/-! Coordinate cutoffs for the actual packet sums after removing each
bin's common vertical carrier. -/
noncomputable section
open FourierTransform
open scoped FourierTransform BigOperators
namespace LipschitzHilbert
variable {κ ι : Type} [Fintype κ] [Fintype ι]

theorem verticalDemodulation_synthesis (nu : κ → ℝ)
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ) :
    verticalDemodulation nu (planarSynthesisSchwartz c f)=
      planarSynthesisSchwartz c (fun i k => scalarVerticalDemodulation (nu k) (f i k)) := by
  ext z k
  simp [planarSynthesisSchwartz,Finset.mul_sum,mul_left_comm]

theorem scalarVerticalDemodulation_bands (f : SchwartzMap (ℝ×ℝ) ℂ)
    (nu theta ell W w cStar CEta Cb Cv : ℝ)
    (hell : 0<ell) (hw : 0<w) (hCb : 0≤Cb)
    (hslope : |theta|≤Cb*w/ell)
    (hspectrum : ∀ xi eta, planarAngularFourier f (xi,eta)≠0 →
      |xi+theta*eta|≤cStar/ell ∧ |eta|≤CEta/w)
    (hbin : ∀ xi eta, planarAngularFourier f (xi,eta)≠0 → |eta-nu|≤Cv/W) :
    (∀ y xi, 𝓕 (planarSchwartzSlice (scalarVerticalDemodulation nu f) y 0) xi≠0 →
      |xi|≤((cStar+Cb*CEta)/ell)/(2*Real.pi)) ∧
    (∀ x eta, 𝓕 (planarVerticalSlice (scalarVerticalDemodulation nu f) x) eta≠0 →
      |eta|≤(Cv/W)/(2*Real.pi)) := by
  have h := planarAngularFourier_coordinate_bands (scalarVerticalDemodulation nu f)
    ((cStar+Cb*CEta)/ell) (Cv/W) (by
      have heq : (scalarVerticalDemodulation nu f : (ℝ×ℝ) → ℂ)=
          fun z => verticalCarrier (-nu) z*f z := by
        funext z
        exact scalarVerticalDemodulation_apply nu f z
      rw [heq]
      exact demodulated_packet_bands f nu theta ell W w cStar CEta Cb Cv hell hw hCb
          hslope hspectrum hbin)
  exact ⟨planarHorizontalSlice_fourier_band _ _ (fun xi eta hn => (h xi eta hn).1),
    planarVerticalSlice_fourier_band _ _ (fun xi eta hn => (h xi eta hn).2)⟩

namespace SourceLabeledLattice
variable {N : ℕ} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

theorem physicalTreePartialSchwartz_demodulated_bands
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (n : ℕ) (r w cStar CEta Cb Cv : ℝ) (nu : κ → ℝ)
    (hr : 0<r) (hw : 0<w) (hcStar : 0≤cStar) (hCEta : 0≤CEta) (hCb : 0≤Cb)
    (hlen : ∀ j : Fin N, j.val<n → r≤P.length j)
    (hspectrum : ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
      |xi+P.rowSlope j l*eta|≤cStar/P.length j ∧ |eta|≤CEta/w)
    (hslope : ∀ j l, |P.rowSlope j l|≤Cb*w/P.length j)
    (hbin : ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
      |eta-nu k|≤Cv/P.width) :
    (∀ y xi, 𝓕 (vectorHorizontalSlice
      (verticalDemodulation nu (P.physicalTreePartialSchwartz 0 c n)) y) xi≠0 →
      |xi|≤((cStar+Cb*CEta)/r)/(2*Real.pi)) ∧
    (∀ x eta, 𝓕 (vectorVerticalSlice
      (verticalDemodulation nu (P.physicalTreePartialSchwartz 0 c n)) x) eta≠0 →
      |eta|≤(Cv/P.width)/(2*Real.pi)) := by
  unfold physicalTreePartialSchwartz
  rw [verticalDemodulation_sum]
  apply vector_sum_bands
  intro j _
  by_cases hj : j.val<n
  · rw [ite_eq_left hj,verticalDemodulation_synthesis]
    apply planarSynthesisSchwartz_coordinate_bands
    · intro a k _ y xi hxi
      have h := (scalarVerticalDemodulation_bands (P.physicalPacket 0 j a.1 a.2 k)
        (nu k) (P.rowSlope j a.1) (P.length j) P.width w cStar CEta Cb Cv
        (P.length_pos j) hw hCb (hslope j a.1) (hspectrum j a.1 a.2 k)
        (hbin j a.1 a.2 k)).1 y xi hxi
      exact h.trans (div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity) hr (hlen j hj)) (by positivity))
    · intro a k _
      exact (scalarVerticalDemodulation_bands (P.physicalPacket 0 j a.1 a.2 k)
        (nu k) (P.rowSlope j a.1) (P.length j) P.width w cStar CEta Cb Cv
        (P.length_pos j) hw hCb (hslope j a.1) (hspectrum j a.1 a.2 k)
        (hbin j a.1 a.2 k)).2
  · rw [ite_eq_right hj,verticalDemodulation_zero]
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
