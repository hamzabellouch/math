import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeSpectrum
import OAI.Analysis.LipschitzHilbert.Estimates.StoppingScaleIntervals

namespace OAI

/-! The long packets form a literal prefix in scale. Every truncated
interval of that prefix has the proved coordinate cutoffs and is bounded
pointwise by the original tree maximum. -/
noncomputable section
open FourierTransform
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

def longPrefix (r : ℝ) : ℕ :=
  (Finset.univ.filter (fun j : Fin N => 32*r<P.length j)).sup (fun j => j.val+1)

theorem longPrefix_le (r : ℝ) : P.longPrefix r≤N := by
  apply Finset.sup_le
  intro j _
  omega

theorem longPrefix_spec (r : ℝ) (j : Fin N) :
    j.val<P.longPrefix r ↔ 32*r<P.length j := by
  unfold longPrefix
  rw [Finset.lt_sup_iff]
  constructor
  · rintro ⟨k,hk,hjk⟩
    have hkj : j≤k := by change j.val≤k.val; omega
    exact (Finset.mem_filter.mp hk).2.trans_le (P.length_antitone hkj)
  · intro hj
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,by omega⟩

def physicalLongIntervalSchwartz (t r : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (lo hi : ℕ) :
    SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ) :=
  P.physicalTreePartialSchwartz t c (min hi (P.longPrefix r))-
    P.physicalTreePartialSchwartz t c (min lo (P.longPrefix r))

theorem physicalLongIntervalSchwartz_norm (t r : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (lo hi : ℕ) (z : ℝ×ℝ) :
    ‖P.physicalLongIntervalSchwartz t r c lo hi z‖≤P.physicalTreeMaximal t c z := by
  simp only [physicalLongIntervalSchwartz,sub_apply,physicalTreePartialSchwartz_apply]
  let a := min lo (P.longPrefix r)
  let b := min hi (P.longPrefix r)
  have ha : a≤N := (min_le_right _ _).trans (P.longPrefix_le r)
  have hb : b≤N := (min_le_right _ _).trans (P.longPrefix_le r)
  rcases le_total a b with hab | hba
  · exact increment_le_intervalOscillation _ N 0 N a b (Nat.zero_le _) hab hb le_rfl
  · rw [norm_sub_rev]
    exact increment_le_intervalOscillation _ N 0 N b a (Nat.zero_le _) hba ha le_rfl

private theorem horizontal_sub (f g : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (y : ℝ) :
    vectorHorizontalSlice (f-g) y=vectorHorizontalSlice f y-vectorHorizontalSlice g y := by
  ext x k
  rfl

private theorem vertical_sub (f g : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (x : ℝ) :
    vectorVerticalSlice (f-g) x=vectorVerticalSlice f x-vectorVerticalSlice g x := by
  ext y k
  rfl

/-- The cutoff scale is the actual horizontal cell length. -/
theorem physicalLongIntervalSchwartz_bands
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (lo hi : ℕ) (r w cStar cEta CEta Cb : ℝ)
    (hr : 0<r) (hw : 0<w) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCb : 0≤Cb)
    (hspectrum : ∀ j l u k ξ η, planarAngularFourier (P.physicalPacket 0 j l u k) (ξ,η)≠0 →
      |ξ+P.rowSlope j l*η|≤cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta)
    (hselector : ∀ j l, |P.rowSlope j l|≤Cb*w/P.length j) :
    (∀ y ξ, 𝓕 (vectorHorizontalSlice (P.physicalLongIntervalSchwartz 0 r c lo hi) y) ξ≠0 →
      |ξ|≤(CEta*Cb+cStar)/(2*Real.pi*r)) ∧
    (∀ x η, 𝓕 (vectorVerticalSlice (P.physicalLongIntervalSchwartz 0 r c lo hi) x) η≠0 →
      |η|≤CEta/(2*Real.pi*w)) := by
  have hp (n : ℕ) := P.physicalTreePartialSchwartz_bands c (min n (P.longPrefix r))
    r w cStar cEta CEta Cb hr hw hcStar hcEta hCEta hCb (by
      intro j hj
      have hl := (P.longPrefix_spec r j).mp (hj.trans_le (min_le_right _ _))
      linarith) hspectrum hselector
  constructor
  · intro y ξ hne
    by_contra hn
    apply hne
    rw [physicalLongIntervalSchwartz,horizontal_sub]
    simp only [sub_eq_add_neg,FourierTransform.fourier_add,FourierTransform.fourier_neg,add_apply,neg_apply]
    have hz (n : ℕ) : 𝓕 (vectorHorizontalSlice
        (P.physicalTreePartialSchwartz 0 c (min n (P.longPrefix r))) y) ξ=0 := by
      by_contra h
      exact hn ((hp n).1 y ξ h)
    rw [hz,hz,neg_zero,add_zero]
  · intro x η hne
    by_contra hn
    apply hne
    rw [physicalLongIntervalSchwartz,vertical_sub]
    simp only [sub_eq_add_neg,FourierTransform.fourier_add,FourierTransform.fourier_neg,add_apply,neg_apply]
    have hz (n : ℕ) : 𝓕 (vectorVerticalSlice
        (P.physicalTreePartialSchwartz 0 c (min n (P.longPrefix r))) x) η=0 := by
      by_contra h
      exact hn ((hp n).2 x η h)
    rw [hz,hz,neg_zero,add_zero]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
