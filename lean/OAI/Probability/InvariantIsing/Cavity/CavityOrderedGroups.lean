import OAI.Probability.InvariantIsing.Cavity.CavityGroupPartition

namespace OAI

/-! Canonical ordered finite spectral groups are literal contiguous windows.
This fixes the full/base spectral ordering in the rational cavity sequence. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityOrderedStart {m : ℕ} (dims : Fin m → ℕ) (a : Fin m) : ℕ :=
  ∑ i : Fin a, dims (Fin.castLE a.isLt.le i)

def cavityOrderedEquiv {N m : ℕ} (dims : Fin m → ℕ) (hsum : ∑ a, dims a=N) :
    ((a : Fin m) × Fin (dims a)) ≃ Fin N :=
  finSigmaFinEquiv.trans (finCongr hsum)

def cavityOrderedGroup {N m : ℕ} (dims : Fin m → ℕ) (hsum : ∑ a, dims a=N)
    (i : Fin N) : Fin m := ((cavityOrderedEquiv dims hsum).symm i).1

lemma cavityOrderedGroup_congr {N m : ℕ} {dims dims' : Fin m → ℕ}
    (hsum : ∑ a, dims a=N) (hsum' : ∑ a, dims' a=N) (heq : dims=dims') :
    cavityOrderedGroup dims hsum=cavityOrderedGroup dims' hsum' := by
  cases heq
  rfl

lemma cavityOrderedEquiv_val {N m : ℕ} (dims : Fin m → ℕ) (hsum : ∑ a, dims a=N)
    (x : (a : Fin m) × Fin (dims a)) :
    (cavityOrderedEquiv dims hsum x).val=cavityOrderedStart dims x.1+x.2.val := by
  simp only [cavityOrderedEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply, cavityOrderedStart]

lemma cavityOrderedGroup_window {N m : ℕ} (dims : Fin m → ℕ) (hsum : ∑ a, dims a=N)
    (a : Fin m) (i : Fin N) :
    cavityOrderedGroup dims hsum i=a ↔
      cavityOrderedStart dims a ≤ i.val ∧ i.val < cavityOrderedStart dims a+dims a := by
  constructor
  · intro ha
    let x := (cavityOrderedEquiv dims hsum).symm i
    have hx : (cavityOrderedEquiv dims hsum x).val=i.val :=
      congrArg Fin.val ((cavityOrderedEquiv dims hsum).apply_symm_apply i)
    rw [cavityOrderedEquiv_val] at hx
    have hxval := x.2.isLt
    have hxa : x.1=a := ha
    simp only [hxa] at hx hxval
    omega
  · rintro ⟨hl,hw⟩
    let j : Fin (dims a) := ⟨i.val-cavityOrderedStart dims a, by omega⟩
    have he : cavityOrderedEquiv dims hsum ⟨a,j⟩=i := by
      apply Fin.ext
      rw [cavityOrderedEquiv_val]
      change cavityOrderedStart dims a+(i.val-cavityOrderedStart dims a)=i.val
      omega
    rw [← he]
    exact congrArg Sigma.fst ((cavityOrderedEquiv dims hsum).symm_apply_apply ⟨a,j⟩)

lemma cavityOrderedGroup_card {N m : ℕ} (dims : Fin m → ℕ) (hsum : ∑ a, dims a=N)
    (a : Fin m) :
    (cavitySpectralGroup (cavityOrderedGroup dims hsum) a).card=dims a :=
  cavity_group_dimension_card dims (cavityOrderedEquiv dims hsum) a

lemma cavityOrderedStart_add_le {N m : ℕ} (dims : Fin m → ℕ) (hsum : ∑ a, dims a=N)
    (a : Fin m) (hd : 0 < dims a) : cavityOrderedStart dims a+dims a ≤ N := by
  let j : Fin (dims a) := ⟨dims a-1, by omega⟩
  have hi := (cavityOrderedEquiv dims hsum ⟨a,j⟩).isLt
  rw [cavityOrderedEquiv_val] at hi
  change cavityOrderedStart dims a+(dims a-1)<N at hi
  omega

end InvariantIsing

end

end OAI
