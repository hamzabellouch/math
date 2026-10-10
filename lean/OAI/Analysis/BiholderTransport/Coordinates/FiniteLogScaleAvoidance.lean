import Mathlib

namespace OAI

section
section
noncomputable section
open Set

namespace WeakMTWTransport

lemma finite_log_scale_avoidance (S : Finset ℝ) {lo hi L : ℝ} (hL : 0≤L)
    (hwide : lo+((S.card:ℝ)+2)*(2*L+1)<hi) :
    ∃ u∈Ioo lo hi, ∀ s∈S, L < |u-s| := by
  classical
  let u : Fin (S.card+1) → ℝ := fun i => lo+((i.val:ℝ)+1)*(2*L+1)
  have hu (i : Fin (S.card+1)) : u i∈Ioo lo hi := by
    have hv0 : (0:ℝ)≤ i.val := Nat.cast_nonneg _
    have hv1 : (i.val:ℝ)<(S.card:ℝ)+1 := by exact_mod_cast i.isLt
    dsimp [u]
    constructor <;> nlinarith [mul_nonneg (show 0≤(S.card:ℝ)+1-i.val by linarith) (show 0≤2*L+1 by linarith)]
  by_contra h
  have hex (i : Fin (S.card+1)) : ∃ s : {s // s∈S}, |u i-s.val|≤L := by
    by_contra H
    apply h
    refine ⟨u i,hu i,?_⟩
    intro s hs
    by_contra hh
    exact H ⟨⟨s,hs⟩,le_of_not_gt hh⟩
  let g : Fin (S.card+1) → {s // s∈S} := fun i => (hex i).choose
  have hg (i : Fin (S.card+1)) : |u i-(g i).val|≤L := (hex i).choose_spec
  have hsep (i j : Fin (S.card+1)) (hij : i.val<j.val) : g i≠g j := by
    intro H
    have H1 := abs_le.mp (hg i)
    have H2 := abs_le.mp (hg j)
    rw [←H] at H2
    have hv : (i.val:ℝ)+1≤j.val := by exact_mod_cast Nat.succ_le_of_lt hij
    dsimp [u] at H1 H2
    have HH := mul_nonneg (show 0≤(j.val:ℝ)-i.val-1 by linarith) (show 0≤2*L+1 by linarith)
    nlinarith only [H1.1,H2.2,HH,hL]
  have hinj : Function.Injective g := by
    intro i j H
    rcases lt_trichotomy i.val j.val with hij|hij|hij
    · exact False.elim (hsep i j hij H)
    · exact Fin.ext hij
    · exact False.elim (hsep j i hij H.symm)
  have HH := Fintype.card_le_of_injective g hinj
  simp only [Fintype.card_fin,Fintype.card_coe] at HH
  omega

lemma finite_spectral_gap_propagation {f : ℕ → ℝ} {N : ℕ} {c ε : ℝ}
    (hgap : 2*ε<c)
    (hbin : ∀ k≤N, f k≤ε ∨ c≤f k)
    (hstep : ∀ k<N, |f (k+1)-f k|≤ε)
    (hzero : c≤f 0) : c≤f N := by
  have H : ∀ k≤N, c≤f k := by
    intro k hk
    induction k with
    | zero => exact hzero
    | succ k ih =>
      have hc := ih (by omega)
      rcases hbin (k+1) hk with hsmall|hlarge
      · have hs := (abs_le.mp (hstep k (by omega))).1
        linarith
      · exact hlarge
  exact H N le_rfl
end WeakMTWTransport

end

end

end

end OAI
