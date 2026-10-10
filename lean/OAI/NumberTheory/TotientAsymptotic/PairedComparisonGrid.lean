import OAI.NumberTheory.TotientAsymptotic.CollisionGrid
import OAI.NumberTheory.TotientAsymptotic.NormalizedComparison

namespace OAI

/-! The actual paired intervals, including the ungridded top and smooth bottom. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def pairedGridUpper {b : ℕ} (δ ζ : ℝ) (n : Fin b → ℕ) (j : ℕ) : ℝ :=
  if j=0 then 1 else if hj : j<b then collisionGridUpper δ j (n ⟨j,hj⟩) else ζ

def pairedGridLower {b : ℕ} (δ : ℝ) (n : Fin b → ℕ) (j : ℕ) : ℝ :=
  if j=0 then 4/5 else if hj : j<b then collisionGridLower δ (n ⟨j,hj⟩) else 0

/-- All comparisons are made with the same finite grid label. The endpoint
`ζ` is the smooth residual cutoff and the top endpoint is exactly one. -/
theorem paired_grid_intervals {b : ℕ} {δ ζ : ℝ} (hb : 1 ≤ b) (hδ : 0 < δ)
    (u v : Fin b → ℝ) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (halign : ∀ j, |u j-v j| ≤ (2*(j.val : ℝ)+1)*δ)
    (htop : max (u ⟨0,hb⟩) (v ⟨0,hb⟩) ≤ 1)
    (hhead : (4/5 : ℝ)≤ min (u ⟨0,hb⟩) (v ⟨0,hb⟩))
    (hfirst : pairedGridUpper δ ζ (fun j => collisionGridIndex δ (u j) (v j)) 1 < 4/5)
    (hnext : ∀ j : Fin b, ∀ hj : j.val+1<b,
      max (u ⟨j.val+1,hj⟩) (v ⟨j.val+1,hj⟩)+(2*(j.val+1 : ℕ)+4 : ℝ)*δ <
        min (u j) (v j))
    (hbottom : ζ+δ < min (u ⟨b-1,by omega⟩) (v ⟨b-1,by omega⟩)) :
    let n := fun j => collisionGridIndex δ (u j) (v j)
    pairedGridUpper δ ζ n 0=1 ∧ pairedGridUpper δ ζ n b=ζ ∧
    (∀ j : Fin b,
      pairedGridLower δ n j ≤ u j ∧ pairedGridLower δ n j ≤ v j ∧
      u j ≤ pairedGridUpper δ ζ n j ∧ v j ≤ pairedGridUpper δ ζ n j) ∧
    (∀ j ∈ Finset.range b,
      pairedGridUpper δ ζ n (j+1) < pairedGridLower δ n j ∧
      pairedGridLower δ n j < pairedGridUpper δ ζ n j) := by
  dsimp only
  let n := fun j => collisionGridIndex δ (u j) (v j)
  have henc (j : Fin b) := collision_grid_enclosure hδ (hu j) (hv j) (halign j)
  have hlo (j : Fin b) := collision_grid_lower_bounds hδ (hu j) (hv j)
  have hzeroU : u ⟨0,hb⟩ ≤ 1 := (le_max_left _ _).trans htop
  have hzeroV : v ⟨0,hb⟩ ≤ 1 := (le_max_right _ _).trans htop
  refine ⟨by simp [pairedGridUpper],by simp [pairedGridUpper,show b ≠ 0 by omega],?_,?_⟩
  · intro j
    by_cases hj0 : j.val=0
    · have he : j=⟨0,hb⟩ := Fin.ext hj0
      subst j
      simp only [pairedGridLower,pairedGridUpper,ite_true]
      exact ⟨hhead.trans (min_le_left _ _),hhead.trans (min_le_right _ _),hzeroU,hzeroV⟩
    · simp only [pairedGridLower,pairedGridUpper,hj0,ite_false,dite_eq_left j.isLt]
      exact ⟨(henc j).1,(henc j).2.1,(henc j).2.2.1.le,(henc j).2.2.2.1.le⟩

  · intro j hj
    have hjb := Finset.mem_range.mp hj
    have hl := hlo ⟨j,hjb⟩
    by_cases hj0 : j=0
    · subst j
      simp only [pairedGridLower,pairedGridUpper,ite_true]
      exact ⟨hfirst,by norm_num⟩
    simp only [pairedGridLower,hj0,ite_false,dite_eq_left hjb]
    constructor
    · by_cases hjn : j+1<b
      · have hg := hnext ⟨j,hjb⟩ hjn
        have he : collisionGridUpper δ (j+1) (n ⟨j+1,hjn⟩) <
            collisionGridLower δ (n ⟨j,hjb⟩) := by
          dsimp [n]
          have := collision_grid_separated hδ (hu ⟨j,hjb⟩) (hv ⟨j,hjb⟩)
            (hu ⟨j+1,hjn⟩) (hv ⟨j+1,hjn⟩) (halign ⟨j+1,hjn⟩) hg
          exact this
        simpa only [pairedGridUpper,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,
          dite_eq_left hjn] using he
      · have hlast : j=b-1 := by omega
        have heq : (⟨b-1,by omega⟩ : Fin b)=⟨j,hjb⟩ := Fin.ext hlast.symm
        have hh : ζ+δ < min (u ⟨j,hjb⟩) (v ⟨j,hjb⟩) := by
          simpa only [heq] using hbottom
        have he : ζ < collisionGridLower δ (n ⟨j,hjb⟩) := by
          dsimp [n]
          linarith [hl.2]
        simpa only [pairedGridUpper,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,
          dite_eq_right hjn] using he
    · have hh := (henc ⟨j,hjb⟩).1.trans_lt (henc ⟨j,hjb⟩).2.2.1
      simpa only [pairedGridUpper,hj0,ite_false,dite_eq_left hjb] using hh

lemma paired_grid_width {b : ℕ} (δ ζ : ℝ) (n : Fin b → ℕ)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 (b-1)) :
    pairedGridUpper δ ζ n j-pairedGridLower δ n j=(2*(j : ℝ)+3)*δ := by
  have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  have hjb : j<b := by have := (Finset.mem_Icc.mp hj).2; omega
  simp only [pairedGridUpper,pairedGridLower,hj0,ite_false,dite_eq_left hjb,
    collisionGridUpper,collisionGridLower,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  ring

lemma paired_grid_approximation {b : ℕ} {δ ζ : ℝ} (hδ : 0 < δ)
    (u v : Fin b → ℝ) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (halign : ∀ j, |u j-v j| ≤ (2*(j.val : ℝ)+1)*δ)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 (b-1)) :
    pairedGridUpper δ ζ (fun j => collisionGridIndex δ (u j) (v j)) j ≤
      u ⟨j,by have := Finset.mem_Icc.mp hj; omega⟩+(2*(b : ℝ)+3)*δ := by
  have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  have hjb : j<b := by have := (Finset.mem_Icc.mp hj).2; omega
  have he := (collision_grid_enclosure hδ (hu ⟨j,hjb⟩) (hv ⟨j,hjb⟩)
    (halign ⟨j,hjb⟩)).2.2.2.2
  simp only [pairedGridUpper,hj0,ite_false,dite_eq_left hjb]
  apply he.trans
  have hle : (j : ℝ) ≤ b := by exact_mod_cast hjb.le
  have ha := mul_le_mul_of_nonneg_right
    (show 2*(j : ℝ)+3≤2*(b : ℝ)+3 by linarith) hδ.le
  exact add_le_add le_rfl ha

lemma paired_grid_gaps {b : ℕ} {δ ζ : ℝ} (hb : 1 ≤ b) (hδ : 0 < δ)
    (u v : Fin b → ℝ) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (halign : ∀ j, |u j-v j| ≤ (2*(j.val : ℝ)+1)*δ)
    (hnext : ∀ j : Fin b, ∀ hj : j.val+1<b,
      max (u ⟨j.val+1,hj⟩) (v ⟨j.val+1,hj⟩)+(2*(j.val+1 : ℕ)+6 : ℝ)*δ <
        min (u j) (v j))
    (hbottom : ζ+3*δ < min (u ⟨b-1,by omega⟩) (v ⟨b-1,by omega⟩)) :
    ∀ j ∈ Finset.Icc 2 b,
      2*δ < pairedGridUpper δ ζ (fun j => collisionGridIndex δ (u j) (v j)) (j-1)-
        pairedGridUpper δ ζ (fun j => collisionGridIndex δ (u j) (v j)) j := by
  intro j hj
  have hj2 := (Finset.mem_Icc.mp hj).1
  have hjb := (Finset.mem_Icc.mp hj).2
  have hp : j-1<b := by omega
  have hp0 : j-1 ≠ 0 := by omega
  have heprev := collision_grid_enclosure hδ (hu ⟨j-1,hp⟩) (hv ⟨j-1,hp⟩)
    (halign ⟨j-1,hp⟩)
  simp only [pairedGridUpper,hp0,ite_false,dite_eq_left hp]
  by_cases hjlt : j<b
  · have hj0 : j ≠ 0 := by omega
    simp only [hj0,ite_false,dite_eq_left hjlt]
    have he := (collision_grid_enclosure hδ (hu ⟨j,hjlt⟩) (hv ⟨j,hjlt⟩)
      (halign ⟨j,hjlt⟩)).2.2.2.2
    have hidx : j-1+1=j := by omega
    have hg := hnext ⟨j-1,hp⟩ (by change j-1+1<b; omega)
    simp only [hidx] at hg
    have hmin := min_le_left (u ⟨j-1,hp⟩) (v ⟨j-1,hp⟩)
    have hmax := le_max_left (u ⟨j,hjlt⟩) (v ⟨j,hjlt⟩)
    linarith [heprev.2.2.1]
  · have hjeq : j=b := by omega
    have hj0 : j ≠ 0 := by omega
    simp only [hj0,ite_false,dite_eq_right hjlt]
    have hg : ζ+3*δ < min (u ⟨j-1,hp⟩) (v ⟨j-1,hp⟩) := by
      simpa only [hjeq] using hbottom
    linarith [min_le_left (u ⟨j-1,hp⟩) (v ⟨j-1,hp⟩),heprev.2.2.1]

lemma paired_grid_first {b : ℕ} {δ ζ : ℝ} (_hb : 1 ≤ b) (hδ : 0 < δ)
    (u v : Fin b → ℝ) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (halign : ∀ j, |u j-v j| ≤ (2*(j.val : ℝ)+1)*δ)
    (hζ : ζ ≤ 4/5) (hfirst : ∀ h : 1<b, u ⟨1,h⟩+5*δ ≤ 4/5) :
    pairedGridUpper δ ζ (fun j => collisionGridIndex δ (u j) (v j)) 1 ≤ 4/5 := by
  by_cases h : 1<b
  · simp only [pairedGridUpper,one_ne_zero,ite_false,dite_eq_left h]
    have he := (collision_grid_enclosure hδ (hu ⟨1,h⟩) (hv ⟨1,h⟩) (halign ⟨1,h⟩)).2.2.2.2
    norm_num only [Nat.cast_one] at he
    exact he.trans (hfirst h)
  · simpa only [pairedGridUpper,one_ne_zero,ite_false,dite_eq_right h] using hζ

end TotientAsymptotic

end

end OAI
