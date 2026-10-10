import OAI.NumberTheory.TotientAsymptotic.ActualSurvivingGeometry

namespace OAI

/-! Finite Ford grids from surviving prime heights. -/

noncomputable section

namespace TotientAsymptotic

lemma collisionMesh_le_hundredth {h : ℕ} {δ : ℝ} (hh : 4≤h)
    (hδ : δ≤2/(h : ℝ)^32) : δ≤1/100 := by
  have hhR : (4 : ℝ)≤h := by exact_mod_cast hh
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤4) hhR 32
  have h0 : (0 : ℝ)<(h : ℝ)^32 := by positivity
  apply hδ.trans
  apply (div_le_iff₀ h0).mpr
  norm_num at hp
  linarith

/-- The grid label is chosen from the actual paired largest factors. Every
width and separation restriction is proved here, including the one-prime case. -/
theorem comparison_grid_from_heights {b h : ℕ} {t : ShiftedPair b} {Y Z δ : ℝ}
    (hb : 0<b) (hbh : b≤h) (hh : 4≤h) (hY : 0<Y) (_hZ : 0<Z) (hZY : Z≤Y)
    (hδ : 0<δ) (hδu : δ≤2/(h : ℝ)^32)
    (hmargin : (2*(h : ℝ)+10)*δ < (1/10 : ℝ)*Z/Y)
    (ht : ComparisonHeightBounds t Y Z)
    (halign : ∀ r, |leftFactorHeight t r/Y-rightFactorHeight t r/Y| ≤
      (2*(r.val : ℝ)+1)*δ) :
    let u := fun r => leftFactorHeight t r/Y
    let v := fun r => rightFactorHeight t r/Y
    let n := fun r => collisionGridIndex δ (u r) (v r)
    let ζ := (7/10 : ℝ)*Z/Y
    n ∈ collisionGridFamilies δ b ∧
    pairedGridUpper δ ζ n 0=1 ∧ pairedGridUpper δ ζ n b=ζ ∧
    (∀ r : Fin b, pairedGridLower δ n r≤u r ∧ pairedGridLower δ n r≤v r ∧
      u r≤pairedGridUpper δ ζ n r ∧ v r≤pairedGridUpper δ ζ n r) ∧
    (∀ r ∈ Finset.range b,
      pairedGridUpper δ ζ n (r+1)<pairedGridLower δ n r ∧
      pairedGridLower δ n r<pairedGridUpper δ ζ n r) ∧
    pairedGridUpper δ ζ n 1<4/5 ∧
    (∀ r ∈ Finset.Icc 2 b,
      2*δ<pairedGridUpper δ ζ n (r-1)-pairedGridUpper δ ζ n r) := by
  dsimp only
  let u := fun r => leftFactorHeight t r/Y
  let v := fun r => rightFactorHeight t r/Y
  let n := fun r => collisionGridIndex δ (u r) (v r)
  let ζ := (7/10 : ℝ)*Z/Y
  have hu (r : Fin b) : 0≤u r := div_nonneg (ht.positive r).1.le hY.le
  have hv (r : Fin b) : 0≤v r := div_nonneg (ht.positive r).2.le hY.le
  have hu1 (r : Fin b) : u r≤1 := (div_le_one hY).mpr (ht.top r).1
  have hv1 (r : Fin b) : v r≤1 := (div_le_one hY).mpr (ht.top r).2
  have htop : max (u ⟨0,hb⟩) (v ⟨0,hb⟩)≤1 := max_le (hu1 _) (hv1 _)
  have hhead : (4/5 : ℝ)≤ min (u ⟨0,hb⟩) (v ⟨0,hb⟩) := by
    rw [min_div_div_right hY.le]
    apply (le_div_iff₀ hY).mpr
    have hh := ht.head hb
    linarith
  have hdsmall := collisionMesh_le_hundredth hh hδu
  have hζ : ζ≤7/10 := by
    apply (div_le_iff₀ hY).mpr
    exact mul_le_mul_of_nonneg_left hZY (by norm_num)
  have hfirst : pairedGridUpper δ ζ n 1<4/5 := by
    by_cases hb1 : 1<b
    · simp only [pairedGridUpper,one_ne_zero,ite_false,dite_eq_left hb1]
      have he := (collision_grid_enclosure hδ (hu ⟨1,hb1⟩) (hv ⟨1,hb1⟩)
        (halign ⟨1,hb1⟩)).2.2.2.2
      have hu1 : u ⟨1,hb1⟩≤18/25 := by
        apply (div_le_iff₀ hY).mpr
        exact (le_max_left _ _).trans (ht.tail _ (by norm_num))
      norm_num only [Nat.cast_one] at he
      linarith
    · simpa only [pairedGridUpper,one_ne_zero,ite_false,dite_eq_right hb1]
        using hζ.trans_lt (by norm_num : (7/10 : ℝ)<4/5)
  have hsep (r : Fin b) (hr : r.val+1<b) :
      max (u ⟨r.val+1,hr⟩) (v ⟨r.val+1,hr⟩)+(2*(r.val+1 : ℕ)+6 : ℝ)*δ <
        min (u r) (v r) := by
    have hs := div_le_div_of_nonneg_right (ht.separated r ⟨r.val+1,hr⟩ (by exact Nat.lt_succ_self _)) hY.le
    have hcoeff : (2*(r.val+1 : ℕ)+6 : ℝ)*δ≤(2*(h : ℝ)+10)*δ := by
      have hrh : (r.val : ℝ)≤h := by exact_mod_cast r.isLt.le.trans hbh
      push_cast
      exact mul_le_mul_of_nonneg_right (by linarith) hδ.le
    have hnorm : (1/10 : ℝ)*Z/Y ≤ min (u r) (v r)-max (u ⟨r.val+1,hr⟩) (v ⟨r.val+1,hr⟩) := by
      simpa only [u,v,min_div_div_right hY.le,max_div_div_right hY.le,sub_div] using hs
    linarith
  have hbottom : ζ+3*δ< min (u ⟨b-1,by omega⟩) (v ⟨b-1,by omega⟩) := by
    have hm := div_le_div_of_nonneg_right (ht.bottom ⟨b-1,by omega⟩) hY.le
    have hcoeff : 3*δ≤(2*(h : ℝ)+10)*δ := by
      have : (0 : ℝ)≤h := Nat.cast_nonneg _
      exact mul_le_mul_of_nonneg_right (by linarith) hδ.le
    have he : (4/5 : ℝ)*Z/Y=ζ+(1/10 : ℝ)*Z/Y := by dsimp [ζ]; ring
    rw [he] at hm
    rw [min_div_div_right hY.le]
    linarith
  have hinter := paired_grid_intervals hb hδ u v hu hv halign htop hhead hfirst
    (by
      intro r hr
      have hs := hsep r hr
      have hh : (2*(r.val+1 : ℕ)+4 : ℝ)*δ≤(2*(r.val+1 : ℕ)+6 : ℝ)*δ := by
        exact mul_le_mul_of_nonneg_right (by linarith) hδ.le
      linarith)
    (by linarith [hbottom])
  refine ⟨collisionGridFamilies_mem hδ u v hu1,hinter.1,hinter.2.1,hinter.2.2.1,hinter.2.2.2,hfirst,?_⟩
  exact paired_grid_gaps hb hδ u v hu hv halign hsep hbottom

end TotientAsymptotic

end

end OAI
