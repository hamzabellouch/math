import OAI.MeasureTheory.Falconer.Estimates.OuterRootGain

namespace OAI

/-! # Simultaneously choosing the small outer-shell parameters -/

namespace Falconer

 theorem exists_outer_shell_parameters (m : ℕ) {χ : ℝ} (hχ : 0 < χ) :
    ∃ β κ σ lam η T : ℝ,
      0 < β ∧ 0 < κ ∧ κ ≤ 1 ∧ κ ≤ 1/1000 ∧ 0 < σ ∧ σ < κ/1000 ∧
      0 < lam ∧ lam ≤ σ ∧ 0 < η ∧ η ≤ 1 ∧
      4000*(dimensionalBranchReserve (m+3) lam σ+σ) ≤ 1 ∧
      (20/κ+1/σ)*(3*((m+3:ℕ):ℝ)+2)+10 < T ∧ β/2 ≤ T ∧
      β+((m+3:ℕ)+4)*lam < χ/4 ∧
      ((m+3:ℕ)+4)*lam+outerRootLoss m lam σ κ η+outerGraphLoss m lam σ ≤ β/8 := by
  let d : ℝ := (m+3:ℕ)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  let β := min (χ/16) (1/16)
  have hβ : 0 < β := lt_min (by positivity) (by norm_num)
  have hβχ : β ≤ χ/16 := min_le_left _ _
  have hβ1 : β ≤ 1/16 := min_le_right _ _
  let κ := min (1/2000) (β/(32000*(d+1)))
  have hκ : 0 < κ := lt_min (by norm_num) (by positivity)
  have hκsmall : κ ≤ 1/2000 := min_le_left _ _
  have hκβ : κ*(32000*(d+1)) ≤ β :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  let r : ℝ := 2*d+3
  let g : ℝ := (1000*(d+1)+32*d)+4*(d+1)+(d+4)
  have hr : 0 < r := by dsimp [r]; positivity
  have hg : 0 < g := by dsimp [g]; positivity
  let b : ℝ := min (χ/(16*(d+4))) (min (κ/2000)
    (min (1/(8000*r)) (min (β*κ/(128000000*r)) (β/(128*g)))))
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨σ,hσ,hσb⟩ := exists_between hb
  have hσχ : σ*(16*(d+4)) ≤ χ :=
    (le_div_iff₀ (by positivity)).mp (hσb.le.trans (min_le_left _ _))
  have hσrest : σ ≤ min (κ/2000)
      (min (1/(8000*r)) (min (β*κ/(128000000*r)) (β/(128*g)))) :=
    hσb.le.trans (min_le_right _ _)
  have hσκ : σ ≤ κ/2000 := hσrest.trans (min_le_left _ _)
  have hrest := hσrest.trans (min_le_right _ _)
  have hσr : σ*(8000*r) ≤ 1 := (le_div_iff₀ (by positivity)).mp (hrest.trans (min_le_left _ _))
  have hrest' := hrest.trans (min_le_right _ _)
  have hσi : σ*(128000000*r) ≤ β*κ :=
    (le_div_iff₀ (by positivity)).mp (hrest'.trans (min_le_left _ _))
  have hσg : σ*(128*g) ≤ β :=
    (le_div_iff₀ (by positivity)).mp (hrest'.trans (min_le_right _ _))
  let η := β/64
  let T := (20/κ+1/σ)*(3*d+2)+β+20
  have hsmall : β+(d+4)*σ < χ/4 := by nlinarith
  have hreserve : dimensionalBranchReserve (m+3) σ σ+σ = r*σ := by
    dsimp [dimensionalBranchReserve,r,d]
    ring
  have hbranch : 4000*(dimensionalBranchReserve (m+3) σ σ+σ) ≤ 1 := by
    rw [hreserve]
    nlinarith
  have hfirst : 500*d*κ ≤ β/64 := by nlinarith [mul_nonneg hκ.le hd]
  have hinv : 10^6*(dimensionalBranchReserve (m+3) σ σ+σ)/κ ≤ β/128 := by
    rw [hreserve]
    apply (div_le_iff₀ hκ).mpr
    nlinarith
  have hgraph : (d+4)*σ+outerGraphLoss m σ σ ≤ β/128 := by
    have he : (d+4)*σ+outerGraphLoss m σ σ = g*σ := by
      dsimp [outerGraphLoss,g,d]
      ring
    rw [he]
    nlinarith
  refine ⟨β,κ,σ,σ,η,T,hβ,hκ,by linarith,by linarith,hσ,by linarith,hσ,le_rfl,
    by dsimp [η]; positivity,by dsimp [η]; linarith,hbranch,?_,?_,hsmall,?_⟩
  · change (20/κ+1/σ)*(3*d+2)+10 < (20/κ+1/σ)*(3*d+2)+β+20
    linarith
  · change β/2 ≤ (20/κ+1/σ)*(3*d+2)+β+20
    have hnonneg : 0 ≤ (20/κ+1/σ)*(3*d+2) := by positivity
    linarith
  · change (d+4)*σ+(500*d*κ+10^6*(dimensionalBranchReserve (m+3) σ σ+σ)/κ+η)+outerGraphLoss m σ σ ≤ β/8
    dsimp [η]
    linarith

end Falconer

end OAI
