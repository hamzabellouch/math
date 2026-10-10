import OAI.MeasureTheory.Falconer.Estimates.PlanarCommonBudget

namespace OAI

/-! A small auxiliary dyadic depth simultaneously separates the base
projections and pays the fixed polynomial cost of the coordinate graph. -/
namespace Falconer

 theorem planar_weak_coefficients {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ τ ε : ℝ, 0 < τ ∧ 0 < ε ∧ τ ≤ 1/2 ∧ τ ≤ κ ∧
      30*ε+6*τ ≤ γ/4 ∧ 7*ε ≤ κ*τ/4 := by
  let τ := min (γ/100) (min (κ/100) (1/100))
  let ε := κ*τ/100
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have htγ : τ ≤ γ/100 := min_le_left _ _
  have htκ : τ ≤ κ/100 := (min_le_right _ _).trans (min_le_left _ _)
  have ht1 : τ ≤ 1/100 := (min_le_right _ _).trans (min_le_right _ _)
  have he : 0 < ε := by dsimp [ε]; positivity
  have heτ : ε ≤ τ/100 := by
    have hh := mul_le_mul_of_nonneg_right hκ1 hτ.le
    dsimp [ε]
    nlinarith
  refine ⟨τ,ε,hτ,he,by linarith,by linarith,by linarith,?_⟩
  dsimp [ε]
  nlinarith [mul_pos hκ hτ]

 theorem planar_weak_depth {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (Nmin : ℕ) :
    ∃ ε : ℝ, ∃ n0 : ℕ, 0 < ε ∧ 0 < n0 ∧ ∀ n : ℕ, n0 ≤ n →
      ∃ l : ℕ, l ≤ n ∧ Nmin ≤ n+2*l+10 ∧
        Real.log 128+7*ε*(n:ℝ)*Real.log 2 ≤ 2*κ*(l:ℝ)*Real.log 2 ∧
        Real.log (4000000*(64:ℝ)^5)+30*ε*(n:ℝ)*Real.log 2+
          6*((l:ℝ)+2)*Real.log 2 ≤ γ*((n+2*l+10:ℕ):ℝ)*Real.log 2 ∧
        Real.log 655+((l:ℝ)+2)*Real.log 2+(1-4*κ)*(n:ℝ)*Real.log 2 ≤
          (1-κ)*((n+2*l+10:ℕ):ℝ)*Real.log 2 := by
  obtain ⟨τ,ε,hτ,hε,ht1,htκ,heγ,heκ⟩ := planar_weak_coefficients hγ hκ hκ1
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A := 2/τ
  let B := 4*Real.log 128/(κ*τ*Real.log 2)
  let C := 2*(Real.log (4000000*(64:ℝ)^5)+12*Real.log 2)/(γ*Real.log 2)
  let D := (Real.log 655+2*Real.log 2)/(κ*Real.log 2)
  obtain ⟨n0,hn0⟩ := exists_nat_gt (max (max 1 (Nmin:ℝ)) (max (max A B) (max C D)))
  have hlarge : ∀ n : ℕ, n0 ≤ n →
      (1:ℝ) < n ∧ (Nmin:ℝ) ≤ n ∧ A ≤ n ∧ B ≤ n ∧ C ≤ n ∧ D ≤ n := by
    intro n hn
    have hnR : (n0:ℝ) ≤ n := Nat.cast_le.mpr hn
    have h0 := le_max_left (max 1 (Nmin:ℝ)) (max (max A B) (max C D))
    have h1 := le_max_right (max 1 (Nmin:ℝ)) (max (max A B) (max C D))
    have h2 := le_max_left (1:ℝ) (Nmin:ℝ)
    have h3 := le_max_right (1:ℝ) (Nmin:ℝ)
    have h4 := le_max_left (max A B) (max C D)
    have h5 := le_max_right (max A B) (max C D)
    have h6 := le_max_left A B
    have h7 := le_max_right A B
    have h8 := le_max_left C D
    have h9 := le_max_right C D
    exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
  have hn0pos : 0 < n0 := by
    have hh := (hlarge n0 le_rfl).1
    exact_mod_cast (show (0:ℝ) < n0 by linarith)
  refine ⟨ε,n0,hε,hn0pos,?_⟩
  intro n hn
  obtain ⟨hn1,hN,hA,hB,hC,hD⟩ := hlarge n hn
  let l := ⌊τ*(n:ℝ)⌋₊
  have hfloor : (l:ℝ) ≤ τ*(n:ℝ) := Nat.floor_le (by positivity)
  have hceil : τ*(n:ℝ) < (l:ℝ)+1 := Nat.lt_floor_add_one _
  have hτn : 2 ≤ τ*(n:ℝ) := by
    have hh := (div_le_iff₀ hτ).1 hA
    nlinarith
  have hlower : τ*(n:ℝ)/2 ≤ (l:ℝ) := by linarith
  have hln : l ≤ n := by
    have hh : (l:ℝ) ≤ n := by nlinarith
    exact_mod_cast hh
  have hsepconst : Real.log 128 ≤ κ*τ*(n:ℝ)*Real.log 2/4 := by
    have hh := (div_le_iff₀ (by positivity : 0 < κ*τ*Real.log 2)).1 hB
    nlinarith
  have hbudgetconst : Real.log (4000000*(64:ℝ)^5)+12*Real.log 2 ≤
      γ*(n:ℝ)*Real.log 2/2 := by
    have hh := (div_le_iff₀ (mul_pos hγ hlog)).1 hC
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 2)).2
    convert hh using 1 <;> ring
  have hlogconst : Real.log 655+2*Real.log 2 ≤ κ*(n:ℝ)*Real.log 2 := by
    have hh := (div_le_iff₀ (mul_pos hκ hlog)).1 hD
    nlinarith
  have hxn : 0 ≤ (n:ℝ)*Real.log 2 := by positivity
  have hNnat : Nmin ≤ n := by exact_mod_cast hN
  refine ⟨l,hln,by omega,?_,?_,?_⟩
  · have he := mul_le_mul_of_nonneg_right heκ hxn
    have hl := mul_le_mul_of_nonneg_left hlower (show 0 ≤ 2*κ*Real.log 2 by positivity)
    nlinarith
  · have he := mul_le_mul_of_nonneg_right heγ hxn
    have hl := mul_le_mul_of_nonneg_left hfloor (show 0 ≤ 6*Real.log 2 by positivity)
    have hnR : ((n+2*l+10:ℕ):ℝ) = (n:ℝ)+2*(l:ℝ)+10 := by norm_cast
    rw [hnR]
    have hmore : 0 ≤ γ*(2*(l:ℝ)+10)*Real.log 2 := by positivity
    have hgn : 0 ≤ γ*(n:ℝ)*Real.log 2 := by positivity
    have hsum : 30*ε*(n:ℝ)*Real.log 2+6*(l:ℝ)*Real.log 2 ≤
        (γ/4)*((n:ℝ)*Real.log 2) := by
      calc
        _ ≤ 30*ε*(n:ℝ)*Real.log 2+6*τ*(n:ℝ)*Real.log 2 := by nlinarith only [hl]
        _ = (30*ε+6*τ)*((n:ℝ)*Real.log 2) := by ring
        _ ≤ _ := he
    calc
      _ = (Real.log (4000000*(64:ℝ)^5)+12*Real.log 2)+
          (30*ε*(n:ℝ)*Real.log 2+6*(l:ℝ)*Real.log 2) := by ring
      _ ≤ γ*(n:ℝ)*Real.log 2/2+(γ/4)*((n:ℝ)*Real.log 2) := add_le_add hbudgetconst hsum
      _ ≤ γ*(n:ℝ)*Real.log 2 := by nlinarith only [hgn]
      _ ≤ γ*((n:ℝ)+2*(l:ℝ)+10)*Real.log 2 := by nlinarith only [hmore]
  · have hl := mul_le_mul_of_nonneg_left hfloor hlog.le
    have ht := mul_le_mul_of_nonneg_right htκ hxn
    have hnR : ((n+2*l+10:ℕ):ℝ) = (n:ℝ)+2*(l:ℝ)+10 := by norm_cast
    rw [hnR]
    have hκ0 : 0 ≤ 1-κ := by linarith
    have hmore : 0 ≤ (1-κ)*(2*(l:ℝ)+10)*Real.log 2 := by positivity
    nlinarith

end Falconer

end OAI
