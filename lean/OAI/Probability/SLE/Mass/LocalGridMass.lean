import OAI.Probability.SLE.Gauge.CoverGrid

namespace OAI

/-! A translated finite grid count for arbitrary sets of bounded diameter.
No regularity of the set being covered is required. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma localGrid_coordinate {r s x y : ℝ} (hr : 0 < r) (_hs : 0 ≤ s)
    (hxy : |y-x| ≤ s) :
    ⌊x/r⌋-(⌈s/r⌉+2)  ≤  ⌊y/r⌋ ∧ ⌊y/r⌋  ≤  ⌊x/r⌋+(⌈s/r⌉+2) := by
  have hx0 := Int.floor_le (x/r)
  have hx1 := Int.lt_floor_add_one (x/r)
  have hy0 := Int.floor_le (y/r)
  have hy1 := Int.lt_floor_add_one (y/r)
  have hc := Int.le_ceil (s/r)
  have hlo : -s/r ≤ (y-x)/r := div_le_div_of_nonneg_right (abs_le.mp hxy).1 hr.le
  have hhi : (y-x)/r ≤ s/r := div_le_div_of_nonneg_right (abs_le.mp hxy).2 hr.le
  rw [sub_div] at hlo hhi
  rw [neg_div] at hlo
  constructor
  · have hh : ((⌊x/r⌋-(⌈s/r⌉+2):ℤ):ℝ) ≤ (⌊y/r⌋:ℝ) := by
      push_cast
      linarith
    exact_mod_cast hh
  · have hh : (⌊y/r⌋:ℝ) ≤ ((⌊x/r⌋+(⌈s/r⌉+2):ℤ):ℝ) := by
      push_cast
      linarith
    exact_mod_cast hh

def localGridIndex (r s : ℝ) (z : ℂ) : Finset (ℤ×ℤ) :=
  let N : ℤ := ⌈s/r⌉+2
  (Finset.Icc (⌊z.re/r⌋-N) (⌊z.re/r⌋+N)) ×ˢ
    (Finset.Icc (⌊z.im/r⌋-N) (⌊z.im/r⌋+N))

lemma localGrid_covers {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (z : ℂ) :
    closedBall z s ⊆ ⋃ i∈localGridIndex r s z, closedBall (coverGridCenter r i) (2*r) := by
  intro w hw
  have hn : ‖w-z‖ ≤ s := by simpa only [mem_closedBall,dist_eq_norm] using hw
  have hx := localGrid_coordinate hr hs ((Complex.abs_re_le_norm (w-z)).trans hn)
  have hy := localGrid_coordinate hr hs ((Complex.abs_im_le_norm (w-z)).trans hn)
  refine mem_iUnion₂.mpr ⟨(⌊w.re/r⌋,⌊w.im/r⌋),?_,coverGrid_floor_distance hr w⟩
  simpa only [localGridIndex,Finset.mem_product,Finset.mem_Icc,Complex.sub_re,Complex.sub_im]
    using And.intro hx hy

lemma localGrid_card_bound {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (z : ℂ) :
    ((localGridIndex r s z).card:ℝ)  ≤  81*max 1 ((s/r)^2) := by
  let N : ℤ := ⌈s/r⌉+2
  have hN : 0 ≤ N := by
    have h := Int.ceil_nonneg (div_nonneg hs hr.le)
    dsimp [N]
    omega
  have hside : 2*(N:ℝ)+1  ≤  2*(s/r)+7 := by
    have hc := Int.ceil_lt_add_one (s/r)
    dsimp [N]
    push_cast
    linarith
  have hside0 : 0 ≤ 2*(N:ℝ)+1 := by exact_mod_cast (show (0:ℤ) ≤ 2*N+1 by omega)
  have hcard : ((localGridIndex r s z).card:ℝ)=(2*(N:ℝ)+1)^2 := by
    have hx := Int.card_Icc_of_le (a:=⌊z.re/r⌋-N) (b:=⌊z.re/r⌋+N) (by omega)
    have hy := Int.card_Icc_of_le (a:=⌊z.im/r⌋-N) (b:=⌊z.im/r⌋+N) (by omega)
    have hx' : ((Finset.Icc (⌊z.re/r⌋-N) (⌊z.re/r⌋+N)).card:ℝ)=2*(N:ℝ)+1 := by
      have h : ((Finset.Icc (⌊z.re/r⌋-N) (⌊z.re/r⌋+N)).card:ℝ)=
          ((⌊z.re/r⌋:ℝ)+(N:ℝ))+1-((⌊z.re/r⌋:ℝ)-(N:ℝ)) := by exact_mod_cast hx
      linarith
    have hy' : ((Finset.Icc (⌊z.im/r⌋-N) (⌊z.im/r⌋+N)).card:ℝ)=2*(N:ℝ)+1 := by
      have h : ((Finset.Icc (⌊z.im/r⌋-N) (⌊z.im/r⌋+N)).card:ℝ)=
          ((⌊z.im/r⌋:ℝ)+(N:ℝ))+1-((⌊z.im/r⌋:ℝ)-(N:ℝ)) := by exact_mod_cast hy
      linarith
    change (((Finset.Icc _ _) ×ˢ (Finset.Icc _ _)).card:ℝ)=_
    rw [Finset.card_product,Nat.cast_mul,hx',hy',pow_two]
  rw [hcard]
  have hratio : 0 ≤ s/r := div_nonneg hs hr.le
  by_cases hsmall : s/r ≤ 1
  · have h : 2*(N:ℝ)+1 ≤ 9 := by linarith
    have hp := pow_le_pow_left₀ hside0 h 2
    norm_num at hp
    exact hp.trans (by nlinarith [le_max_left (1:ℝ) ((s/r)^2)])
  · have hlarge : 1 ≤ s/r := (lt_of_not_ge hsmall).le
    have h : 2*(N:ℝ)+1 ≤ 9*(s/r) := by linarith
    have hp := pow_le_pow_left₀ hside0 h 2
    calc
      _  ≤  (9*(s/r))^2 := hp
      _ = 81*(s/r)^2 := by ring
      _  ≤  _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)

lemma localGrid_mass_bound
    (μ : Measure ℂ) {r s H : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (hH : 0 ≤ H)
    (hcell : ∀ i : ℤ×ℤ, μ (closedBall (coverGridCenter r i) (2*r))  ≤  ENNReal.ofReal H)
    (A : Set ℂ) (hA : ∀ x∈A, ∀ y∈A, dist x y ≤ s) :
    μ A  ≤  ENNReal.ofReal (81*H*max 1 ((s/r)^2)) := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | ⟨z,hz⟩
  · simp
  have hcover : A ⊆ closedBall z s := by
    intro w hw
    exact hA w hw z hz
  calc
    μ A  ≤  μ (⋃ i∈localGridIndex r s z, closedBall (coverGridCenter r i) (2*r)) :=
      measure_mono (hcover.trans (localGrid_covers hr hs z))
    _  ≤  ∑ i∈localGridIndex r s z, μ (closedBall (coverGridCenter r i) (2*r)) := measure_biUnion_finset_le _ _
    _  ≤  ∑ _i∈localGridIndex r s z, ENNReal.ofReal H := Finset.sum_le_sum (fun i _ => hcell i)
    _ = ENNReal.ofReal (((localGridIndex r s z).card:ℝ)*H) := by
      simp only [Finset.sum_const,nsmul_eq_mul,ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
    _  ≤  _ := ENNReal.ofReal_le_ofReal (by
      have h := mul_le_mul_of_nonneg_right (localGrid_card_bound hr hs z) hH
      nlinarith)

end SLEExactGauge

end

end OAI
