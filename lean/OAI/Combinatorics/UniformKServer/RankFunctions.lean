import Mathlib

namespace OAI

                                    
section

                                                                      
                                                          
noncomputable section
namespace UniformKServer.RankFunctions

def pstar : ℝ := 1/24
def sstar : ℝ := 5/8
def rank (β p : ℝ) : ℝ :=
  if p ≤ pstar then 1-β*p
  else if p ≤ sstar then
    (sstar-p)^2 * (18/7-(β-3)*(6/49+1152/343*(p-pstar)))
  else 0

def gap (p : ℝ) : ℝ :=
  if p ≤ pstar then p
  else if p ≤ sstar then (sstar-p)^2*(6/49+1152/343*(p-pstar))
  else 0

def allowed (β : ℝ) : Prop := 3 ≤ β ∧ β ≤ 3+1/100

def A (β : ℝ) : ℝ := 18/7-(β-3)*102/49
def B (β : ℝ) : ℝ := (β-3)*1152/343
def h (p : ℝ) : ℝ := max (sstar-p) 0
def middle (β p : ℝ) : ℝ := A β*(h p)^2+B β*(h p)^3

theorem coeff_bounds {β : ℝ} (hβ : allowed β) :
    2 ≤ A β ∧ 0 ≤ B β ∧ B β ≤ 1/20 ∧ A β+B β*(7/12) ≤ 3 ∧
    2*A β*(7/12)+3*B β*(7/12)^2 = β := by
  dsimp [allowed] at hβ
  dsimp [A, B]
  constructor
  · linarith [hβ.2]
  constructor
  · linarith [hβ.1]
  constructor
  · linarith [hβ.2]
  constructor
  · linarith [hβ.1]
  · ring

theorem h_nonneg (p : ℝ) : 0 ≤ h p := le_max_right _ _
theorem h_antitone : Antitone h := by
  intro p q hpq
  apply max_le_max <;> linarith

theorem h_diff {p q : ℝ} (hpq : p ≤ q) : h p-h q ≤ q-p := by
  unfold h
  by_cases hp : p ≤ sstar
  · rw [max_eq_left (sub_nonneg.mpr hp)]
    have hq := le_max_left (sstar-q) 0
    linarith
  · rw [max_eq_right (by linarith : sstar-p ≤ 0)]
    have hq := le_max_right (sstar-q) 0
    linarith

theorem h_bound {p : ℝ} (hp : pstar ≤ p) : h p ≤ 7/12 := by
  unfold h pstar sstar at *
  apply max_le <;> linarith

theorem middle_match (β : ℝ) : middle β pstar = 1-β*pstar := by
  norm_num [middle, h, pstar, sstar, A, B]
  ring

theorem rank_middle {β p : ℝ} (hp : pstar ≤ p) : rank β p = middle β p := by
  by_cases he : p = pstar
  · subst p
    simp only [rank, le_refl, ↓reduceIte, middle_match]
  have hn : ¬p ≤ pstar := fun hh => he (le_antisymm hh hp)
  unfold rank
  rw [ite_eq_right hn]
  by_cases hs : p ≤ sstar
  · rw [ite_eq_left hs]
    unfold middle h
    rw [max_eq_left (sub_nonneg.mpr hs)]
    unfold A B sstar pstar
    ring
  · rw [ite_eq_right hs]
    simp [middle, h, max_eq_right (by linarith : sstar-p ≤ 0)]

theorem middle_antitone {β : ℝ} (hβ : allowed β) : Antitone (middle β) := by
  have hc := coeff_bounds hβ
  intro p q hpq
  unfold middle
  gcongr
  · linarith [hc.1]
  · exact h_nonneg q
  · exact h_antitone hpq
  · exact hc.2.1
  · exact h_nonneg q
  · exact h_antitone hpq

theorem middle_drop {β p q : ℝ} (hβ : allowed β) (hp : pstar ≤ p) (hpq : p ≤ q) :
    middle β p-middle β q ≤ β*(q-p) := by
  have hc := coeff_bounds hβ
  have hx₀ := h_nonneg p
  have hy₀ := h_nonneg q
  have hx := h_bound hp
  have hxy := h_antitone hpq
  have hy := hxy.trans hx
  have hs : h p^2-h q^2 ≤ 2*(7/12)*(h p-h q) := by
    have := mul_le_mul_of_nonneg_left (show h p+h q ≤ 2*(7/12) by linarith)
      (sub_nonneg.mpr hxy)
    nlinarith
  have hp2 : h p^2 ≤ (7/12)^2 := by nlinarith
  have hq2 : h q^2 ≤ (7/12)^2 := by nlinarith
  have hpq2 : h p*h q ≤ (7/12)^2 := by nlinarith
  have ht : h p^3-h q^3 ≤ 3*(7/12)^2*(h p-h q) := by
    have := mul_le_mul_of_nonneg_left (show h p^2+h p*h q+h q^2 ≤ 3*(7/12)^2 by linarith)
      (sub_nonneg.mpr hxy)
    nlinarith
  calc
    middle β p-middle β q ≤ (2*A β*(7/12)+3*B β*(7/12)^2)*(h p-h q) := by
      have := mul_le_mul_of_nonneg_left hs (show 0 ≤ A β by linarith [hc.1])
      have := mul_le_mul_of_nonneg_left ht hc.2.1
      unfold middle
      nlinarith
    _ = β*(h p-h q) := by rw [hc.2.2.2.2]
    _ ≤ β*(q-p) := mul_le_mul_of_nonneg_left (h_diff hpq) (by linarith [hβ.1])

theorem h_convex : ConvexOn ℝ Set.univ h := by
  have hf : ConvexOn ℝ Set.univ (fun p : ℝ => sstar-p) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    nlinarith [congrArg (fun z : ℝ => sstar*z) hab]
  exact hf.sup (convexOn_const 0 convex_univ)

theorem middle_convex {β : ℝ} (hβ : allowed β) : ConvexOn ℝ Set.univ (middle β) := by
  have hc := coeff_bounds hβ
  have h2 := (h_convex.pow (fun x _ => h_nonneg x) 2).smul (show 0 ≤ A β by linarith [hc.1])
  have h3 := (h_convex.pow (fun x _ => h_nonneg x) 3).smul hc.2.1
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  exact (h2.add h3).2 hx hy ha hb hab

theorem rank_convex {β : ℝ} (hβ : allowed β) : ConvexOn ℝ Set.univ (rank β) := by
  let F : ℝ → ℝ := fun p => middle β p+β*p-1
  have hlin : ConvexOn ℝ Set.univ (fun p : ℝ => β*p-1) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    nlinarith
  have hF : ConvexOn ℝ (Set.Ici pstar) F := by
    have := (middle_convex hβ).add hlin
    refine ⟨convex_Ici _, ?_⟩
    intro x hx y hy a b ha hb hab
    simpa [F, Pi.add_apply, sub_eq_add_neg, add_assoc] using
      this.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  have hm : MonotoneOn F (Set.Ici pstar) := by
    intro p hp q hq hpq
    have := middle_drop hβ hp hpq
    dsimp [F]; linarith
  have he : (0 : ℝ) = F pstar := by
    dsimp [F]; rw [middle_match]; ring
  have hg := convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici
    (convexOn_const (0 : ℝ) (convex_Iic pstar)) hF (fun _ _ _ _ _ => le_refl _) hm he
  have hlin' : ConvexOn ℝ Set.univ (fun p : ℝ => 1-β*p) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    nlinarith
  have heq : rank β = (Set.Iic pstar).piecewise (fun _ => 0) F + (fun p => 1-β*p) := by
    ext p
    simp only [Pi.add_apply, Set.piecewise, Set.mem_Iic]
    by_cases hp : p ≤ pstar
    · simp [hp, rank]
    · simp only [ite_eq_right hp]
      rw [rank_middle (by linarith : pstar ≤ p)]
      dsimp [F]; ring
  rw [heq]
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  exact (hg.add hlin').2 hx hy ha hb hab

theorem rank_antitone {β : ℝ} (hβ : allowed β) : Antitone (rank β) := by
  intro p q hpq
  by_cases hq : q ≤ pstar
  · have hp : p ≤ pstar := hpq.trans hq
    simp only [rank, ite_eq_left hp, ite_eq_left hq]
    nlinarith [hβ.1]
  · rw [rank_middle (by linarith : pstar ≤ q)]
    by_cases hp : pstar ≤ p
    · rw [rank_middle hp]
      exact middle_antitone hβ hpq
    · calc
        middle β q ≤ middle β pstar := middle_antitone hβ (by linarith)
        _ = 1-β*pstar := middle_match β
        _ ≤ rank β p := by rw [rank, ite_eq_left (by linarith : p ≤ pstar)]; nlinarith [hβ.1]

theorem rank_zero (β : ℝ) : rank β 0 = 1 := by norm_num [rank, pstar]
theorem rank_cutoff (β : ℝ) : rank β sstar = 0 := by norm_num [rank, pstar, sstar]
theorem rank_beyond {β p : ℝ} (hp : sstar ≤ p) : rank β p = 0 := by
  rw [rank_middle (by dsimp [pstar, sstar] at *; linarith), middle]
  simp [h, max_eq_right (sub_nonpos.mpr hp)]

theorem rank_nonneg {β p : ℝ} (hβ : allowed β) : 0 ≤ rank β p := by
  by_cases hp : p ≤ pstar
  · rw [rank, ite_eq_left hp]
    have : β*p ≤ β*pstar := mul_le_mul_of_nonneg_left hp (by linarith [hβ.1])
    dsimp [pstar] at this
    nlinarith [hβ.2]
  · rw [rank_middle (by linarith)]
    have hc := coeff_bounds hβ
    have ha : 0 ≤ A β := by linarith [hc.1]
    have hb := hc.2.1
    have hh := h_nonneg p
    unfold middle
    positivity

theorem rank_le_one {β p : ℝ} (hβ : allowed β) (hp : 0 ≤ p) : rank β p ≤ 1 := by
  simpa only [rank_zero] using rank_antitone hβ hp

theorem rank_positive {β p : ℝ} (hβ : allowed β) (hp : p < sstar) : 0 < rank β p := by
  by_cases hpp : p ≤ pstar
  · rw [rank, ite_eq_left hpp]
    have : β*p ≤ β*pstar := mul_le_mul_of_nonneg_left hpp (by linarith [hβ.1])
    dsimp [pstar] at this
    nlinarith [hβ.2]
  · rw [rank_middle (by linarith)]
    have hc := coeff_bounds hβ
    have hh : 0 < h p := lt_of_lt_of_le (sub_pos.mpr hp) (le_max_left _ _)
    have ha : 0 < A β := by linarith [hc.1]
    have hb := hc.2.1
    unfold middle
    positivity

theorem rank_affine (β p : ℝ) : rank β p = rank 3 p-(β-3)*gap p := by
  unfold rank gap
  split_ifs <;> ring

theorem gap_nonneg {p : ℝ} (hp : 0 ≤ p) : 0 ≤ gap p := by
  unfold gap
  split_ifs with h₁ h₂
  · exact hp
  · have : 0 ≤ p-pstar := by linarith
    positivity
  · rfl

theorem rank_parameter_antitone {β γ p : ℝ} (hβγ : β ≤ γ) (hp : 0 ≤ p) :
    rank γ p ≤ rank β p := by
  rw [rank_affine γ, rank_affine β]
  nlinarith [gap_nonneg hp]

theorem gap_comparison {β p : ℝ} (hβ : allowed β) (hp : pstar/4 ≤ p) :
    rank β p/96 ≤ gap p ∧ gap p ≤ rank β p := by
  by_cases h₁ : p ≤ pstar
  · simp only [rank, gap, ite_eq_left h₁]
    have hp₀ : 0 ≤ p := by dsimp [pstar] at *; linarith
    have hlow : 0 ≤ β*p := mul_nonneg (by linarith [hβ.1]) hp₀
    have hu : β*p ≤ β*pstar := mul_le_mul_of_nonneg_left h₁ (by linarith [hβ.1])
    dsimp [pstar] at hp h₁ hu
    constructor <;> nlinarith [hβ.2]
  · by_cases h₂ : p ≤ sstar
    · simp only [rank, gap, ite_eq_right h₁, ite_eq_left h₂]
      let c : ℝ := 6/49+1152/343*(p-pstar)
      have hc : 6/49 ≤ c ∧ c ≤ 102/49 := by
        dsimp [c, pstar, sstar] at *
        constructor <;> linarith
      have hz : 0 ≤ β-3 ∧ β-3 ≤ 1/100 := by constructor <;> linarith [hβ.1, hβ.2]
      have hprod : 0 ≤ (β-3)*c ∧ (β-3)*c ≤ (1/100)*(102/49) := by
        constructor
        · exact mul_nonneg hz.1 (by linarith [hc.1])
        · exact mul_le_mul hz.2 hc.2 (by linarith [hc.1]) (by norm_num)
      have hlo : (18/7-(β-3)*c)/96 ≤ c := by linarith [hc.1, hprod.1]
      have hhi : c ≤ 18/7-(β-3)*c := by linarith [hc.2, hprod.2]
      constructor
      · have := mul_le_mul_of_nonneg_left hlo (sq_nonneg (sstar-p))
        dsimp [c] at this; nlinarith only [this]
      · exact mul_le_mul_of_nonneg_left hhi (sq_nonneg (sstar-p))
    · simp [rank, gap, h₁, h₂]

theorem sqrt_diff_aux {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hroot : 1 ≤ Real.sqrt x+Real.sqrt y) :
    |Real.sqrt x-Real.sqrt y| ≤ |x-y| := by
  have hid : |Real.sqrt x-Real.sqrt y| *(Real.sqrt x+Real.sqrt y) = |x-y| := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)), ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]
  have := abs_nonneg (Real.sqrt x-Real.sqrt y)
  nlinarith

theorem left_bound {β p : ℝ} (hβ : allowed β) (_hp : 0 ≤ p) (hpp : p ≤ pstar) :
    1/4 ≤ rank β p := by
  rw [rank, ite_eq_left hpp]
  have : β*p ≤ β*pstar := mul_le_mul_of_nonneg_left hpp (by linarith [hβ.1])
  dsimp [pstar] at this
  nlinarith [hβ.2]

theorem sqrt_left {β p q : ℝ} (hβ : allowed β) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpp : p ≤ pstar) (hqq : q ≤ pstar) :
    |Real.sqrt (rank β p)-Real.sqrt (rank β q)| ≤ 4*|p-q| := by
  have hlp := left_bound hβ hp hpp
  have hlq := left_bound hβ hq hqq
  have hsp : (1/2 : ℝ) ≤ Real.sqrt (rank β p) := by
    nlinarith [Real.sq_sqrt (rank_nonneg hβ (p := p)), Real.sqrt_nonneg (rank β p)]
  have hsq : (1/2 : ℝ) ≤ Real.sqrt (rank β q) := by
    nlinarith [Real.sq_sqrt (rank_nonneg hβ (p := q)), Real.sqrt_nonneg (rank β q)]
  calc
    |Real.sqrt (rank β p)-Real.sqrt (rank β q)| ≤ |rank β p-rank β q| :=
      sqrt_diff_aux (rank_nonneg hβ) (rank_nonneg hβ) (by linarith)
    _ = β*|p-q| := by
      simp only [rank, ite_eq_left hpp, ite_eq_left hqq]
      rw [show 1-β*p-(1-β*q) = -β*(p-q) by ring, abs_mul, abs_neg,
        abs_of_nonneg (by linarith [hβ.1] : 0 ≤ β)]
    _ ≤ 4*|p-q| := mul_le_mul_of_nonneg_right (by linarith [hβ.2]) (abs_nonneg _)

theorem coeff_at {β p : ℝ} (hβ : allowed β) (hp : pstar ≤ p) :
    2 ≤ A β+B β*h p ∧ A β+B β*h p ≤ 3 := by
  have hc := coeff_bounds hβ
  have hm := mul_le_mul_of_nonneg_left (h_bound hp) hc.2.1
  have h0 := mul_nonneg hc.2.1 (h_nonneg p)
  constructor <;> linarith [hc.1, hc.2.2.2.1]

theorem sqrt_middle_eq (β p : ℝ) :
    Real.sqrt (middle β p) = h p*Real.sqrt (A β+B β*h p) := by
  have he : middle β p = (h p)^2*(A β+B β*h p) := by unfold middle; ring
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (h_nonneg _)]

theorem sqrt_middle_ordered {β p q : ℝ} (hβ : allowed β)
    (hp : pstar ≤ p) (hpq : p ≤ q) :
    |Real.sqrt (rank β p)-Real.sqrt (rank β q)| ≤ 4*(q-p) := by
  have hq : pstar ≤ q := hp.trans hpq
  have hc := coeff_bounds hβ
  have hCp := coeff_at hβ hp
  have hCq := coeff_at hβ hq
  have hx := h_nonneg p
  have hy := h_nonneg q
  have hxy := h_antitone hpq
  have hCxy : A β+B β*h q ≤ A β+B β*h p := by nlinarith [hc.2.1]
  have hSxy := Real.sqrt_le_sqrt hCxy
  have hSp₀ : 1 ≤ Real.sqrt (A β+B β*h p) := by
    apply (Real.le_sqrt (by norm_num) (by linarith [hCp.1])).mpr
    norm_num; linarith [hCp.1]
  have hSq₀ : 1 ≤ Real.sqrt (A β+B β*h q) := by
    apply (Real.le_sqrt (by norm_num) (by linarith [hCq.1])).mpr
    norm_num; linarith [hCq.1]
  have hSp : Real.sqrt (A β+B β*h p) ≤ 2 := by
    apply (Real.sqrt_le_left (by norm_num)).mpr
    norm_num; linarith [hCp.2]
  have hroot : Real.sqrt (A β+B β*h p)-Real.sqrt (A β+B β*h q) ≤ B β*(h p-h q) := by
    have hh := sqrt_diff_aux (by linarith [hCp.1] : 0 ≤ A β+B β*h p)
      (by linarith [hCq.1] : 0 ≤ A β+B β*h q) (by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hSxy), abs_of_nonneg (sub_nonneg.mpr hCxy)] at hh
    nlinarith only [hh]
  have hcost : h p*Real.sqrt (A β+B β*h p)-h q*Real.sqrt (A β+B β*h q) ≤
      (2+(7/12)*B β)*(h p-h q) := by
    have h1 := mul_le_mul_of_nonneg_left hSp (sub_nonneg.mpr hxy)
    have h2 := mul_le_mul_of_nonneg_left hroot hy
    have h3 := mul_le_mul_of_nonneg_right (h_bound hq) (mul_nonneg hc.2.1 (sub_nonneg.mpr hxy))
    nlinarith only [h1,h2,h3]
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt (rank_antitone hβ hpq))),
    rank_middle hp, rank_middle hq, sqrt_middle_eq, sqrt_middle_eq]
  calc
    _ ≤ (2+(7/12)*B β)*(h p-h q) := hcost
    _ ≤ 4*(h p-h q) := mul_le_mul_of_nonneg_right (by linarith [hc.2.2.1]) (sub_nonneg.mpr hxy)
    _ ≤ 4*(q-p) := by linarith [h_diff hpq]

theorem sqrt_rank_lipschitz {β : ℝ} (hβ : allowed β) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) :
    |Real.sqrt (rank β p)-Real.sqrt (rank β q)| ≤ 4*|p-q| := by
  wlog hpq : p ≤ q generalizing p q
  · simpa only [abs_sub_comm] using this hq hp (le_of_not_ge hpq)
  rw [abs_sub_comm p q, abs_of_nonneg (sub_nonneg.mpr hpq)]
  by_cases hq' : q ≤ pstar
  · have hh := sqrt_left hβ hp hq (hpq.trans hq') hq'
    simpa only [abs_sub_comm p q, abs_of_nonneg (sub_nonneg.mpr hpq)] using hh
  · by_cases hp' : pstar ≤ p
    · exact sqrt_middle_ordered hβ hp' hpq
    · have hpp : p ≤ pstar := le_of_lt (lt_of_not_ge hp')
      have hqq : pstar ≤ q := le_of_lt (lt_of_not_ge hq')
      have h1 := sqrt_left hβ hp (by norm_num [pstar]) hpp (le_refl pstar)
      have h2 := sqrt_middle_ordered hβ (le_refl pstar) hqq
      have htri := abs_sub_le (Real.sqrt (rank β p)) (Real.sqrt (rank β pstar)) (Real.sqrt (rank β q))
      rw [abs_sub_comm p pstar, abs_of_nonneg (sub_nonneg.mpr hpp)] at h1
      linarith

theorem rank_properties (β : ℝ) (hβ : allowed β) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (rank β) ∧
    AntitoneOn (rank β) (Set.Icc (0 : ℝ) 1) ∧
    (∀ p ∈ Set.Icc (0 : ℝ) 1, 0 ≤ rank β p ∧ rank β p ≤ 1) ∧
    (∀ p ∈ Set.Icc (0 : ℝ) pstar, rank β p = 1-β*p) ∧
    (∀ p ∈ Set.Ico (0 : ℝ) sstar, 0 < rank β p) ∧
    (∀ p ∈ Set.Icc sstar (1 : ℝ), rank β p = 0) ∧
    (∀ p ∈ Set.Icc (0 : ℝ) 1, rank β p = rank 3 p-(β-3)*gap p) ∧
    (∀ p ∈ Set.Icc (0 : ℝ) 1, 0 ≤ gap p) ∧
    (∀ p ∈ Set.Icc (pstar/4) 1, rank β p/96 ≤ gap p ∧ gap p ≤ rank β p) ∧
    (∀ p ∈ Set.Icc (0 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1,
      |Real.sqrt (rank β p)-Real.sqrt (rank β q)| ≤ 4*|p-q|) := by
  refine ⟨(rank_convex hβ).subset (Set.subset_univ _) (convex_Icc _ _),
    (rank_antitone hβ).antitoneOn _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp; exact ⟨rank_nonneg hβ, rank_le_one hβ hp.1⟩
  · intro p hp; simp [rank, hp.2]
  · intro p hp; exact rank_positive hβ hp.2
  · intro p hp; exact rank_beyond hp.1
  · intro p hp; exact rank_affine β p
  · intro p hp; exact gap_nonneg hp.1
  · intro p hp; exact gap_comparison hβ hp.1
  · intro p hp q hq; exact sqrt_rank_lipschitz hβ hp.1 hq.1

end UniformKServer.RankFunctions

end


end

end OAI
