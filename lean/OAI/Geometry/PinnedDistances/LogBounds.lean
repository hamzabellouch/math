import OAI.Geometry.PinnedDistances.WeightedSelection

namespace OAI

universe u1 u2 u3 u4 u5 u6

section
/- Finite log-distance normalization. The diagonal is excluded in the energy
   and counted explicitly, with mass 1/n, in the ball estimate. -/

noncomputable section
open scoped BigOperators
namespace WeakPinned.Bounded
variable {P : Type u1} [Fintype P] [DecidableEq P]

def logCost (u : P → ℂ) (x y : P) : ℝ :=
  if x=y then 0 else |Real.log ‖u x-u y‖|

def logAverage (u : P → ℂ) : ℝ :=
  (∑ x, ∑ y, logCost u x y)/((Fintype.card P : ℝ)*((Fintype.card P : ℝ)-1))

omit [Fintype P] in
lemma logCost_nonneg (u : P → ℂ) (x y : P) : 0 ≤ logCost u x y := by
  unfold logCost; split_ifs <;> positivity

lemma logAverage_sum_bound (u : P → ℂ) (C : ℝ) (hn : 2 ≤ Fintype.card P)
    (hC : logAverage u ≤ C) :
    (∑ x, ∑ y, logCost u x y) ≤ C*(Fintype.card P : ℝ)*((Fintype.card P : ℝ)-1) := by
  have hnR : (2:ℝ) ≤ Fintype.card P := by exact_mod_cast hn
  have hp : 0 < (Fintype.card P : ℝ)*((Fintype.card P : ℝ)-1) := mul_pos (by linarith) (by linarith)
  simpa only [mul_assoc] using (div_le_iff₀ hp).mp hC

lemma logAverage_nonneg (u : P → ℂ) (hn : 2 ≤ Fintype.card P) : 0 ≤ logAverage u := by
  have hnR : (2:ℝ) ≤ Fintype.card P := by exact_mod_cast hn
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => logCost_nonneg _ _ _))) (mul_nonneg (by linarith) (by linarith))

/-- One actual vertex serves as a tightness center: a row of the nonnegative
    distance-log matrix has at most the average row energy. -/
lemma log_center (u : P → ℂ) (C : ℝ) (hn : 2 ≤ Fintype.card P) (hC : logAverage u ≤ C) :
    ∃ x : P, (∑ y, logCost u x y) ≤ C*(Fintype.card P : ℝ) := by
  have hnR : (2:ℝ) ≤ Fintype.card P := by exact_mod_cast hn
  have hC0 : 0 ≤ C := (logAverage_nonneg u hn).trans hC
  have hsum := logAverage_sum_bound u C hn hC
  by_contra hnot
  push Not at hnot
  have hpos : Finset.univ.Nonempty (α:=P) := Finset.card_pos.mp (by simpa using (show 0<Fintype.card P by omega))
  have hs := Finset.sum_lt_sum_of_nonempty hpos (fun x _ => hnot x)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  nlinarith

omit [Fintype P] in
lemma log_cost_large (u : P → ℂ) (R : ℝ) (hR : 1 < R) (x y : P) (hxy : R < ‖u x-u y‖) :
    Real.log R ≤ logCost u x y := by
  have hne : x ≠ y := by intro he; subst y; simp at hxy; linarith
  rw [logCost,ite_eq_right hne]
  have hl := Real.log_le_log (by linarith : 0<R) hxy.le
  exact hl.trans (le_abs_self _)

/-- A normalized empirical tail bound from the average logarithmic cost. -/
lemma normalized_tail_card (u : P → ℂ) (C : ℝ) (x : P)
    (hx : (∑ y, logCost u x y) ≤ C*(Fintype.card P : ℝ))
    (hn : 2 ≤ Fintype.card P) (R : ℝ) (hR : 1 < R) :
    ((Finset.univ.filter (fun y => R < ‖u y-u x‖)).card : ℝ)/(Fintype.card P : ℝ) ≤ C/Real.log R := by
  let A := Finset.univ.filter (fun y => R < ‖u y-u x‖)
  have hlog := Real.log_pos hR
  have hn0 : (0:ℝ)<Fintype.card P := by exact_mod_cast (show 0<Fintype.card P by omega)
  have hs : (A.card : ℝ)*Real.log R ≤ ∑ y, logCost u x y := by
    calc
      (A.card : ℝ)*Real.log R = ∑ y ∈ A, Real.log R := by simp
      _ ≤ ∑ y ∈ A, logCost u x y := by
        apply Finset.sum_le_sum
        intro y hy
        apply log_cost_large u R hR x y
        simpa only [norm_sub_rev] using (Finset.mem_filter.mp hy).2
      _ ≤ ∑ y, logCost u x y := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun y _ _ => logCost_nonneg u x y)
  apply (div_le_div_iff₀ hn0 hlog).mpr
  nlinarith

omit [Fintype P] in
lemma log_cost_close (u : P → ℂ) (hu : Function.Injective u) (z : ℂ) (r : ℝ)
    (_hr : 0<r) (_hr2 : r<1/2) (x y : P) (hx : ‖u x-z‖<r) (hy : ‖u y-z‖<r) (hxy : x≠y) :
    -Real.log (2*r) ≤ logCost u x y := by
  have hne : u x-u y ≠ 0 := sub_ne_zero.mpr (fun h => hxy (hu h))
  have hp := norm_pos_iff.mpr hne
  have hd : ‖u x-u y‖<2*r := by
    have hh := norm_sub_le_norm_sub_add_norm_sub (u x) z (u y)
    rw [norm_sub_rev z] at hh
    linarith
  have hh := Real.log_le_log hp hd.le
  rw [logCost,ite_eq_right hxy]
  have habs := neg_le_abs (Real.log ‖u x-u y‖)
  linarith

/-- The true n^-1 diagonal term in the concentration estimate. The points may
    be arbitrarily close; injectivity is the only geometric condition. -/
lemma small_ball_card (u : P → ℂ) (hu : Function.Injective u) (C : ℝ)
    (hn : 2 ≤ Fintype.card P) (hC : logAverage u ≤ C) (z : ℂ) (r : ℝ)
    (hr : 0<r) (hr2 : r<1/2) :
    (((Finset.univ.filter (fun x => ‖u x-z‖<r)).card : ℝ)/(Fintype.card P : ℝ))^2 ≤
      1/(Fintype.card P : ℝ)+C/(-Real.log (2*r)) := by
  let A := Finset.univ.filter (fun x => ‖u x-z‖<r)
  let T := -Real.log (2*r)
  have hT : 0<T := by dsimp [T]; exact neg_pos.mpr (Real.log_neg (by positivity) (by linarith))
  have hnR : (2:ℝ) ≤ Fintype.card P := by exact_mod_cast hn
  have hn0 : (0:ℝ)<Fintype.card P := by linarith
  have hC0 : 0 ≤ C := (logAverage_nonneg u hn).trans hC
  have ha : (A.card : ℝ) ≤ Fintype.card P := by exact_mod_cast Finset.card_le_univ A
  have ha0 : (0:ℝ) ≤ A.card := Nat.cast_nonneg _
  have hsum := logAverage_sum_bound u C hn hC
  have hpoint : ∀ x y : P, (if x∈A ∧ y∈A ∧ x≠y then T else 0) ≤ logCost u x y := by
    intro x y
    split_ifs with h
    · exact log_cost_close u hu z r hr hr2 x y (Finset.mem_filter.mp h.1).2
        (Finset.mem_filter.mp h.2.1).2 h.2.2
    · exact logCost_nonneg _ _ _
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun x _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun y _ => hpoint x y))
  have heq : (∑ x : P, ∑ y : P, if x∈A ∧ y∈A ∧ x≠y then T else 0) =
      (A.card : ℝ)*((A.card : ℝ)-1)*T := by
    have hrw (x : P) : (∑ y : P, if x∈A ∧ y∈A ∧ x≠y then T else 0) =
        if x∈A then ((A.card : ℝ)-1)*T else 0 := by
      by_cases hx : x∈A
      · simp only [hx,true_and,ite_eq_left]
        have hf : Finset.univ.filter (fun y => y∈A ∧ x≠y)=A.erase x := by
          ext y; simp [ne_comm, and_comm]
        rw [← Finset.sum_filter,hf,Finset.sum_const,Finset.card_erase_of_mem hx,nsmul_eq_mul]
        rw [Nat.cast_sub (Finset.one_le_card.mpr ⟨x,hx⟩),Nat.cast_one]
      · simp [hx]
    simp_rw [hrw]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul]
    ring
  rw [heq] at hs
  have hcub : (A.card : ℝ)^2*T ≤ (Fintype.card P : ℝ)*T+C*(Fintype.card P : ℝ)^2 := by
    have hCT := mul_nonneg hC0 hn0.le
    have hAT := mul_le_mul_of_nonneg_right ha hT.le
    nlinarith
  change ((A.card : ℝ)/(Fintype.card P : ℝ))^2 ≤ 1/(Fintype.card P : ℝ)+C/T
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hn0)).mpr
  apply (mul_le_mul_iff_left₀ hT).mp
  have he : (1/(Fintype.card P : ℝ)+C/T)*(Fintype.card P : ℝ)^2*T =
      (Fintype.card P : ℝ)*T+C*(Fintype.card P : ℝ)^2 := by field_simp [ne_of_gt hn0, ne_of_gt hT]
  rw [he]
  exact hcub

end WeakPinned.Bounded

namespace WeakPinned.Bounded
open Hierarchy Variance Global NumberField MeasureTheory
open scoped BigOperators

lemma weighted_deviation {J : Type u2} [Fintype J] (p f : J → ℝ) (a : ℝ)
    (hp : ∀ j, 0≤ p j) (hs : ∑ j, p j=1) :
    (∑ j, p j*|f j-∑ k, p k*f k|) ≤ 2*∑ j, p j*|f j-a| := by
  have hm : |a-∑ j, p j*f j| ≤ ∑ j, p j*|f j-a| := by
    have he : a-(∑ j,p j*f j) = ∑ j,p j*(a-f j) := by
      simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hs,one_mul]
    rw [he]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul,abs_of_nonneg (hp j),abs_sub_comm]
  calc
    _ ≤ ∑ j, p j*(|f j-a|+|a-∑ k,p k*f k|) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (abs_sub_le (f j) a _) (hp j)
    _ = (∑ j,p j*|f j-a|)+|a-∑ k,p k*f k| := by
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hs,one_mul]
    _ ≤ _ := by linarith

variable {P : Type u3} [Fintype P] [DecidableEq P]

def pairMean (f : P → P → ℝ) : ℝ := ∑ x, ∑ y, pairProb Finset.univ x y * f x y

lemma pairWeight_nonneg (hn : 2≤ Fintype.card P) (x y : P) : 0 ≤ pairProb Finset.univ x y := by
  have hn' : (2:ℝ)≤ Fintype.card P := by exact_mod_cast hn
  simp only [pairProb,Finset.mem_univ,true_and,Finset.card_univ]
  split_ifs
  · exact div_nonneg zero_le_one (mul_nonneg (by positivity) (by linarith))
  · exact le_rfl

lemma pairMean_one (hn : 2≤ Fintype.card P) : pairMean (fun _ _ : P => 1)=1 := by
  simp only [pairMean,mul_one,sum_pairProb Finset.univ (by simpa using hn)]
  apply sum_prob
  exact Finset.card_pos.mp (by simpa using (show 0<Fintype.card P by omega))

lemma pairMean_mono (hn : 2≤ Fintype.card P) {f g : P → P → ℝ}
    (h : ∀ x y, x≠y → f x y≤ g x y) : pairMean f≤ pairMean g := by
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  by_cases hxy : x=y
  · subst y; simp [pairProb]
  · exact mul_le_mul_of_nonneg_left (h x y hxy) (pairWeight_nonneg hn x y)

lemma pairMean_add (f g : P → P → ℝ) : pairMean (fun x y => f x y+g x y)=pairMean f+pairMean g := by
  simp only [pairMean,mul_add,Finset.sum_add_distrib]

lemma pairMean_mul (c : ℝ) (f : P → P → ℝ) : pairMean (fun x y => c*f x y)=c*pairMean f := by
  simp only [pairMean,Finset.mul_sum]; congr 1; funext x
  apply Finset.sum_congr rfl; intro y _; ring

lemma pairMean_left (hn : 2≤ Fintype.card P) (f : P → ℝ) :
    pairMean (fun x _ => f x)=∑ x, prob Finset.univ x*f x := by
  simp only [pairMean,← Finset.sum_mul,sum_pairProb Finset.univ (by simpa using hn)]

lemma pairMean_right (hn : 2≤ Fintype.card P) (f : P → ℝ) :
    pairMean (fun _ y => f y)=∑ y, prob Finset.univ y*f y := by
  rw [pairMean,Finset.sum_comm]
  simp_rw [pairProb_symm Finset.univ _ _,← Finset.sum_mul,sum_pairProb Finset.univ (by simpa using hn)]

lemma pairMean_deviation (hn : 2≤ Fintype.card P) (f : P → P → ℝ) (a : ℝ) :
    pairMean (fun x y => |f x y-pairMean f|)≤2*pairMean (fun x y => |f x y-a|) := by
  have h := weighted_deviation (fun z : P×P => pairProb Finset.univ z.1 z.2)
    (fun z => f z.1 z.2) a (fun z => pairWeight_nonneg hn z.1 z.2)
    (by simpa only [Fintype.sum_prod_type,pairMean,mul_one] using pairMean_one (P:=P) hn)
  simpa only [Fintype.sum_prod_type,pairMean] using h

lemma pairMean_overlap (d : Depth P) (_hn : 2≤ Fintype.card P) :
    pairMean (weightedOverlap d.mass)=weightedIntegral d.mass (pairCell Finset.univ) := by
  exact (weighted_pair d.mass (pairProb Finset.univ)).symm

lemma depth_center_bound (d : Depth P) (hn : 2≤ Fintype.card P) :
    pairMean (fun x y => |d.value x y-d.M|) ≤ weightedIntegral d.mass (pairCell Finset.univ)+
      2*(∑ x, prob Finset.univ x*d.potential x) := by
  calc
    _ ≤ pairMean (fun x y => weightedOverlap d.mass x y+d.potential x+d.potential y) := by
      apply pairMean_mono hn
      intro x y hxy
      rw [show weightedOverlap d.mass x y=d.overlapLength x y hxy from d.mass_overlap hn x y hxy,
        d.depth_identity hn x y hxy]
      have hL := d.overlapLength_nonneg x y hxy
      have hx := d.potential_nonneg x
      have hy := d.potential_nonneg y
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    _ = _ := by rw [pairMean_add,pairMean_add,pairMean_overlap d hn,pairMean_left hn,pairMean_right hn]; ring

end WeakPinned.Bounded

namespace WeakPinned.Bounded
open Hierarchy Variance Global NumberField MeasureTheory
open scoped BigOperators
variable {P : Type u4} [Fintype P] [DecidableEq P]

def singleScale (d : Depth P) : ℝ :=
  weightedIntegral d.mass (pairCell Finset.univ)+∑ x, prob Finset.univ x*d.potential x

lemma singleScale_nonneg (d : Depth P) : 0 ≤ singleScale d := by
  refine add_nonneg (Finset.sum_nonneg (fun C _ => mul_nonneg (d.mass_nonneg C) (pairCell_nonneg _ _))) ?_
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg _ (d.potential_nonneg x)
  simp only [prob,Finset.mem_univ,ite_true]; positivity

lemma scaleEval_eq (d d' : Depth P) : scaleEval d d'=singleScale d+singleScale d' := by
  simp only [scaleEval,singleScale,massEval,potentialEval,mul_add,Finset.sum_add_distrib]; ring

lemma singleScale_le_left (d d' : Depth P) : singleScale d≤ scaleEval d d' := by
  rw [scaleEval_eq]; exact le_add_of_nonneg_right (singleScale_nonneg d')

lemma singleScale_le_right (d d' : Depth P) : singleScale d'≤ scaleEval d d' := by
  rw [scaleEval_eq]; exact le_add_of_nonneg_left (singleScale_nonneg d)

def rawDepth (u : P → ℂ) (x y : P) : ℝ := -Real.log ‖u x-u y‖
def pairGridError (u : P → ℂ) (ω : Grid.FullSample) (x y : P) : ℝ :=
  if x=y then 0 else |Grid.error ω (u x) (u y)|

lemma raw_center_grid_bound (u : P → ℂ) (d : Depth P) (ω : Grid.FullSample)
    (hn : 2≤ Fintype.card P) (hd : ∀ x y, x≠y → d.value x y=Grid.depth ω (u x) (u y)) :
    pairMean (fun x y => |rawDepth u x y-pairMean (rawDepth u)|) ≤
      4*singleScale d+2*pairMean (pairGridError u ω) := by
  have h1 := pairMean_deviation hn (rawDepth u) d.M
  have h2 : pairMean (fun x y => |rawDepth u x y-d.M|) ≤
      pairMean (fun x y => |d.value x y-d.M|)+pairMean (pairGridError u ω) := by
    rw [← pairMean_add]
    apply pairMean_mono hn
    intro x y hxy
    simp only [pairGridError,ite_eq_right hxy]
    have he : rawDepth u x y-d.M=(d.value x y-d.M)-Grid.error ω (u x) (u y) := by
      rw [hd x y hxy]; simp only [rawDepth,Grid.error]; ring
    rw [he]
    exact abs_sub _ _
  have h3 := depth_center_bound d hn
  have hL : 0≤ weightedIntegral d.mass (pairCell Finset.univ) :=
    Finset.sum_nonneg (fun C _ => mul_nonneg (d.mass_nonneg C) (pairCell_nonneg _ _))
  unfold singleScale
  linarith

lemma pairGridError_integrable (u : P → ℂ) (hu : Function.Injective u) :
    Integrable (fun ω => pairMean (pairGridError u ω)) Grid.fullLaw := by
  apply integrable_finsetSum
  intro x _
  apply integrable_finsetSum
  intro y _
  by_cases hxy : x=y
  · simp only [pairGridError,hxy,ite_true,mul_zero]; exact integrable_zero _ _ _
  · simpa only [pairGridError,ite_eq_right hxy] using
      ((Grid.error_integrable_full (hu.ne hxy)).abs.const_mul (pairProb Finset.univ x y))

lemma mean_pairGridError (u : P → ℂ) (hu : Function.Injective u) (hn : 2≤ Fintype.card P) :
    (∫ ω, pairMean (pairGridError u ω) ∂ Grid.fullLaw)≤4 := by
  have hi (x y : P) : Integrable (fun ω => pairProb Finset.univ x y*pairGridError u ω x y) Grid.fullLaw := by
    by_cases hxy : x=y
    · simp only [pairGridError,hxy,ite_true,mul_zero]; exact integrable_zero _ _ _
    · simpa only [pairGridError,ite_eq_right hxy] using
        ((Grid.error_integrable_full (hu.ne hxy)).abs.const_mul (pairProb Finset.univ x y))
  simp only [pairMean]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hi x y))]
  simp_rw [integral_finsetSum _ (fun y _ => hi _ y),integral_const_mul]
  calc
    _ ≤ ∑ x,∑ y,pairProb Finset.univ x y*4 := by
      apply Finset.sum_le_sum; intro x _
      apply Finset.sum_le_sum; intro y _
      apply mul_le_mul_of_nonneg_left _ (pairWeight_nonneg hn x y)
      by_cases hxy : x=y
      · simp only [pairGridError,hxy,ite_true,integral_zero]; norm_num
      · simpa only [pairGridError,ite_eq_right hxy] using Grid.mean_abs_error_full (hu.ne hxy)
    _ = 4 := by
      have h := pairMean_one (P:=P) hn
      simp only [pairMean,mul_one] at h
      simp only [← Finset.sum_mul,h,one_mul]

variable {K : Type u5} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

omit [NumberField K] in
include h₁ h₂ in
lemma arch_log_center_bound (hn : 2≤ Fintype.card P) (v : InfinitePlace K) :
    pairMean (fun x y => |rawDepth (fun x => v.embedding (Z₁ x)) x y-
      pairMean (rawDepth (fun x => v.embedding (Z₁ x)))|) ≤ 4*archMean Z₁ Z₂ scaleEval v+8 := by
  let u : P → ℂ := fun x => v.embedding (Z₁ x)
  let L := pairMean (fun x y => |rawDepth u x y-pairMean (rawDepth u)|)
  have hu : Function.Injective u := v.embedding.injective.comp h₁
  have he := mean_pairGridError u hu hn
  have hbound : ∀ᵐ ω ∂ Grid.fullLaw, L≤4*scaleEval (arch Z₁ v ω) (arch Z₂ v ω)+2*pairMean (pairGridError u ω) := by
    filter_upwards [good_ae Z₁ h₁ v] with ω hgood
    have h := raw_center_grid_bound u (arch Z₁ v ω) ω hn (fun x y hxy => by simp [arch,hgood,hxy,u])
    have hs := singleScale_le_left (arch Z₁ v ω) (arch Z₂ v ω)
    dsimp only [L]
    linarith
  have hh := integral_mono_ae (integrable_const L)
    (((integrable_scaleEval Z₁ Z₂ h₁ h₂ hn v).const_mul 4).add ((pairGridError_integrable u hu).const_mul 2)) hbound
  simp only [Pi.add_apply] at hh
  rw [integral_add ((integrable_scaleEval Z₁ Z₂ h₁ h₂ hn v).const_mul 4)
    ((pairGridError_integrable u hu).const_mul 2),integral_const_mul,integral_const_mul] at hh
  simp only [integral_const,MeasureTheory.probReal_univ,one_smul] at hh
  change L≤4*archMean Z₁ Z₂ scaleEval v+8
  change L≤4*archMean Z₁ Z₂ scaleEval v+2*(∫ ω,pairMean (pairGridError u ω) ∂ Grid.fullLaw) at hh
  linarith

end WeakPinned.Bounded

namespace WeakPinned.Bounded
open Variance
variable {P : Type u6} [Fintype P] [DecidableEq P]

def logNormalize (u : P → ℂ) (x : P) : ℂ := (Real.exp (pairMean (rawDepth u)) : ℂ)*u x

lemma logNormalize_injective (u : P → ℂ) (hu : Function.Injective u) :
    Function.Injective (logNormalize u) := by
  intro x y h
  apply hu
  exact mul_left_cancel₀ (by exact_mod_cast (Real.exp_ne_zero (pairMean (rawDepth u)))) h

lemma logAverage_pairMean (u : P → ℂ) :
    logAverage u=pairMean (fun x y => |Real.log ‖u x-u y‖|) := by
  unfold logAverage pairMean
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  by_cases hxy : x=y
  · simp [pairProb,logCost,hxy]
  · simp [pairProb,logCost,hxy,div_eq_mul_inv,mul_comm]

lemma logNormalize_log (u : P → ℂ) (hu : Function.Injective u) (x y : P) (hxy : x≠y) :
    Real.log ‖logNormalize u x-logNormalize u y‖=pairMean (rawDepth u)+Real.log ‖u x-u y‖ := by
  have hz : ‖u x-u y‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hu.ne hxy))
  simp only [logNormalize,← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rw [Real.log_mul (Real.exp_ne_zero _) hz,Real.log_exp]

lemma logNormalize_bound (u : P → ℂ) (hu : Function.Injective u) (hn : 2≤Fintype.card P) :
    logAverage (logNormalize u)=pairMean (fun x y => |rawDepth u x y-pairMean (rawDepth u)|) := by
  rw [logAverage_pairMean]
  apply le_antisymm
  all_goals
    apply pairMean_mono hn
    intro x y hxy
    rw [logNormalize_log u hu x y hxy]
    have he : |pairMean (rawDepth u)+Real.log ‖u x-u y‖|=|rawDepth u x y-pairMean (rawDepth u)| := by
      rw [← abs_neg]; congr 1; unfold rawDepth; ring
    rw [he]

lemma logAverage_translate (u : P → ℂ) (b : ℂ) : logAverage (fun x => u x+b)=logAverage u := by
  simp only [logAverage,logCost,add_sub_add_right_eq_sub]

end WeakPinned.Bounded

end
end

end OAI
