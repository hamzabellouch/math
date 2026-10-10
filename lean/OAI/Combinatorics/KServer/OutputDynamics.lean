import Mathlib
import OAI.Combinatorics.KServer.Allocation

namespace OAI

/- The two output formulas, finite-star algebra and static cap-proportion feasibility. -/


noncomputable section
open Finset
open scoped BigOperators
namespace KServer.OutputDynamics
variable {I : Type*} [Fintype I]

def variation (x y : I → ℝ) : ℝ := ∑ i, |x i - y i|
def excess (d : I → ℝ) (q : ℝ) : ℝ := max ((∑ i, d i) - q) 0

def holesI (R : ℝ) (a : I → ℝ) : I → ℝ := fun i => R * a i
def outputI (d : I → ℝ) (q : ℝ) (a : I → ℝ) : I → ℝ :=
  fun i => d i - holesI (excess d q) a i

lemma variation_nonneg (x y : I → ℝ) : 0 ≤ variation x y :=
  sum_nonneg fun _ _ => abs_nonneg _

lemma variation_triangle (x y z : I → ℝ) : variation x z ≤ variation x y + variation y z := by
  rw [variation, variation, variation, ← sum_add_distrib]
  exact sum_le_sum fun i _ => abs_sub_le (x i) (y i) (z i)

lemma variation_sum (x y : I → ℝ) : |(∑ i, x i) - ∑ i, y i| ≤ variation x y := by
  rw [← sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

lemma positive_part_lipschitz (x y : ℝ) : |max x 0 - max y 0| ≤ |x - y| := by
  exact abs_max_sub_max_le_abs x y 0

lemma excess_lipschitz (d e : I → ℝ) (q p : ℝ) :
    |excess d q - excess e p| ≤ variation d e + |q - p| := by
  apply (positive_part_lipschitz _ _).trans
  calc |((∑ i, d i) - q) - ((∑ i, e i) - p)| =
      |((∑ i, d i) - ∑ i, e i) + (p - q)| := by congr 1; ring
    _ ≤ |(∑ i, d i) - ∑ i, e i| + |p - q| := abs_add_le _ _
    _ ≤ variation d e + |q - p| := by rw [abs_sub_comm p q]; exact add_le_add (variation_sum d e) (le_refl _)

lemma excess_nonneg (d : I → ℝ) (q : ℝ) : 0 ≤ excess d q := le_max_right _ _

omit [Fintype I] in
lemma holesI_nonneg {R : ℝ} {a : I → ℝ} (hR : 0 ≤ R) (ha : ∀ i, 0 ≤ a i) :
    ∀ i, 0 ≤ holesI R a i := fun i => mul_nonneg hR (ha i)

lemma holesI_sum {a : I → ℝ} (ha : ∑ i, a i = 1) (R : ℝ) :
    ∑ i, holesI R a i = R := by simp [holesI, ← mul_sum, ha]

lemma holesI_movement {R R' : ℝ} {a a' : I → ℝ} (hR' : 0 ≤ R')
    (ha : ∀ i, 0 ≤ a i) (hsa : ∑ i, a i = 1) :
    variation (holesI R' a') (holesI R a) ≤ |R' - R| + R' * variation a' a := by
  calc variation (holesI R' a') (holesI R a) ≤
      ∑ i, (R' * |a' i - a i| + |R' - R| * a i) := by
        apply sum_le_sum
        intro i _
        change |R' * a' i - R * a i| ≤ _
        calc _ = |R' * (a' i - a i) + (R' - R) * a i| := by congr 1; ring
          _ ≤ |R' * (a' i - a i)| + |(R' - R) * a i| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hR', abs_of_nonneg (ha i)]
    _ = _ := by rw [sum_add_distrib, ← mul_sum, ← mul_sum, hsa, mul_one]; unfold variation; ring

lemma outputI_budget {a : I → ℝ} (ha : ∑ i, a i = 1) (d : I → ℝ) (q : ℝ) :
    ∑ i, outputI d q a i = min (∑ i, d i) q := by
  unfold outputI
  rw [sum_sub_distrib, holesI_sum ha]
  unfold excess
  by_cases h : (∑ i, d i) ≤ q
  · rw [max_eq_right (by linarith), min_eq_left h]; ring
  · rw [max_eq_left (by linarith), min_eq_right (le_of_not_ge h)]; ring

lemma hole_bound {n B f b : I → ℝ} {β e q : ℝ}
    (hp : (∑ i, (n i - β * B i + f i)) ≤ q)
    (hc : (∑ i, (b i - f i)) ≤ e) (hβ : 0 ≤ β) (he : 0 ≤ e)
    (hB : ∀ i, 0 ≤ B i) :
    excess (fun i => n i + b i) q ≤ β * (∑ i, B i) + e := by
  apply max_le
  · have hi : (∑ i, (n i + b i)) - q ≤
        β * (∑ i, B i) + ∑ i, (b i - f i) := by
      have hs : (∑ i, (n i + b i)) - (∑ i, (n i - β * B i + f i)) =
          β * (∑ i, B i) + ∑ i, (b i - f i) := by
        rw [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
        apply sum_congr rfl; intro i _; ring
      linarith
    linarith
  · exact add_nonneg (mul_nonneg hβ (sum_nonneg fun i _ => hB i)) he

/-- Rule I at a regular coordinate. This includes S=0 without division. -/
lemma regular_hole {S R β βi e η B a : ℝ}
    (hS : 0 ≤ S) (hR : 0 ≤ R) (he : 0 ≤ e) (hB : 0 ≤ B)
    (ha : 0 ≤ a) (_hη : 0 ≤ 1 + η) (hβ : 0 ≤ β) (hβi : 0 ≤ βi)
    (hr : R ≤ β * S + e) (hp : S * a ≤ (1 + η) * B)
    (hroom : (β * S + e) * (1 + η) ≤ βi * S)
    (hzero : S = 0 → e = 0) : R * a ≤ βi * B := by
  by_cases hs : S = 0
  · have he0 := hzero hs
    have hr0 : R = 0 := by rw [hs, he0] at hr; nlinarith
    rw [hr0, zero_mul]
    exact mul_nonneg hβi hB
  · have hsp : 0 < S := lt_of_le_of_ne hS (Ne.symm hs)
    have h1 := mul_le_mul_of_nonneg_left hp (add_nonneg (mul_nonneg hβ hS) he)
    have h2 := mul_le_mul_of_nonneg_right hroom hB
    have h3 := mul_le_mul_of_nonneg_right hr ha
    nlinarith

lemma dominant_hole {S R β βi e η B a : ℝ}
    (he : 0 ≤ e) (hB : 0 ≤ B) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hβ : 0 ≤ β)
    (hr : R ≤ β * S + e) (hp : S * a ≤ (1 + η) * B)
    (hroom : β * (1 + η) ≤ βi) : R * a ≤ βi * B + e := by
  have h1 := mul_le_mul_of_nonneg_right hr ha
  have h2 := mul_le_mul_of_nonneg_left hp hβ
  have h3 := mul_le_mul_of_nonneg_right hroom hB
  have h4 := mul_le_mul_of_nonneg_left ha1 he
  nlinarith

/-- The error margin used on regular children, including zero core mass. -/
lemma regular_parameter_room {S β βi e η g : ℝ}
    (hS : 0 ≤ S) (he : 0 ≤ e) (hη : η ≤ 1)
    (hgap : β + g ≤ βi) (hηgap : β * η ≤ g / 2)
    (herr : 4 * e ≤ g * S) : (β * S + e) * (1 + η) ≤ βi * S := by
  have hp := mul_le_mul_of_nonneg_right hηgap hS
  have hq := mul_le_mul_of_nonneg_right hgap hS
  have hr := mul_le_mul_of_nonneg_left hη he
  nlinarith

/-- Literal regular-coordinate lower bound for Rule I, and its upper cap. -/
lemma outputI_regular {n B f b a η βi : I → ℝ} {β e q : ℝ}
    (hp : (∑ i, (n i - β * B i + f i)) ≤ q)
    (hc : (∑ i, (b i - f i)) ≤ e) (hβ : 0 ≤ β) (he : 0 ≤ e)
    (hB : ∀ i, 0 ≤ B i) (ha : ∀ i, 0 ≤ a i)
    (hprop : ∀ i, (∑ j, B j) * a i ≤ (1 + η i) * B i)
    (hzero : (∑ i, B i) = 0 → e = 0)
    (i : I) (hβi : 0 ≤ βi i) (hη : 0 ≤ 1 + η i)
    (hroom : (β * (∑ j, B j) + e) * (1 + η i) ≤ βi i * (∑ j, B j))
    (fc : ℝ) (hfc : fc ≤ b i) :
    n i - βi i * B i + fc ≤ outputI (fun j => n j + b j) q a i ∧
      outputI (fun j => n j + b j) q a i ≤ n i + b i := by
  have hr := hole_bound hp hc hβ he hB
  have hh := regular_hole (sum_nonneg fun j _ => hB j) (excess_nonneg _ _)
    he (hB i) (ha i) hη hβ hβi hr (hprop i) hroom hzero
  have hn := holesI_nonneg (excess_nonneg (fun j => n j + b j) q) ha i
  unfold outputI holesI at *
  constructor <;> dsimp at * <;> linarith

lemma outputI_dominant {n B f b a η βi : I → ℝ} {β e q : ℝ}
    (hp : (∑ i, (n i - β * B i + f i)) ≤ q)
    (hc : (∑ i, (b i - f i)) ≤ e) (hβ : 0 ≤ β) (he : 0 ≤ e)
    (hB : ∀ i, 0 ≤ B i) (ha : ∀ i, 0 ≤ a i) (has : ∑ i, a i = 1)
    (hprop : ∀ i, (∑ j, B j) * a i ≤ (1 + η i) * B i)
    (o : I) (hroom : β * (1 + η o) ≤ βi o)
    (fc : ℝ) (hfc : fc ≤ b o - e) :
    n o - βi o * B o + fc ≤ outputI (fun j => n j + b j) q a o ∧
      outputI (fun j => n j + b j) q a o ≤ n o + b o := by
  have ha1 : a o ≤ 1 := by
    rw [← has]
    exact single_le_sum (fun j _ => ha j) (mem_univ o)
  have hh := dominant_hole he (hB o) (ha o) ha1 hβ
    (hole_bound hp hc hβ he hB) (hprop o) hroom
  have hn := holesI_nonneg (excess_nonneg (fun j => n j + b j) q) ha o
  unfold outputI holesI at *
  constructor <;> dsimp at * <;> linarith

/-! Rule II: the finite type I here indexes sides only, with the dominant
coordinate stored separately. Thus the formulation includes an empty side set. -/
def sideOutput (d w : I → ℝ) (D : ℝ) : I → ℝ := fun i => d i - D * w i
def dominantOutput (do_ q : ℝ) (d w : I → ℝ) (D : ℝ) : ℝ :=
  min do_ (q - ∑ i, sideOutput d w D i)
def dominantHole (R : ℝ) (ω : I → ℝ) : ℝ := max (R - ∑ i, ω i) 0

def totalExcess (do_ : ℝ) (d : I → ℝ) (q : ℝ) : ℝ :=
  max (do_ + (∑ i, d i) - q) 0

lemma dominant_hole_identity {do_ q D : ℝ} {d w : I → ℝ}
    (hD : 0 ≤ D) (hw : ∀ i, 0 ≤ w i) :
    do_ - dominantOutput do_ q d w D =
      dominantHole (totalExcess do_ d q) (fun i => D * w i) := by
  have hW : 0 ≤ ∑ i, D * w i := sum_nonneg fun i _ => mul_nonneg hD (hw i)
  have hs : (∑ i, sideOutput d w D i) = (∑ i, d i) - ∑ i, D * w i := by
    simp only [sideOutput, sum_sub_distrib]
  unfold dominantOutput dominantHole totalExcess
  rw [hs]
  have hsub (a b : ℝ) : a - min a b = max 0 (a - b) := by
    by_cases h : a ≤ b
    · rw [min_eq_left h, max_eq_left (by linarith)]; ring
    · rw [min_eq_right (le_of_not_ge h), max_eq_right (by linarith)]
  rw [hsub, max_comm (0 : ℝ)]
  by_cases hr : 0 ≤ do_ + (∑ i, d i) - q
  · rw [max_eq_left hr]
    congr 1
    ring
  · have he : do_ + (∑ i, d i) - q ≤ 0 := le_of_not_ge hr
    rw [max_eq_right he, max_eq_right (show do_ - (q - ((∑ i, d i) - ∑ i, D * w i)) ≤ 0 by linarith),
      max_eq_right (show (0 : ℝ) - (∑ i, D * w i) ≤ 0 by linarith)]

lemma holesII_sum {R : ℝ} {ω : I → ℝ} (_hω : ∀ i, 0 ≤ ω i) :
    dominantHole R ω + (∑ i, ω i) = max R (∑ i, ω i) := by
  unfold dominantHole
  rw [← max_add_add_right]
  congr 1 <;> ring

/-- Feasibility, with exactly the parent lower bound, regular flex caps,
side-proportion inequalities and dominant parameter slack used in §05. -/
lemma outputII_feasibility {n B f fc b w βi θ z : I → ℝ}
    {no Bo fo fco bo β βo D q : ℝ}
    (hD : 0 ≤ D) (hw : ∀ i, 0 ≤ w i) (_hB : ∀ i, 0 ≤ B i)
    (hβo : 0 ≤ βo) (hBo : 0 ≤ Bo)
    (hlcap : ∀ i, fc i ≤ b i) (hucap : ∀ i, b i ≤ f i)
    (hdomcap : fco ≤ bo)
    (hparent : no - β * Bo + fo + (∑ i, (n i - β * B i + f i)) ≤ q)
    (hupper : ∀ i, D * w i ≤ βi i * B i)
    (hlower : ∀ i, β * B i - D * θ i * z i ≤ D * w i)
    (hslack : D * (∑ i, θ i * z i) ≤
      (no - β * Bo + fo) - (no - βo * Bo + fco)) :
    (∀ i, n i - βi i * B i + fc i ≤ sideOutput (fun j => n j + b j) w D i ∧
       sideOutput (fun j => n j + b j) w D i ≤ n i + b i) ∧
    (no - βo * Bo + fco ≤ dominantOutput (no + bo) q (fun j => n j + b j) w D ∧
       dominantOutput (no + bo) q (fun j => n j + b j) w D ≤ no + bo) ∧
    dominantOutput (no + bo) q (fun j => n j + b j) w D +
       (∑ i, sideOutput (fun j => n j + b j) w D i) ≤ q := by
  have hside : ∀ i, n i - βi i * B i + fc i ≤ sideOutput (fun j => n j + b j) w D i ∧
       sideOutput (fun j => n j + b j) w D i ≤ n i + b i := by
    intro i
    have := hlcap i
    have := hupper i
    have := mul_nonneg hD (hw i)
    constructor <;> dsimp [sideOutput] <;> linarith
  have hs : (∑ i, sideOutput (fun j => n j + b j) w D i) ≤
        (∑ i, (n i - β * B i + f i)) + D * (∑ i, θ i * z i) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro i _
    have := hucap i
    have := hlower i
    dsimp [sideOutput]
    nlinarith
  have hrem : no - βo * Bo + fco ≤
      q - (∑ i, sideOutput (fun j => n j + b j) w D i) := by linarith
  have hdc : no - βo * Bo + fco ≤ no + bo := by
    have := mul_nonneg hβo hBo
    linarith
  refine ⟨hside, ⟨le_min hdc hrem, min_le_left _ _⟩, ?_⟩
  have := min_le_right (no + bo) (q - ∑ i, sideOutput (fun j => n j + b j) w D i)
  unfold dominantOutput
  linarith

lemma dominantHole_lipschitz (R R' : ℝ) (ω ω' : I → ℝ) :
    |dominantHole R' ω' - dominantHole R ω| ≤ |R' - R| + variation ω' ω := by
  apply (positive_part_lipschitz _ _).trans
  calc |(R' - ∑ i, ω' i) - (R - ∑ i, ω i)| =
      |(R' - R) - ((∑ i, ω' i) - ∑ i, ω i)| := by congr 1; ring
    _ ≤ |R' - R| + |(∑ i, ω' i) - ∑ i, ω i| := abs_sub _ _
    _ ≤ _ := add_le_add (le_refl _) (variation_sum _ _)

lemma holesII_movement (R R' : ℝ) (ω ω' : I → ℝ) :
    |dominantHole R' ω' - dominantHole R ω| + variation ω' ω ≤
      |R' - R| + 2 * variation ω' ω := by
  have := dominantHole_lipschitz R R' ω ω'
  linarith

lemma scaled_movement {D D' Cw : ℝ} {w w' : I → ℝ} (hD' : 0 ≤ D')
    (hw : ∀ i, 0 ≤ w i) (hws : (∑ i, w i) ≤ Cw) :
    variation (fun i => D' * w' i) (fun i => D * w i) ≤
      D' * variation w' w + Cw * |D' - D| := by
  calc variation (fun i => D' * w' i) (fun i => D * w i) ≤
      (∑ i, (D' * |w' i - w i| + |D' - D| * w i)) := by
        apply sum_le_sum
        intro i _
        calc |D' * w' i - D * w i| = |D' * (w' i - w i) + (D' - D) * w i| := by congr 1; ring
          _ ≤ |D' * (w' i - w i)| + |(D' - D) * w i| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hD', abs_of_nonneg (hw i)]
    _ = D' * variation w' w + |D' - D| * (∑ i, w i) := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum]; rfl
    _ ≤ _ := by have := mul_le_mul_of_nonneg_left hws (abs_nonneg (D' - D)); nlinarith

lemma output_from_holes_movement (d d' ζ ζ' : I → ℝ) :
    variation (fun i => d' i - ζ' i) (fun i => d i - ζ i) ≤
      variation d' d + variation ζ' ζ := by
  rw [variation, variation, variation, ← sum_add_distrib]
  apply sum_le_sum
  intro i _
  calc |(d' i - ζ' i) - (d i - ζ i)| = |(d' i - d i) - (ζ' i - ζ i)| := by congr 1; ring
    _ ≤ _ := abs_sub _ _

/-- The parent coefficient is genuinely one, independent of degree. -/
lemma outputI_movement {d d' a a' : I → ℝ} {q q' : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hsa : ∑ i, a i = 1) :
    variation (outputI d' q' a') (outputI d q a) ≤
      |q' - q| + 2 * variation d' d + excess d' q' * variation a' a := by
  have ho := output_from_holes_movement d d' (holesI (excess d q) a) (holesI (excess d' q') a')
  have hh := holesI_movement (R := excess d q) (a' := a') (excess_nonneg d' q') ha hsa
  have he := excess_lipschitz d' d q' q
  change variation (outputI d' q' a') (outputI d q a) ≤ _ at ho
  linarith


/-- A star as one dominant coordinate and a (possibly empty) finite side set. -/
def withDominant (x : ℝ) (xs : I → ℝ) : Option I → ℝ
  | none => x
  | some i => xs i

def holesII (R : ℝ) (ω : I → ℝ) : Option I → ℝ :=
  withDominant (dominantHole R ω) ω

def outputII (do_ q : ℝ) (d w : I → ℝ) (D : ℝ) : Option I → ℝ :=
  withDominant (dominantOutput do_ q d w D) (sideOutput d w D)

lemma variation_dominant (x x' : ℝ) (xs xs' : I → ℝ) :
    variation (withDominant x' xs') (withDominant x xs) = |x'-x|+variation xs' xs := by
  simp only [variation,Fintype.sum_option,withDominant]

lemma holesII_vector_sum {R : ℝ} {ω : I → ℝ} (hω : ∀ i, 0 ≤ ω i) :
    (∑ i, holesII R ω i)=max R (∑ i, ω i) := by
  simp only [holesII,Fintype.sum_option,withDominant]
  exact holesII_sum hω

lemma holesII_nonneg (R : ℝ) {ω : I → ℝ} (hω : ∀ i, 0 ≤ ω i) :
    ∀ i, 0 ≤ holesII R ω i := by
  intro i
  cases i with
  | none => exact le_max_right _ _
  | some i => exact hω i

lemma outputII_is_holes {do_ q D : ℝ} {d w : I → ℝ}
    (hD : 0 ≤ D) (hw : ∀ i, 0 ≤ w i) :
    outputII do_ q d w D = fun i => withDominant do_ d i -
      holesII (excess (withDominant do_ d) q) (fun i => D*w i) i := by
  have hr : excess (withDominant do_ d) q=totalExcess do_ d q := by
    simp only [excess,totalExcess,Fintype.sum_option,withDominant]
  funext i
  cases i with
  | none =>
    have hh := dominant_hole_identity (do_ := do_) (q := q) (d := d) hD hw
    simp only [outputII,withDominant,holesII,hr]
    linarith
  | some i => rfl

/-- Literal Rule II, not merely an assumed hole formula; coefficient of parent
movement is exactly one, also for inserted/deleted zero side coordinates. -/
lemma outputII_movement {do_ do' q q' D D' Cw : ℝ} {d d' w w' : I → ℝ}
    (hD : 0 ≤ D) (hD' : 0 ≤ D') (hw : ∀ i, 0 ≤ w i) (hw' : ∀ i, 0 ≤ w' i)
    (hws : (∑ i, w i) ≤ Cw) :
    variation (outputII do' q' d' w' D') (outputII do_ q d w D) ≤
      |q'-q|+2*variation (withDominant do' d') (withDominant do_ d)+
      2*D'*variation w' w+2*Cw*|D'-D| := by
  rw [outputII_is_holes hD' hw',outputII_is_holes hD hw]
  have hh := holesII_movement (excess (withDominant do_ d) q)
    (excess (withDominant do' d') q') (fun i => D*w i) (fun i => D'*w' i)
  have he := excess_lipschitz (withDominant do' d') (withDominant do_ d) q' q
  have hwv := scaled_movement hD' hw hws (w' := w') (D := D)
  have hv : variation (fun i => withDominant do' d' i -
        holesII (excess (withDominant do' d') q') (fun i => D'*w' i) i)
      (fun i => withDominant do_ d i -
        holesII (excess (withDominant do_ d) q) (fun i => D*w i) i) ≤
      variation (withDominant do' d') (withDominant do_ d) +
      |dominantHole (excess (withDominant do' d') q') (fun i => D'*w' i)-
        dominantHole (excess (withDominant do_ d) q) (fun i => D*w i)|+
      variation (fun i => D'*w' i) (fun i => D*w i) := by
    have h := output_from_holes_movement (withDominant do_ d) (withDominant do' d')
      (holesII (excess (withDominant do_ d) q) (fun i => D*w i))
      (holesII (excess (withDominant do' d') q') (fun i => D'*w' i))
    simpa only [holesII,variation_dominant,add_assoc] using h
  linarith

lemma variation_le_mass {z z' : I → ℝ} (hz : ∀ i, 0 ≤ z i) (hz' : ∀ i, 0 ≤ z' i) :
    variation z' z ≤ (∑ i, z' i)+(∑ i, z i) := by
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro i _
  apply abs_sub_le_iff.mpr
  constructor <;> linarith [hz i,hz' i]

/-- A switch uses the actual old rule, without evaluating the unused rule at the
old inputs. These are the full downcrossing/upcrossing estimates of §05. -/
lemma downcross_movement {R R' D' Cr Cw : ℝ} {a : Option I → ℝ} {w' : I → ℝ}
    (hR : 0 ≤ R) (hR' : 0 ≤ R') (hD' : 0 ≤ D') (ha : ∀ i, 0 ≤ a i)
    (hsa : ∑ i, a i=1) (hw' : ∀ i, 0 ≤ w' i) (hws : (∑ i, w' i) ≤ Cw)
    (hr : R' ≤ Cr*D') :
    variation (holesII R' (fun i => D'*w' i)) (holesI R a) ≤
      |R'-R|+(2*Cr+Cw)*D' := by
  have hws' : (∑ i, D'*w' i) ≤ Cw*D' := by
    rw [←mul_sum]; nlinarith [mul_le_mul_of_nonneg_left hws hD']
  have hmax : max R' (∑ i, D'*w' i) ≤ R'+Cw*D' := by
    apply max_le
    · have hnn : 0 ≤ Cw := le_trans (sum_nonneg fun i _ => hw' i) hws
      nlinarith
    · linarith
  have hv := variation_le_mass (holesI_nonneg hR ha)
    (holesII_nonneg R' (fun i => mul_nonneg hD' (hw' i)))
  rw [holesI_sum hsa,holesII_vector_sum (fun i => mul_nonneg hD' (hw' i))] at hv
  have h1 := neg_le_abs (R'-R)
  nlinarith

lemma upcross_movement {R R' D D' S' Cr Cw : ℝ} {a' : Option I → ℝ} {w : I → ℝ}
    (hR : 0 ≤ R) (hR' : 0 ≤ R') (hD : 0 ≤ D) (_hD' : 0 ≤ D')
    (ha' : ∀ i, 0 ≤ a' i) (hsa : ∑ i, a' i=1)
    (hw : ∀ i, 0 ≤ w i) (hws : (∑ i, w i) ≤ Cw)
    (hr : R' ≤ Cr*S') (hreg : D' ≤ S'/2) :
    variation (holesI R' a') (holesII R (fun i => D*w i)) ≤
      |R'-R|+(2*Cr+Cw/2)*S'+Cw*|D'-D| := by
  have hc : 0 ≤ Cw := le_trans (sum_nonneg fun i _ => hw i) hws
  have hws' : (∑ i, D*w i) ≤ Cw*D := by
    rw [←mul_sum]; nlinarith [mul_le_mul_of_nonneg_left hws hD]
  have hmax : max R (∑ i, D*w i) ≤ R+Cw*D := by
    apply max_le
    · nlinarith
    · linarith
  have hv := variation_le_mass (holesII_nonneg R (fun i => mul_nonneg hD (hw i)))
    (holesI_nonneg hR' ha')
  rw [holesI_sum hsa,holesII_vector_sum (fun i => mul_nonneg hD (hw i))] at hv
  have h1 := neg_le_abs (R'-R)
  have h2 := mul_le_mul_of_nonneg_left (neg_le_abs (D'-D)) hc
  have h3 := mul_le_mul_of_nonneg_left hreg hc
  nlinarith

end KServer.OutputDynamics
end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeldWeights

/-- Literal regular gap weight; zero coordinates are harmless placeholders. -/
def regular (A a : ℝ) : ℝ := 1+max 0 (Real.log (A/a))

lemma regular_one (A a : ℝ) : 1 ≤ regular A a := by
  unfold regular; linarith [le_max_left (0:ℝ) (Real.log (A/a))]

lemma regular_log (A a : ℝ) : 1+Real.log (A/a) ≤ regular A a := by
  unfold regular; exact add_le_add le_rfl (le_max_right (0:ℝ) (Real.log (A/a)))

lemma regular_eq {A a : ℝ} (ha : 0<a) (hA : a≤A) :
    regular A a=1+Real.log (A/a) := by
  exact congrArg (fun x : ℝ => 1+x) (max_eq_right (Real.log_nonneg ((one_le_div ha).mpr hA)))

lemma regular_exp {A a : ℝ} (hA : 0<A) (ha : 0<a) :
    Real.exp (-regular A a) ≤ a/A := by
  have h : Real.log (A/a) ≤ regular A a := by linarith [regular_log A a]
  have he := Real.exp_le_exp.mpr (neg_le_neg h)
  rw [Real.exp_neg (Real.log (A/a)),Real.exp_log (div_pos hA ha)] at he
  simpa only [inv_div] using he

lemma regular_upper {A a k : ℝ} (hk : 1≤k) (hA : 0≤A)
    (hAk : A≤(11/10)*k) (ha : (9/100000:ℝ)≤a) :
    regular A a ≤ 20002*(1+Real.log (k+1)) := by
  have hk0 : 0<k := by linarith
  have ha0 : 0<a := by linarith
  have he : 0≤Real.log (k+1) := Real.log_nonneg (by linarith)
  have hlog : Real.log (A/a) ≤ 20000+Real.log (k+1) := by
    by_cases hAz : A=0
    · simp [hAz]; linarith
    have hA0 : 0<A := lt_of_le_of_ne hA (Ne.symm hAz)
    have hx : A/a ≤ 20000*(k+1) := by
      apply (div_le_iff₀ ha0).mpr
      have hm := mul_le_mul_of_nonneg_left ha (show 0≤20000*(k+1) by positivity)
      nlinarith
    have hl := Real.log_le_log (div_pos hA0 ha0) hx
    rw [Real.log_mul (by norm_num : (20000:ℝ)≠0) (by positivity : k+1≠0)] at hl
    have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<20000)
    linarith
  have hm : max 0 (Real.log (A/a)) ≤ 20000+Real.log (k+1) := max_le (by linarith) hlog
  unfold regular
  nlinarith

lemma log_reciprocal_lower {u : ℝ} (hu : 0<u) (hu1 : u≤1/4) :
    1 ≤ Real.log (1/u) := by
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  have hr : (4:ℝ)≤1/u := (le_div_iff₀ hu).mpr (by linarith)
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<4) hr
  have he : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  rw [he] at hl
  norm_num at h2
  linarith

lemma side_lower {A a u : ℝ} (_hA : 0<A) (ha : 0<a) (hu : 0<u)
    (hu1 : u≤1/4) (has : a≤2*u*A) :
    (1/2:ℝ)*(1+Real.log (1/u)) ≤ regular A a := by
  have hx : 1/(2*u)≤A/a := by
    apply (div_le_div_iff₀ (show 0<2*u by positivity) ha).mpr
    nlinarith
  have hl := Real.log_le_log (by positivity : 0<1/(2*u)) hx
  rw [Real.log_div (by norm_num) (by positivity),Real.log_one,
    Real.log_mul (by norm_num) hu.ne'] at hl
  have hr : Real.log (1/u) = -Real.log u := by simp
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hrec := log_reciprocal_lower hu hu1
  have hr2 : (1/2:ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh; exact hh
  -- The sharper logarithm relation avoids any numerical estimate of e.
  have hrec2 : 2*Real.log 2≤Real.log (1/u) := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<4)
      ((le_div_iff₀ hu).mpr (by linarith) : (4:ℝ)≤1/u)
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have hw := regular_log A a
  rw [hr] at hrec2 ⊢
  linarith

variable {J : Type} [Fintype J]

omit [Fintype J] in
lemma exp_sum {A : ℝ} {a : J → ℝ} (S : Finset J) (hA : 0<A)
    (ha : ∀ i∈S, 0<a i) (hS : (∑ i∈S,a i)≤(101/100)*A) :
    (∑ i∈S, Real.exp (-regular A (a i))) ≤ 2 := by
  have h := sum_le_sum (s:=S) (fun i hi => regular_exp hA (ha i hi))
  rw [←sum_div] at h
  have hh := (div_le_iff₀ hA).mpr hS
  linarith

omit [Fintype J] in
lemma side_exp_sum {A U : ℝ} {a : J → ℝ} (S : Finset J) (hA : 0<A)
    (ha : ∀ i∈S, 0<a i) (hS : (∑ i∈S,a i)≤2*U) :
    (∑ i∈S, Real.exp (-regular A (a i))) ≤ 2*(U/A) := by
  have h := sum_le_sum (s:=S) (fun i hi => regular_exp hA (ha i hi))
  rw [←sum_div] at h
  have hh := div_le_div_of_nonneg_right hS hA.le
  simpa only [mul_div_assoc] using h.trans hh

end KServer.HeldWeights

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CausalSimplex
open AdaptiveMinimization SimplexFamilies AdaptiveAllocation
variable {J R : Type} [Fintype J] [DecidableEq J] [Fintype R]

/-- Current held parameters and raw ranks. The latter are used only for the
initial minimizing selection, never substituted for the affine rank input. -/
structure Input (J R : Type) [Fintype J] where
  data : SimplexFamilies.Data J R
  ranks : J × R → ℝ
  epoch : ℕ

def prepared (old new : SimplexFamilies.Data J R) : SimplexFamilies.Data J R :=
  { old with flags := preparedFlags old.active new.active new.flags }

def prepare (C ell : ℝ) (old new : SimplexFamilies.Data J R)
    (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  (SimplexFamilies.family C ell).update (prepared old new) p
    (∑ i, core (prepared old new) p i) a

def candidate (C ell : ℝ) (old new : SimplexFamilies.Data J R)
    (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  ChangingDomains.transposeSimplex new.active (∑ i, core (prepared old new) p i) (prepare C ell old new p a)

/-- The membership branch totalizes the mathematical rule off its admitted
rank/parameter domain. The ordinary regular/marked lemmas below prove it is
never used on genuine source data. Wholesale steps use the canonical base. -/
def move (C ell : ℝ) (old new : Input J R) (p : J × R → ℝ) (a : J → ℝ) : J → ℝ := by
  classical
  exact if old.epoch = new.epoch then
    if candidate C ell old.data new.data p a ∈ ChangingDomains.simplex new.data.active
      then candidate C ell old.data new.data p a else ChangingDomains.canonical new.data.active
  else ChangingDomains.canonical new.data.active

lemma move_mem (C ell : ℝ) (old new : Input J R) (p : J × R → ℝ) (a : J → ℝ) :
    move C ell old new p a ∈ ChangingDomains.simplex new.data.active := by
  classical
  unfold move
  split_ifs with he hm
  · exact hm
  · exact ChangingDomains.canonical_mem _
  · exact ChangingDomains.canonical_mem _

/-- Only initialization changes the seed; the potential and coefficient are
the exact source primitives already proved affine in the raw ranks. -/
def model (C ell : ℝ) : Family (Input J R) (J × R) J where
  domain d := ChangingDomains.simplex d.data.active
  compact _data := ChangingDomains.simplex_compact _
  seed d := ⟨(SimplexFamilies.family C ell).update d.data d.ranks
    (∑ i, core d.data d.ranks i) (ChangingDomains.canonical d.data.active),
    (SimplexFamilies.family C ell).update_mem _ _ _ _⟩
  offset _ _ := 0
  coefficient d := SimplexFamilies.coefficient C ell d.data
  offset_continuous _ := continuousOn_const
  coefficient_continuous d := SimplexFamilies.coefficient_continuous C ell d.data

lemma model_value (C ell : ℝ) (d : Input J R) (p : J × R → ℝ) (a : J → ℝ) :
    (model C ell).value d p a = (SimplexFamilies.family C ell).value d.data p a := rfl

lemma model_update (C ell : ℝ) (d : Input J R) (p : J × R → ℝ) (c : ℝ) (a : J → ℝ) :
    (model C ell).update d p c a = (SimplexFamilies.family C ell).update d.data p c a := rfl

def transport (C ell : ℝ) : Transport (model (J:=J) (R:=R) C ell) where
  map := move C ell
  mem old new p a _ := move_mem C ell old new p a

variable {Ω : Type} [Fintype Ω]

def mass (d : Input J R) : ℝ := ∑ i, core d.data d.ranks i

def run (C ell : ℝ) (d : ℕ → Ω → Input J R) : ℕ → Ω → J → ℝ :=
  state (model C ell) (transport C ell) d (fun t ω => (d t ω).ranks)
    (fun t ω => mass (d t ω))

omit [Fintype Ω] in
lemma run_mem (C ell : ℝ) (d : ℕ → Ω → Input J R) (t : ℕ) (ω : Ω) :
    run C ell d t ω ∈ ChangingDomains.simplex (d t ω).data.active :=
  state_mem (model C ell) (transport C ell) d (fun t ω => (d t ω).ranks)
    (fun t ω => mass (d t ω)) t ω

omit [Fintype Ω] in
lemma run_initial (C ell : ℝ) (d : ℕ → Ω → Input J R) (ω : Ω) :
    run C ell d 0 ω=(SimplexFamilies.family C ell).update (d 0 ω).data (d 0 ω).ranks
      (mass (d 0 ω)) (ChangingDomains.canonical (d 0 ω).data.active) := rfl

omit [Fintype Ω] in
lemma run_successor (C ell : ℝ) (d : ℕ → Ω → Input J R) (t : ℕ) (ω : Ω) :
    run C ell d (t+1) ω=(SimplexFamilies.family C ell).update (d (t+1) ω).data (d (t+1) ω).ranks
      (mass (d (t+1) ω)) (move C ell (d t ω) (d (t+1) ω) (d (t+1) ω).ranks (run C ell d t ω)) := rfl

omit [Fintype Ω] in
lemma run_adapted (C ell : ℝ) (d : ℕ → Ω → Input J R) (H : ℕ → Ω → ℕ)
    (href : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    (hd : ∀ t ω z, H t ω=H t z → d t ω=d t z) (t : ℕ) (ω z : Ω)
    (he : H t ω=H t z) : run C ell d t ω=run C ell d t z := by
  exact state_adapted _ _ _ _ _ H href hd
    (fun t ω z h => congrArg Input.ranks (hd t ω z h))
    (fun t ω z h => congrArg mass (hd t ω z h)) t ω z he

end KServer.CausalSimplex

namespace KServer.CausalSimplex
open AdaptiveMinimization SimplexFamilies AdaptiveAllocation
variable {J R : Type} [Fintype J] [DecidableEq J] [Fintype R]

lemma candidate_regular (A B : Finset J) (f g : J → R → Bool) (h h' : J → ℝ)
    (hh : ∀ i, 1≤h i) (hh' : ∀ i, 1≤h' i) (C ell ct : ℝ)
    (p : J × R → ℝ) (a : J → ℝ) :
    candidate C ell (regular A f h (fun i => ct*h i/ell) hh)
      (regular B g h' (fun i => ct*h' i/ell) hh') p a=
      regularTransport C ell ct A B g h hh p a := rfl

lemma move_regular {A B : Finset J} (hA : A.Nonempty) (hB : B.Nonempty)
    (f g : J → R → Bool) (h h' : J → ℝ)
    (hh : ∀ i, 1≤h i) (hh' : ∀ i, 1≤h' i)
    {C ell ct ηmax Cexp : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0<ct)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (htail : ∑ i∈A, Real.exp (-h i)≤Cexp)
    (hgap : 2*(25+32*Cexp)*(1+ηmax)<C*ct)
    (p : J × R → ℝ) (hp : ∀ ir, 0≤p ir) (a : J → ℝ)
    (ha : a∈ChangingDomains.simplex A) (r r' : J × R → ℝ) (e : ℕ) :
    move C ell ⟨regular A f h (fun i => ct*h i/ell) hh,r,e⟩
      ⟨regular B g h' (fun i => ct*h' i/ell) hh',r',e⟩ p a=
      regularTransport C ell ct A B g h hh p a := by
  classical
  have hm := regular_transport_mem hA hB g h hh hC hl hc hmax hCexp htail hgap p hp a ha
  unfold move
  dsimp only
  rw [ite_eq_left rfl, candidate_regular]
  exact ite_eq_left hm

/-- The fully specified causal successor is the source's prepared/deleted/
minimized successor on an ordinary unmarked epoch. No policy-existence or
expected drift statement is an assumption. -/
lemma regular_successor {Ω : Type} [Fintype Ω] (d : ℕ → Ω → Input J R)
    (t : ℕ) (ω : Ω) {A B : Finset J} (hA : A.Nonempty) (hB : B.Nonempty)
    (f g : J → R → Bool) (h h' : J → ℝ)
    (hh : ∀ i, 1≤h i) (hh' : ∀ i, 1≤h' i)
    {C ell ct ηmax Cexp : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0<ct)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (htail : ∑ i∈A, Real.exp (-h i)≤Cexp)
    (hgap : 2*(25+32*Cexp)*(1+ηmax)<C*ct)
    (hp : ∀ ir, 0≤(d (t+1) ω).ranks ir)
    (hold : (d t ω).data=regular A f h (fun i => ct*h i/ell) hh)
    (hnew : (d (t+1) ω).data=regular B g h' (fun i => ct*h' i/ell) hh')
    (he : (d t ω).epoch=(d (t+1) ω).epoch) :
    run C ell d (t+1) ω = regularStep C ell ct A B g h h' hh hh'
      (d (t+1) ω).ranks (run C ell d t ω) := by
  have ha := run_mem C ell d t ω
  rw [hold] at ha
  change run C ell d t ω∈ChangingDomains.simplex A at ha
  have hm := move_regular hA hB f g h h' hh hh' hC hl hc hmax hCexp htail hgap
    (d (t+1) ω).ranks hp (run C ell d t ω) ha (d t ω).ranks (d (t+1) ω).ranks (d t ω).epoch
  have eo : d t ω=⟨regular A f h (fun i => ct*h i/ell) hh,(d t ω).ranks,(d t ω).epoch⟩ :=
    congrArg (fun v => (⟨v,(d t ω).ranks,(d t ω).epoch⟩ : Input J R)) hold
  have en : d (t+1) ω=⟨regular B g h' (fun i => ct*h' i/ell) hh',(d (t+1) ω).ranks,(d t ω).epoch⟩ := by
    calc
      d (t+1) ω = ⟨regular B g h' (fun i => ct*h' i/ell) hh',
          (d (t+1) ω).ranks,(d (t+1) ω).epoch⟩ :=
        congrArg (fun v => (⟨v,(d (t+1) ω).ranks,(d (t+1) ω).epoch⟩ : Input J R)) hnew
      _ = _ := by rw [he]
  have hm' : move C ell (d t ω) (d (t+1) ω) (d (t+1) ω).ranks (run C ell d t ω)=
      regularTransport C ell ct A B g h hh (d (t+1) ω).ranks (run C ell d t ω) :=
    (congrArg₂ (fun old new : Input J R => move C ell old new
      (d (t+1) ω).ranks (run C ell d t ω)) eo en).trans hm
  rw [run_successor,hm']
  unfold mass
  rw [hnew]
  rfl

lemma candidate_marked (A B : Finset J) (f g : J → R → Bool) (o : J)
    (h h' : J → ℝ) (u u' : ℝ) (hu : 0<u) (hu1 : u≤1)
    (hu' : 0<u') (hu1' : u'≤1) (hh : ∀ i≠o, 1≤h i) (hh' : ∀ i≠o, 1≤h' i)
    (C ell ct : ℝ) (p : J × R → ℝ) (a : J → ℝ) :
    candidate C ell (marked A f o h (fun i => ct*h i/ell) u hu hu1 hh)
      (marked B g o h' (fun i => ct*h' i/ell) u' hu' hu1' hh') p a=
      markedTransport C ell ct A B g o h u hu hu1 hh p a := rfl

lemma move_marked {A B : Finset J} {o : J} (hoA : o∈A) (hB : B.Nonempty)
    (f g : J → R → Bool) (h h' : J → ℝ) {u u' : ℝ}
    (hu : 0<u) (hu1 : u≤1) (hu' : 0<u') (hu1' : u'≤1)
    (ho : h o=u) (hh : ∀ i≠o, 1≤h i) (hh' : ∀ i≠o, 1≤h' i)
    {C ell ct ηmax Cexp c : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0<ct)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (hsideC : 0<c) (hsideC1 : c≤1)
    (hside : ∀ i∈A, i≠o → c*(1+Real.log (1/u))≤h i)
    (htail : ∑ i∈A.erase o, Real.exp (-h i)≤Cexp*u)
    (hgap : 2*((25*c+2+32*Cexp)/c)*(1+ηmax)<C*ct)
    (p : J × R → ℝ) (hp : ∀ ir, 0≤p ir) (a : J → ℝ)
    (ha : a∈ChangingDomains.simplex A) (r r' : J × R → ℝ) (e : ℕ) :
    move C ell ⟨marked A f o h (fun i => ct*h i/ell) u hu hu1 hh,r,e⟩
      ⟨marked B g o h' (fun i => ct*h' i/ell) u' hu' hu1' hh',r',e⟩ p a=
      markedTransport C ell ct A B g o h u hu hu1 hh p a := by
  classical
  have hm := marked_transport_mem hoA hB g h hu hu1 ho hh hC hl hc hmax hCexp
    hsideC hsideC1 hside htail hgap p hp a ha
  unfold move
  dsimp only
  rw [ite_eq_left rfl, candidate_marked]
  exact ite_eq_left hm

lemma move_wholesale (C ell : ℝ) (old new : Input J R) (p : J × R → ℝ)
    (a : J → ℝ) (he : old.epoch≠new.epoch) :
    move C ell old new p a=ChangingDomains.canonical new.data.active := by
  simp only [move,ite_eq_right he]

lemma marked_successor {Ω : Type} [Fintype Ω] (d : ℕ → Ω → Input J R)
    (t : ℕ) (ω : Ω) {A B : Finset J} {o : J} (hoA : o∈A) (hB : B.Nonempty)
    (f g : J → R → Bool) (h h' : J → ℝ) {u u' : ℝ}
    (hu : 0<u) (hu1 : u≤1) (hu' : 0<u') (hu1' : u'≤1)
    (ho : h o=u) (hh : ∀ i≠o, 1≤h i) (hh' : ∀ i≠o, 1≤h' i)
    {C ell ct ηmax Cexp c : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0<ct)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (hsideC : 0<c) (hsideC1 : c≤1)
    (hside : ∀ i∈A, i≠o → c*(1+Real.log (1/u))≤h i)
    (htail : ∑ i∈A.erase o, Real.exp (-h i)≤Cexp*u)
    (hgap : 2*((25*c+2+32*Cexp)/c)*(1+ηmax)<C*ct)
    (hp : ∀ ir, 0≤(d (t+1) ω).ranks ir)
    (hold : (d t ω).data=marked A f o h (fun i => ct*h i/ell) u hu hu1 hh)
    (hnew : (d (t+1) ω).data=marked B g o h' (fun i => ct*h' i/ell) u' hu' hu1' hh')
    (he : (d t ω).epoch=(d (t+1) ω).epoch) :
    run C ell d (t+1) ω = markedStep C ell ct A B g o h h' u u' hu hu1 hu' hu1' hh hh'
      (d (t+1) ω).ranks (run C ell d t ω) := by
  have ha := run_mem C ell d t ω
  rw [hold] at ha
  change run C ell d t ω∈ChangingDomains.simplex A at ha
  have hm := move_marked hoA hB f g h h' hu hu1 hu' hu1' ho hh hh' hC hl hc hmax hCexp
    hsideC hsideC1 hside htail hgap (d (t+1) ω).ranks hp (run C ell d t ω) ha
    (d t ω).ranks (d (t+1) ω).ranks (d t ω).epoch
  have eo : d t ω=⟨marked A f o h (fun i => ct*h i/ell) u hu hu1 hh,
      (d t ω).ranks,(d t ω).epoch⟩ :=
    congrArg (fun v => (⟨v,(d t ω).ranks,(d t ω).epoch⟩ : Input J R)) hold
  have en : d (t+1) ω=⟨marked B g o h' (fun i => ct*h' i/ell) u' hu' hu1' hh',
      (d (t+1) ω).ranks,(d t ω).epoch⟩ := by
    calc
      d (t+1) ω = ⟨marked B g o h' (fun i => ct*h' i/ell) u' hu' hu1' hh',
          (d (t+1) ω).ranks,(d (t+1) ω).epoch⟩ :=
        congrArg (fun v => (⟨v,(d (t+1) ω).ranks,(d (t+1) ω).epoch⟩ : Input J R)) hnew
      _ = _ := by rw [he]
  have hm' : move C ell (d t ω) (d (t+1) ω) (d (t+1) ω).ranks (run C ell d t ω)=
      markedTransport C ell ct A B g o h u hu hu1 hh (d (t+1) ω).ranks (run C ell d t ω) :=
    (congrArg₂ (fun old new : Input J R => move C ell old new
      (d (t+1) ω).ranks (run C ell d t ω)) eo en).trans hm
  rw [run_successor,hm']
  unfold mass
  rw [hnew]
  rfl

end KServer.CausalSimplex

end

end OAI
