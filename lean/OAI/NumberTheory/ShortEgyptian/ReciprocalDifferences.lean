import OAI.NumberTheory.ShortEgyptian.SecondDerivative

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

noncomputable def reciprocalProduct (as : List ℝ) (x : ℝ) : ℝ :=
  (as.map (fun a => 1 / (x + a))).prod

@[simp] theorem reciprocalProduct_nil (x : ℝ) : reciprocalProduct [] x = 1 := rfl
@[simp] theorem reciprocalProduct_cons (a : ℝ) (as : List ℝ) (x : ℝ) :
    reciprocalProduct (a :: as) x = 1 / (x + a) * reciprocalProduct as x := rfl

theorem reciprocalProduct_shift (as : List ℝ) (x h : ℝ) :
    reciprocalProduct (as.map (· + h)) x = reciprocalProduct as (x + h) := by
  simp only [reciprocalProduct, List.map_map, Function.comp_def]
  congr 2
  funext a
  congr 1
  ring

def expandDifference (h : ℝ) : List ℝ → List (List ℝ)
  | [] => []
  | a :: as => (a :: (a + h) :: as.map (· + h)) ::
      (expandDifference h as).map (a :: ·)

@[simp] theorem expandDifference_length (h : ℝ) (as : List ℝ) :
    (expandDifference h as).length = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simpa only [expandDifference, List.length_cons, List.length_map] using congrArg (· + 1) ih

theorem expandDifference_shape {h H : ℝ} (hh : 0 ≤ h)
    (as : List ℝ) (has : ∀ a ∈ as, 0 ≤ a ∧ a ≤ H) :
    ∀ bs ∈ expandDifference h as,
      bs.length = as.length + 1 ∧ ∀ b ∈ bs, 0 ≤ b ∧ b ≤ H + h := by
  induction as with
  | nil => simp [expandDifference]
  | cons a as ih =>
    intro bs hbs
    have ha := has a (by simp)
    have has' : ∀ b ∈ as, 0 ≤ b ∧ b ≤ H := fun b hb => has b (by simp [hb])
    simp only [expandDifference, List.mem_cons] at hbs
    rcases hbs with rfl | hbs
    · refine ⟨by simp, ?_⟩
      intro b hb
      simp only [List.mem_cons, List.mem_map] at hb
      rcases hb with rfl | rfl | ⟨c, hc, rfl⟩
      · exact ⟨ha.1, by linarith [ha.2]⟩
      · exact ⟨by linarith [ha.1], by linarith [ha.2]⟩
      · exact ⟨by linarith [(has' c hc).1], by linarith [(has' c hc).2]⟩
    · obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hbs
      obtain ⟨hcl, hcp⟩ := ih has' cs hcs
      refine ⟨by simp [hcl], ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨ha.1, by linarith [ha.2]⟩
      · exact hcp b hb

theorem reciprocalProduct_difference (as : List ℝ) {x h : ℝ}
    (hx : 0 < x) (hh : 0 ≤ h) (has : ∀ a ∈ as, 0 ≤ a) :
    reciprocalProduct as x - reciprocalProduct as (x + h) =
      h * ((expandDifference h as).map (fun bs => reciprocalProduct bs x)).sum := by
  induction as with
  | nil => simp [expandDifference]
  | cons a as ih =>
    have ha : 0 ≤ a := has a (by simp)
    have htail := ih (fun b hb => has b (by simp [hb]))
    have hfrac : 1 / (x + a) - 1 / (x + h + a) =
        h * (1 / (x + a) * (1 / (x + (a + h)))) := by
      have h1 : x + a ≠ 0 := by linarith
      have h2 : x + h + a ≠ 0 := by linarith
      have h3 : x + (a + h) ≠ 0 := by linarith
      field_simp
      ring
    simp only [expandDifference, List.map_cons, List.map_map, Function.comp_def,
      List.sum_cons, reciprocalProduct_cons, reciprocalProduct_shift]
    rw [List.sum_map_mul_left]
    linear_combination reciprocalProduct as (x + h) * hfrac + (1 / (x + a)) * htail

def backwardDifferences : List ℝ → (ℝ → ℝ) → ℝ → ℝ
  | [], f => f
  | h :: hs, f => fun x => backwardDifferences hs f x - backwardDifferences hs f (x + h)

def reciprocalTerms : List ℝ → List (List ℝ)
  | [] => [[0]]
  | h :: hs => (reciprocalTerms hs).flatMap (expandDifference h)

theorem reciprocalTerms_shape (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) :
    (reciprocalTerms hs).length = hs.length.factorial ∧
      ∀ as ∈ reciprocalTerms hs,
        as.length = hs.length + 1 ∧ ∀ a ∈ as, 0 ≤ a ∧ a ≤ hs.sum := by
  induction hs with
  | nil => simp [reciprocalTerms]
  | cons h hs ih =>
    have hh : 0 ≤ h := hhs h (by simp)
    have hhs' : ∀ t ∈ hs, 0 ≤ t := fun t ht => hhs t (by simp [ht])
    obtain ⟨hlen, hshape⟩ := ih hhs'
    constructor
    · simp only [reciprocalTerms, List.length_flatMap, expandDifference_length]
      have heq : ((reciprocalTerms hs).map List.length) =
          (reciprocalTerms hs).map (fun _ => hs.length + 1) := by
        apply List.map_congr_left
        intro as has
        exact (hshape as has).1
      rw [heq]
      simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, hlen, List.length_cons, Nat.factorial_succ]
      exact Nat.mul_comm _ _
    · intro as has
      obtain ⟨bs, hbs, has⟩ := List.mem_flatMap.mp has
      obtain ⟨hbsl, hbsp⟩ := hshape bs hbs
      obtain ⟨hasl, hasp⟩ := expandDifference_shape hh bs hbsp as has
      refine ⟨by simpa [hbsl] using hasl, ?_⟩
      intro a ha
      simpa only [List.sum_cons, add_comm] using hasp a ha

theorem reciprocalTerms_difference (ts : List (List ℝ)) {x h : ℝ}
    (hx : 0 < x) (hh : 0 ≤ h) (hts : ∀ as ∈ ts, ∀ a ∈ as, 0 ≤ a) :
    (ts.map (fun as => reciprocalProduct as x)).sum -
      (ts.map (fun as => reciprocalProduct as (x + h))).sum =
      h * ((ts.flatMap (expandDifference h)).map (fun bs => reciprocalProduct bs x)).sum := by
  induction ts with
  | nil => simp
  | cons as ts ih =>
    have has := reciprocalProduct_difference as hx hh (hts as (by simp))
    have htail := ih (fun bs hbs => hts bs (by simp [hbs]))
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append]
    linarith

theorem backwardDifferences_reciprocal (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h)
    {x : ℝ} (hx : 0 < x) :
    backwardDifferences hs (fun y => 1 / y) x =
      hs.prod * ((reciprocalTerms hs).map (fun as => reciprocalProduct as x)).sum := by
  induction hs generalizing x with
  | nil => simp [backwardDifferences, reciprocalTerms]
  | cons h hs ih =>
    have hh : 0 ≤ h := hhs h (by simp)
    have hhs' : ∀ t ∈ hs, 0 ≤ t := fun t ht => hhs t (by simp [ht])
    have hs' := (reciprocalTerms_shape hs hhs').2
    have heq := reciprocalTerms_difference (reciprocalTerms hs) hx hh
      (fun as has a ha => (hs' as has).2 a ha |>.1)
    simp only [backwardDifferences, reciprocalTerms, List.prod_cons]
    rw [ih hhs' hx, ih hhs' (by linarith)]
    linear_combination hs.prod * heq

theorem reciprocalProduct_bounds (as : List ℝ) {x U V : ℝ}
    (hU : 0 < U) (hUV : U ≤ V)
    (has : ∀ a ∈ as, U ≤ x + a ∧ x + a ≤ V) :
    (1 / V) ^ as.length ≤ reciprocalProduct as x ∧
      reciprocalProduct as x ≤ (1 / U) ^ as.length := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have ha := has a (by simp)
    have has' : ∀ b ∈ as, U ≤ x + b ∧ x + b ≤ V := fun b hb => has b (by simp [hb])
    obtain ⟨hlo, hhi⟩ := ih has'
    have hV : 0 < V := hU.trans_le hUV
    have hxa : 0 < x + a := hU.trans_le ha.1
    have hl := one_div_le_one_div_of_le hxa ha.2
    have hu := one_div_le_one_div_of_le hU ha.1
    simp only [reciprocalProduct_cons, List.length_cons, pow_succ']
    exact ⟨mul_le_mul hl hlo (by positivity) (by positivity),
      mul_le_mul hu hhi (by linarith [pow_nonneg (le_of_lt (one_div_pos.mpr hV)) as.length]) (by positivity)⟩

theorem backwardDifferences_reciprocal_bounds (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {x U V : ℝ}
    (hU : 0 < U) (hx : U ≤ x) (hxV : x + hs.sum ≤ V) :
    hs.prod * hs.length.factorial * (1 / V) ^ (hs.length + 1) ≤
        backwardDifferences hs (fun y => 1 / y) x ∧
      backwardDifferences hs (fun y => 1 / y) x ≤
        hs.prod * hs.length.factorial * (1 / U) ^ (hs.length + 1) := by
  have hsum : 0 ≤ hs.sum := List.sum_nonneg hhs
  have hUV : U ≤ V := by linarith
  have hp : 0 ≤ hs.prod := List.prod_nonneg hhs
  obtain ⟨hlen, hshape⟩ := reciprocalTerms_shape hs hhs
  have hb (as : List ℝ) (has : as ∈ reciprocalTerms hs) :
      (1 / V) ^ (hs.length + 1) ≤ reciprocalProduct as x ∧
        reciprocalProduct as x ≤ (1 / U) ^ (hs.length + 1) := by
    obtain ⟨hal, hap⟩ := hshape as has
    have hh := reciprocalProduct_bounds as (x := x) hU hUV (fun a ha => by
      obtain ⟨ha0, haH⟩ := hap a ha
      constructor <;> linarith)
    simpa only [hal] using hh
  have hlo := List.sum_le_sum (fun as has => (hb as has).1)
  have hhi := List.sum_le_sum (fun as has => (hb as has).2)
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, hlen] at hlo hhi
  rw [backwardDifferences_reciprocal hs hhs (hU.trans_le hx)]
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlo hp
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hhi hp

end ShortEgyptian

end OAI
