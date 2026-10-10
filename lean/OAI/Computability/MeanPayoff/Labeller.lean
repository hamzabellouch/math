import OAI.Computability.MeanPayoff.GridLabels

namespace OAI

namespace MeanPayoff.Label

variable {n : ℕ}

theorem dyadic_splits {d : ℕ} (hd : 12 ≤ d) :
    (2 : ℤ)^d = 4096*2^(d-12) ∧
    (2 : ℤ)^(d-7) = 32*2^(d-12) ∧
    (2 : ℤ)^(d-1) = 2048*2^(d-12) := by
  constructor
  · nth_rw 1 [show d = (d-12)+12 by omega]
    rw [pow_add]
    norm_num
    ring
  constructor
  · rw [show d-7 = (d-12)+5 by omega, pow_add]
    norm_num
    ring
  · rw [show d-1 = (d-12)+11 by omega, pow_add]
    norm_num
    ring

theorem narrow_rank {a b : Fin n → ℚ}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hbase : ¬ ∀ i, 1 < a i*b i) (d : ℕ) :
    d-7 + budget a (fun i => 4/3*b i) ha (fun i => mul_pos (by norm_num) (hb i))
      < d + budget a b ha hb ∧
    d-7 + budget (fun i => 4/3*a i) b (fun i => mul_pos (by norm_num) (ha i)) hb
      < d + budget a b ha hb := by
  have hd := budget_decreases ha hb ha (fun i => mul_pos (by norm_num) (hb i)) hbase
    (a' := a) (b' := fun i => 4/3*b i) (fun i => by
      have h := mul_pos (ha i) (hb i)
      nlinarith only [h])
  have hu := budget_decreases ha hb (fun i => mul_pos (by norm_num) (ha i)) hb hbase
    (a' := fun i => 4/3*a i) (b' := b) (fun i => by
      have h := mul_pos (ha i) (hb i)
      nlinarith only [h])
  omega

theorem continuation_rank {a b : Fin n → ℚ}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hbase : ¬ ∀ i, 1 < a i*b i) (d : ℕ) (labels : Fin n → Bool) :
    d + budget (reweight a labels) (reweight b (fun i => !(labels i)))
      (reweight_pos ha labels) (reweight_pos hb (fun i => !(labels i)))
      < d + budget a b ha hb := by
  have h := budget_decreases ha hb (reweight_pos ha labels)
    (reweight_pos hb (fun i => !(labels i))) hbase (fun i => by
      rw [reweight_product])
  omega

theorem good_width {F : Vec (Fin n) → Vec (Fin n)} {A : Vec (Fin n)}
    {D E : ℤ} {a b : Fin n → ℚ} {labels : Fin n → Bool} (h : D = E) :
    Good F A D a b labels ↔ Good F A E a b labels := by rw [h]

def labeller (G : Game) (A : Vec (Fin G.n)) (d : ℕ) (a b : Fin G.n → ℚ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    {labels : Fin G.n → Bool // Good (operator G) A ((2 : ℤ)^d) a b labels} := by
  by_cases hbase : ∀ i, 1 < a i*b i
  · exact ⟨massLabels b, massBase_good (by positivity) ha hb hbase⟩
  · by_cases hsmall : d < 12
    · let z := (basic G A (shift A ((2 : ℤ)^d))
        (fun i => by
          dsimp [shift]
          exact le_add_of_nonneg_right (by positivity))).1
      exact ⟨widthLabels A z ((2 : ℤ)^d), widthBase_good G (by positivity) a b⟩
    · have hd : 12 ≤ d := Nat.le_of_not_gt hsmall
      let t : ℤ := 2^(d-12)
      have ht : 0 < t := by dsimp [t]; positivity
      have hs := dyadic_splits hd
      have hD : (2 : ℤ)^d = 4096*t := hs.1
      have hq : (2 : ℤ)^(d-7) = 32*t := hs.2.1
      have hr : (2 : ℤ)^(d-1) = 2048*t := hs.2.2
      let ad : Fin G.n → ℚ := fun i => (4/3)*a i
      let bd : Fin G.n → ℚ := fun i => (4/3)*b i
      have had : ∀ i, 0 < ad i := fun i => mul_pos (by norm_num) (ha i)
      have hbd : ∀ i, 0 < bd i := fun i => mul_pos (by norm_num) (hb i)
      have hdn : d-7+budget a bd ha hbd < d+budget a b ha hb := (narrow_rank ha hb hbase d).1
      have hun : d-7+budget ad b had hb < d+budget a b ha hb := (narrow_rank ha hb hbase d).2
      have hpn : d-1+budget a b ha hb < d+budget a b ha hb := by omega
      let downChild := fun g : Grid G.n =>
        labeller G (fun i => gridPivot A t g i-16*t) (d-7) a bd ha hbd
      let down : Grid G.n → (Fin G.n → Bool) := fun g => (downChild g).val
      have hdgood : ∀ g, Good (operator G) (fun i => gridPivot A t g i-16*t)
          (32*t) a bd (down g) := by
        intro g
        exact (good_width hq).mp (downChild g).property
      let upChild := fun g : Grid G.n =>
        labeller G (fun i => gridPivot A t g i-16*t) (d-7) ad b had hb
      let up : Grid G.n → (Fin G.n → Bool) := fun g => (upChild g).val
      have hugood : ∀ g, Good (operator G) (fun i => gridPivot A t g i-16*t)
          (32*t) ad b (up g) := by
        intro g
        exact (good_width hq).mp (upChild g).property
      let provisional := labeller G (fun i => finalPivot A t down up i-1024*t) (d-1) a b ha hb
      have hpgood : Good (operator G) (fun i => finalPivot A t down up i-1024*t)
          (2048*t) a b provisional.val := by
        exact (good_width hr).mp provisional.property
      let abar := reweight a provisional.val
      let bbar := reweight b (fun i => !(provisional.val i))
      have ha' : ∀ i, 0 < abar i := reweight_pos ha _
      have hb' : ∀ i, 0 < bbar i := reweight_pos hb _
      have hcn : d+budget abar bbar ha' hb' < d+budget a b ha hb :=
        continuation_rank ha hb hbase d _
      let continuation := labeller G A d abar bbar ha' hb'
      have hcgood : Good (operator G) A (4096*t) abar bbar continuation.val := by
        exact (good_width hD).mp continuation.property
      refine ⟨override A (downPivot A t down) (finalPivot A t down up) t continuation.val, ?_⟩
      apply (good_width hD).mpr
      exact passes_good G.positive (operator_laws G) ht ha hb down up hdgood hugood hpgood hcgood
termination_by d + budget a b ha hb
decreasing_by
  all_goals first | exact hdn | exact hun | exact hpn | exact hcn

theorem labeller_good (G : Game) (A : Vec (Fin G.n)) (d : ℕ) (a b : Fin G.n → ℚ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    Good (operator G) A ((2 : ℤ)^d) a b (labeller G A d a b ha hb).val :=
  (labeller G A d a b ha hb).property

end MeanPayoff.Label

end OAI
