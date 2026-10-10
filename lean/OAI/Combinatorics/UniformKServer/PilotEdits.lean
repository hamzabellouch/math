import Mathlib
import OAI.Combinatorics.UniformKServer.PilotDrift
import OAI.Combinatorics.UniformKServer.PilotFiltering

namespace OAI

noncomputable section

namespace UniformKServer.PilotEdits

section
open PilotCompact
attribute [local instance] Classical.propDecidable

/-- A fixed admissible pilot template, independent of the input law and horizon. -/
structure Template where
  sigma : ℝ
  R : ℝ
  gamma : ℝ
  delta : ℝ
  L : ℝ
  shift : ℕ
  sigma_pos : 0 < sigma
  sigma_le_one : sigma ≤ 1
  R_large : 256 ≤ R
  L_nonneg : 0 ≤ L
  gamma_pos : 0 < gamma
  gamma_sigma : gamma ≤ sigma/64
  gamma_L : gamma ≤ 1/(1+L)
  delta_pos : 0 < delta
  delta_small : delta ≤ 1/4112
  shift_large : 100*R ≤ gamma*(2:ℝ)^shift

def rate (T : Template) : ℝ := driftConstant T.sigma T.gamma T.delta T.L T.shift

variable {X Ω I : Type*} [Fintype X] [MetricSpace X] [Fintype Ω] [Fintype I]

def average (w : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, w ω*f ω

def potential (T : I → Template) (a : I → ℝ) (r τ : ℝ) (N : ℕ)
    (μ : X → ℝ) (g : I → ℕ → X → ℝ) : ℝ :=
  ∑ i, a i * ∑ j ∈ Finset.range N, value (r*τ^j) (T i).sigma (T i).R μ (g i j)

/-- Finite form of the posterior identity of the source. `filtered t` is the
new pre-move posterior at step t+1; `post t` is the previous post-move measure.
The test-function identity is over every old measurable function, not merely
on an event selected later by the edit rule. -/
structure Flow (X Ω : Type*) [Fintype X] [Fintype Ω] (k : ℕ) where
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_total : ∑ ω, weight ω = 1
  filtration : ℕ → Setoid Ω
  refines : ∀ t ω ω', (filtration (t+1)).r ω ω' → (filtration t).r ω ω'
  post : ℕ → Ω → X → ℝ
  filtered : ℕ → Ω → X → ℝ
  mover : ℕ → Ω → X → ℝ
  request : ℕ → Ω → X
  post_nonneg : ∀ t ω y, 0 ≤ post t ω y
  post_total : ∀ t ω, ∑ y, post t ω y = k
  filtered_nonneg : ∀ t ω y, 0 ≤ filtered t ω y
  filtered_total : ∀ t ω, ∑ y, filtered t ω y = k
  mover_nonneg : ∀ t ω y, 0 ≤ mover t ω y
  mover_total : ∀ t ω, ∑ y, mover t ω y = 1
  mover_le : ∀ t ω y, mover t ω y ≤ filtered t ω y
  update : ∀ t ω y, post (t+1) ω y = filtered t ω y - mover t ω y +
    if y = request t ω then 1 else 0
  post_measurable : ∀ t ω ω', (filtration t).r ω ω' → post t ω = post t ω'
  filtering : ∀ t (b : Ω → ℝ), (∀ ω ω', (filtration t).r ω ω' → b ω = b ω') →
    ∀ y, (∑ ω, weight ω*b ω*(filtered t ω y-post t ω y)) = 0

def moverCost {k : ℕ} (F : Flow X Ω k) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ y, F.mover t ω y*dist (F.request t ω) y

end

section
open PilotCompact
attribute [local instance] Classical.propDecidable
variable {X Ω I : Type*} [Fintype X] [MetricSpace X] [Fintype Ω] [Fintype I]

lemma average_add (w f g : Ω → ℝ) :
    average w (fun ω => f ω+g ω) = average w f+average w g := by
  simp [average,mul_add,Finset.sum_add_distrib]

lemma average_sub (w f g : Ω → ℝ) :
    average w (fun ω => f ω-g ω) = average w f-average w g := by
  simp [average,mul_sub,Finset.sum_sub_distrib]

lemma average_smul (w f : Ω → ℝ) (c : ℝ) :
    average w (fun ω => c*f ω) = c*average w f := by
  simp only [average,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

lemma average_mono (w f g : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (h : ∀ ω, f ω ≤ g ω) :
    average w f ≤ average w g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hw ω)

lemma potential_bounds (T : I → Template) (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (r τ : ℝ) (hr : 0 < r) (hτ : 2 ≤ τ) (N k : ℕ)
    (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hμk : ∑ y, μ y = k)
    (g : I → ℕ → X → ℝ) (hg : ∀ i j y, g i j y ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ potential T a r τ N μ g ∧
      potential T a r τ N μ g ≤ 2*k*(∑ i, a i)*(∑ j ∈ Finset.range N, r*τ^j) := by
  have hτ0 : 0 < τ := by linarith
  have hval : ∀ i j, 0 ≤ value (r*τ^j) (T i).sigma (T i).R μ (g i j) ∧
      value (r*τ^j) (T i).sigma (T i).R μ (g i j) ≤ 2*(r*τ^j)*k := by
    intro i j
    simpa only [hμk] using value_bounds (r*τ^j) (T i).sigma (T i).R (by positivity)
      (T i).sigma_pos (T i).sigma_le_one (T i).R_large μ (g i j) hμ (hg i j)
  constructor
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (ha i)
      (Finset.sum_nonneg fun j _ => (hval i j).1)
  · calc
      _ ≤ ∑ i, a i * ∑ j ∈ Finset.range N, 2*(r*τ^j)*k :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun j _ => (hval i j).2) (ha i)
      _ = _ := by
        have he : ∀ j, 2*(r*τ^j)*(k:ℝ) = (2*k)*(r*τ^j) := by intro j; ring
        simp_rw [he,←Finset.mul_sum,←Finset.sum_mul]
        ring

lemma potential_filtering {k : ℕ} (F : Flow X Ω k)
    (T : I → Template) (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (r τ : ℝ) (N t : ℕ) (g : Ω → I → ℕ → X → ℝ)
    (hmeas : ∀ i j ω ω', (F.filtration t).r ω ω' → g ω i j = g ω' i j) :
    average F.weight (fun ω => potential T a r τ N (F.filtered t ω) (g ω)) ≤
      average F.weight (fun ω => potential T a r τ N (F.post t ω) (g ω)) := by
  have he : ∀ μ : Ω → X → ℝ,
      average F.weight (fun ω => potential T a r τ N (μ ω) (g ω)) =
        ∑ i, a i * ∑ j ∈ Finset.range N,
          ∑ ω, F.weight ω*value (r*τ^j) (T i).sigma (T i).R (μ ω) (g ω i j) := by
    intro μ
    simp only [average,potential,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro ω _
    ring
  rw [he,he]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (ha i)
  apply Finset.sum_le_sum
  intro j _
  exact filtering (r*τ^j) (T i).sigma (T i).R F.weight (F.filtration t)
    (F.post t) (F.filtered t) (fun ω => g ω i j) F.weight_nonneg
    (F.post_measurable t) (hmeas i j) (F.filtering t)

lemma potential_drift {k : ℕ} (hk : 2 ≤ k) (F : Flow X Ω k)
    (T : I → Template) (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (r τ : ℝ) (hr : 0 < r) (hτ : 2 ≤ τ) (N t : ℕ) (ω : Ω)
    (g : I → ℕ → X → ℝ)
    (hg : ∀ i j y, g i j y ∈ Set.Icc (0:ℝ) 1)
    (hLip : ∀ i j y z, |g i j y-g i j z| ≤ (T i).L*(dist y z/(r*τ^j))) :
    potential T a r τ N (F.post (t+1) ω) g - potential T a r τ N (F.filtered t ω) g ≤
      (∑ i, a i*rate (T i))*(1+Real.log (k+1))*moverCost F t ω := by
  have hu : F.post (t+1) ω = fun y => F.filtered t ω y-F.mover t ω y+
      if y=F.request t ω then 1 else 0 := funext (F.update t ω)
  have hi : ∀ i, (∑ j ∈ Finset.range N,
      (value (r*τ^j) (T i).sigma (T i).R (F.post (t+1) ω) (g i j)-
        value (r*τ^j) (T i).sigma (T i).R (F.filtered t ω) (g i j))) ≤
      rate (T i)*(1+Real.log (k+1))*moverCost F t ω := by
    intro i
    apply le_trans (Finset.sum_le_sum fun j _ => le_max_left _ 0)
    simpa only [hu,rate,moverCost] using pilot_drift r τ (T i).sigma (T i).R (T i).gamma
      (T i).delta (T i).L N (T i).shift k hr hτ (T i).sigma_pos (T i).sigma_le_one
      (T i).R_large (T i).L_nonneg (T i).gamma_pos (T i).gamma_sigma (T i).gamma_L
      (T i).delta_pos (T i).delta_small hk (T i).shift_large (F.filtered t ω)
      (F.mover t ω) (g i) (F.request t ω) (F.filtered_nonneg t ω) (F.filtered_total t ω)
      (F.mover_nonneg t ω) (F.mover_total t ω) (F.mover_le t ω) (hg i) (hLip i)
  calc
    _ = ∑ i, a i * ∑ j ∈ Finset.range N,
      (value (r*τ^j) (T i).sigma (T i).R (F.post (t+1) ω) (g i j)-
        value (r*τ^j) (T i).sigma (T i).R (F.filtered t ω) (g i j)) := by
      simp only [potential,Finset.sum_sub_distrib,mul_sub]
    _ ≤ ∑ i, a i*(rate (T i)*(1+Real.log (k+1))*moverCost F t ω) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hi i) (ha i)
    _ = _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

end
variable {X Ω I : Type*} [Fintype X] [MetricSpace X] [Fintype Ω] [Fintype I]

/-- The finite-family pilot edit budget, companion Corollary pilot-edits.
All constants on the right are fixed before choosing the law and horizon. -/
theorem pilot_edits {k : ℕ} (hk : 2 ≤ k) (F : Flow X Ω k)
    (T : I → Template) (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (r τ : ℝ) (hr : 0 < r) (hτ : 2 ≤ τ) (N H : ℕ)
    (g : ℕ → Ω → I → ℕ → X → ℝ)
    (hg : ∀ t ω i j y, g t ω i j y ∈ Set.Icc (0:ℝ) 1)
    (hLip : ∀ t ω i j y z, |g t ω i j y-g t ω i j z| ≤
      (T i).L*(dist y z/(r*τ^j)))
    (hmeas : ∀ t i j ω ω', (F.filtration t).r ω ω' → g t ω i j = g t ω' i j)
    (charge : ℕ → Ω → ℝ) (_hc : ∀ t ω, 0 ≤ charge t ω)
    (hedit : ∀ t ω, charge t ω ≤
      potential T a r τ N (F.post (t+1) ω) (g t ω) -
        potential T a r τ N (F.post (t+1) ω) (g (t+1) ω)) :
    (∑ t ∈ Finset.range H, average F.weight (charge t)) ≤
      (∑ i, a i*rate (T i)) * (1+Real.log (k+1)) *
        (∑ t ∈ Finset.range H, average F.weight (moverCost F t)) +
      2*k*(∑ i, a i)*(∑ j ∈ Finset.range N, r*τ^j)
 := by
  let D := (∑ i, a i*rate (T i))*(1+Real.log (k+1))
  let init := 2*(k:ℝ)*(∑ i, a i)*(∑ j ∈ Finset.range N, r*τ^j)
  let Φ := fun t => average F.weight (fun ω => potential T a r τ N (F.post t ω) (g t ω))
  have hstep : ∀ t, Φ (t+1)+average F.weight (charge t) ≤
      Φ t + D*average F.weight (moverCost F t) := by
    intro t
    have he := average_mono F.weight (charge t)
      (fun ω => potential T a r τ N (F.post (t+1) ω) (g t ω)-
        potential T a r τ N (F.post (t+1) ω) (g (t+1) ω)) F.weight_nonneg (hedit t)
    rw [average_sub] at he
    have hd := average_mono F.weight
      (fun ω => potential T a r τ N (F.post (t+1) ω) (g t ω)-
        potential T a r τ N (F.filtered t ω) (g t ω))
      (fun ω => D*moverCost F t ω) F.weight_nonneg
      (fun ω => potential_drift hk F T a ha r τ hr hτ N t ω (g t ω) (hg t ω) (hLip t ω))
    rw [average_sub,average_smul] at hd
    have hf := potential_filtering F T a ha r τ N t (g t) (hmeas t)
    dsimp only [Φ]
    linarith
  have htel : ∀ H, (∑ t ∈ Finset.range H, average F.weight (charge t))+Φ H ≤
      Φ 0 + D*(∑ t ∈ Finset.range H, average F.weight (moverCost F t)) := by
    intro H
    induction H with
    | zero => simp
    | succ H ih =>
      rw [Finset.sum_range_succ,Finset.sum_range_succ]
      have hs := hstep H
      nlinarith
  have hterminal : 0 ≤ Φ H := by
    apply Finset.sum_nonneg
    intro ω _
    exact mul_nonneg (F.weight_nonneg ω)
      (potential_bounds T a ha r τ hr hτ N k (F.post H ω) (F.post_nonneg H ω)
        (F.post_total H ω) (g H ω) (hg H ω)).1
  have hinit : Φ 0 ≤ init := by
    have hh := average_mono F.weight
      (fun ω => potential T a r τ N (F.post 0 ω) (g 0 ω))
      (fun _ => init) F.weight_nonneg (fun ω =>
        (potential_bounds T a ha r τ hr hτ N k (F.post 0 ω) (F.post_nonneg 0 ω)
        (F.post_total 0 ω) (g 0 ω) (hg 0 ω)).2)
    simpa only [Φ,average,←Finset.sum_mul,F.weight_total,one_mul] using hh
  have htotal := htel H
  change _ ≤ D*(∑ t ∈ Finset.range H, average F.weight (moverCost F t))+init
  linarith

end UniformKServer.PilotEdits

end

end OAI
