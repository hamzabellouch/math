import OAI.Probability.ThorpShuffle.SpectralDecay

namespace OAI

universe uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def splitPosition (d : ℕ) : Position (d + 1) ≃ Bool × Position d :=
  (Fin.consEquiv (fun _ : Fin (d + 1) => Bool)).symm

def scatterPosition (d : ℕ) : Bool × Position d ≃ Position (d + 1) :=
  (splitPosition d).symm.trans (rotate (d + 1))

def physicalFlow (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Coins (d + 1)) (x : Position (d + 1)) : ℝ :=
  flow (B ∘ (splitPosition d).symm) (w ∘ (splitPosition d).symm) c
    ((scatterPosition d).symm x)

def physicalFree (d : ℕ) (B : Position (d + 1) → Bool)
    (c : Coins (d + 1)) (x : Position (d + 1)) : Bool :=
  B ((step (d + 1) c).symm x)

theorem step_symm_scatter (d : ℕ) (c : Coins (d + 1)) (p : Bool × Position d) :
    (step (d + 1) c).symm (scatterPosition d p) =
      (splitPosition d).symm (pairMap c p) := by
  simp [step, scatterPosition, splitPosition, pairSwitch, pairMap]

@[simp] theorem physicalFlow_scatter (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Coins (d + 1)) (p : Bool × Position d) :
    physicalFlow d B w c (scatterPosition d p) =
      flow (B ∘ (splitPosition d).symm) (w ∘ (splitPosition d).symm) c p := by
  simp [physicalFlow]

@[simp] theorem physicalFree_scatter (d : ℕ) (B : Position (d + 1) → Bool)
    (c : Coins (d + 1)) (p : Bool × Position d) :
    physicalFree d B c (scatterPosition d p) =
      B ((splitPosition d).symm (pairMap c p)) := by
  rw [physicalFree, step_symm_scatter]

theorem physicalFlow_sum (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Coins (d + 1)) :
    (∑ x, physicalFlow d B w c x) = ∑ x, w x := by
  calc
    _ = ∑ p, physicalFlow d B w c (scatterPosition d p) :=
      (Equiv.sum_comp (scatterPosition d) (physicalFlow d B w c)).symm
    _ = ∑ p, w ((splitPosition d).symm p) := by
      simp only [physicalFlow_scatter]
      exact flow_sum (B ∘ (splitPosition d).symm)
        (w ∘ (splitPosition d).symm) c
    _ = _ := Equiv.sum_comp (splitPosition d).symm w

theorem physicalFlow_energy_le (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Coins (d + 1)) :
    (∑ x, physicalFlow d B w c x ^ 2) ≤ ∑ x, w x ^ 2 := by
  calc
    _ = ∑ p, physicalFlow d B w c (scatterPosition d p) ^ 2 :=
      (Equiv.sum_comp (scatterPosition d) (fun x => physicalFlow d B w c x ^ 2)).symm
    _ ≤ ∑ p, w ((splitPosition d).symm p) ^ 2 := by
      simp only [physicalFlow_scatter]
      exact flow_energy_le (B ∘ (splitPosition d).symm)
        (w ∘ (splitPosition d).symm) c
    _ = _ := Equiv.sum_comp (splitPosition d).symm (fun x => w x ^ 2)

theorem physicalFlow_support (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (hw : ∀ x, B x = false → w x = 0)
    (c : Coins (d + 1)) (x : Position (d + 1))
    (hx : physicalFree d B c x = false) : physicalFlow d B w c x = 0 := by
  obtain ⟨p, rfl⟩ := (scatterPosition d).surjective x
  rw [physicalFree_scatter] at hx
  rw [physicalFlow_scatter]
  exact flow_support _ _ (fun p => hw ((splitPosition d).symm p)) c p hx

theorem physicalFlow_uniform (d : ℕ) (B : Position (d + 1) → Bool)
    (r : ℝ) (c : Coins (d + 1)) (x : Position (d + 1)) :
    physicalFlow d B (fun y => if B y then r else 0) c x =
      if physicalFree d B c x then r else 0 := by
  obtain ⟨p, rfl⟩ := (scatterPosition d).surjective x
  rw [physicalFlow_scatter, physicalFree_scatter]
  exact flow_uniform _ r c p

def freeCount {α : Type uα} [Fintype α] (B : α → Bool) : ℕ :=
  (Finset.univ.filter (fun x => B x = true)).card

def centeredPoint {α : Type uα} [Fintype α] [DecidableEq α]
    (B : α → Bool) (tag : α) (x : α) : ℝ :=
  (if x = tag then 1 else 0) - (1 / (freeCount B : ℝ)) * (if B x then 1 else 0)

theorem freeCount_pos {α : Type uα} [Fintype α] (B : α → Bool) (tag : α)
    (ht : B tag = true) : 0 < freeCount B := by
  apply Finset.card_pos.mpr
  exact ⟨tag, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩

theorem sum_free_indicator {α : Type uα} [Fintype α] (B : α → Bool) :
    (∑ x : α, if B x then (1 : ℝ) else 0) = freeCount B := by
  exact Finset.sum_boole _ _

theorem centeredPoint_sum {α : Type uα} [Fintype α] [DecidableEq α]
    (B : α → Bool) (tag : α) (ht : B tag = true) :
    (∑ x, centeredPoint B tag x) = 0 := by
  have hm : (freeCount B : ℝ) ≠ 0 := by exact_mod_cast (freeCount_pos B tag ht).ne'
  unfold centeredPoint
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_free_indicator]
  simp [hm]

theorem centeredPoint_support {α : Type uα} [Fintype α] [DecidableEq α]
    (B : α → Bool) (tag : α) (ht : B tag = true)
    (x : α) (hx : B x = false) : centeredPoint B tag x = 0 := by
  have hxt : x ≠ tag := by intro h; subst x; simp_all
  simp [centeredPoint, hx, hxt]

theorem centeredPoint_energy {α : Type uα} [Fintype α] [DecidableEq α]
    (B : α → Bool) (tag : α) (ht : B tag = true) :
    (∑ x, centeredPoint B tag x ^ 2) = 1 - 1 / (freeCount B : ℝ) := by
  have hm : (freeCount B : ℝ) ≠ 0 := by exact_mod_cast (freeCount_pos B tag ht).ne'
  have hpoint (x : α) : centeredPoint B tag x ^ 2 =
      (if x = tag then (1 - 2 / (freeCount B : ℝ)) else 0) +
        (1 / (freeCount B : ℝ)) ^ 2 * (if B x then 1 else 0) := by
    by_cases hx : x = tag
    · subst x
      simp [centeredPoint, ht]
      ring
    · cases hB : B x <;> simp [centeredPoint, hx, hB]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_free_indicator]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  field_simp
  ring

structure CenteredState (d : ℕ) where
  free : Position d → Bool
  weight : Position d → ℝ
  mass_zero : ∑ x, weight x = 0
  supported : ∀ x, free x = false → weight x = 0
  energy_le_one : ∑ x, weight x ^ 2 ≤ 1

def initialState (d : ℕ) (B : Position d → Bool) (tag : Position d)
    (ht : B tag = true) : CenteredState d where
  free := B
  weight := centeredPoint B tag
  mass_zero := centeredPoint_sum B tag ht
  supported := centeredPoint_support B tag ht
  energy_le_one := by
    rw [centeredPoint_energy B tag ht]
    exact sub_le_self _ (by positivity)

def nextState (d : ℕ) (v : CenteredState (d + 1)) (c : Coins (d + 1)) :
    CenteredState (d + 1) where
  free := physicalFree d v.free c
  weight := physicalFlow d v.free v.weight c
  mass_zero := by rw [physicalFlow_sum]; exact v.mass_zero
  supported := physicalFlow_support d v.free v.weight v.supported c
  energy_le_one := (physicalFlow_energy_le d v.free v.weight c).trans v.energy_le_one

def iterateState (d : ℕ) (v : CenteredState (d + 1)) :
    (t : ℕ) → History (d + 1) t → CenteredState (d + 1)
  | 0, _ => v
  | t + 1, ω => nextState d (iterateState d v t (fun i => ω i.castSucc)) (ω (Fin.last t))

def expectedEnergy (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ) : ℝ :=
  mean (fun ω : History (d + 1) t => ∑ x, (iterateState d v t ω).weight x ^ 2)

theorem expectedEnergy_nonneg (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ) :
    0 ≤ expectedEnergy d v t := by
  unfold expectedEnergy mean
  positivity

theorem expectedEnergy_le_one (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ) :
    expectedEnergy d v t ≤ 1 := by
  unfold expectedEnergy mean
  have hc : (0 : ℝ) < Fintype.card (History (d + 1) t) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hc).mpr
  calc
    _ ≤ ∑ _ω : History (d + 1) t, (1 : ℝ) :=
      Finset.sum_le_sum (fun ω _ => (iterateState d v t ω).energy_le_one)
    _ = _ := by simp

end Conditional

end Thorp

end

end OAI
