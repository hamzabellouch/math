import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.SpecifiedFailures
import OAI.Probability.CriticalPercolation.ProductMeasure.ContourProbability

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.Boundary

def gridSlot (v : Grid) : ℕ := Nat.pair v.1.toNat v.2.toNat

def quadrant (v : Grid) : Prop := 0≤v.1 ∧ 0≤v.2

lemma gridSlot_injective : Set.InjOn gridSlot {v | quadrant v} := by
  intro v hv w hw he
  have hh := Nat.pairEquiv.injective (show Nat.pairEquiv (v.1.toNat,v.2.toNat)=
    Nat.pairEquiv (w.1.toNat,w.2.toNat) from he)
  change (v.1.toNat,v.2.toNat)=(w.1.toNat,w.2.toNat) at hh
  have hx := congrArg Prod.fst hh
  have hy := congrArg Prod.snd hh
  apply Prod.ext <;> dsimp only [quadrant,Set.mem_ofPred_eq] at hv hw <;> omega

lemma gridSlot_east (v : Grid) (hv : quadrant v) : gridSlot v<gridSlot (v+(1,0)) := by
  change Nat.pair v.1.toNat v.2.toNat<Nat.pair (v.1+1).toNat (v.2+0).toNat
  rw [add_zero]
  exact Nat.pair_lt_pair_left _ (by dsimp [quadrant] at hv; omega)

lemma gridSlot_north (v : Grid) (hv : quadrant v) : gridSlot v<gridSlot (v+(0,1)) := by
  change Nat.pair v.1.toNat v.2.toNat<Nat.pair (v.1+0).toNat (v.2+1).toNat
  rw [add_zero]
  exact Nat.pair_lt_pair_right _ (by dsimp [quadrant] at hv; omega)

def gridFailure {Ω : Type*} (F : ℕ → Set Ω) (v : Grid) : Set Ω :=
  if quadrant v then F (gridSlot v) else ∅

lemma specified_grid_failures {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℕ → MeasurableSpace Ω) (hM : Monotone M)
    (F : ℕ → Set Ω) (hF : ∀ n, MeasurableSet[M (n+1)] (F n))
    (B : Set Ω) (hB : MeasurableSet[M 0] B)
    (ε : ℝ) (hε : 0≤ε)
    (hcond : ∀ n A, MeasurableSet[M n] A → A⊆B → μ.real (A∩F n)≤ε*μ.real A)
    (s : Finset Grid) : μ.real (B∩⋂ z∈s, gridFailure F z)≤μ.real B*ε^s.card := by
  by_cases hs : ∀ z∈s, quadrant z
  · have he : (⋂ z∈s, gridFailure F z)=⋂ n∈s.image gridSlot, F n := by
      ext ω
      constructor
      · intro h
        refine Set.mem_iInter.mpr fun n => Set.mem_iInter.mpr fun hn => ?_
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hn
        have hh := Set.mem_iInter.mp (Set.mem_iInter.mp h z) hz
        simpa only [gridFailure,ite_eq_left (hs z hz)] using hh
      · intro h
        refine Set.mem_iInter.mpr fun z => Set.mem_iInter.mpr fun hz => ?_
        have hh := Set.mem_iInter.mp (Set.mem_iInter.mp h (gridSlot z))
          (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
        simpa only [gridFailure,ite_eq_left (hs z hz)] using hh
    rw [he]
    have hc : (s.image gridSlot).card=s.card := Finset.card_image_iff.mpr (by
      intro z hz w hw he
      exact gridSlot_injective (hs z hz) (hs w hw) he)
    have h := specified_failures_with_initialization μ M hM F hF B hB ε hε hcond
      (s.image gridSlot)
    rwa [hc] at h
  · push Not at hs
    obtain ⟨z,hz,hq⟩ := hs
    have he : (⋂ z∈s, gridFailure F z)=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω h
      have hh := Set.mem_iInter.mp (Set.mem_iInter.mp h z) hz
      simp only [gridFailure,ite_eq_right hq,Set.mem_empty_iff_false] at hh
    rw [he,Set.inter_empty,measureReal_empty]
    positivity

theorem infinitely_many_good_from_tests {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℕ → MeasurableSpace Ω) (hM : Monotone M)
    (F : ℕ → Set Ω) (hF : ∀ n, MeasurableSet[M (n+1)] (F n))
    (B : Set Ω) (hmB : MeasurableSet[M 0] B) (hB : 0<μ.real B)
    (S : Ω → Set Grid)
    (hroot : ∀ ω∈B, (0,0)∈S ω)
    (hquad : ∀ ω∈B, ∀ v∈S ω, quadrant v)
    (hchild : ∀ ω∈B, ∀ z, z∉S ω →
      (∃ y∈S ω, z=y+(1,0) ∨ z=y+(0,1)) → ω∈F (gridSlot z))
    (q : ℝ) (hq₀ : 0≤q) (hq : 8*q<1)
    (hcond : ∀ n A, MeasurableSet[M n] A → A⊆B →
      μ.real (A∩F n)≤q^4*μ.real A) :
    0<μ.real (B∩{ω | (S ω).Infinite}) := by
  apply infinite_good_positive μ B S (gridFailure F) hB hroot hquad ?_ q hq₀ hq
    (specified_grid_failures μ M hM F hF B hmB (q^4) (by positivity) hcond)
  intro ω hω z hz hc
  have hqz : quadrant z := by
    obtain ⟨y,hy,he|he⟩ := hc
    · rw [he]
      have h := hquad ω hω y hy
      change 0≤y.1+1 ∧ 0≤y.2+0
      exact ⟨by linarith [h.1],by linarith [h.2]⟩
    · rw [he]
      have h := hquad ω hω y hy
      change 0≤y.1+0 ∧ 0≤y.2+1
      exact ⟨by linarith [h.1],by linarith [h.2]⟩
  simpa only [gridFailure,ite_eq_left hqz] using hchild ω hω z hz hc

end CriticalPercolation.Boundary
end
end
end

end OAI
