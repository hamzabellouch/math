import OAI.Probability.BenjaminiSchramm.CriticalUpwardDecay

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] [Nonempty V] (G : BondGraph V E)

theorem subcritical_uniform_upward_exponential (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) :
    ∃ C : ℝ, 0 < C ∧ ∀ x a,
      (law p).real ((criticalModel G).weightHit (ENNReal.ofReal (Real.exp a)) x) ≤
        C * Real.exp (-a) := by
  let H := criticalModel G
  let hHq := criticalModel_quasiTransitive G hq
  let S := ∑ o ∈ (H.orbitRepresentatives hHq).roots, H.tiltedSusceptibility p 1 o
  have hS : S < ⊤ := ENNReal.sum_lt_top.mpr
    (criticalModel_fullTiltedSusceptibility_lt_top_of_lt_pc G hc hl hq p hp)
  have hχ (x : V) : H.tiltedSusceptibility p 1 x ≤ S := by
    obtain ⟨o,ho,φ,rfl⟩ := (H.orbitRepresentatives hHq).cover x
    rw [H.tiltedSusceptibility_aut]
    exact Finset.single_le_sum (fun _ _ => bot_le) ho
  refine ⟨S.toReal+1,by positivity,fun x a => ?_⟩
  have hb := ENNReal.toReal_mono hS.ne
    ((H.weightHit_measure_mul_le p (ENNReal.ofReal (Real.exp a)) x).trans (hχ x))
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos a).le] at hb
  have hlaw : H.law p = (law p : Measure (Set E)) := rfl
  rw [hlaw] at hb
  change Real.exp a * (law p).real (H.weightHit (ENNReal.ofReal (Real.exp a)) x) ≤ S.toReal at hb
  have he : Real.exp a * Real.exp (-a) = 1 := by rw [← Real.exp_add]; simp
  have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-a)).le
  calc
    _ = (Real.exp a * (law p).real (H.weightHit (ENNReal.ofReal (Real.exp a)) x)) *
        Real.exp (-a) := by rw [mul_right_comm,he,one_mul]
    _ ≤ S.toReal * Real.exp (-a) := hm
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos (-a)).le

end Percolation.BenjaminiSchramm

end

end OAI
