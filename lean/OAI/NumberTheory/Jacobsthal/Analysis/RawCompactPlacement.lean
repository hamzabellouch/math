import OAI.NumberTheory.Jacobsthal.Paths.RawFullHitIncreasing

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.FirstHitKernels

lemma gapAt_antitone_cost {r T U : ℝ} (hr : 0 ≤ r) (hTU : T ≤ U) : gapAt r U ≤ gapAt r T :=
  mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hTU)) hr

lemma increasingCosts_before_smallGap {a b : ℕ} {h : RawHistory b}
    (hh : h ∈ increasingCosts a b) {r K : ℝ} (hr : 0 ≤ r)
    (i j : Finset.Iic b) (haj : a ≤ j.1)
    (hi : K < gapAt r (h i).2) (hj : gapAt r (h j).2 ≤ K) : i.1 < j.1 := by
  by_contra hn
  have hji : j.1 ≤ i.1 := by omega
  have hc := hh j i haj hji
  have hg := gapAt_antitone_cost hr hc
  exact (not_lt_of_ge (hg.trans hj)) hi

lemma rawEvenHit_actual_anchor (a : ℕ) (v H : ℝ) (h0 : RawHistory a) :
    ∀ᵐ z ∂rawEvenMarkedHitKernel a v H h0,
      let q := rawEvenFinalCycle a z
      q.2.2 ⟨q.1,Finset.mem_Iic.mpr (by omega)⟩ ∈ regenerationSet :=
  rawEvenHit_anchor_regenerates a v H h0

theorem rawEvenHit_before_compact {r b0 b1 K : ℝ} (hr : 0 < r) (hb0 : 0 < b0)
    (hb1 : 0 < b1) (hK : K ≤ 6*b0) (a : ℕ) (h0 : RawHistory a) :
    ∀ᵐ z ∂rawEvenMarkedHitKernel a (Real.log (r/b1)) (Real.log (b1/(10*b0))) h0,
      let q := rawEvenFinalCycle a z
      ∀ j : Finset.Iic (q.1+2*(q.2.1+1)), a ≤ j.1 →
        gapAt r (q.2.2 j).2 ≤ K → q.1+1 < j.1 := by
  filter_upwards [rawEvenHit_ae_geometric hr hb0 hb1 a h0,
    rawEvenHit_increasing a (Real.log (r/b1)) (Real.log (b1/(10*b0))) h0] with z hG hI
  obtain ⟨tau,_ht0,_ht1,_hF,_hg0,_hg1,_hx0,_hx1,_hx2,_hx3,hgap,_hratio⟩ := hG
  have hR := rawEvenFinalCycle_record a z
  rw [hR] at hgap
  rcases he : rawEvenFinalCycle a z with ⟨t,n,h⟩
  change rawEvenFinalCycle a z ∈ selectedIncreasing a at hI
  rw [he] at hI hgap
  change h ∈ increasingCosts a (t+2*(n+1)) at hI
  change 6*b0 < gapAt r (h ⟨t+1,Finset.mem_Iic.mpr (by omega)⟩).2 at hgap
  change ∀ j : Finset.Iic (t+2*(n+1)), a ≤ j.1 → gapAt r (h j).2 ≤ K → t+1 < j.1
  intro j haj hj
  exact increasingCosts_before_smallGap hI hr.le ⟨t+1,Finset.mem_Iic.mpr (by omega)⟩ j haj
    (hK.trans_lt hgap) hj

theorem rawEvenHit_before_compact_extension {r b0 b1 K : ℝ} (hr : 0 < r) (hb0 : 0 < b0)
    (hb1 : 0 < b1) (hK : K ≤ 6*b0) (a : ℕ) (h0 : RawHistory a) :
    ∀ᵐ z ∂rawEvenMarkedHitKernel a (Real.log (r/b1)) (Real.log (b1/(10*b0))) h0,
      let q := rawEvenFinalCycle a z
      ∀ (c : ℕ) (_hc : q.1+2*(q.2.1+1) ≤ c),
        ∀ᵐ y ∂rawExtension (q.1+2*(q.2.1+1)) c q.2.2,
          ∀ j : Finset.Iic c, a ≤ j.1 → gapAt r (y j).2 ≤ K → q.1+1 < j.1 := by
  filter_upwards [rawEvenHit_ae_geometric hr hb0 hb1 a h0,
    rawEvenHit_increasing a (Real.log (r/b1)) (Real.log (b1/(10*b0))) h0] with z hG hI
  obtain ⟨tau,_ht0,_ht1,_hF,_hg0,_hg1,_hx0,_hx1,_hx2,_hx3,hgap,_hratio⟩ := hG
  have hR := rawEvenFinalCycle_record a z
  rw [hR] at hgap
  rcases he : rawEvenFinalCycle a z with ⟨t,n,h⟩
  change rawEvenFinalCycle a z ∈ selectedIncreasing a at hI
  rw [he] at hI hgap
  change h ∈ increasingCosts a (t+2*(n+1)) at hI
  change 6*b0 < gapAt r (h ⟨t+1,Finset.mem_Iic.mpr (by omega)⟩).2 at hgap
  change ∀ (c : ℕ) (hc : t+2*(n+1) ≤ c), ∀ᵐ y ∂rawExtension (t+2*(n+1)) c h,
    ∀ j : Finset.Iic c, a ≤ j.1 → gapAt r (y j).2 ≤ K → t+1 < j.1
  intro c hc
  filter_upwards [rawExtension_preserves_increasing hc h hI,rawExtension_retains_prefix hc h] with y hy hp
  have heval := congrFun hp (⟨t+1,Finset.mem_Iic.mpr (by omega)⟩ : Finset.Iic (t+2*(n+1)))
  change y ⟨t+1,Finset.mem_Iic.mpr (by omega)⟩=h ⟨t+1,Finset.mem_Iic.mpr (by omega)⟩ at heval
  intro j haj hj
  apply increasingCosts_before_smallGap hy hr.le ⟨t+1,Finset.mem_Iic.mpr (by omega)⟩ j haj _ hj
  rw [heval]
  exact hK.trans_lt hgap

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
