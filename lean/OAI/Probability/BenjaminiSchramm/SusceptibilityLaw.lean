import OAI.Probability.BenjaminiSchramm.SusceptibilityDerivative
import OAI.Probability.BenjaminiSchramm.CriticalSusceptibility
import OAI.Probability.BenjaminiSchramm.ReciprocalGrowth

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem rootSusceptibility_lower_of_critical_volume
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hpc0 : 0 < (pc G : ℝ)) (hpc1 : (pc G : ℝ) < 1)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 < c) (hmin : ∀ i, 1 ≤ c * weight i)
    (hvol : ∀ x, PowerTail (criticalTail G (volumeEvent G) x) (1 / 2)) :
    ∃ k : ℝ, 0 < k ∧ ∀ p : unitInterval,
      (pc G : ℝ) / 2 < p → p < pc G →
      k / ((pc G : ℝ) - p) ≤ rootSusceptibility G root weight p := by
  obtain ⟨d,hd,hdeg⟩ := exists_degree_bound G hqt
  let K : ℝ := (d : ℝ) * c ^ 2 / (1 - pc G)
  have hK : 0 < K := by dsimp [K]; positivity
  have hparam (t : ℝ) (ht : t ∈ Set.Ioo ((pc G : ℝ) / 2) (pc G : ℝ)) :
      t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(by linarith [ht.1]),ht.2.le.trans (pc G).2.2⟩
  have hC (p : unitInterval) (z : V) :
      susceptibility G p z ≤ c * rootSusceptibility G root weight p :=
    susceptibility_le_rootSusceptibility G root weight hw hcover c hc.le hmin p z
  have hderiv (t : ℝ) (ht : t ∈ Set.Ioo ((pc G : ℝ) / 2) (pc G : ℝ)) :
      deriv (realRootSusceptibility G root weight) t ≤
        K * realRootSusceptibility G root weight t ^ 2 := by
    let p : unitInterval := ⟨t,hparam t ht⟩
    have hp0 : 0 < (p : ℝ) := by dsimp [p]; linarith [ht.1]
    have hp : p < pc G := ht.2
    have hh := rootSusceptibility_derivative_upper G hloc hqt root weight hw hw1
      d hdeg c hc.le p hp0 hp (hC p)
    have hnum : 0 ≤ (d : ℝ) * (c * rootSusceptibility G root weight p) ^ 2 := by positivity
    have hden : 0 < 1 - (pc G : ℝ) := sub_pos.mpr hpc1
    have hle :
        (d : ℝ) * (c * rootSusceptibility G root weight p) ^ 2 / (1 - p) ≤
        (d : ℝ) * (c * rootSusceptibility G root weight p) ^ 2 / (1 - pc G) :=
      div_le_div_of_nonneg_left hnum hden (by change 1 - (pc G : ℝ) ≤ 1 - t; linarith [ht.2])
    have he :
        (d : ℝ) * (c * rootSusceptibility G root weight p) ^ 2 / (1 - pc G) =
        K * rootSusceptibility G root weight p ^ 2 := by dsimp [K]; ring
    change deriv (realRootSusceptibility G root weight) (p : ℝ) ≤
      K * realRootSusceptibility G root weight (p : ℝ) ^ 2
    rw [realRootSusceptibility_coe]
    exact hh.trans (hle.trans_eq he)
  have hunbounded (t : ℝ) (ht : t ∈ Set.Ioo ((pc G : ℝ) / 2) (pc G : ℝ))
      (B : ℝ) : ∃ s, t ≤ s ∧ s < (pc G : ℝ) ∧
        B < realRootSusceptibility G root weight s := by
    let p : unitInterval := ⟨t,hparam t ht⟩
    let x : V := Classical.ofNonempty
    obtain ⟨q,hpq,hq,hB⟩ := susceptibility_unbounded_below_critical G hloc hqt hpc0
      x (hvol x) p ht.2 (c * B)
    refine ⟨q,hpq,hq,?_⟩
    rw [realRootSusceptibility_coe]
    have hh := hB.trans_le (hC q x)
    nlinarith
  refine ⟨1 / K,one_div_pos.mpr hK,fun p hp0 hp => ?_⟩
  have hh := reciprocal_lower_of_derivative_upper
    (realRootSusceptibility G root weight) ((pc G : ℝ) / 2) (pc G : ℝ) K hK
    (fun t ht => by
      let q : unitInterval := ⟨t,hparam t ht⟩
      have hh := rootSusceptibility_one_le G hloc hqt root weight hw hw1 q ht.2
      rw [←realRootSusceptibility_coe] at hh
      exact zero_lt_one.trans_le hh)
    (fun t ht => by
      let q : unitInterval := ⟨t,hparam t ht⟩
      have hq0 : 0 < (q : ℝ) := by dsimp [q]; linarith [ht.1]
      exact (hasDerivAt_realRootSusceptibility G hloc hqt root weight q hq0 ht.2).differentiableAt)
    hderiv hunbounded p ⟨hp0,hp⟩
  simpa only [realRootSusceptibility_coe,div_div] using hh

theorem susceptibilityLaw_of_critical_volume [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hpc1 : (pc G : ℝ) < 1)
    (hvol : ∀ x, PowerTail (criticalTail G (volumeEvent G) x) (1 / 2)) :
    SusceptibilityLaw G := by
  obtain ⟨O,hO⟩ := hqt
  have hqt : QuasiTransitive G := ⟨O,hO⟩
  have hOne : O.Nonempty := by
    obtain ⟨o,ho,_⟩ := hO (Classical.ofNonempty : V)
    exact ⟨o,ho⟩
  let : Nonempty O := hOne.to_subtype
  let root : O → V := Subtype.val
  let c : ℝ := Fintype.card O
  let weight : O → ℝ := fun _ => 1 / c
  have hc : 0 < c := by dsimp [c]; exact_mod_cast Fintype.card_pos
  have hw (i : O) : 0 ≤ weight i := (one_div_pos.mpr hc).le
  have hw1 : ∑ i, weight i = 1 := by
    simp only [weight,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    change c * (1 / c) = 1
    exact mul_one_div_cancel hc.ne'
  have hmin (i : O) : 1 ≤ c * weight i := by
    dsimp [weight]
    rw [mul_one_div_cancel hc.ne']
  have hcover (x : V) : ∃ i, x ∈ vertexOrbit G (root i) := by
    obtain ⟨o,ho,a,b,hab,hax⟩ := hO x
    exact ⟨⟨o,ho⟩,a,b,hab,hax⟩
  have hpc0 : 0 < (pc G : ℝ) := pc_pos G hloc hqt
  obtain ⟨k,hk,hroot⟩ := rootSusceptibility_lower_of_critical_volume G hloc hqt hpc0 hpc1
    root weight hw hw1 hcover c hc hmin hvol
  obtain ⟨a,ha,hlower⟩ := exists_rootSusceptibility_lower G hconn hloc hqt root weight
    hw hw1 hcover ((pc G : ℝ) / 2) (by positivity)
  obtain ⟨A,hA,hupper⟩ := susceptibility_upper_of_critical_volume G hqt hvol
  intro x
  refine ⟨a*k,A,(pc G : ℝ)/2,mul_pos ha hk,hA,by positivity,?_⟩
  intro p hp hnear
  have hp0 : (pc G : ℝ) / 2 < p := by linarith
  refine ⟨?_,hupper p hp x⟩
  calc
    a*k / ((pc G : ℝ) - p) = a * (k / ((pc G : ℝ) - p)) := by ring
    _ ≤ a * rootSusceptibility G root weight p :=
      mul_le_mul_of_nonneg_left (hroot p hp0 hp) ha.le
    _ ≤ susceptibility G p x := hlower p hp0.le hp x

end Percolation.BenjaminiSchramm

end OAI
