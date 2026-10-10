import OAI.Probability.BenjaminiSchramm.NormalizedHalfspace

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem infimalAdjustedCrossing_bound_at_limit [Countable E] [Nonempty V]
    (hq : G.QuasiTransitive) (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x)
    (p : unitInterval) (hp : 0 < p) (t : ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hbelow : ∀ q : unitInterval, q < p → (G.infimalAdjustedCrossing a q t).toReal ≤ b) :
    (G.infimalAdjustedCrossing a p t).toReal ≤ b := by
  by_contra hn
  have hbp : b < (G.infimalAdjustedCrossing a p t).toReal := lt_of_not_ge hn
  let c := (b+(G.infimalAdjustedCrossing a p t).toReal)/2
  have hbc : b < c := by dsimp [c]; linarith
  have hcp : c < (G.infimalAdjustedCrossing a p t).toReal := by dsimp [c]; linarith
  obtain ⟨S,hS,hcover⟩ := hq
  let : Finite S := hS.to_subtype
  have hroot (x : V) : c < (G.law p).real (G.adjustedHalfspaceHit a x 0 t) :=
    hcp.trans_le (ENNReal.toReal_mono (measure_ne_top _ _)
      (iInf_le (fun y => G.law p (G.adjustedHalfspaceHit a y 0 t)) x))
  obtain ⟨q,_hhalf,hqp,hqroot⟩ := BernoulliProduct.exists_lower_parameter
    (fun x : S => G.adjustedHalfspaceHit a x 0 t) (fun x => G.adjustedHalfspaceHit_upper a x 0 t)
    (fun x => G.adjustedHalfspaceHit_hasFiniteOpenWitness a x 0 t) p hp (fun _ => c)
    (fun x => by simpa only [BernoulliProduct.law_const,law] using hroot x)
  have hcq : ENNReal.ofReal c ≤ G.infimalAdjustedCrossing a q t := by
    apply le_iInf
    intro x
    obtain ⟨o,ho,φ,rfl⟩ := hcover x
    rw [Aut.adjustedHalfspaceHit_measure G a ha φ]
    have hr := hqroot ⟨o,ho⟩
    rw [BernoulliProduct.law_const] at hr
    exact ENNReal.ofReal_le_of_le_toReal hr.le
  have hcqr := ENNReal.toReal_mono
    (lt_of_le_of_lt (G.infimalAdjustedCrossing_le_one a q t) (by simp)).ne hcq
  rw [ENNReal.toReal_ofReal (hb.trans hbc.le)] at hcqr
  exact hbc.not_ge (hcqr.trans (hbelow q hqp))

end CriticalPercolation.BondGraph

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Nonempty V] (G : BondGraph V E)

theorem subcritical_infimal_adjusted_crossing_bound (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (a : V → ℝ) (m M : ℝ) (hm : 0 < m)
    (ha : ∀ x, m ≤ a x ∧ a x ≤ M) (p : unitInterval) (hp : p < pc G) (t : ℝ) (ht : 0 ≤ t) :
    ((criticalModel G).infimalAdjustedCrossing a p t).toReal ≤ Real.exp (-t) := by
  let H := criticalModel G
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  have hne (s : ℝ) : H.infimalAdjustedCrossing a p s ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (H.infimalAdjustedCrossing_le_one a p s)
  obtain ⟨C,_hC,hC⟩ := subcritical_uniform_upward_exponential G hc hl hq p hp
  let D := Real.log M-Real.log m
  apply supermultiplicative_exp_bound (fun s => (H.infimalAdjustedCrossing a p s).toReal)
    (fun _ => ENNReal.toReal_nonneg) (by simp) ?_ (C*Real.exp D) ?_ t ht
  · intro s u hs hu
    have h := ENNReal.toReal_mono (hne (s+u))
      (H.infimalAdjustedCrossing_supermultiplicative hHc hl hHq a m M hm ha p hs hu)
    rwa [ENNReal.toReal_mul] at h
  · intro s _hs
    let x := Classical.arbitrary V
    have hhit : H.adjustedHalfspaceHit a x 0 s ⊆
        H.weightHit (ENNReal.ofReal (Real.exp (s-D))) x := by
      rintro ω ⟨y,hy,hxy⟩
      refine ⟨y,?_,?_⟩
      · rw [criticalModel_openGraph]
        exact (conn_iff_reachable G ω x y).mp (conn_mono G Set.inter_subset_left hxy)
      · have hd := (abs_le.mp (H.orbitAdjustedHeight_sub_bound a m M hm ha x y)).2
        have hlo : s-D ≤ H.modularLogHeight x y := by
          change s ≤ H.orbitAdjustedHeight a x y at hy
          linarith
        have he := Real.exp_le_exp.mpr hlo
        rw [CriticalPercolation.BondGraph.modularLogHeight,
          Real.exp_log (H.modularRatio_pos hHc hl y x)] at he
        exact ENNReal.ofReal_le_ofReal he
    have hroot : (H.infimalAdjustedCrossing a p s).toReal ≤
        (law p).real (H.adjustedHalfspaceHit a x 0 s) :=
      ENNReal.toReal_mono (measure_ne_top _ _)
        (iInf_le (fun z => H.law p (H.adjustedHalfspaceHit a z 0 s)) x)
    have hh := hroot.trans ((measureReal_mono hhit).trans (hC x (s-D)))
    have he : C*Real.exp (-(s-D)) = (C*Real.exp D)*Real.exp (-s) := by
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
    rwa [he] at hh

theorem critical_infimal_adjusted_crossing_bound (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (a : V → ℝ)
    (hauto : ∀ (φ : (criticalModel G).Aut) x, a (φ.vertex x) = a x)
    (m M : ℝ) (hm : 0 < m) (ha : ∀ x, m ≤ a x ∧ a x ≤ M) (t : ℝ) (ht : 0 ≤ t) :
    ((criticalModel G).infimalAdjustedCrossing a (pc G) t).toReal ≤ Real.exp (-t) :=
  (criticalModel G).infimalAdjustedCrossing_bound_at_limit (criticalModel_quasiTransitive G hq)
    a hauto (pc G) (pc_pos G hl hq) t (Real.exp (-t)) (Real.exp_pos _).le
    (fun p hp => subcritical_infimal_adjusted_crossing_bound G hc hl hq a m M hm ha p hp t ht)

end Percolation.BenjaminiSchramm

end

end OAI
