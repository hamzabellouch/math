import OAI.Probability.BenjaminiSchramm.HalfspaceConcatenation
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteOpenWitness

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace Percolation.BenjaminiSchramm

lemma supermultiplicative_exp_bound (P : ℝ → ℝ) (hP : ∀ t, 0 ≤ P t)
    (hzero : P 0 = 1) (hmul : ∀ s t, 0 ≤ s → 0 ≤ t → P s * P t ≤ P (s+t))
    (C : ℝ) (hbound : ∀ t, 0 ≤ t → P t ≤ C * Real.exp (-t))
    (t : ℝ) (ht : 0 ≤ t) : P t ≤ Real.exp (-t) := by
  have hpow (n : ℕ) : P t ^ n ≤ P ((n : ℝ)*t) := by
    induction n with
    | zero => simp only [pow_zero,Nat.cast_zero,zero_mul,hzero,le_refl]
    | succ n ih =>
      calc
        _ = P t ^ n * P t := pow_succ _ _
        _ ≤ P ((n : ℝ)*t) * P t := mul_le_mul_of_nonneg_right ih (hP t)
        _ ≤ P ((n : ℝ)*t+t) := hmul _ _ (mul_nonneg (Nat.cast_nonneg n) ht) ht
        _ = _ := by congr 1; push_cast; ring
  by_contra hfail
  have hlt : Real.exp (-t) < P t := lt_of_not_ge hfail
  have hone : 1 < P t * Real.exp t := by
    have h := mul_lt_mul_of_pos_right hlt (Real.exp_pos t)
    simpa only [← Real.exp_add,neg_add_cancel,Real.exp_zero] using h
  obtain ⟨n,hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hone).eventually
    (eventually_gt_atTop C)).exists
  have hb := (hpow n).trans (hbound _ (mul_nonneg (Nat.cast_nonneg n) ht))
  have hm := mul_le_mul_of_nonneg_right hb (pow_nonneg (Real.exp_pos t).le n)
  have he : Real.exp (-((n : ℝ)*t)) * Real.exp t ^ n = 1 := by
    rw [← Real.exp_nat_mul,← Real.exp_add,neg_add_cancel,Real.exp_zero]
  rw [← mul_pow,mul_assoc,he,mul_one] at hm
  exact hn.not_ge hm

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma infimalUpwardCrossing_le_one [Nonempty V] (p : unitInterval) (t : ℝ) :
    G.infimalUpwardCrossing p t ≤ 1 :=
  (iInf_le (fun x => G.law p (G.upwardHalfspaceHit x t)) (Classical.arbitrary V)).trans
    (prob_le_one)

lemma upwardHalfspaceHit_hasFiniteOpenWitness (x : V) (t : ℝ) :
    BernoulliProduct.HasFiniteOpenWitness (G.upwardHalfspaceHit x t) := by
  intro ω hω
  obtain ⟨s,hs,hsa⟩ := G.upwardHalfspaceHit_finiteWitness x t ω hω
  exact ⟨s,s.finite_toSet,hs,hsa⟩

lemma Aut.upwardHalfspaceHit_preimage (φ : G.Aut) (x : V) (t : ℝ) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' G.upwardHalfspaceHit (φ.vertex x) t =
      G.upwardHalfspaceHit x t := by
  have hD : φ.vertex ⁻¹' {v | 0 ≤ G.modularLogHeight (φ.vertex x) v} =
      {v | 0 ≤ G.modularLogHeight x v} := by
    ext v
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,Aut.modularLogHeight]
  ext ω
  have hmask : φ.edge ⁻¹' (φ.edge '' ω ∩ Percolation.internalEdges G.ends
      {v | 0 ≤ G.modularLogHeight (φ.vertex x) v}) =
      ω ∩ Percolation.internalEdges G.ends {v | 0 ≤ G.modularLogHeight x v} := by
    rw [Set.preimage_inter,Set.preimage_image_eq _ φ.edge.injective,
      ← Percolation.internalEdges_aut_preimage G.ends φ.preserves,hD]
  have hconn (y : V) :
      Percolation.Conn G.ends (φ.edge '' ω ∩ Percolation.internalEdges G.ends
        {v | 0 ≤ G.modularLogHeight (φ.vertex x) v}) (φ.vertex x) (φ.vertex y) ↔
      Percolation.Conn G.ends (ω ∩ Percolation.internalEdges G.ends
        {v | 0 ≤ G.modularLogHeight x v}) x y := by
    rw [← Percolation.conn_aut_iff G.ends φ.preserves,hmask]
  constructor
  · rintro ⟨y,hy,hxy⟩
    obtain ⟨z,rfl⟩ := φ.vertex.surjective y
    exact ⟨z,by simpa only [Set.mem_ofPred_eq,Aut.modularLogHeight] using hy,(hconn z).mp hxy⟩
  · rintro ⟨y,hy,hxy⟩
    exact ⟨φ.vertex y,by simpa only [Set.mem_ofPred_eq,Aut.modularLogHeight] using hy,(hconn y).mpr hxy⟩

lemma Aut.upwardHalfspaceHit_measure [Countable E] (φ : G.Aut) (p : unitInterval)
    (x : V) (t : ℝ) :
    G.law p (G.upwardHalfspaceHit (φ.vertex x) t) = G.law p (G.upwardHalfspaceHit x t) := by
  conv_lhs => rw [← G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_upwardHalfspaceHit _ _),φ.upwardHalfspaceHit_preimage]

theorem infimalUpwardCrossing_bound_at_limit [Countable E] [Nonempty V]
    (hq : G.QuasiTransitive) (p : unitInterval) (hp : 0 < p) (t : ℝ) (b : ℝ)
    (hb : 0 ≤ b)
    (hbelow : ∀ q : unitInterval, q < p → (G.infimalUpwardCrossing q t).toReal ≤ b) :
    (G.infimalUpwardCrossing p t).toReal ≤ b := by
  by_contra hn
  have hbp : b < (G.infimalUpwardCrossing p t).toReal := lt_of_not_ge hn
  let c := (b + (G.infimalUpwardCrossing p t).toReal)/2
  have hbc : b < c := by dsimp [c]; linarith
  have hcp : c < (G.infimalUpwardCrossing p t).toReal := by dsimp [c]; linarith
  obtain ⟨S,hS,hcover⟩ := hq
  let : Finite S := hS.to_subtype
  have hroot (x : V) : c < (G.law p).real (G.upwardHalfspaceHit x t) :=
    hcp.trans_le (ENNReal.toReal_mono (measure_ne_top _ _)
      (iInf_le (fun y => G.law p (G.upwardHalfspaceHit y t)) x))
  obtain ⟨q,_hhalf,hqp,hqroot⟩ := BernoulliProduct.exists_lower_parameter
    (fun x : S => G.upwardHalfspaceHit x t) (fun x => G.upwardHalfspaceHit_upper x t)
    (fun x => G.upwardHalfspaceHit_hasFiniteOpenWitness x t) p hp (fun _ => c)
    (fun x => by simpa only [BernoulliProduct.law_const,law] using hroot x)
  have hcq : ENNReal.ofReal c ≤ G.infimalUpwardCrossing q t := by
    apply le_iInf
    intro x
    obtain ⟨o,ho,φ,rfl⟩ := hcover x
    rw [φ.upwardHalfspaceHit_measure]
    have hr := hqroot ⟨o,ho⟩
    rw [BernoulliProduct.law_const] at hr
    exact ENNReal.ofReal_le_of_le_toReal hr.le
  have hcqr := ENNReal.toReal_mono
    (lt_of_le_of_lt (G.infimalUpwardCrossing_le_one q t) (by simp)).ne hcq
  rw [ENNReal.toReal_ofReal (hb.trans hbc.le)] at hcqr
  exact hbc.not_ge (hcqr.trans (hbelow q hqp))

end CriticalPercolation.BondGraph

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Encodable V] [Countable E] [Nonempty V] (G : BondGraph V E)

theorem subcritical_infimal_upward_crossing_bound (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (t : ℝ) (ht : 0 ≤ t) :
    ((criticalModel G).infimalUpwardCrossing p t).toReal ≤ Real.exp (-t) := by
  let H := criticalModel G
  have hHc := criticalModel_connected G hc
  have hHq := criticalModel_quasiTransitive G hq
  have hne (a : ℝ) : H.infimalUpwardCrossing p a ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (H.infimalUpwardCrossing_le_one p a)
  obtain ⟨C,_hC,hC⟩ := subcritical_uniform_upward_exponential G hc hl hq p hp
  apply supermultiplicative_exp_bound (fun a => (H.infimalUpwardCrossing p a).toReal)
    (fun _ => ENNReal.toReal_nonneg) (by simp) ?_ C ?_ t ht
  · intro a b ha hb
    have h := ENNReal.toReal_mono (hne (a+b))
      (H.infimalUpwardCrossing_supermultiplicative hHc hl hHq p ha hb)
    rwa [ENNReal.toReal_mul] at h
  · intro a _ha
    let x := Classical.arbitrary V
    have hhit : H.upwardHalfspaceHit x a ⊆ H.weightHit (ENNReal.ofReal (Real.exp a)) x := by
      rintro ω ⟨y,hy,hxy⟩
      refine ⟨y,?_,?_⟩
      · rw [criticalModel_openGraph]
        exact (conn_iff_reachable G ω x y).mp (conn_mono G Set.inter_subset_left hxy)
      · have he := Real.exp_le_exp.mpr hy
        rw [CriticalPercolation.BondGraph.modularLogHeight,
          Real.exp_log (H.modularRatio_pos hHc hl y x)] at he
        exact ENNReal.ofReal_le_ofReal he
    have hroot : (H.infimalUpwardCrossing p a).toReal ≤
        (law p).real (H.upwardHalfspaceHit x a) :=
      ENNReal.toReal_mono (measure_ne_top _ _)
        (iInf_le (fun z => H.law p (H.upwardHalfspaceHit z a)) x)
    exact hroot.trans ((measureReal_mono hhit).trans (hC x a))

theorem critical_infimal_upward_crossing_bound (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (t : ℝ) (ht : 0 ≤ t) :
    ((criticalModel G).infimalUpwardCrossing (pc G) t).toReal ≤ Real.exp (-t) :=
  (criticalModel G).infimalUpwardCrossing_bound_at_limit (criticalModel_quasiTransitive G hq)
    (pc G) (pc_pos G hl hq) t (Real.exp (-t)) (Real.exp_pos _).le
    (fun p hp => subcritical_infimal_upward_crossing_bound G hc hl hq p hp t ht)

end Percolation.BenjaminiSchramm

end

end OAI
