import Mathlib
import OAI.Geometry.Cannon.ScalarLimits.OscillationPairwise
import OAI.Geometry.Cannon.Energy.Extend

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open Set Filter Topology
open Set MeasureTheory
open scoped BigOperators
open Set unitInterval

namespace CannonApprox

open CannonGrid CannonChart CannonPacking CannonCrossEnergy CannonScalarEnergy CannonAnnular Metric

theorem exists_scalar_annular_constant {X : Type*} [MetricSpace X]
    [LocallyPathConnectedSpace X] (Q : ℕ) (CP C c L : ℝ)
    (hpack : PolynomialPacking (X := X) Q CP) (hCP : 0 ≤ CP)
    (hC : 0 ≤ C) (hc : 0 < c) (hL : 1 ≤ L)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (e : CannonGrid.Square → X), Topology.IsEmbedding e →
      ∀ (d₁ : ℝ), (∀ A : Set CannonGrid.Square, IsCompact A →
        (∃ x ∈ A, x.1 = 0) → (∃ x ∈ A, x.1 = 1) → d₁ ≤ diam (e '' A)) →
      ∀ {β γ : Type*} [Fintype β] [Fintype γ]
        (ξ : β → X) (p : γ → X) (h : X → X), Continuous h →
      ∀ (o : X) (R r d₀ s : ℝ),
      0 < R → R ≤ 1 → 4*R < d₁ → 0 < r → r ≤ R/2 →
      (L*(L*2+1)+3)*r ≤ R/4 →
      max (C+2) (max c 1)*(r/R) ≤ 1 →
      0 < s → L*s ≤ R/2 → Metric.ball o (4*R) ⊆ range e →
      (∀ i j, i ≠ j → r/R ≤ dist (ξ i) (ξ j)) →
      (∀ i j, i ≠ j → r ≤ dist (p i) (p j)) →
      (∀ y : X, ∃ j, dist (p j) y ≤ r) →
      (∀ u v, dist u o ≤ 3*R → dist v o ≤ 3*R →
        dist (h u) (h v) ≤ C/R * dist u v) →
      (∀ u v, dist u o ≤ 3*R → dist v o ≤ 3*R →
        c/R * dist u v ≤ dist (h u) (h v)) →
      (∀ u v, dist u o ≤ 2*R → dist v o ≤ 2*R →
        R ≤ dist u v → d₀ ≤ dist (h u) (h v)) →
      ∀ (ω : β → ℝ), MacroscopicAdmissible ξ (r/R) d₀ ω →
      ∀ (ρ : γ → ℝ), (∀ j, 0 ≤ ρ j) →
      Admissible (fun j => e ⁻¹' Metric.ball (p j) (2*r)) ρ →
      ∀ (n : ℕ) (hn : 0 < n),
      (∀ z : CannonGrid.Square, ∀ i : Index (3*n), weight (3*n) z i ≠ 0 →
        dist (e z) (e (vertex (3*n) (by omega) i)) < r) →
      ∀ a b : CannonGrid.Square, dist o (e a) ≤ s → dist o (e b) ≤ s →
      let f := scalar (fun j => e ⁻¹' Metric.ball (p j) (2*r)) ρ n hn
      (f b-f a)^2 ≤ E*(∑ j, (ω j)^2)*
        (∑ j ∈ Finset.univ.filter
          (fun j => R/4 ≤ dist (p j) o ∧ dist (p j) o ≤ 4*R), (ρ j)^2) := by
  classical
  let A := L*(L*2+1)+3
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hA : 0 < A := by dsimp [A]; positivity
  have hAone : 1 ≤ A := by dsimp [A]; nlinarith [sq_nonneg L]
  obtain ⟨E,hE,hbound⟩ := exists_packed_annular_constant Q CP C c A hpack hCP hC hc hA
  refine ⟨E,hE,?_⟩
  intro e he d₁ hd₁ β γ _ _ ξ p h hh o R r d₀ s hR hRone hdR hr hrR hAr
    hscaleT hs hsR hchart hξsep hpsep hpnet hzoom hlow hlarge ω hω ρ hρ hadm n hn hmesh a b ha hb
  let Cells := fun j => e ⁻¹' Metric.ball (p j) (2*r)
  let f := scalar Cells ρ n hn
  have hf := (scalar_properties Cells ρ hρ hadm n hn).1
  have hfI := (scalar_properties Cells ρ hρ hadm n hn).2.1
  let α := {j : γ // R/2 ≤ dist (p j) o ∧ dist (p j) o ≤ 3*R}
  let q : α → X := fun i => p i.val
  have hq (i : α) : R/2 ≤ dist (q i) o ∧ dist (q i) o ≤ 3*R := i.property
  have hqsep (i j : α) (hne : i ≠ j) : r ≤ dist (q i) (q j) :=
    hpsep i.val j.val (fun heq => hne (Subtype.ext heq))
  have hnet (y : X) (hy : R ≤ dist y o) (hy' : dist y o ≤ 2*R) :
      ∃ i : α, dist (q i) y ≤ r := by
    obtain ⟨j,hj⟩ := hpnet y
    have ht₁ := dist_triangle y (p j) o
    have ht₂ := dist_triangle (p j) y o
    rw [dist_comm y (p j)] at ht₁
    have hmem : R/2 ≤ dist (p j) o ∧ dist (p j) o ≤ 3*R := by constructor <;> linarith
    exact ⟨⟨j,hmem⟩,hj⟩
  have hchartq (i : α) : Metric.ball (q i) (L*(L*2+1)*r) ⊆ range e := by
    intro y hy
    apply hchart
    change dist y o < 4*R
    have ht := dist_triangle y (q i) o
    have hhq := (hq i).2
    change dist y (q i) < L*(L*2+1)*r at hy
    change A*r ≤ R/4 at hAr
    dsimp [A] at hAr
    nlinarith
  have hinner : 2 < L*(L*2+1) := by nlinarith [sq_nonneg (L-1)]
  have hclosedq (i : α) : Metric.closedBall (q i) (2*r) ⊆ range e := by
    intro y hy
    apply hchartq i
    change dist y (q i) < L*(L*2+1)*r
    exact (show dist y (q i) ≤ 2*r from hy).trans_lt (mul_lt_mul_of_pos_right hinner hr)
  let K (i : α) := e ⁻¹' Metric.closedBall (q i) (2*r)
  have hK (i : α) : IsCompact (K i) := (isClosed_closedBall.preimage he.continuous).isCompact
  have hKn (i : α) : (K i).Nonempty := by
    obtain ⟨x,hx⟩ := hclosedq i (Metric.mem_closedBall_self (by positivity : 0 ≤ 2*r))
    refine ⟨x,?_⟩
    change e x ∈ Metric.closedBall (q i) (2*r)
    rw [hx]
    exact Metric.mem_closedBall_self (by positivity)
  let lo := fun i => sInf (f '' K i)
  let hi := fun i => sSup (f '' K i)
  have hlu (i : α) : lo i ≤ hi i :=
    csInf_le_csSup ((hKn i).image f) ((hK i).image hf).bddBelow ((hK i).image hf).bddAbove
  have hrange (i : α) (z : X) (hz : dist z (q i) ≤ 2*r) :
      extend e f z ∈ Icc (lo i) (hi i) := by
    obtain ⟨x,rfl⟩ := hclosedq i hz
    rw [extend_apply e he.injective]
    exact mem_rangeInterval hf (hK i) hz
  have hlocal (i : α) : hi i-lo i ≤ ∑ j ∈ Finset.univ.filter
      (fun j => dist (p j) (q i) ≤ A*r), ρ j := by
    apply oscillation_le_of_pairwise hf (hK i)
      (Finset.sum_nonneg (fun j _ => hρ j))
    intro x hx y hy
    exact scalar_local_oscillation e he L 2 r hL (by norm_num) hr hpaths (q i)
      (hchartq i) p ρ hρ hadm n hn hmesh x y
      (by simpa only [K,mem_preimage,mem_closedBall,dist_comm] using hx)
      (by simpa only [K,mem_preimage,mem_closedBall,dist_comm] using hy)
  have hscaleS : max A 1*r ≤ 1 := by
    rw [max_eq_left hAone]
    exact hAr.trans ((div_le_self hR.le (by norm_num : (1:ℝ) ≤ 4)).trans hRone)
  have hordered (a b : CannonGrid.Square) (ha : dist o (e a) ≤ s) (hb : dist o (e b) ≤ s)
      (hab : f a ≤ f b) :
      (f b-f a)^2 ≤ E*(∑ j, (ω j)^2)*
        (∑ j ∈ Finset.univ.filter
          (fun j => R/4 ≤ dist (p j) o ∧ dist (p j) o ≤ 4*R), (ρ j)^2) := by
    obtain ⟨π,hπ⟩ := hpaths o (e a) (e b) s hs ha hb
    have hπr (v : unitInterval) : π v ∈ range e := by
      apply hchart
      change dist (π v) o < 4*R
      have hv := hπ v
      change dist o (π v) < L*s at hv
      rw [dist_comm] at hv
      linarith
    have hlev : ∀ t : ℝ, ∃ S : Set X, t ∈ Ioo (f a) (f b) →
        IsPreconnected S ∧ 4*R < diam S ∧ (∃ z ∈ S, dist z o ≤ R/2) ∧
        ∀ z ∈ S, extend e f z = t := by
      intro t
      by_cases ht : t ∈ Ioo (f a) (f b)
      · have ht01 : t ∈ Ioo (0:ℝ) 1 :=
          ⟨(hfI a).1.trans_lt ht.1,ht.2.trans_le (hfI b).2⟩
        obtain ⟨S,hS,hcon,_,hd,hval,hhit⟩ :=
          scalar_ambient_level e he Cells ρ hρ hadm n hn d₁ hd₁ t ht01
        obtain ⟨v,hv⟩ := hhit π hπr ht.1 ht.2
        refine ⟨S,fun _ => ⟨hcon.isPreconnected,hdR.trans_le hd,⟨π v,hv,?_⟩,hval⟩⟩
        have hpv := hπ v
        change dist o (π v) < L*s at hpv
        simpa only [dist_comm] using hpv.le.trans hsR
      · exact ⟨∅,fun htt => (ht htt).elim⟩
    choose Clevel hlevel using hlev
    exact hbound q ξ p h hh (extend e f) lo hi o R r d₀ (f a) (f b)
      hR hr hrR hAr hscaleT hscaleS hab hlu hq hqsep hξsep hpsep hnet hzoom hlow
      hlarge hrange ω hω ρ hρ hlocal Clevel hlevel
  rcases le_total (f a) (f b) with hab | hab
  · exact hordered a b ha hb hab
  · change (f b-f a)^2 ≤ _
    have hsquare : (f b-f a)^2 = (f a-f b)^2 := by ring
    rw [hsquare]
    exact hordered b a hb ha hab

end CannonApprox

end
end
end
end
end
end
end
end
end

end OAI
