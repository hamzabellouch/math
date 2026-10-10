import OAI.Probability.BenjaminiSchramm.LayerFirstMoments
import OAI.Probability.BenjaminiSchramm.IntegerLayerFirstVisit
import OAI.Probability.BenjaminiSchramm.CrossingPositivity

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm

lemma integer_first_layer_walk {V : Type*} {H : SimpleGraph V}
    (f : V → ℤ) (hjump : ∀ {v w}, H.Adj v w → f w ≤ f v+1 ∧ f v ≤ f w+1)
    {x y : V} (p : H.Walk x y) (m : ℤ) (hx : f x < m) (hy : m ≤ f y) :
    ∃ z, f z=m ∧ ∃ q : H.Walk x z, q.length ≤ p.length ∧
      ∀ v ∈ q.support, f v ≤ m := by
  let S := p.support.toFinset.filter fun v => m ≤ f v
  have hyS : y ∈ S := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr p.end_mem_support,hy⟩
  obtain ⟨z,hzS,hzp,hfirst⟩ := p.exists_mem_support_forall_mem_support_imp_eq S
    ⟨y,Finset.mem_filter.mpr ⟨hyS,p.end_mem_support⟩⟩
  have hz : m ≤ f z := (Finset.mem_filter.mp hzS).2
  have hbelow (v : V) (hv : v ∈ (p.takeUntil z hzp).support) (hvz : v ≠ z) : f v < m := by
    by_contra hn
    have hvS : v ∈ S := Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr (p.support_takeUntil_subset_support hzp hv),le_of_not_gt hn⟩
    exact hvz (hfirst v hvS hv)
  have hj {v w : V} (hvw : H.Adj v w) : |(f w : ℝ)-(f v : ℝ)| ≤ 1 := by
    obtain ⟨h₁,h₂⟩ := hjump hvw
    have h₁' : (f w : ℝ) ≤ (f v : ℝ)+1 := by exact_mod_cast h₁
    have h₂' : (f v : ℝ) ≤ (f w : ℝ)+1 := by exact_mod_cast h₂
    rw [abs_le]
    constructor <;> linarith
  have hx' : (f x : ℝ) < (m : ℝ)-1/2 := by
    have hh : f x ≤ m-1 := by omega
    have hh' : (f x : ℝ) ≤ (m : ℝ)-1 := by exact_mod_cast hh
    linarith
  have hbl : ∀ v ∈ (p.takeUntil z hzp).support, v ≠ z → (f v : ℝ) < (m : ℝ)-1/2 := by
    intro v hv hvz
    have hh : f v ≤ m-1 := by have := hbelow v hv hvz; omega
    have hh' : (f v : ℝ) ≤ (m : ℝ)-1 := by exact_mod_cast hh
    linarith
  have hzhi := walk_endpoint_height_bound (fun v => (f v : ℝ)) 1 ((m : ℝ)-1/2)
    (by norm_num) hj (p.takeUntil z hzp) hx' hbl
  have hzm : f z=m := by
    have hh : f z ≤ m := (integer_half_ceiling _ _).mp hzhi
    omega
  refine ⟨z,hzm,p.takeUntil z hzp,p.length_takeUntil_le_length hzp,fun v hv => ?_⟩
  by_cases hvz : v=z
  · simp only [hvz,hzm,le_refl]
  · exact (hbelow v hv hvz).le

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] in
lemma adjustedUpLayerMoment_walk_lower (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (R u : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e → |G.orbitAdjustedHeight a v w| ≤ R)
    (p : unitInterval) (n : ℕ) (hn : 0 < n) {x y : V}
    (w : G.fullGraph.Walk x y) (hy : (n : ℤ) ≤ G.adjustedLayerIndex a R u x y) :
    ENNReal.ofReal ((p : ℝ)^w.length) ≤ G.adjustedUpLayerMoment a R p n x u := by
  let f := G.adjustedLayerIndex a R u x
  have hj {v z : V} (hvz : G.fullGraph.Adj v z) : f z ≤ f v+1 ∧ f v ≤ f z+1 := by
    obtain ⟨⟨e,_he,heq⟩,_hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hvz
    have hh := G.adjustedLayerIndex_edge_jump hc hl a R u hR hjump x v z e
      (by rw [heq]; simp) (by rw [heq]; simp)
    change f v-1 ≤ f z ∧ f z ≤ f v+1 at hh
    exact ⟨hh.2,by omega⟩
  have hx : f x < (n : ℤ) := by simp only [f,G.adjustedLayerIndex_self]; exact_mod_cast hn
  obtain ⟨z,hz,q,hqlen,hq⟩ := integer_first_layer_walk f hj w n hx hy
  have hg : G.fullGraph = Percolation.openSimpleGraph G.ends Set.univ :=
    criticalModel_openGraph G.ends Set.univ
  let ι : G.fullGraph →g Percolation.openSimpleGraph G.ends Set.univ :=
    ⟨id,fun {_ _} h => by simpa only [←hg,id_eq] using h⟩
  obtain ⟨s,hs,hconn⟩ := walk_finite_open_restriction G.ends (q.map ι)
    {v | f v ≤ (n : ℤ)} (by
      intro v hv
      rw [SimpleGraph.Walk.support_map] at hv
      change v ∈ q.support.map id at hv
      exact hq v (by simpa only [List.map_id_fun,id_eq] using hv))
  have hslen0 : s.card ≤ q.length := by simpa only [SimpleGraph.Walk.length_map] using hs
  have hslen : s.card ≤ w.length := hslen0.trans hqlen
  let F : Set (Set E) := {ω | (s : Set E) ⊆ ω}
  have hF : MeasurableSet F := Percolation.measurableSet_finiteWitness F
    (fun _ _ h hs => hs.trans h) (fun _ hs => ⟨s,hs,Set.Subset.rfl⟩)
  have hmeasure : G.law p F = ENNReal.ofReal ((p : ℝ)^s.card) := by
    rw [←Percolation.finite_open_probability p s]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  calc
    _ ≤ ENNReal.ofReal ((p : ℝ)^s.card) := ENNReal.ofReal_le_ofReal
      (pow_le_pow_of_le_one p.2.1 p.2.2 hslen)
    _ = G.law p F := hmeasure.symm
    _ = ∫⁻ ω, F.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂G.law p :=
      (lintegral_indicator_one hF).symm
    _ ≤ _ := by
      apply lintegral_mono
      intro ω
      by_cases hω : ω ∈ F
      · rw [Set.indicator_of_mem hω]
        apply le_trans _ (ENNReal.le_tsum z)
        exact (ite_eq_left ⟨hz,hconn ω hω⟩).symm.le
      · rw [Set.indicator_of_notMem hω]
        exact bot_le

theorem adjustedUpLayerMoment_finite_energy [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ) (hu : ¬G.CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp : 0 < (p : ℝ)) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ (n : ℕ) (x : V) (u : ℝ),
      ENNReal.ofReal ((p : ℝ)^(A*n+B)) ≤
        G.adjustedUpLayerMoment (G.stationaryOrbitWeight μ) R p n x u := by
  let a := G.stationaryOrbitWeight μ
  obtain ⟨A,B,hA,hB,hpath⟩ := G.stationaryOrbitHeight_orbit_above hc hl hq μ hμ hstat hu
  refine ⟨A*R,A*R+B,mul_pos hA hR,add_nonneg (mul_pos hA hR).le hB,fun n x u => ?_⟩
  by_cases hn : n=0
  · subst n
    have hb : (p : ℝ)^(A*R+B) ≤ 1 := Real.rpow_le_one p.2.1 p.2.2 (add_nonneg (mul_pos hA hR).le hB)
    have hz := G.adjustedUpLayerMoment_zero_ge_one a R p x u
    rw [←ENNReal.ofReal_one] at hz
    simpa only [Nat.cast_zero,mul_zero,zero_add,a] using
      (ENNReal.ofReal_le_ofReal hb).trans hz
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨y,w,_horb,hlen,_hlow,hy⟩ := hpath (((n : ℝ)+1)*R)
    (mul_nonneg (by positivity) hR.le) x (G.vertexOrbit x)
  have hend : (n : ℤ) ≤ G.adjustedLayerIndex a R u x y := by
    have hh := (G.adjustedLayerIndex_height_bounds a R u hR x y).2
    by_contra hf
    have hi : G.adjustedLayerIndex a R u x y ≤ (n : ℤ)-1 := by omega
    have hir : (G.adjustedLayerIndex a R u x y : ℝ) ≤ (n : ℝ)-1 := by exact_mod_cast hi
    nlinarith
  have hlen' : (w.length : ℝ) ≤ A*R*(n : ℝ)+(A*R+B) := by nlinarith [hlen]
  have hpow := Real.rpow_le_rpow_of_exponent_ge hp p.2.2 hlen'
  rw [Real.rpow_natCast] at hpow
  exact (ENNReal.ofReal_le_ofReal hpow).trans
    (G.adjustedUpLayerMoment_walk_lower hc hl a R u hR hjump p n hnpos w hend)

omit [Countable V] [Countable E] in
theorem stationaryOrbitHeight_bounded_jumps [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i) :
    ∃ R : ℝ, 0 < R ∧ ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R := by
  obtain ⟨K,hK⟩ := G.uniform_ball_bound hq 1
  obtain ⟨D,hD,hbound⟩ := G.stationaryOrbitHeight_uniform_comparison hc hl μ hμ
  refine ⟨D+max 0 (Real.log (K : ℝ))+1,by positivity,fun e v w hv hw => ?_⟩
  have hr := G.modularLogHeight_edge_jump hc hl K hK v v w e hv hw
  rw [G.modularLogHeight_self,sub_zero] at hr
  have hh := abs_add_le
    (G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w-G.modularLogHeight v w)
    (G.modularLogHeight v w)
  rw [sub_add_cancel] at hh
  exact hh.trans ((add_le_add (hbound v w) (hr.trans (le_max_right _ _))).trans
    (le_add_of_nonneg_right (by norm_num)))

end CriticalPercolation.BondGraph

end

end OAI
