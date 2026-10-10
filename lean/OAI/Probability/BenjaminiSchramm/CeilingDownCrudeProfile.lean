import OAI.Probability.BenjaminiSchramm.UniformHeightDescent
import OAI.Probability.BenjaminiSchramm.FirstHeightPeakWalk
import OAI.Probability.BenjaminiSchramm.SlabFractionalProfileShift

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem stationaryOrbitHeight_bounded_descent_to_level
    [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ k : ℝ, 0 ≤ k → ∀ x,
      ∃ y, ∃ w : G.fullGraph.Walk x y, (w.length : ℝ) ≤ A*k+B ∧
        -k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y ∧
        G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y ≤ -k ∧
        ∀ v ∈ w.support, G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x y ≤
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0 := by
  obtain ⟨ε,hε,L,hstep⟩ := G.stationaryOrbitHeight_uniform_descent hc hl hq μ hμ hstat hu
  let a := G.stationaryOrbitWeight μ
  refine ⟨(L : ℝ)/ε+1,L,by positivity,Nat.cast_nonneg _,fun k hk x => ?_⟩
  let n := ⌈k/ε⌉₊
  have hn : k ≤ (n : ℝ)*ε := (div_le_iff₀ hε).mp (Nat.le_ceil (k/ε))
  have hn' : (n : ℝ) ≤ k/ε+1 := (Nat.ceil_lt_add_one (div_nonneg hk hε.le)).le
  obtain ⟨y,w,hwlen,hw,hwy⟩ := G.height_descent_iterate hc hl a ε hε.le L hstep n x
  let f := fun v => -G.orbitAdjustedHeight a x v
  have hj : ∀ {u v}, G.fullGraph.Adj u v → |f v-f u| ≤ R := by
    intro u v huv
    have huv' : (Percolation.openSimpleGraph G.ends Set.univ).Adj u v := by
      rw [←criticalModel_openGraph G.ends Set.univ]
      exact huv
    obtain ⟨e,_he,he⟩ := huv'.2
    have hv := hjump e u v (by rw [he]; simp) (by rw [he]; simp)
    have hh : |G.orbitAdjustedHeight a x v-G.orbitAdjustedHeight a x u| ≤ R := by
      rw [G.orbitAdjustedHeight_change_base hc hl a x u v]
      simpa only [add_sub_cancel_left] using hv
    simpa only [f,neg_sub_neg,abs_sub_comm] using hh
  obtain ⟨z,q,hqlen,hz,hzR,hbound⟩ := first_height_peak_walk f R hR hj w 0 k
    (by simp [f]) (by simpa [f] using hk) (by dsimp [f]; linarith)
    (fun v hv => by dsimp [f]; exact neg_nonneg.mpr (hw v hv))
  refine ⟨z,q,?_,by dsimp [f] at hzR; linarith,by dsimp [f] at hz; linarith,?_⟩
  · have hqn : q.length ≤ n*L := hqlen.trans hwlen
    have hqn' : (q.length : ℝ) ≤ (n : ℝ)*L := by exact_mod_cast hqn
    have hm := mul_le_mul_of_nonneg_right hn' (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    calc
      _ ≤ (n : ℝ)*L := hqn'
      _ ≤ (k/ε+1)*L := hm
      _ = ((L : ℝ)/ε+1)*k+L-k := by ring
      _ ≤ ((L : ℝ)/ε+1)*k+L := by linarith
  · intro v hv
    have hh := hbound v hv
    dsimp [f] at hh
    exact ⟨by linarith [hh.2],by linarith [hh.1]⟩

variable [Countable V] [Countable E]

theorem ceiling_down_crude_profile [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp0 : (0 : ℝ) < p) (hp1 : (p : ℝ) < 1)
    (Vcoef : ℝ) (hV : 0 < Vcoef)
    (hzero : ∀ q : ℝ, 0 < q → q < 1 → ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ c : ℝ, 0 ≤ c → ∀ x : V,
        (∫⁻ ω, (restrictedLayerCount G.ends
          (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ c})
          {v | -2*R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
            G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 2*R} ω x)^q ∂G.law p) ≤
          C*ENNReal.ofReal (Real.exp (Vcoef*c))) :
    ∃ T : ℝ, 0 < T ∧ ∀ q : ℝ, 0 < q → q < 1 → ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ k : ℝ, 0 ≤ k → ∀ x : V,
        (∫⁻ ω, (restrictedLayerCount G.ends
          (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0})
          {v | -k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
            G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ -k+R} ω x)^q ∂G.law p) ≤
          C*ENNReal.ofReal (Real.exp (T*k)) := by
  let a := G.stationaryOrbitWeight μ
  obtain ⟨A,B,hA,hB,hpaths⟩ := G.stationaryOrbitHeight_bounded_descent_to_level
    hc hl hq μ hμ hstat hu R hR.le hjump
  let δ := min (p : ℝ) (1-p)
  have hδ : 0 < δ := lt_min hp0 (sub_pos.mpr hp1)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans p.2.2
  let s := -Real.log δ
  have hs : 0 ≤ s := neg_nonneg.mpr (Real.log_nonpos hδ.le hδ1)
  let T := s*A+Vcoef+1
  refine ⟨T,by dsimp [T]; positivity,fun q hq0 hq1 => ?_⟩
  obtain ⟨D,hD,hbound⟩ := hzero q hq0 hq1
  refine ⟨D*ENNReal.ofReal (Real.exp (s*B+Vcoef*R)),
    ENNReal.mul_lt_top hD ENNReal.ofReal_lt_top,fun k hk x => ?_⟩
  obtain ⟨y,w,hlen,hylo,hyhi,hw⟩ := hpaths k hk x
  let h := G.orbitAdjustedHeight a x y
  let I := Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight a x v ≤ 0}
  let J := Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight a y v ≤ -h}
  let W : Set V := {v | -k-R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ -k+R}
  let Z : Set V := {v | -2*R ≤ G.orbitAdjustedHeight a y v ∧ G.orbitAdjustedHeight a y v ≤ 2*R}
  have hIJ : I ⊆ J := Percolation.internalEdges_mono G.ends (by
    intro v hv
    change G.orbitAdjustedHeight a x v ≤ 0 at hv
    change G.orbitAdjustedHeight a y v ≤ -h
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y v
    dsimp [h]
    linarith)
  have hWZ : W ⊆ Z := by
    intro v hv
    have hh := G.orbitAdjustedHeight_change_base hc hl a x y v
    change -k-R ≤ G.orbitAdjustedHeight a x v ∧ G.orbitAdjustedHeight a x v ≤ -k+R at hv
    exact ⟨by linarith [hv.1],by linarith [hv.2]⟩
  let f : G.fullGraph →g Percolation.openSimpleGraph G.ends Set.univ :=
    ⟨id,fun {_ _} h => by rw [←criticalModel_openGraph G.ends Set.univ]; exact h⟩
  obtain ⟨F,hF,hconn⟩ := walk_finite_open_restriction G.ends (w.reverse.map f)
    {v | G.orbitAdjustedHeight a y v ≤ -h} (by
      intro v hv
      have hv' : v ∈ w.support := by
        rw [SimpleGraph.Walk.support_map] at hv
        change v ∈ w.reverse.support.map id at hv
        simpa only [List.map_id_fun,id_eq,SimpleGraph.Walk.support_reverse,List.mem_reverse] using hv
      have hh := G.orbitAdjustedHeight_change_base hc hl a x y v
      dsimp [h]
      linarith [(hw v hv').2])
  have hcard : F.card ≤ w.length := by
    simpa only [SimpleGraph.Walk.length_map,SimpleGraph.Walk.length_reverse] using hF
  have hcost : ENNReal.ofReal (δ^w.length) ≤ ENNReal.ofReal (δ^F.card) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hδ.le hδ1 hcard)
  have hXY := (mul_le_mul' hcost le_rfl).trans
    (forced_path_fractional_layer_comparison G.ends p F I J W Z hIJ hWZ y x hconn hq0.le)
  have hcancel := finite_energy_cancel_length _ _ δ A B k w.length hδ hδ1 hlen hXY
  have hceil : 0 ≤ -h := by dsimp [h]; linarith
  have hmoment := hbound (-h) hceil y
  apply hcancel.trans ((mul_le_mul' le_rfl hmoment).trans ?_)
  have he : -Real.log δ*(A*k+B)+Vcoef*(-h) ≤ (s*B+Vcoef*R)+T*k := by
    have hh : -h ≤ k+R := by dsimp [h]; linarith
    have hh' := mul_le_mul_of_nonneg_left hh hV.le
    dsimp [s,T]
    nlinarith
  calc
    _ = D*ENNReal.ofReal (Real.exp (-Real.log δ*(A*k+B)+Vcoef*(-h))) := by
      rw [Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]
      ac_rfl
    _ ≤ D*ENNReal.ofReal (Real.exp ((s*B+Vcoef*R)+T*k)) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he))
    _ = _ := by rw [Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _),mul_assoc]

end CriticalPercolation.BondGraph

end

end OAI
