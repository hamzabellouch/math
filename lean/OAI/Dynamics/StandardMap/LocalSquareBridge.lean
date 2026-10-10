import OAI.Dynamics.StandardMap.BridgeScalars

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma actual_local_square_product (k : ℝ) (hc : BridgeScalarControl k)
    (np nm Bp Bm : ℕ) (hnp : 1 ≤ np) (hnm : 1 ≤ nm)
    (hBp : Bp=np ∨ Bp=np+1) (hBm : Bm=nm ∨ Bm=nm+1) (hBp2 : 2 ≤ Bp) (hBm2 : 2 ≤ Bm)
    (lx ux ly uy : ℝ) (hly : ly ≤ uy) (hlxlen : ux-lx < 1/4) (hlylen : uy-ly < 1/4)
    (hIx : Icc lx ux ⊆ Icc (0:ℝ) 1) (hIy : Icc ly uy ⊆ Icc (0:ℝ) 1)
    (W H : Torus → ℝ) (hW : Continuous W) (hH : Continuous H) (hW0 : ∀ z, 0 ≤ W z)
    (h δ : ℝ) (hδ : 0 ≤ δ) (hδh : δ < h/2)
    (hWp : ∀ z w : ℝ × ℝ,
      dist (liftIter k (-(Bm:ℤ)) z) (liftIter k (-(Bm:ℤ)) w) ≤
        8/growthBase k^((4/5:ℝ)*(Bm-1:ℕ)) → |W (liftProjection z)-W (liftProjection w)| ≤ δ)
    (hHp : ∀ z w : ℝ × ℝ,
      dist (liftIter k (Bp:ℤ) z) (liftIter k (Bp:ℤ) w) ≤
        8/growthBase k^((4/5:ℝ)*(Bp-1:ℕ)) → |H (liftProjection z)-H (liftProjection w)| ≤ δ) :
    (ENNReal.ofReal (Real.exp (-1152*Real.pi))*volume (Icc ly uy))*
      (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (Icc lx ux))*
      (∫⁻ z in {z : ℝ × ℝ | z ∈ Icc lx ux ×ˢ Icc ly uy ∧
        prefixEligible k Bp (np+1) z.swap ∧ prefixEligible k Bm (nm+1) z ∧ h < H (liftProjection z)},
        ENNReal.ofReal (W (liftProjection z))) ≤
    ENNReal.ofReal (Real.exp (1152*Real.pi))*
      (16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+
        (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume (Icc lx ux))*
          ENNReal.ofReal δ*volume (Icc ly uy))*
      (16*area {z | h/2 < H z}) := by
  classical
  let Ix := Icc lx ux
  let Iy := Icc ly uy
  let square := Ix ×ˢ Iy
  let S : Set (ℝ × ℝ) := (Iy ×ˢ Ix) ∩
    {z | prefixEligible k Bp (np+1) z ∧ h ≤ H (liftProjection z.swap)}
  have hS : IsCompact S := by
    apply (isCompact_Icc.prod isCompact_Icc).inter_right
    exact (isClosed_prefixEligible k Bp (np+1)).inter
      (isClosed_le continuous_const (hH.comp (continuous_liftProjection.comp continuous_swap)))
  have hdir (z : ℝ × ℝ) (hz : z ∈ S) := hc.prefix_dirichlet Bp np hnp hBp hBp2 z hz.2.1
  obtain ⟨E,X,hE,hX,hXbase,hcover,hinj,hreg,hrep⟩ := actual_compact_graph_labels_full k np hnp
    hc.nonneg hc.graph_geom hc.graph_small S hS (fun z hz => (hdir z hz).1)
    (fun z hz => (hdir z hz).2) ly uy ly ⟨le_rfl,hly⟩ hlylen (fun z hz => hz.1.1)
  let f : (ℝ × ℝ) → (ℝ × ℝ) := fun z => (X z,z.2)
  have hfc : ContinuousOn f (E ×ˢ Iy) := hX.prodMk continuous_snd.continuousOn
  obtain ⟨J,hJ,hdet⟩ := forward_chart_jacobian k np E Iy X ly hX
    (fun s hs y hy => (hreg s hs y hy).1)
    (fun s hs y hy => (hreg s hs y hy).2.1)
    (fun s hs y hy => (hreg s hs y hy).2.2.2.2)
  let V := f '' (E ×ˢ Iy)
  have hV : IsCompact V := (hE.prod isCompact_Icc).image_of_continuousOn hfc
  have hVH : ∀ z ∈ V, liftProjection z ∈ {z | h/2 < H z} := by
    rintro z ⟨v,hv,rfl⟩
    obtain ⟨w,hw,hwX⟩ := hrep v.1 hv.1
    have hh := graph_endpoint_close k hc.nonneg (f v) w.swap np Bp hnp hBp
      (hwX v.2 hv.2).1 (hwX v.2 hv.2).2.2
    have htpt := hHp (f v) w.swap hh
    have hth := hw.2.2
    change h/2 < H (liftProjection (f v))
    have hab := (abs_le.mp htpt).1
    linarith
  have hVb : V ⊆ Ioc (-2:ℝ) 2 ×ˢ Ioc (-2:ℝ) 2 := by
    rintro z ⟨v,hv,rfl⟩
    obtain ⟨w,hw,hwX⟩ := hrep v.1 hv.1
    have hy := hIy hv.2
    have hyw := hIy hw.1.1
    have hxw := hIx hw.1.2
    have hd : |v.2-w.1| ≤ 1 := by apply abs_le.mpr; constructor <;> linarith [hy.1,hy.2,hyw.1,hyw.2]
    have hmove := (hwX v.2 hv.2).2.1
    have ha0 : 0 ≤ 24/growthBase k^((4/5:ℝ)) := by
      have hp : 0 < growthBase k := by have := growthBase_ge_four k hc.nonneg; linarith
      positivity
    refine ⟨interval_small_move w.2 (X v) hxw (hmove.trans ?_),⟨by linarith [hy.1],by linarith [hy.2]⟩⟩
    nlinarith [hc.slope_small,abs_nonneg (v.2-w.1)]
  have hVm : volume V ≤ 16*area {z | h/2 < H z} :=
    bounded_lift_event _ V (isOpen_lt continuous_const hH).measurableSet hV.measurableSet hVb hVH
  let U : Set (ℝ × ℝ) := square ∩ {z | prefixEligible k Bm (nm+1) z}
  have hUcl : IsClosed U := (isClosed_Icc.prod isClosed_Icc).inter (isClosed_prefixEligible k Bm (nm+1))
  let T := (E ×ˢ Iy) ∩ f ⁻¹' U
  have hTcl : IsClosed T := hfc.preimage_isClosed_of_isClosed (hE.isClosed.prod isClosed_Icc) hUcl
  let A := {z : ℝ × ℝ | z ∈ square ∧ prefixEligible k Bp (np+1) z.swap ∧
    prefixEligible k Bm (nm+1) z ∧ h < H (liftProjection z)}
  have hA : A ⊆ f '' T := by
    intro z hz
    have hzS : z.swap ∈ S := ⟨⟨hz.1.2,hz.1.1⟩,hz.2.1,by simpa only [Prod.swap_swap] using hz.2.2.2.le⟩
    obtain ⟨s,hs,hxs⟩ := hcover z.swap hzS
    change X (s,z.2)=z.1 at hxs
    refine ⟨(s,z.2),⟨⟨hs,hz.1.2⟩,?_⟩,?_⟩
    · change (X (s,z.2),z.2) ∈ U
      rw [hxs]
      exact ⟨hz.1,hz.2.2.1⟩
    · exact Prod.ext hxs rfl
  let c := Real.exp (-1152*Real.pi)
  let C := Real.exp (1152*Real.pi)
  let d := ENNReal.ofReal (c*(1-(24/growthBase k^((4/5:ℝ)))^2))*volume Ix
  let K := 16*(∫⁻ z, ENNReal.ofReal (W z) ∂area)+d*ENNReal.ofReal δ*volume Iy
  have hslice (s : ℝ) (hs : s ∈ E) : d*(∫⁻ y in Iy, T.indicator ((fun z => ENNReal.ofReal (W (liftProjection z))) ∘ f) (s,y)) ≤ K := by
    let Xs : ℝ → ℝ := fun y => X (s,y)
    let Xs' : ℝ → ℝ := fun y => boundaryValue (orbitCoefficient k y (Xs y)) (np+1)
    let D : Set ℝ := Iy ∩ (fun y => (Xs y,y)) ⁻¹' U
    have hXs : ContinuousOn Xs Iy := hX.comp (continuousOn_const.prodMk continuousOn_id) (fun y hy => ⟨hs,hy⟩)
    have hDc : IsClosed D := (hXs.prodMk continuousOn_id).preimage_isClosed_of_isClosed isClosed_Icc hUcl
    have hxi (y : ℝ) (hy : y ∈ D) : Xs y ∈ Ix := hy.2.1.1
    have hxd (y : ℝ) (hy : y ∈ Iy) : HasStrictDerivAt Xs (Xs' y) y := (hreg s hs y hy).2.2.1
    have hxS (y : ℝ) (hy : y ∈ Iy) : |Xs' y| ≤ 24/growthBase k^((4/5:ℝ)) := (hreg s hs y hy).2.2.2.1
    have hxL (y : ℝ) (hy : y ∈ D) (z : ℝ) (hz : z ∈ D) :
        |Xs y-Xs z| ≤ (24/growthBase k^((4/5:ℝ)))*|y-z| :=
      forward_graph_lipschitz Iy Xs Xs' _ (convex_Icc ly uy)
        (fun y hy => (hxd y hy).hasDerivAt) hxS y z hy.1 hz.1
    have hdirD (y : ℝ) (hy : y ∈ D) := hc.prefix_dirichlet Bm nm hnm hBm hBm2 (Xs y,y) hy.2.2
    have hb := actual_backward_slice k nm Bm hnm hBm hc.nonneg hc.graph_geom hc.graph_small hc.slope_small
      D hDc.measurableSet Xs Xs' lx ux hlxlen hIx (fun y hy => hIy hy.1)
      hxi (fun y hy => hxd y hy.1) (fun y hy => hxS y hy.1) hxL
      (fun y hy => (hdirD y hy).1) (fun y hy => (hdirD y hy).2) W hW hW0 δ hδ hWp
    have he : (fun y => T.indicator ((fun z => ENNReal.ofReal (W (liftProjection z))) ∘ f) (s,y)) =
        D.indicator (fun y => ENNReal.ofReal (W (liftProjection (Xs y,y)))) := by
      funext y
      by_cases hy : y ∈ D
      · have ht : (s,y) ∈ T := ⟨⟨hs,hy.1⟩,hy.2⟩
        simp only [indicator_of_mem ht,indicator_of_mem hy,Function.comp_apply,f,Xs]
      · have ht : (s,y) ∉ T := fun ht => hy ⟨ht.1.2,ht.2⟩
        simp only [indicator_of_notMem ht,indicator_of_notMem hy]
    rw [he,setLIntegral_indicator hDc.measurableSet,inter_eq_left.mpr (show D ⊆ Iy from inter_subset_left)]
    apply hb.trans
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_left (measure_mono (show D ⊆ Iy from inter_subset_left)) (by positivity)
  have hb := scaled_weighted_chart_product E Iy T A V f J
    (fun z => ENNReal.ofReal (W (liftProjection z))) c C d K
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt (isCompact_Icc.measure_lt_top (μ := (volume : Measure ℝ)))))
    hE.measurableSet measurableSet_Icc hTcl.measurableSet inter_subset_left hA Subset.rfl
    hJ hinj (fun z hz => (hdet z hz).1) (fun z hz => (hdet z hz).2) hslice
  exact hb.trans (mul_le_mul_of_nonneg_left hVm (by positivity))
end StandardMapEntropy

end OAI
