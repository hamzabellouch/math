import OAI.Dynamics.StandardMap.EntropyIntegral

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma actual_backward_carry_full (k : ℝ) (n : ℕ) (hn : 1 ≤ n) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (D : Set ℝ) (X X' : ℝ → ℝ) (l u : ℝ)
    (hlen : u-l < 1/4)
    (hXI : ∀ y ∈ D, X y ∈ Icc l u)
    (hX : ∀ y ∈ D, HasStrictDerivAt X (X' y) y)
    (hXs : ∀ y ∈ D, |X' y| ≤ 24/growthBase k^((4/5:ℝ)))
    (hXL : ∀ y ∈ D, ∀ z ∈ D, |X y-X z| ≤ (24/growthBase k^((4/5:ℝ)))*|y-z|)
    (htrans : (24/growthBase k^((4/5:ℝ)))^2 < 1)
    (ht : ∀ y ∈ D, tSolution (orbitCoefficient k (X y) y) (n+1) ≠ 0)
    (hU : ∀ y ∈ D, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k (X y) y) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ))) :
    ∃ Θ : ℝ × ℝ → ℝ, ∃ J : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ),
      ContinuousOn Θ (Icc l u ×ˢ D) ∧
      (∀ y ∈ D, Θ (X y,y)=y) ∧
      (∀ y ∈ D, ∀ v ∈ Icc l u,
        liftedOrbit k v (Θ (v,y)) (n+1)=liftedOrbit k (X y) y (n+1)) ∧
      InjOn (fun z : ℝ × ℝ => (z.1,Θ z)) (Icc l u ×ˢ D) ∧
      (∀ z ∈ Icc l u ×ˢ D, HasFDerivWithinAt (fun w => (w.1,Θ w)) (J z) (Icc l u ×ˢ D) z) ∧
      (∀ z ∈ Icc l u ×ˢ D,
        Real.exp (-1152*Real.pi)*(1-(24/growthBase k^((4/5:ℝ)))^2) ≤ |(J z).det| ∧
        |(J z).det| ≤ Real.exp (1152*Real.pi)*(1+(24/growthBase k^((4/5:ℝ)))^2)) ∧
      (∀ y ∈ D, ∀ v ∈ Icc l u,
        |Θ (v,y)-y| ≤ (24/growthBase k^((4/5:ℝ)))*|v-X y| ∧
        ∀ i : Fin n, |liftedOrbit k v (Θ (v,y)) (i+1)-liftedOrbit k (X y) y (i+1)| ≤
          8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) := by
  classical
  let a : ℝ := 24/growthBase k^((4/5:ℝ))
  have hp : 0 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have ha : 0 ≤ a := div_nonneg (by norm_num) (Real.rpow_pos_of_pos hp _).le
  let S : Set (ℝ × ℝ) := (fun y => (X y,y)) '' D
  have htS : ∀ z ∈ S, tSolution (orbitCoefficient k z.1 z.2) (n+1) ≠ 0 := by
    rintro z ⟨y,hy,rfl⟩; exact ht y hy
  have hUS : ∀ z ∈ S, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k z.1 z.2) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ)) := by
    rintro z ⟨y,hy,rfl⟩; exact hU y hy
  obtain ⟨b,hbc,hb⟩ := continuous_contracting_graph_pack_full k n hn hk hq hsmall S htS hUS
  let Θ : ℝ × ℝ → ℝ := fun z => b (X z.2,z.2) (z.1-X z.2)
  have hmem (y : ℝ) (hy : y ∈ D) : (X y,y) ∈ S := mem_image_of_mem _ hy
  have hdist (y : ℝ) (hy : y ∈ D) (v : ℝ) (hv : v ∈ Icc l u) : |v-X y| < 1/4 := by
    have hxy := hXI y hy
    apply abs_lt.mpr
    constructor <;> linarith [hxy.1,hxy.2,hv.1,hv.2]
  have hXc : ContinuousOn X D := fun y hy => (hX y hy).hasDerivAt.continuousAt.continuousWithinAt
  have hXcs : ContinuousOn (fun z : ℝ × ℝ => X z.2) (Icc l u ×ˢ D) :=
    hXc.comp continuous_snd.continuousOn (fun z hz => hz.2)
  have hΘ : ContinuousOn Θ (Icc l u ×ˢ D) := by
    apply hbc.comp ((hXcs.prodMk continuous_snd.continuousOn).prodMk
      (continuous_fst.continuousOn.sub hXcs))
    intro z hz
    exact ⟨hmem z.2 hz.2,abs_le.mp (hdist z.2 hz.2 z.1 hz.1).le⟩
  have hbase (y : ℝ) (hy : y ∈ D) : Θ (X y,y)=y := by
    simpa [Θ] using (hb (X y,y) (hmem y hy)).1
  have hlevel (y : ℝ) (hy : y ∈ D) (v : ℝ) (hv : v ∈ Icc l u) :
      liftedOrbit k v (Θ (v,y)) (n+1)=liftedOrbit k (X y) y (n+1) := by
    simpa only [add_sub_cancel] using (hb (X y,y) (hmem y hy)).2.1 (v-X y) (hdist y hy v hv).le
  have htn (y : ℝ) (hy : y ∈ D) (v : ℝ) (hv : v ∈ Icc l u) :
      tSolution (orbitCoefficient k v (Θ (v,y))) (n+1) ≠ 0 := by
    simpa only [add_sub_cancel] using (hb (X y,y) (hmem y hy)).2.2.1 (v-X y) (hdist y hy v hv).le
  have hback (y : ℝ) (hy : y ∈ D) (v : ℝ) (hv : v ∈ Icc l u) (w : ℝ) (hw : w ∈ Icc l u) :
      |Θ (v,y)-Θ (w,y)| ≤ a*|v-w| := by
    simpa only [sub_sub_sub_cancel_right] using (hb (X y,y) (hmem y hy)).2.2.2.2.2.1
      (v-X y) (w-X y) (hdist y hy v hv).le (hdist y hy w hw).le
  let J : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := fun z =>
    planeMatrix 1 0
      (-sSolution (orbitCoefficient k z.1 (Θ z)) (n+1)/tSolution (orbitCoefficient k z.1 (Θ z)) (n+1))
      ((tSolution (orbitCoefficient k (X z.2) z.2) (n+1)+sSolution (orbitCoefficient k (X z.2) z.2) (n+1)*X' z.2)/
        tSolution (orbitCoefficient k z.1 (Θ z)) (n+1))
  refine ⟨Θ,J,hΘ,hbase,hlevel,?_,?_,?_,?_⟩
  · apply transverse_sweep_injective (fun z : ℝ × ℝ => liftedOrbit k z.1 z.2 (n+1)) X Θ
      (Icc l u) D a a (convex_Icc l u).isPreconnected ha ha (by simpa only [← sq] using htrans)
      hXI hbase
    · intro y hy
      exact hΘ.comp (continuousOn_id.prodMk continuousOn_const) (fun v hv => ⟨hv,hy⟩)
    · exact hlevel
    · intro y hy v hv
      exact ⟨_,_,htn y hy v hv,hasStrictFDerivAt_liftedOrbit k v (Θ (v,y)) (n+1)⟩
    · exact hXL
    · exact hback
  · intro z hz
    apply sweep_graph_derivative (fun z : ℝ × ℝ => liftedOrbit k z.1 z.2 (n+1)) X Θ
      (Icc l u ×ˢ D) z _ _ _ _ _
      (hasStrictFDerivAt_liftedOrbit k z.1 (Θ z) (n+1))
      (hasStrictFDerivAt_liftedOrbit k (X z.2) z.2 (n+1)) (hX z.2 hz.2)
      (htn z.2 hz.2 z.1 hz.1) (hΘ z hz) _ (hlevel z.2 hz.2 z.1 hz.1)
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hlevel w.2 hw.2 w.1 hw.1
  · intro z hz
    have hr := (hb (X z.2,z.2) (hmem z.2 hz.2)).2.2.2.2.2.2.1 0 (z.1-X z.2)
      (by norm_num) (hdist z.2 hz.2 z.1 hz.1)
    simp only [add_zero,add_sub_cancel,(hb (X z.2,z.2) (hmem z.2 hz.2)).1] at hr
    have hs0 := (hb (X z.2,z.2) (hmem z.2 hz.2)).2.2.2.2.1 0 (by norm_num)
    simp only [add_zero,(hb (X z.2,z.2) (hmem z.2 hz.2)).1,boundaryValue,neg_div,abs_neg] at hs0
    have hbj := transverse_jacobian_bounds
      (sSolution (orbitCoefficient k (X z.2) z.2) (n+1))
      (tSolution (orbitCoefficient k (X z.2) z.2) (n+1))
      (tSolution (orbitCoefficient k z.1 (Θ z)) (n+1)) (X' z.2)
      a a (Real.exp (-1152*Real.pi)) (Real.exp (1152*Real.pi))
      (ht z.2 hz.2) (htn z.2 hz.2 z.1 hz.1) (Real.exp_pos _).le (Real.exp_pos _).le
      ha ha (by simpa only [← sq] using htrans.le)
      (by simpa only [abs_div] using hr.1) (by simpa only [abs_div] using hr.2)
      hs0 (hXs z.2 hz.2)
    simpa only [J,planeMatrix_det,one_mul,zero_mul,sub_zero,← sq] using hbj
  · intro y hy v hv
    refine ⟨?_,?_⟩
    · have hh := hback y hy v hv (X y) (hXI y hy)
      rw [hbase y hy] at hh
      exact hh
    · intro i
      have hh := (hb (X y,y) (hmem y hy)).2.2.2.2.2.2.2.1 (v-X y) (hdist y hy v hv).le i
      simpa only [add_sub_cancel] using hh
end StandardMapEntropy

end OAI
