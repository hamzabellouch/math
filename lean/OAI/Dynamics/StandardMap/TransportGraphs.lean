import OAI.Dynamics.StandardMap.MiddleCount

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma actual_compact_graph_labels_full (k : ℝ) (n : ℕ) (hn : 1 ≤ n) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (S : Set (ℝ × ℝ)) (hs : IsCompact S)
    (ht : ∀ z ∈ S, tSolution (orbitCoefficient k z.1 z.2) (n+1) ≠ 0)
    (hU : ∀ z ∈ S, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k z.1 z.2) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ)))
    (l u yc : ℝ) (hyc : yc ∈ Icc l u) (hlen : u-l < 1/4)
    (hSp : ∀ z ∈ S, z.1 ∈ Icc l u) :
    ∃ E : Set ℝ, ∃ X : ℝ × ℝ → ℝ,
      IsCompact E ∧ ContinuousOn X (E ×ˢ Icc l u) ∧
      (∀ s ∈ E, X (s,yc)=s) ∧
      (∀ z ∈ S, ∃ s ∈ E, X (s,z.1)=z.2) ∧
      InjOn (fun w => (X w,w.2)) (E ×ˢ Icc l u) ∧
      (∀ s ∈ E, ∀ y ∈ Icc l u,
        liftedOrbit k y (X (s,y)) (n+1)=liftedOrbit k yc s (n+1) ∧
        tSolution (orbitCoefficient k y (X (s,y))) (n+1) ≠ 0 ∧
        HasStrictDerivAt (fun v => X (s,v)) (boundaryValue (orbitCoefficient k y (X (s,y))) (n+1)) y ∧
        |boundaryValue (orbitCoefficient k y (X (s,y))) (n+1)| ≤ 24/growthBase k^((4/5:ℝ)) ∧
        Real.exp (-1152*Real.pi) ≤
          |tSolution (orbitCoefficient k yc s) (n+1)|/
          |tSolution (orbitCoefficient k y (X (s,y))) (n+1)| ∧
        |tSolution (orbitCoefficient k yc s) (n+1)|/
          |tSolution (orbitCoefficient k y (X (s,y))) (n+1)| ≤ Real.exp (1152*Real.pi)) ∧
      (∀ s ∈ E, ∃ z ∈ S, ∀ y ∈ Icc l u,
        liftedOrbit k y (X (s,y)) (n+1)=liftedOrbit k z.1 z.2 (n+1) ∧
        |X (s,y)-z.2| ≤ (24/growthBase k^((4/5:ℝ)))*|y-z.1| ∧
        ∀ i : Fin n, |liftedOrbit k y (X (s,y)) (i+1)-liftedOrbit k z.1 z.2 (i+1)| ≤
          8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) := by
  classical
  obtain ⟨b,hbc,hb⟩ := continuous_contracting_graph_pack_full k n hn hk hq hsmall S ht hU
  let I := Icc l u
  let g : (ℝ × ℝ) → ℝ → ℝ := fun z y => b z (y-z.1)
  have hdist (z : ℝ × ℝ) (hz : z ∈ S) (y : ℝ) (hy : y ∈ I) : |y-z.1| < 1/4 := by
    have hzI:=hSp z hz
    apply abs_lt.mpr
    constructor <;> linarith [hy.1,hy.2,hzI.1,hzI.2]
  have hgc : ContinuousOn (fun z : (ℝ × ℝ) × ℝ => g z.1 z.2) (S ×ˢ I) := by
    apply hbc.comp (continuous_fst.prodMk (continuous_snd.sub (continuous_fst.comp continuous_fst))).continuousOn
    intro z hz
    exact ⟨hz.1,abs_le.mp (hdist z.1 hz.1 z.2 hz.2).le⟩
  have hcont (z : ℝ × ℝ) (hz : z ∈ S) : ContinuousOn (g z) I :=
    hgc.comp (continuousOn_const.prodMk continuousOn_id) (fun y hy => ⟨hz,hy⟩)
  have hterm (z : ℝ × ℝ) (hz : z ∈ S) (y : ℝ) (hy : y ∈ I) :
      liftedOrbit k y (g z y) (n+1)=liftedOrbit k z.1 z.2 (n+1) := by
    simpa only [add_sub_cancel] using (hb z hz).2.1 (y-z.1) (hdist z hz y hy).le
  have htn (z : ℝ × ℝ) (hz : z ∈ S) (y : ℝ) (hy : y ∈ I) :
      tSolution (orbitCoefficient k y (g z y)) (n+1) ≠ 0 := by
    simpa only [add_sub_cancel] using (hb z hz).2.2.1 (y-z.1) (hdist z hz y hy).le
  have hreg (z : ℝ × ℝ) (hz : z ∈ S) (y : ℝ) (hy : y ∈ I) :
      ∃ s t : ℝ, t ≠ 0 ∧ HasStrictFDerivAt (fun v : ℝ × ℝ => liftedOrbit k v.1 v.2 (n+1))
        (s • ContinuousLinearMap.fst ℝ ℝ ℝ+t • ContinuousLinearMap.snd ℝ ℝ ℝ) (y,g z y) :=
    ⟨sSolution (orbitCoefficient k y (g z y)) (n+1),
      tSolution (orbitCoefficient k y (g z y)) (n+1),htn z hz y hy,
      hasStrictFDerivAt_liftedOrbit k y (g z y) (n+1)⟩
  have huni (z : ℝ × ℝ) (hz : z ∈ S) (w : ℝ × ℝ) (hw : w ∈ S)
      (he : g z yc=g w yc) : ∀ y ∈ I, g z y=g w y := by
    have htval : liftedOrbit k z.1 z.2 (n+1)=liftedOrbit k w.1 w.2 (n+1) := by
      rw [← hterm z hz yc hyc,← hterm w hw yc hyc,he]
    exact regular_graphs_coincide (fun v : ℝ × ℝ => liftedOrbit k v.1 v.2 (n+1))
      (g z) (g w) I (convex_Icc l u).isPreconnected (hcont z hz) (hcont w hw)
      (liftedOrbit k z.1 z.2 (n+1)) (hterm z hz)
      (fun y hy => (hterm w hw y hy).trans htval.symm) (hreg z hz) yc hyc he
  obtain ⟨E,X,hE,hEeq,hX,hXbase,hXg,hrepAll⟩ := compact_graph_relabel S I hs isCompact_Icc yc hyc g hgc huni
  have hrep (s : ℝ) (hs : s ∈ E) : ∃ z ∈ S, ∀ y ∈ I, X (s,y)=g z y := by
    rw [hEeq] at hs
    obtain ⟨z,hz,rfl⟩:=hs
    exact ⟨z,hz,hXg z hz⟩
  have hXlevel (s : ℝ) (hs : s ∈ E) (y : ℝ) (hy : y ∈ I) :
      liftedOrbit k y (X (s,y)) (n+1)=liftedOrbit k yc s (n+1) := by
    obtain ⟨z,hz,hzX⟩:=hrep s hs
    rw [hzX y hy,hterm z hz y hy,← hterm z hz yc hyc,← hzX yc hyc,hXbase s hs]
  have hXtn (s : ℝ) (hs : s ∈ E) (y : ℝ) (hy : y ∈ I) :
      tSolution (orbitCoefficient k y (X (s,y))) (n+1) ≠ 0 := by
    obtain ⟨z,hz,hzX⟩:=hrep s hs
    rw [hzX y hy]
    exact htn z hz y hy
  refine ⟨E,X,hE,hX,hXbase,?_,?_,?_,?_⟩
  · intro z hz
    have hl : g z yc ∈ E := by rw [hEeq]; exact mem_image_of_mem _ hz
    refine ⟨g z yc,hl,?_⟩
    rw [hXg z hz z.1 (hSp z hz)]
    simpa [g] using (hb z hz).1
  · exact regular_graph_family_no_crossing (fun v : ℝ × ℝ => liftedOrbit k v.1 v.2 (n+1))
      (fun s y => X (s,y)) E I yc (convex_Icc l u).isPreconnected hyc
      (fun s hs => hX.comp (continuousOn_const.prodMk continuousOn_id) (fun y hy => ⟨hs,hy⟩))
      hXbase hXlevel (fun s hs y hy => ⟨_,_,hXtn s hs y hy,hasStrictFDerivAt_liftedOrbit k y (X (s,y)) (n+1)⟩)
  · intro s hs y hy
    refine ⟨hXlevel s hs y hy,hXtn s hs y hy,?_⟩
    obtain ⟨z,hz,hzXall⟩:=hrepAll s hs
    have hzX (v : ℝ) (_hv : v ∈ I) := hzXall v
    have heyc : g z yc=s := (hzX yc hyc).symm.trans (hXbase s hs)
    have hxstrict : HasStrictDerivAt (fun v => X (s,v))
        (boundaryValue (orbitCoefficient k y (X (s,y))) (n+1)) y := by
      have hd' := ((hb z hz).2.2.2.1 (y-z.1) (hdist z hz y hy)).comp y
        ((hasStrictDerivAt_id y).sub_const z.1)
      simp only [mul_one,add_sub_cancel] at hd'
      rw [hzX y hy]
      convert! hd' using 1
      funext v
      exact hzXall v
    have hbd := (hb z hz).2.2.2.2.1 (y-z.1) (hdist z hz y hy).le
    have hratio := (hb z hz).2.2.2.2.2.2.1 (yc-z.1) (y-z.1) (hdist z hz yc hyc) (hdist z hz y hy)
    simp only [add_sub_cancel] at hbd hratio
    change |boundaryValue (orbitCoefficient k y (g z y)) (n+1)| ≤ _ at hbd
    change Real.exp (-1152*Real.pi) ≤ |tSolution (orbitCoefficient k yc (g z yc)) (n+1)|/
      |tSolution (orbitCoefficient k y (g z y)) (n+1)| ∧
      |tSolution (orbitCoefficient k yc (g z yc)) (n+1)|/
      |tSolution (orbitCoefficient k y (g z y)) (n+1)| ≤ Real.exp (1152*Real.pi) at hratio
    rw [← hzX y hy] at hbd
    rw [heyc,← hzX y hy] at hratio
    exact ⟨hxstrict,hbd,hratio⟩
  · intro s hs
    obtain ⟨z,hz,hzXall⟩:=hrepAll s hs
    refine ⟨z,hz,?_⟩
    intro y hy
    rw [hzXall y]
    refine ⟨hterm z hz y hy,?_,?_⟩
    · have hh := (hb z hz).2.2.2.2.2.1 (y-z.1) 0 (hdist z hz y hy).le (by norm_num)
      simpa only [sub_zero,(hb z hz).1] using hh
    · intro i
      have hh := (hb z hz).2.2.2.2.2.2.2.1 (y-z.1) (hdist z hz y hy).le i
      simpa only [add_sub_cancel] using hh
end StandardMapEntropy

end OAI
