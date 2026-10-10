import OAI.Dynamics.StandardMap.VagueSupport

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace StandardMapEntropy
def UnitArray (d : DistanceArray) : Prop := ∀ s t : DyadicTime, d.val s t ≤ |(t:ℝ)-(s:ℝ)|
def TreeArray (d : DistanceArray) : Prop := ∀ v x y z : DyadicTime,
  min (d.val v x+d.val v y-d.val x y) (d.val v y+d.val v z-d.val y z) ≤
    d.val v x+d.val v z-d.val x z
lemma isClosed_unitArray : IsClosed {d : DistanceArray | UnitArray d} := by
  unfold UnitArray
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun s => isClosed_iInter fun t => isClosed_le (continuous_arrayEval s t) continuous_const
lemma isClosed_treeArray : IsClosed {d : DistanceArray | TreeArray d} := by
  unfold TreeArray
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun v => isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z => ?_
  have hc (a b c : DyadicTime) : Continuous (fun d : DistanceArray => d.val a b+d.val a c-d.val b c) :=
    ((continuous_arrayEval a b).add (continuous_arrayEval a c)).sub (continuous_arrayEval b c)
  exact isClosed_le ((hc v x y).min (hc v y z)) (hc v x z)
lemma unitArray_diff (d : DistanceArray) (hd : UnitArray d) (s t u v : DyadicTime) :
    |d.val s t-d.val u v| ≤ |(s:ℝ)-(u:ℝ)|+|(t:ℝ)-(v:ℝ)| := by
  have ht := d.property.2.2.2.1
  have hsy := d.property.2.2.1
  have h1 := ht s u t
  have h2 := ht u v t
  have h3 := ht u s v
  have h4 := ht s t v
  have hsu := hd s u
  have htv := hd t v
  rw [abs_sub_comm] at hsu htv
  have hste : d.val u s=d.val s u := hsy _ _
  have hvte : d.val v t=d.val t v := hsy _ _
  rw [abs_le]
  constructor <;> linarith
lemma unitArray_lipschitz (d : DistanceArray) (hd : UnitArray d) :
    LipschitzWith 2 (fun p : DyadicTime × DyadicTime => d.val p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have h := unitArray_diff d hd p.1 p.2 q.1 q.2
  rw [Real.dist_eq,Prod.dist_eq]
  change |d.val p.1 p.2-d.val q.1 q.2| ≤ (2:ℝ)*max |(p.1:ℝ)-(q.1:ℝ)| |(p.2:ℝ)-(q.2:ℝ)|
  linarith [le_max_left |(p.1:ℝ)-(q.1:ℝ)| |(p.2:ℝ)-(q.2:ℝ)|,
    le_max_right |(p.1:ℝ)-(q.1:ℝ)| |(p.2:ℝ)-(q.2:ℝ)|]
lemma denseRange_dyadicTime : DenseRange ((↑) : DyadicTime → ℝ) := dyadicTime_dense
lemma dyadicPairDense : IsDenseInducing (Prod.map ((↑) : DyadicTime → ℝ) ((↑) : DyadicTime → ℝ)) :=
  ((isUniformInducing_val (dyadicTimes:Set ℝ)).prod (isUniformInducing_val (dyadicTimes:Set ℝ))).isDenseInducing
    (denseRange_dyadicTime.prodMap denseRange_dyadicTime)
noncomputable def realArray (d : DistanceArray) (s t : ℝ) : ℝ :=
  dyadicPairDense.extend (fun p : DyadicTime × DyadicTime => d.val p.1 p.2) (s,t)
lemma continuous_realArray (d : DistanceArray) (hd : UnitArray d) :
    Continuous (fun p : ℝ × ℝ => realArray d p.1 p.2) :=
  (uniformContinuous_uniformly_extend
    ((isUniformInducing_val (dyadicTimes:Set ℝ)).prod (isUniformInducing_val (dyadicTimes:Set ℝ)))
    (denseRange_dyadicTime.prodMap denseRange_dyadicTime) (unitArray_lipschitz d hd).uniformContinuous).continuous
@[simp] lemma realArray_coe (d : DistanceArray) (hd : UnitArray d) (s t : DyadicTime) :
    realArray d (s:ℝ) (t:ℝ)=d.val s t :=
  uniformly_extend_of_ind
    ((isUniformInducing_val (dyadicTimes:Set ℝ)).prod (isUniformInducing_val (dyadicTimes:Set ℝ)))
    (denseRange_dyadicTime.prodMap denseRange_dyadicTime) (unitArray_lipschitz d hd).uniformContinuous (s,t)
lemma realArray_nonneg (d : DistanceArray) (hd : UnitArray d) (s t : ℝ) : 0 ≤ realArray d s t := by
  apply isClosed_property2 (p := fun s t => 0 ≤ realArray d s t) dyadicTime_dense (isClosed_le continuous_const (continuous_realArray d hd)) _ s t
  intro x y; simpa only [realArray_coe d hd] using d.property.1 x y
lemma realArray_le (d : DistanceArray) (hd : UnitArray d) (s t : ℝ) : realArray d s t ≤ |t-s| := by
  apply isClosed_property2 (p := fun s t => realArray d s t ≤ |t-s|) dyadicTime_dense (isClosed_le (continuous_realArray d hd) ((continuous_snd.sub continuous_fst).abs)) _ s t
  intro x y; simpa only [realArray_coe d hd] using hd x y
lemma realArray_self (d : DistanceArray) (hd : UnitArray d) (s : ℝ) : realArray d s s=0 := by
  have h0 := realArray_nonneg d hd s s
  have h1 := realArray_le d hd s s
  simp only [sub_self,abs_zero] at h1
  exact le_antisymm h1 h0
lemma realArray_symm (d : DistanceArray) (hd : UnitArray d) (s t : ℝ) : realArray d s t=realArray d t s := by
  apply isClosed_property2 (p := fun s t => realArray d s t=realArray d t s) dyadicTime_dense
    (isClosed_eq (continuous_realArray d hd) ((continuous_realArray d hd).comp (continuous_snd.prodMk continuous_fst))) _ s t
  intro x y; simpa only [realArray_coe d hd] using d.property.2.2.1 x y
lemma realArray_triangle (d : DistanceArray) (hd : UnitArray d) (s t u : ℝ) :
    realArray d s u ≤ realArray d s t+realArray d t u := by
  have hc := continuous_realArray d hd
  apply isClosed_property3 dyadicTime_dense
    (isClosed_le (hc.comp (continuous_fst.prodMk continuous_snd.snd))
      ((hc.comp (continuous_fst.prodMk continuous_snd.fst)).add (hc.comp (continuous_snd.fst.prodMk continuous_snd.snd)))) _ s t u
  intro x y z; simpa only [realArray_coe d hd] using d.property.2.2.2.1 x y z
lemma realArray_tree (d : DistanceArray) (hd : UnitArray d) (ht : TreeArray d) (v x y z : ℝ) :
    min (realArray d v x+realArray d v y-realArray d x y) (realArray d v y+realArray d v z-realArray d y z) ≤
      realArray d v x+realArray d v z-realArray d x z := by
  have hc := continuous_realArray d hd
  let e : DyadicTime × DyadicTime × DyadicTime × DyadicTime → ℝ × ℝ × ℝ × ℝ :=
    Prod.map ((↑) : DyadicTime → ℝ) (Prod.map ((↑) : DyadicTime → ℝ) (Prod.map ((↑) : DyadicTime → ℝ) ((↑) : DyadicTime → ℝ)))
  have he : DenseRange e := denseRange_dyadicTime.prodMap (denseRange_dyadicTime.prodMap (denseRange_dyadicTime.prodMap denseRange_dyadicTime))
  have hcl : IsClosed {p : ℝ × ℝ × ℝ × ℝ |
      min (realArray d p.1 p.2.1+realArray d p.1 p.2.2.1-realArray d p.2.1 p.2.2.1)
        (realArray d p.1 p.2.2.1+realArray d p.1 p.2.2.2-realArray d p.2.2.1 p.2.2.2) ≤
        realArray d p.1 p.2.1+realArray d p.1 p.2.2.2-realArray d p.2.1 p.2.2.2} := by
    apply isClosed_le
    · apply Continuous.min
      · exact ((hc.comp (continuous_fst.prodMk continuous_snd.fst)).add (hc.comp (continuous_fst.prodMk continuous_snd.snd.fst))).sub
          (hc.comp (continuous_snd.fst.prodMk continuous_snd.snd.fst))
      · exact ((hc.comp (continuous_fst.prodMk continuous_snd.snd.fst)).add (hc.comp (continuous_fst.prodMk continuous_snd.snd.snd))).sub
          (hc.comp (continuous_snd.snd.fst.prodMk continuous_snd.snd.snd))
    · exact ((hc.comp (continuous_fst.prodMk continuous_snd.fst)).add (hc.comp (continuous_fst.prodMk continuous_snd.snd.snd))).sub
        (hc.comp (continuous_snd.fst.prodMk continuous_snd.snd.snd))
  have hh := isClosed_property he hcl (fun p => by simpa only [e,Prod.map,realArray_coe d hd] using ht p.1 p.2.1 p.2.2.1 p.2.2.2) (v,x,y,z)
  exact hh
end StandardMapEntropy

end OAI
