import Mathlib
import OAI.Probability.Perceptron.Variational.UniformQuantileCells

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]
lemma gaussianBackward_label_mono_parameters {I : Type*} {f : E→ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (l : List (I×ℝ)) (a b : I→ℝ)
    (ha : ∀ c∈l,0≤a c.1) (hab : ∀ c∈l,a c.1≤b c.1) :
    ∀ x,gaussianBackward μ (l.map fun c=>(a c.1,c.2)) f x≤
      gaussianBackward μ (l.map fun c=>(b c.1,c.2)) f x := by
  have hb : ∀ c∈l,0≤b c.1:=fun c hc=>(ha c hc).trans (hab c hc)
  induction l with
  | nil => intro x; rfl
  | cons c l ih =>
    have ha':=fun d hd=>ha d (List.mem_cons_of_mem c hd)
    have hb':=fun d hd=>hb d (List.mem_cons_of_mem c hd)
    have hab':=fun d hd=>hab d (List.mem_cons_of_mem c hd)
    have hla : LipschitzWith L (gaussianBackward μ (l.map fun d=>(a d.1,d.2)) f) := by
      apply gaussianBackward_lipschitz μ hf
      intro d hd
      obtain ⟨e,he,rfl⟩:=List.mem_map.mp hd
      exact ha' e he
    have hlb : LipschitzWith L (gaussianBackward μ (l.map fun d=>(b d.1,d.2)) f) := by
      apply gaussianBackward_lipschitz μ hf
      intro d hd
      obtain ⟨e,he,rfl⟩:=List.mem_map.mp hd
      exact hb' e he
    intro x
    simp only [List.map_cons,gaussianBackward]
    exact (gaussianEntropic_mono_parameter μ hla c.2 x (hab c List.mem_cons_self)).trans
      (gaussianEntropic_mono μ hla hlb (hb c List.mem_cons_self) c.2 (ih ha' hab' hb') x)
end

lemma sphericalHeatValue_ofFn_mono_parameters (n N : ℕ) (a b σ : Fin N→ℝ)
    (ha : ∀ i,0≤a i) (hab : ∀ i,a i≤b i) :
    sphericalHeatValue n (List.ofFn fun i=>(a i,σ i))≤
      sphericalHeatValue n (List.ofFn fun i=>(b i,σ i)) := by
  have hm:=gaussianBackward_label_mono_parameters (stdGaussian (Spin (n+1)))
    (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ)))
    (List.ofFn fun i=>(i,σ i)) a b
    (by intro c hc; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hc; exact ha i)
    (by intro c hc; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hc; exact hab i) 0
  simp only [List.map_ofFn,Function.comp_def] at hm
  unfold sphericalHeatValue
  simp only [List.map_ofFn,Function.comp_def]
  exact sub_le_sub_right (div_le_div_of_nonneg_right hm (by positivity)) _

theorem finiteSphericalFieldValue_grid_bracket {d : ℕ} (w h : Fin (d+1)→ℝ)
    (hw : ∀ i,0<w i) (hw1 : ∑ i,w i=1) (hh : Monotone h) (hh0 : 0≤h 0)
    (H : ℝ) (hhH : h (Fin.last d)≤H) (k : ℕ) :
    ∃ v u : Fin (k+2)→ℝ,
      v∈Icc (fun _=>0) (fun _=>2*H) ∧ u∈Icc (fun _=>0) (fun _=>2*H) ∧
      (∀ n,sphericalGridValue n k v≤finiteSphericalFieldValue n d w h ∧
        finiteSphericalFieldValue n d w h≤ sphericalGridValue n k u) ∧
      |sphericalGridDual k v-sphericalGridDual k u|≤H/(k+1:ℕ) := by
  let e : Fin (d+1)→Time:=fun i=>⟨fieldExponents w i,fieldExponents_nonneg w hw i,
    (fieldExponents_lt_one w hw hw1 i).le⟩
  let A : Fin (d+1)→Fin (k+2):=fun i=>(uniformQuantileCell k (e i)).castSucc
  let B : Fin (d+1)→Fin (k+2):=fun i=>(uniformQuantileCell k (e i)).succ
  let V:=fieldVariances d h
  let v:=gridVariance (List.ofFn fun i=>(A i,V i))
  let u:=gridVariance (List.ofFn fun i=>(B i,V i))
  have hV : ∀ i,0≤V i:=fieldVariances_nonneg d h hh hh0
  have he : Monotone e:=(fieldExponents_strictMono w hw).monotone
  have hA : Monotone A:=fun i j hij=>Fin.castSucc_le_castSucc_iff.mpr (uniformQuantileCell_mono k (he hij))
  have hB : Monotone B:=fun i j hij=>Fin.succ_le_succ_iff.mpr (uniformQuantileCell_mono k (he hij))
  have hvn : ∀ i,0≤v i:=fun i=>gridVariance_nonneg _ (by
    intro c hc; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hc; exact hV j) i
  have hun : ∀ i,0≤u i:=fun i=>gridVariance_nonneg _ (by
    intro c hc; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hc; exact hV j) i
  have hvsum : (∑ i,v i)=2*h (Fin.last d) := by
    rw [gridVariance_sum,List.map_ofFn,List.sum_ofFn]; exact fieldVariances_sum d h
  have husum : (∑ i,u i)=2*h (Fin.last d) := by
    rw [gridVariance_sum,List.map_ofFn,List.sum_ofFn]; exact fieldVariances_sum d h
  refine ⟨v,u,⟨hvn,?_⟩,⟨hun,?_⟩,?_,?_⟩
  · intro i
    calc
      v i≤∑ j,v j:=Finset.single_le_sum (fun j _=>hvn j) (Finset.mem_univ i)
      _≤2*H:=by rw [hvsum]; linarith
  · intro i
    calc
      u i≤∑ j,u j:=Finset.single_le_sum (fun j _=>hun j) (Finset.mem_univ i)
      _≤2*H:=by rw [husum]; linarith
  · intro n
    have hlo:=sphericalGridValue_compress n k (List.ofFn fun i=>(A i,V i))
      (List.pairwise_ofFn.mpr (fun i j hij=>hA hij.le))
      (by intro c hc; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hc; exact hV i)
    have hup:=sphericalGridValue_compress n k (List.ofFn fun i=>(B i,V i))
      (List.pairwise_ofFn.mpr (fun i j hij=>hB hij.le))
      (by intro c hc; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hc; exact hV i)
    simp only [List.map_ofFn,Function.comp_def] at hlo hup
    rw [←hlo,←hup,finiteSphericalFieldValue_eq_heat w h hw hw1 hh hh0]
    constructor
    · apply sphericalHeatValue_ofFn_mono_parameters
      · intro i; exact uniformExponents_nonneg k (A i)
      · intro i
        have hi:=(uniformQuantileCell_bounds k (e i)).1
        change (uniformExponents k (A i))≤fieldExponents w i
        simpa only [uniformExponents,uniformQuantileGrid,Nat.cast_add,Nat.cast_one] using (show (uniformQuantileGrid k (uniformQuantileCell k (e i)).castSucc : ℝ) ≤ (e i : ℝ) from hi)
    · apply sphericalHeatValue_ofFn_mono_parameters
      · exact fieldExponents_nonneg w hw
      · intro i
        have hi:=(uniformQuantileCell_bounds k (e i)).2
        change fieldExponents w i≤uniformExponents k (B i)
        simpa only [uniformExponents,uniformQuantileGrid,Nat.cast_add,Nat.cast_one] using (show (e i : ℝ) ≤ (uniformQuantileGrid k (uniformQuantileCell k (e i)).succ : ℝ) from hi)
  · have hg:=sphericalGridDual_step_gap A B V hV (fun i=>Fin.castSucc_le_succ _)
      (fun i=>by dsimp [A,B]; simp)
    refine hg.trans ?_
    rw [fieldVariances_sum]
    have hk : (0:ℝ)<(k+1:ℕ):=by positivity
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(k+1:ℕ))).mpr
    field_simp
    nlinarith


theorem finiteSphericalFieldValue_depth_uniform (H : ℝ) (hH : 0≤H)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ d (w h : Fin (d+1)→ℝ)
      (hw : ∀ i,0<w i) (hw1 : ∑ i,w i=1),
      Monotone h → 0≤h 0 → h (Fin.last d)≤H →
      |finiteSphericalFieldValue n d w h-
        sInf (finiteSphericalDualValues w h (fun i=>(hw i).le) hw1)|<ε := by
  obtain ⟨k,hk⟩:=exists_nat_gt (2*H/ε)
  have hk0 : (0:ℝ)<(k+1:ℕ):=by
    exact lt_of_le_of_lt (div_nonneg (mul_nonneg (by norm_num) hH) hε.le)
      (hk.trans (by push_cast; linarith))
  have hgap : H/(k+1:ℕ)<ε/2 := by
    apply (div_lt_iff₀ hk0).mpr
    have hek : 2*H<ε*(k+1:ℕ):=by
      have h:= (div_lt_iff₀ hε).mp hk
      push_cast
      nlinarith
    linarith
  have hu:=sphericalGridValue_compact_uniform k (2*H)
  rw [Metric.tendstoUniformlyOn_iff] at hu
  filter_upwards [hu (ε/2) (by positivity)] with n hn
  intro d w h hw hw1 hh hh0 hhH
  obtain ⟨v,u,hv,hu,hbr,hgap'⟩:=finiteSphericalFieldValue_grid_bracket w h hw hw1 hh hh0 H hhH k
  have hf:=(finiteSphericalFieldValue_pointwise_dual w h hw hw1 hh hh0).choose_spec.2.2.2
  have hvl:=(sphericalGridValue_compact_uniform k (2*H)).tendsto_at hv
  have hul:=(sphericalGridValue_compact_uniform k (2*H)).tendsto_at hu
  have hBD : sphericalGridDual k v≤ sInf (finiteSphericalDualValues w h (fun i=>(hw i).le) hw1) :=
    le_of_tendsto_of_tendsto hvl hf (Eventually.of_forall fun m=>(hbr m).1)
  have hDU : sInf (finiteSphericalDualValues w h (fun i=>(hw i).le) hw1)≤ sphericalGridDual k u :=
    le_of_tendsto_of_tendsto hf hul (Eventually.of_forall fun m=>(hbr m).2)
  have hnv:=hn v hv
  have hnu:=hn u hu
  rw [Real.dist_eq] at hnv hnu
  have hGU : sphericalGridDual k u-sphericalGridDual k v≤H/(k+1:ℕ) := by
    linarith [(abs_le.mp hgap').1]
  exact abs_lt.mpr ⟨by linarith [(abs_lt.mp hnv).2,(hbr n).1],
    by linarith [(abs_lt.mp hnu).1,(hbr n).2]⟩
end SphericalPerceptronFreeEnergy

end

end OAI
