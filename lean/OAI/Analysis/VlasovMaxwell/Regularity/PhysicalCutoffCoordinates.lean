import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.NullConeFlux
import OAI.Analysis.VlasovMaxwell.Population.DyadicCut

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def physicalCutoffCoordinates (T r : ℝ) (n v w : Vec) : Fin 4 → ℝ :=
  ![1/q v,Real.sqrt ((1-dot n (velocity v))/2),
    Real.sqrt ((1-dot n (velocity w))/2),r/max 1 T]

lemma physicalCutoffCoordinates_pos {T r : ℝ} {n v w : Vec}
    (hn : ‖n‖=1) (hr : 0<r) : ∀ i,0<physicalCutoffCoordinates T r n v w i := by
  intro i
  fin_cases i <;> simp only [physicalCutoffCoordinates]
  · exact one_div_pos.mpr (q_pos v)
  · exact Real.sqrt_pos.mpr (div_pos (cone_denom_pos v n hn) (by norm_num))
  · exact Real.sqrt_pos.mpr (div_pos (cone_denom_pos w n hn) (by norm_num))
  · exact div_pos hr (lt_of_lt_of_le (by norm_num) (le_max_left _ _))

lemma real_deficit_le_two {n : Vec} (hn : ‖n‖=1) (v : Vec) : 1-dot n (velocity v) ≤ 2 := by
  have h := (abs_dot_le n (velocity v)).trans (by simpa only [hn,one_mul] using (norm_velocity_lt_one v).le)
  linarith [neg_abs_le (dot n (velocity v))]

lemma physicalCutoffCoordinates_le_one {T r : ℝ} {n v w : Vec}
    (hn : ‖n‖=1) (hr : r ≤ max 1 T) : ∀ i,physicalCutoffCoordinates T r n v w i≤1 := by
  intro i
  fin_cases i <;> simp only [physicalCutoffCoordinates]
  · apply (div_le_one (q_pos v)).mpr
    have hs := q_sq v
    nlinarith [q_pos v,sq_nonneg ‖v‖]
  · apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · nlinarith [real_deficit_le_two hn v]
  · apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · nlinarith [real_deficit_le_two hn w]
  · exact (div_le_one (lt_of_lt_of_le (by norm_num) (le_max_left _ _))).mpr hr

lemma angularCoordinate_log_deriv {d : ℝ→ℝ} {d' t : ℝ}
    (hd : HasDerivAt d d' t) (hp : 0<d t) :
    deriv (fun s => Real.sqrt (d s/2)) t / Real.sqrt (d t/2) = d'/(2*d t) := by
  have hhalf : 0<d t/2 := by positivity
  have hs := ((hd.div_const 2).sqrt hhalf.ne').deriv
  rw [hs]
  have hq := Real.sq_sqrt hhalf.le
  have hn := (Real.sqrt_pos.mpr hhalf).ne'
  field_simp
  rw [hq]
  ring

lemma dyadicMultiFactor_curve_locally_finite {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, ContinuousAt (g i) t) (hx : ∀ i,0<g i t) :
    ∃ N : ℕ, (∀ i,2≤(2:ℝ)^N*g i t) ∧
      ∀ᶠ r in 𝓝 t, ∀ n : ι→ℕ, n∉dyadicBox ι N → dyadicMultiFactor n (fun i => g i r)=0 := by
  classical
  have hp (i : ι) := pow_unbounded_of_one_lt (4/g i t) (by norm_num : (1:ℝ)<2)
  choose Ns hNs using hp
  let N := ∑ i,Ns i
  have hN (i : ι) : 4<(2:ℝ)^N*g i t := by
    have hNi : Ns i≤N := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    exact ((div_lt_iff₀ (hx i)).mp (hNs i)).trans_le
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hNi) (hx i).le)
  refine ⟨N,fun i => by linarith [hN i],?_⟩
  have he : ∀ᶠ r in 𝓝 t, ∀ i,g i t/2<g i r := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hg i).eventually (Ioi_mem_nhds (by linarith [hx i]))
  filter_upwards [he] with r hr n hn
  have hb : ∃ i,N≤n i := by
    by_contra hb
    push Not at hb
    apply hn
    simpa only [dyadicBox,Fintype.mem_piFinset,Finset.mem_range] using hb
  obtain ⟨i,hi⟩ := hb
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply dyadicFactor_zero_large
  have hpN : 0<(2:ℝ)^N := by positivity
  have hpni : (2:ℝ)^N≤(2:ℝ)^(n i) := pow_le_pow_right₀ (by norm_num) hi
  have hgr : 0≤g i r := le_of_lt ((by linarith [hx i] : 0<g i t/2).trans (hr i))
  have hh := mul_le_mul_of_nonneg_right hpni hgr
  have hh' := mul_lt_mul_of_pos_left (hr i) hpN
  linarith [hN i]

noncomputable def selectedDyadicBox {ι : Type*} [Fintype ι] (N : ℕ) (S : Set (ι→ℕ)) : Finset (ι→ℕ) := by
  classical
  exact (dyadicBox ι N).filter (fun n => n∈S)

def selectedDyadicCutoff {ι : Type*} [Fintype ι] (S : Set (ι→ℕ)) (x : ι→ℝ) : ℝ :=
  ∑' n : ι→ℕ, S.indicator (fun n => dyadicMultiFactor n x) n

lemma selectedDyadicCutoff_curve_eventually {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, ContinuousAt (g i) t) (hx : ∀ i,0<g i t)
    (S : Set (ι→ℕ)) :
    ∃ N : ℕ, (∀ i,2≤(2:ℝ)^N*g i t) ∧
      (fun r => selectedDyadicCutoff S (fun i => g i r)) =ᶠ[𝓝 t]
        (fun r => ∑ n∈selectedDyadicBox N S,dyadicMultiFactor n (fun i => g i r)) := by
  classical
  obtain ⟨N,hN,he⟩ := dyadicMultiFactor_curve_locally_finite hg hx
  refine ⟨N,hN,?_⟩
  filter_upwards [he] with r hr
  unfold selectedDyadicCutoff
  rw [tsum_eq_sum (s:=dyadicBox ι N) (fun n hn => ?_)]
  · simpa only [selectedDyadicBox,id_eq] using (Finset.sum_indicator_eq_sum_filter (dyadicBox ι N) (fun _ n => dyadicMultiFactor n (fun i => g i r)) (fun _ => S) id)
  · by_cases hs : n∈S
    · rw [indicator_of_mem hs,hr n hn]
    · exact indicator_of_notMem hs _

lemma differentiableAt_selectedDyadicCutoff_curve {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, DifferentiableAt ℝ (g i) t) (hx : ∀ i,0<g i t)
    (S : Set (ι→ℕ)) : DifferentiableAt ℝ (fun r => selectedDyadicCutoff S (fun i => g i r)) t := by
  classical
  obtain ⟨N,_hN,he⟩ := selectedDyadicCutoff_curve_eventually (fun i => (hg i).continuousAt) hx S
  exact (DifferentiableAt.fun_sum (u:=selectedDyadicBox N S) (fun n _ => differentiableAt_dyadicMultiFactor_curve hg n)).congr_of_eventuallyEq he

lemma selectedDyadicCutoff_local_box {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} {N : ℕ}
    (he : ∀ᶠ r in 𝓝 t,∀ n : ι→ℕ,n∉dyadicBox ι N → dyadicMultiFactor n (fun i=>g i r)=0)
    (S : Set (ι→ℕ)) :
    (fun r => selectedDyadicCutoff S (fun i => g i r)) =ᶠ[𝓝 t]
      (fun r => ∑ n∈selectedDyadicBox N S,dyadicMultiFactor n (fun i=>g i r)) := by
  classical
  filter_upwards [he] with r hr
  unfold selectedDyadicCutoff
  rw [tsum_eq_sum (s:=dyadicBox ι N) (fun n hn => ?_)]
  · simpa only [selectedDyadicBox,id_eq] using (Finset.sum_indicator_eq_sum_filter
      (dyadicBox ι N) (fun _ n => dyadicMultiFactor n (fun i=>g i r)) (fun _=>S) id)
  · by_cases hs : n∈S
    · rw [indicator_of_mem hs,hr n hn]
    · exact indicator_of_notMem hs _

lemma selectedDyadicBox_compl {ι : Type*} [Fintype ι] (N : ℕ) (S : Set (ι→ℕ)) :
    selectedDyadicBox N Sᶜ=dyadicBox ι N \ selectedDyadicBox N S := by
  classical
  simp only [selectedDyadicBox,mem_compl_iff,Finset.filter_not]

lemma selectedDyadicCutoff_derivative_cancel {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ}
    (hg : ∀ i,DifferentiableAt ℝ (g i) t) (hp : ∀ i,0<g i t)
    (h1 : ∀ i,g i t≤1) (S : Set (ι→ℕ)) :
    deriv (fun r=>selectedDyadicCutoff S (fun i=>g i r)) t =
      -deriv (fun r=>selectedDyadicCutoff Sᶜ (fun i=>g i r)) t := by
  classical
  obtain ⟨N,hN,he⟩ := dyadicMultiFactor_curve_locally_finite (fun i=>(hg i).continuousAt) hp
  rw [(selectedDyadicCutoff_local_box he S).deriv_eq,
      (selectedDyadicCutoff_local_box he Sᶜ).deriv_eq,
      selectedDyadicBox_compl]
  simpa only [deriv_fun_sum (fun n _=>differentiableAt_dyadicMultiFactor_curve hg n)] using
    selected_dyadic_derivative_cancel hg N h1 hN (selectedDyadicBox N S) (Finset.filter_subset _ _)

lemma selectedDyadicCutoff_derivative_boundary {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ}
    (hg : ∀ i,DifferentiableAt ℝ (g i) t) (hp : ∀ i,0<g i t)
    (h1 : ∀ i,g i t≤1) (S : Set (ι→ℕ))
    (hne : deriv (fun r=>selectedDyadicCutoff S (fun i=>g i r)) t≠0) :
    ∃ n∈S,∃ m∉S,0<dyadicMultiFactor n (fun i=>g i t) ∧
      0<dyadicMultiFactor m (fun i=>g i t) ∧ ∀ i,m i ≤ n i+2 ∧ n i ≤ m i+2 := by
  classical
  obtain ⟨N,hN,he⟩ := dyadicMultiFactor_curve_locally_finite (fun i=>(hg i).continuousAt) hp
  rw [(selectedDyadicCutoff_local_box he S).deriv_eq] at hne
  obtain ⟨⟨n,hn,hnpos⟩,⟨m,hm,hmpos⟩⟩ := selected_dyadic_derivative_boundary hg N h1 hN
    (selectedDyadicBox N S) (Finset.filter_subset _ _) hne
  have hnS : n∈S := (Finset.mem_filter.mp hn).2
  have hmS : m∉S := by
    intro hmS
    exact (Finset.mem_sdiff.mp hm).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hm).1,hmS⟩)
  exact ⟨n,hnS,m,hmS,hnpos,hmpos,dyadicMultiFactor_positive_index_comparison hnpos hmpos⟩

end RVM

end

end OAI
