import OAI.Probability.FKMaps.SimpleWalk

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Histogram
variable {ι : Type*} [Fintype ι]

def cube (δ : ℝ) (a : ι → ℝ) : Set (ι → ℝ) := pi univ (fun i => Ico (a i) (a i+δ))

lemma measurableSet_cube (δ : ℝ) (a : ι → ℝ) : MeasurableSet (cube δ a) :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Ico)

lemma volume_cube (δ : ℝ) (a : ι → ℝ) :
    volume (cube δ a)=ENNReal.ofReal δ ^ Fintype.card ι := by
  rw [cube,volume_pi,Measure.pi_pi]
  simp

lemma mem_cube_dist {δ : ℝ} {a x : ι → ℝ} (hδ : 0≤δ) (hx : x∈cube δ a) : dist x a≤δ := by
  apply (dist_pi_le_iff hδ).mpr
  intro i
  have hi := hx i (mem_univ i)
  rw [Real.dist_eq]
  exact abs_le.mpr ⟨by linarith [hi.1],by linarith [hi.2]⟩

def boxLaw (δ : ℝ) (a : ι → ℝ) : Measure (ι → ℝ) :=
  (ENNReal.ofReal δ ^ Fintype.card ι)⁻¹ • volume.restrict (cube δ a)

lemma boxLaw_probability {δ : ℝ} (hδ : 0<δ) (a : ι → ℝ) :
    IsProbabilityMeasure (boxLaw δ a) := by
  constructor
  simp only [boxLaw,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul,volume_cube]
  exact ENNReal.inv_mul_cancel (pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr hδ)))
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

lemma boxLaw_dist {δ : ℝ} (hδ : 0≤δ) (a : ι → ℝ) :
    ∀ᵐ x ∂boxLaw δ a, dist x a≤δ := by
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem (measurableSet_cube δ a)] with x hx
  exact mem_cube_dist hδ hx

lemma boxLaw_withDensity (δ : ℝ) (a : ι → ℝ) :
    boxLaw δ a=volume.withDensity ((cube δ a).indicator
      (fun _ => (ENNReal.ofReal δ ^ Fintype.card ι)⁻¹)) := by
  rw [withDensity_indicator (measurableSet_cube δ a),withDensity_const]
  rfl

end FKCRT.Histogram
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Histogram
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [MeasurableSpace Ω]
  [MeasurableSingletonClass Ω]

def mixture (μ : Measure Ω) (φ : Ω → ι → ℝ) (δ : ℝ) : Measure (ι → ℝ) :=
  ∑ ω, μ {ω} • boxLaw δ (φ ω)

lemma mixture_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (φ : Ω → ι → ℝ) {δ : ℝ} (hδ : 0<δ) :
    IsProbabilityMeasure (mixture μ φ δ) := by
  have (ω : Ω) : IsProbabilityMeasure (boxLaw δ (φ ω)) := boxLaw_probability hδ (φ ω)
  constructor
  simp only [mixture,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul,
    measure_univ,mul_one]
  rw [sum_measure_singleton,Finset.coe_univ,measure_univ]

def density (μ : Measure Ω) (φ : Ω → ι → ℝ) (δ : ℝ) (x : ι → ℝ) : ℝ≥0∞ :=
  ∑ ω,μ {ω} * (cube δ (φ ω)).indicator
    (fun _ => (ENNReal.ofReal δ ^ Fintype.card ι)⁻¹) x

omit [MeasurableSingletonClass Ω] in
lemma measurable_density (μ : Measure Ω) (φ : Ω → ι → ℝ) (δ : ℝ) :
    Measurable (density μ φ δ) := by
  apply Finset.measurable_sum
  intro ω hω
  exact measurable_const.mul (measurable_const.indicator (measurableSet_cube δ (φ ω)))

omit [MeasurableSingletonClass Ω] in
lemma mixture_withDensity (μ : Measure Ω) (φ : Ω → ι → ℝ) (δ : ℝ) :
    mixture μ φ δ=volume.withDensity (density μ φ δ) := by
  ext s hs
  rw [withDensity_apply _ hs]
  simp only [mixture,Measure.finsetSum_apply,density]
  have hm (ω : Ω) : Measurable (fun x : ι → ℝ => μ {ω} * (cube δ (φ ω)).indicator
      (fun _ => (ENNReal.ofReal δ ^ Fintype.card ι)⁻¹) x) :=
    measurable_const.mul (measurable_const.indicator (measurableSet_cube δ (φ ω)))
  rw [lintegral_finsetSum _ (fun ω _ => hm ω)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Measure.smul_apply,smul_eq_mul,boxLaw_withDensity,
    withDensity_apply _ hs,lintegral_const_mul _
      (measurable_const.indicator (measurableSet_cube δ (φ ω)))]

omit [MeasurableSingletonClass Ω] in
lemma integral_mixture (μ : Measure Ω) [IsProbabilityMeasure μ]
    (φ : Ω → ι → ℝ) {δ : ℝ} (hδ : 0<δ) (F : BoundedContinuousFunction (ι → ℝ) ℝ) :
    (∫ x,F x ∂mixture μ φ δ)=∑ ω,(μ {ω}).toReal * ∫ x,F x ∂boxLaw δ (φ ω) := by
  have (ω : Ω) : IsProbabilityMeasure (boxLaw δ (φ ω)) := boxLaw_probability hδ (φ ω)
  have hi (ω : Ω) : Integrable F (μ {ω} • boxLaw δ (φ ω)) := by
    exact (F.integrable (boxLaw δ (φ ω))).smul_measure (measure_ne_top _ _)
  rw [mixture,integral_finsetSum_measure (fun ω _ => hi ω)]
  simp only [integral_smul_measure,smul_eq_mul]

lemma box_integral_lipschitz {δ : ℝ} (hδ : 0<δ) (a : ι → ℝ)
    (F : BoundedContinuousFunction (ι → ℝ) ℝ) {L : ℝ≥0} (hF : LipschitzWith L F) :
    |(∫ x,F x ∂boxLaw δ a)-F a|≤L*δ := by
  have := boxLaw_probability hδ a
  have hconst : (∫ x,F a ∂boxLaw δ a)=F a := by simp
  rw [← hconst,← integral_sub (F.integrable _) (integrable_const _)]
  apply abs_integral_le_integral_abs.trans
  calc
    (∫ x,|F x-F a| ∂boxLaw δ a) ≤ ∫ x,(L:ℝ)*δ ∂boxLaw δ a := by
      apply integral_mono_ae ((F.integrable _).sub (integrable_const _)).abs (integrable_const _)
      filter_upwards [boxLaw_dist hδ.le a] with x hx
      exact (hF.dist_le_mul x a).trans (mul_le_mul_of_nonneg_left hx L.coe_nonneg)
    _ = _ := by simp

lemma integral_mixture_close (μ : Measure Ω) [IsProbabilityMeasure μ]
    (φ : Ω → ι → ℝ) {δ : ℝ} (hδ : 0<δ)
    (F : BoundedContinuousFunction (ι → ℝ) ℝ) {L : ℝ≥0} (hF : LipschitzWith L F) :
    |(∫ x,F x ∂mixture μ φ δ)-(∫ ω,F (φ ω) ∂μ)|≤L*δ := by
  have hi : Integrable (fun ω => F (φ ω)) μ := Integrable.of_finite
  rw [integral_mixture μ φ hδ F,integral_fintype hi,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ ω,|(μ {ω}).toReal * (∫ x,F x ∂boxLaw δ (φ ω)) - μ.real {ω} • F (φ ω)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ω,(μ {ω}).toReal*((L:ℝ)*δ) := by
      apply Finset.sum_le_sum
      intro ω _
      rw [smul_eq_mul,measureReal_def,← mul_sub,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_mul_of_nonneg_left (box_integral_lipschitz hδ (φ ω) F hF) ENNReal.toReal_nonneg
    _ = _ := by
      rw [← Finset.sum_mul,← ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _),
        sum_measure_singleton,Finset.coe_univ,measure_univ,ENNReal.toReal_one,one_mul]

end FKCRT.Histogram
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Histogram
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [MeasurableSpace Ω]
  [MeasurableSingletonClass Ω]

omit [Fintype ι] in
lemma mem_lattice_cube {δ : ℝ} (hδ : 0<δ) (a : ι → ℕ) {x : ι → ℝ}
    (hx : ∀ i,0≤x i) : x∈cube δ (fun i => δ*(a i:ℝ))↔a=fun i => ⌊x i/δ⌋₊ := by
  constructor
  · intro h
    apply funext
    intro i
    have hi := h i (mem_univ i)
    symm
    apply (Nat.floor_eq_iff (div_nonneg (hx i) hδ.le)).mpr
    constructor
    · exact (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hi.1)
    · apply (div_lt_iff₀ hδ).mpr
      simpa only [add_mul,mul_add,one_mul,mul_one,mul_comm] using hi.2
  · rintro rfl
    intro i _
    have hfloor := (Nat.floor_eq_iff (div_nonneg (hx i) hδ.le)).mp (rfl : ⌊x i/δ⌋₊=⌊x i/δ⌋₊)
    constructor
    · simpa only [mul_comm] using (le_div_iff₀ hδ).mp hfloor.1
    · simpa only [add_mul,mul_add,one_mul,mul_one,mul_comm] using (div_lt_iff₀ hδ).mp hfloor.2

lemma density_lattice (μ : Measure Ω) (a : Ω → ι → ℕ) {δ : ℝ} (hδ : 0<δ)
    {x : ι → ℝ} (hx : ∀ i,0≤x i) :
    density μ (fun ω i => δ*(a ω i:ℝ)) δ x=
      μ {ω | a ω=fun i => ⌊x i/δ⌋₊}*(ENNReal.ofReal δ ^ Fintype.card ι)⁻¹ := by
  classical
  let s : Finset Ω := Finset.univ.filter (fun ω => a ω=fun i => ⌊x i/δ⌋₊)
  have hset : (s : Set Ω)={ω | a ω=fun i => ⌊x i/δ⌋₊} := by ext ω; simp [s]
  rw [density,← hset,← sum_measure_singleton,Finset.sum_mul]
  simp only [s,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : a ω=fun i => ⌊x i/δ⌋₊
  · rw [ite_eq_left h,indicator_of_mem ((mem_lattice_cube hδ _ hx).mpr h)]
  · rw [ite_eq_right h,indicator_of_notMem (mt (mem_lattice_cube hδ _ hx).mp h),mul_zero]

omit [MeasurableSingletonClass Ω] in
lemma density_lattice_negative (μ : Measure Ω) (a : Ω → ι → ℕ) {δ : ℝ}
    (hδ : 0≤δ) {x : ι → ℝ} (hx : ∃ i,x i<0) :
    density μ (fun ω i => δ*(a ω i:ℝ)) δ x=0 := by
  obtain ⟨i,hi⟩ := hx
  apply Finset.sum_eq_zero
  intro ω _
  have hn : x∉cube δ (fun i => δ*(a ω i:ℝ)) := by
    intro h
    have hh := (h i (mem_univ i)).1
    have hz : 0≤δ*(a ω i:ℝ) := mul_nonneg hδ (Nat.cast_nonneg _)
    linarith
  rw [indicator_of_notMem hn,mul_zero]

lemma floor_mesh_tendsto {δ : ℕ → ℝ} (hδ : ∀ n,0<δ n)
    (hlim : Tendsto δ atTop (𝓝 0)) {x : ℝ} (hx : 0≤x) :
    Tendsto (fun n => δ n*(⌊x/δ n⌋₊:ℝ)) atTop (𝓝 x) := by
  have hl (n : ℕ) := Nat.floor_le (div_nonneg hx (hδ n).le)
  have hu (n : ℕ) := Nat.lt_floor_add_one (x/δ n)
  have hlow : Tendsto (fun n => x-δ n) atTop (𝓝 x) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
  · intro n
    have h := (div_lt_iff₀ (hδ n)).mp (hu n)
    nlinarith
  · intro n
    simpa only [mul_comm] using (le_div_iff₀ (hδ n)).mp (hl n)

end FKCRT.Histogram
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

def located : List (ℕ×ℕ) → List (ℕ×ℕ)
  | [] => []
  | x::xs => x::(located xs).map (fun y => (x.1+y.1,y.2))

def observed {N : ℕ} (a : ℕ) (xs : List (ℕ×ℕ)) (d : Path N) : Prop :=
  ∀ x∈located xs,(a:ℤ)+pathSum d x.1=x.2

lemma tracePoints_observed (a R : ℕ) (xs : List (ℕ×ℕ)) (d : Path (traceSize R xs)) :
    tracePoints a R xs d↔observed a xs d := by
  induction xs generalizing a with
  | nil => simp [tracePoints,observed,located]
  | cons x xs ih =>
    obtain ⟨⟨d,e⟩,rfl⟩ := (splitPathAt x.1 (traceSize R xs)).symm.surjective d
    simp only [tracePoints,Equiv.apply_symm_apply,ih,observed,located,List.mem_cons,
      List.mem_map,forall_eq_or_imp,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂]
    change ((a:ℤ)+pathSum d x.1=x.2 ∧
      ∀ y∈located xs,(x.2:ℤ)+pathSum e y.1=y.2)↔
      ((a:ℤ)+pathSum (Fin.append d e) x.1=x.2 ∧
      ∀ y∈located xs,(a:ℤ)+pathSum (Fin.append d e) (x.1+y.1)=y.2)
    simp only [pathSum_append_left d e le_rfl,pathSum_append_right]
    constructor <;> rintro ⟨hx,hxs⟩ <;> refine ⟨hx,?_⟩ <;> intro y hy
    · have h := hxs y hy; linarith
    · have h := hxs y hy; linarith

lemma pathMass_firstHit_observed (a R : ℕ) (xs : List (ℕ×ℕ)) :
    pathMass (traceSize R xs) (fun d => firstHit a d ∧ observed a xs d)=
      traceKilledWeight a R xs := by
  rw [← pathMass_traceExcursion]
  apply pathMass_congr
  intro d
  rw [traceExcursion_iff,tracePoints_observed]

lemma traceSize_eq_sum (R : ℕ) (xs : List (ℕ×ℕ)) :
    traceSize R xs=(xs.map Prod.fst).sum+R := by
  induction xs with
  | nil => simp [traceSize]
  | cons x xs ih => simp [traceSize,ih,Nat.add_assoc]

lemma pathSum_cast {N M : ℕ} (h : N=M) (d : Path N) (k : ℕ) :
    pathSum (fun i : Fin M => d (Fin.cast h.symm i)) k=pathSum d k := by
  subst M
  rfl

lemma pathMass_cast {N M : ℕ} (h : N=M) (P : Path M → Prop) :
    pathMass N (fun d => P (fun i : Fin M => d (Fin.cast h.symm i)))=pathMass M P := by
  subst M
  rfl

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

/-- Even grid time immediately below t, for the odd duration 2n+1. -/
def evenGrid (n : ℕ) (t : ℝ) : ℕ := 2*⌊((2*n+1:ℕ):ℝ)*t/2⌋₊

lemma even_evenGrid (n : ℕ) (t : ℝ) : Even (evenGrid n t) := even_two_mul _

lemma evenGrid_mono (n : ℕ) {s t : ℝ} (h : s≤t) : evenGrid n s≤evenGrid n t := by
  unfold evenGrid
  exact Nat.mul_le_mul_left _ (Nat.floor_mono (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)) (by norm_num)))

@[simp] lemma evenGrid_zero (n : ℕ) : evenGrid n 0=0 := by simp [evenGrid]

lemma evenGrid_le (n : ℕ) {t : ℝ} (ht : t≤1) : evenGrid n t≤2*n := by
  have h : ((2*n+1:ℕ):ℝ)*t/2<(n:ℝ)+1 := by
    have he := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (2*n+1) : (0:ℝ)≤(2*n+1:ℕ))
    push_cast at he ⊢
    linarith
  have hh : ⌊((2*n+1:ℕ):ℝ)*t/2⌋₊≤n := (Nat.floor_lt' (by omega : n+1≠0)).mpr
    (by exact_mod_cast h) |> Nat.le_of_lt_succ
  exact Nat.mul_le_mul_left 2 hh

lemma evenGrid_error (n : ℕ) {t : ℝ} (ht : 0≤t) :
    0≤((2*n+1:ℕ):ℝ)*t-(evenGrid n t:ℝ) ∧
    ((2*n+1:ℕ):ℝ)*t-(evenGrid n t:ℝ)<2 := by
  have hnonneg : 0≤((2*n+1:ℕ):ℝ)*t/2 := by positivity
  have hl := Nat.floor_le hnonneg
  have hu := Nat.lt_floor_add_one (((2*n+1:ℕ):ℝ)*t/2)
  unfold evenGrid
  push_cast at hl hu ⊢
  constructor <;> linarith

lemma evenGrid_ratio (t : ℝ) (ht : 0≤t) :
    Tendsto (fun n => (evenGrid n t:ℝ)/((2*n+1:ℕ):ℝ)) atTop (𝓝 t) := by
  have hN : Tendsto (fun n : ℕ => ((2*n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun n => by show n≤2*n+1; omega) tendsto_id)
  have hzero : Tendsto (fun n => (2:ℝ)/((2*n+1:ℕ):ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hN
  have hl : Tendsto (fun n => t-2/((2*n+1:ℕ):ℝ)) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub hzero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
  · intro n
    have hpos : 0<((2*n+1:ℕ):ℝ) := by positivity
    have he := (evenGrid_error n ht).2
    apply (le_div_iff₀ hpos).mpr
    rw [sub_mul,div_mul_cancel₀ _ hpos.ne']
    linarith
  · intro n
    exact (div_le_iff₀ (by positivity : 0<((2*n+1:ℕ):ℝ))).mpr
      (by have h := (evenGrid_error n ht).1; linarith)

/-- Successive durations at a deterministic increasing list of observation times. -/
def gridDurations {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ) (i : Fin m) : ℕ :=
  evenGrid n (u i.succ)-evenGrid n (u i.castSucc)

def gridRemainder {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ) : ℕ :=
  2*n-evenGrid n (u (Fin.last m))

lemma gridDurations_even {m : ℕ} (u : Fin (m+1) → unitInterval) (hu : Monotone u)
    (n : ℕ) (i : Fin m) : Even (gridDurations u n i) := by
  exact (Nat.even_sub (evenGrid_mono n (hu i.castSucc_lt_succ.le))).mpr
    (iff_of_true (even_evenGrid n _) (even_evenGrid n _))

lemma gridRemainder_even {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ) :
    Even (gridRemainder u n) :=
  (Nat.even_sub (evenGrid_le n (u (Fin.last m)).property.2)).mpr
    (iff_of_true (even_two_mul n) (even_evenGrid n _))

lemma gridDurations_ratio {m : ℕ} (u : Fin (m+1) → unitInterval) (hu : Monotone u)
    (i : Fin m) :
    Tendsto (fun n => (gridDurations u n i:ℝ)/((2*n+1:ℕ):ℝ)) atTop
      (𝓝 ((u i.succ:ℝ)-(u i.castSucc:ℝ))) := by
  have h := (evenGrid_ratio (u i.succ) (u i.succ).property.1).sub
    (evenGrid_ratio (u i.castSucc) (u i.castSucc).property.1)
  apply h.congr'
  exact Filter.Eventually.of_forall (fun n => by
    dsimp only [gridDurations]
    rw [Nat.cast_sub (evenGrid_mono n (hu i.castSucc_lt_succ.le)),sub_div])

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
open TreeCoding

/-- The heat density for one-dimensional standard Brownian motion. -/
def heat (t x : ℝ) : ℝ := Real.exp (-x^2/(2*t))/Real.sqrt (2*Real.pi*t)

lemma heat_pos {t : ℝ} (ht : 0<t) (x : ℝ) : 0<heat t x := by
  exact div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (by positivity))

lemma heat_continuousOn : ContinuousOn (fun tx : ℝ×ℝ => heat tx.1 tx.2) {tx | 0<tx.1} := by
  intro tx htx
  change 0<tx.1 at htx
  unfold heat
  have h1 : 2*tx.1≠0 := by positivity
  have h2 : Real.sqrt (2*Real.pi*tx.1)≠0 := by positivity
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := assumption)

/-- Full span-two uniform local limit, now for the explicitly reflected simple kernel. -/
theorem kernel_uniform_local_limit :
    ∃ E : ℕ → ℝ, (∀ n,0≤E n) ∧ Tendsto E atTop (𝓝 0) ∧
      ∀ (N : ℕ), 0<N → ∀ z : ℤ, Even ((N:ℤ)+z) →
        |Real.sqrt N*kernel N z-(Real.sqrt (2*Real.pi)/Real.pi)*
          Real.exp (-((z:ℝ)/Real.sqrt N)^2/2)|≤E N := by
  obtain ⟨E,hE,hEt,h⟩ := binaryOffspring.uniform_local_limit
  have hsub : Tendsto (fun n : ℕ => n-1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b+1,fun n hn => by omega⟩
  refine ⟨fun N => E (N-1),fun N => hE _,hEt.comp hsub,?_⟩
  intro N hN z hz
  have hn : N-1+1=N := by omega
  have hnR : ((N-1:ℕ):ℝ)+1=(N:ℝ) := by exact_mod_cast hn
  simpa only [hn,hnR,binary_kernel,binaryOffspring_sigma,one_mul] using h (N-1) z (by simpa only [hn] using hz)

lemma kernel_local_limit {N : ℕ → ℕ} {z : ℕ → ℤ} {x : ℝ}
    (hN : Tendsto N atTop atTop)
    (hz : ∀ᶠ n in atTop,Even ((N n:ℤ)+z n))
    (hx : Tendsto (fun n => (z n:ℝ)/Real.sqrt (N n:ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n => Real.sqrt (N n:ℝ)*kernel (N n) (z n)) atTop
      (𝓝 ((Real.sqrt (2*Real.pi)/Real.pi)*Real.exp (-x^2/2))) := by
  obtain ⟨E,_hE,hEt,hE⟩ := kernel_uniform_local_limit
  have hmodel := ((Real.continuous_exp.tendsto (-x^2/2)).comp ((hx.pow 2).neg.div_const 2)).const_mul
      (Real.sqrt (2*Real.pi)/Real.pi)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun n => (Real.sqrt (2*Real.pi)/Real.pi)*
      Real.exp (-((z n:ℝ)/Real.sqrt (N n:ℝ))^2/2)-E (N n)) atTop _ by
      simpa using hmodel.sub (hEt.comp hN))
    (show Tendsto (fun n => (Real.sqrt (2*Real.pi)/Real.pi)*
      Real.exp (-((z n:ℝ)/Real.sqrt (N n:ℝ))^2/2)+E (N n)) atTop _ by
      simpa using hmodel.add (hEt.comp hN))
  · filter_upwards [hz,hN.eventually (eventually_gt_atTop 0)] with n hn hnn
    have hh := (abs_le.mp (hE (N n) hnn (z n) hn)).1
    linarith
  · filter_upwards [hz,hN.eventually (eventually_gt_atTop 0)] with n hn hnn
    have hh := (abs_le.mp (hE (N n) hnn (z n) hn)).2
    linarith

lemma sqrt_ratio_tendsto {N T : ℕ → ℕ} {t : ℝ}
    (hr : Tendsto (fun n => (N n:ℝ)/(T n:ℝ)) atTop (𝓝 t)) :
    Tendsto (fun n => Real.sqrt (N n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 (Real.sqrt t)) := by
  simpa only [Function.comp_def,Real.sqrt_div (Nat.cast_nonneg _)] using Real.continuous_sqrt.tendsto t |>.comp hr

/-- Kernel limit at arbitrary macroscopic times and spatial lattice sites. -/
theorem kernel_scaled_limit {N T : ℕ → ℕ} {z : ℕ → ℤ} {t x : ℝ}
    (ht : 0<t) (hN : Tendsto N atTop atTop) (hT : Tendsto T atTop atTop)
    (hr : Tendsto (fun n => (N n:ℝ)/(T n:ℝ)) atTop (𝓝 t))
    (hz : ∀ᶠ n in atTop,Even ((N n:ℤ)+z n))
    (hx : Tendsto (fun n => (z n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n => Real.sqrt (T n:ℝ)*kernel (N n) (z n)) atTop (𝓝 (2*heat t x)) := by
  have hs := sqrt_ratio_tendsto hr
  have ht' : 0<Real.sqrt t := Real.sqrt_pos.mpr ht
  have hz' : Tendsto (fun n => (z n:ℝ)/Real.sqrt (N n:ℝ)) atTop (𝓝 (x/Real.sqrt t)) := by
    apply (hx.div hs (ne_of_gt ht')).congr'
    filter_upwards [hT.eventually (eventually_gt_atTop 0),hN.eventually (eventually_gt_atTop 0)] with n hn hnn
    have htp : Real.sqrt (T n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hn))
    have hnp : Real.sqrt (N n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hnn))
    dsimp only [Pi.div_apply]
    field_simp
  have hc := (kernel_local_limit hN hz hz').div hs (ne_of_gt ht')
  have hm : ((Real.sqrt (2*Real.pi)/Real.pi)*Real.exp (-(x/Real.sqrt t)^2/2))/Real.sqrt t=2*heat t x := by
    rw [heat,div_pow,Real.sq_sqrt ht.le,Real.sqrt_mul (by positivity : 0≤2*Real.pi)]
    have hpi : Real.sqrt (2*Real.pi)^2=2*Real.pi := Real.sq_sqrt (by positivity)
    have hpis : Real.sqrt (2*Real.pi)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    have harg : -(x^2/t)/2= -x^2/(2*t) := by ring
    rw [harg]
    field_simp
    nlinarith
  rw [hm] at hc
  apply hc.congr'
  filter_upwards [hN.eventually (eventually_gt_atTop 0),hT.eventually (eventually_gt_atTop 0)] with n hn hnt
  have hnp : Real.sqrt (N n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have htp : Real.sqrt (T n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hnt))
  dsimp only [Pi.div_apply]
  field_simp

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

lemma cast_div_sqrt_tendsto_zero {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) (c : ℝ) :
  Tendsto (fun n => c/Real.sqrt (T n:ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hT))

/-- The killed heat kernel obtained from the proved discrete reflection principle. -/
def killedHeat (t x y : ℝ) : ℝ := heat t (y-x)-heat t (y+x)

lemma killed_scaled_limit {N T a b : ℕ → ℕ} {t x y : ℝ}
    (ht : 0<t) (hN : Tendsto N atTop atTop) (hT : Tendsto T atTop atTop)
    (hr : Tendsto (fun n => (N n:ℝ)/(T n:ℝ)) atTop (𝓝 t))
    (hz : ∀ᶠ n in atTop,Even ((N n:ℤ)+(b n:ℤ)-a n))
    (hx : Tendsto (fun n => (a n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 x))
    (hy : Tendsto (fun n => (b n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 y)) :
    Tendsto (fun n => Real.sqrt (T n:ℝ)*killed (N n) (a n) (b n)) atTop
      (𝓝 (2*killedHeat t x y)) := by
  have hm : Tendsto (fun n => (((b n:ℤ)-a n:ℤ):ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 (y-x)) := by
    simpa only [Int.cast_sub,Int.cast_natCast,sub_div] using hy.sub hx
  have hp : Tendsto (fun n => (((b n:ℤ)+a n+2:ℤ):ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 (y+x)) := by
    simpa only [Int.cast_add,Int.cast_ofNat,Int.cast_natCast,add_div,add_zero] using
      (hy.add hx).add (cast_div_sqrt_tendsto_zero hT 2)
  have hz1 : ∀ᶠ n in atTop, Even ((N n:ℤ)+((b n:ℤ)-a n)) := by
    filter_upwards [hz] with n hn; convert hn using 1; ring
  have hz2 : ∀ᶠ n in atTop, Even ((N n:ℤ)+((b n:ℤ)+a n+2)) := by
    filter_upwards [hz] with n hn
    have he : (N n:ℤ)+((b n:ℤ)+a n+2)=((N n:ℤ)+b n-a n)+2*((a n:ℤ)+1) := by ring
    rw [he]
    exact hn.add (even_two_mul ((a n:ℤ)+1))
  have h := (kernel_scaled_limit ht hN hT hr hz1 hm).sub (kernel_scaled_limit ht hN hT hr hz2 hp)
  simpa only [killed_reflection,mul_sub,killedHeat] using h

lemma sqrt_div_nat_tendsto_zero {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun n => Real.sqrt (T n:ℝ)/(T n:ℝ)) atTop (𝓝 0) := by
  apply (cast_div_sqrt_tendsto_zero hT 1).congr'
  filter_upwards [hT.eventually (eventually_gt_atTop 0)] with n hn
  have htp : 0<(T n:ℝ) := by exact_mod_cast hn
  have hsp : Real.sqrt (T n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr htp)
  have hs := Real.sq_sqrt htp.le
  field_simp
  nlinarith

lemma entrance_scaled_limit {N T b : ℕ → ℕ} {t y : ℝ}
    (ht : 0<t) (hN : Tendsto N atTop atTop) (hT : Tendsto T atTop atTop)
    (hr : Tendsto (fun n => (N n:ℝ)/(T n:ℝ)) atTop (𝓝 t))
    (hz : ∀ᶠ n in atTop,Even ((N n:ℤ)+b n))
    (hy : Tendsto (fun n => (b n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 y)) :
    Tendsto (fun n => (T n:ℝ)*killed (N n) 0 (b n)) atTop (𝓝 (4*y/t*heat t y)) := by
  have hsmall : Tendsto (fun n => (b n:ℝ)/(T n:ℝ)) atTop (𝓝 0) := by
    have h := hy.mul (sqrt_div_nat_tendsto_zero hT)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [hT.eventually (eventually_gt_atTop 0)] with n hn
    have hs : Real.sqrt (T n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hn))
    field_simp
  have hnum : Tendsto (fun n => 2*((b n:ℝ)+1)/Real.sqrt (T n:ℝ)) atTop (𝓝 (2*y)) := by
    simpa only [add_zero,mul_div_assoc,add_div] using (hy.add (cast_div_sqrt_tendsto_zero hT 1)).const_mul 2
  have hden : Tendsto (fun n => ((N n:ℝ)+b n+2)/(T n:ℝ)) atTop (𝓝 t) := by
    simpa only [add_div,add_zero] using (hr.add hsmall).add
      (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hT) :
        Tendsto (fun n => (2:ℝ)/(T n:ℝ)) atTop (𝓝 0))
  have hk := kernel_scaled_limit ht hN hT hr hz (by simpa only [Int.cast_natCast] using hy)
  have h := (hnum.div hden (ne_of_gt ht)).mul hk
  have hi : 2*y/t*(2*heat t y)=4*y/t*heat t y := by ring
  rw [hi] at h
  apply h.congr'
  filter_upwards [hT.eventually (eventually_gt_atTop 0)] with n hn
  have htp : (T n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hs : Real.sqrt (T n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have hd : (N n:ℝ)+b n+2≠0 := by positivity
  rw [killed_entrance]
  dsimp only [Pi.mul_apply,Pi.div_apply]
  field_simp

/-- Terminal first-hitting density at macroscopic time. -/
lemma firstHit_scaled_limit {N T b : ℕ → ℕ} {t y : ℝ}
    (ht : 0<t) (hN : Tendsto N atTop atTop) (hT : Tendsto T atTop atTop)
    (hr : Tendsto (fun n => ((N n:ℝ)+1)/(T n:ℝ)) atTop (𝓝 t))
    (hz : ∀ᶠ n in atTop,Even (((N n+1:ℕ):ℤ)+((b n:ℤ)+1)))
    (hy : Tendsto (fun n => (b n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 y)) :
    Tendsto (fun n => (T n:ℝ)*pathMass (N n+1) (firstHit (b n))) atTop
      (𝓝 (2*y/t*heat t y)) := by
  have hN' : Tendsto (fun n => N n+1) atTop atTop := tendsto_atTop_mono (fun n => by omega) hN
  have hy' : Tendsto (fun n => (((b n:ℤ)+1:ℤ):ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 y) := by
    simpa only [Int.cast_add,Int.cast_one,Int.cast_natCast,add_div,add_zero] using
      hy.add (cast_div_sqrt_tendsto_zero hT 1)
  have hk := kernel_scaled_limit ht hN' hT (by simpa only [Nat.cast_add,Nat.cast_one] using hr) hz hy'
  have hnum : Tendsto (fun n => ((b n:ℝ)+1)/Real.sqrt (T n:ℝ)) atTop (𝓝 y) := by
    simpa only [Int.cast_add,Int.cast_one,Int.cast_natCast] using hy'
  have h := (hnum.div hr (ne_of_gt ht)).mul hk
  have hi : y/t*(2*heat t y)=2*y/t*heat t y := by ring
  rw [hi] at h
  apply h.congr'
  filter_upwards [hT.eventually (eventually_gt_atTop 0)] with n hn
  have htp : (T n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hs : Real.sqrt (T n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have hd : (N n:ℝ)+1≠0 := by positivity
  rw [firstHit_formula]
  dsimp only [Pi.mul_apply,Pi.div_apply]
  field_simp

end FKCRT.SimpleWalk
end

end OAI
