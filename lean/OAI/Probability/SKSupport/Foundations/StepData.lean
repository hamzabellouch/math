import Mathlib
import OAI.Probability.SKSupport.Diffusion.VariableFeedbackEuler
import OAI.Probability.SKSupport.Foundations.SumRangeBlocks
import OAI.Probability.SKSupport.Foundations.Cascade

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace ZeroTemperatureSK.FiniteVerification
open Heat WeakIto
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

structure StepData (N : ℕ) (h : ℝ≥0) (c : ℕ → ℝ≥0) (F D : ℕ → ℝ → ℝ → ℝ) where
  C₂ : ℝ≥0
  C₃ : ℝ≥0
  Ct : ℝ≥0
  L : ℝ≥0
  Γ : ℝ≥0
  smooth : ∀ k t, ContDiff ℝ 3 (F k t)
  gradient_bound : ∀ k t z, |deriv (F k t) z| ≤ 1
  seam : ∀ k < N, F k (((k+1:ℕ):ℝ)*(h:ℝ)) = F (k+1) (((k+1:ℕ):ℝ)*(h:ℝ))
  coefficient_bound : ∀ k < N, c k ≤ Γ
  second_bound : ∀ k < N, ∀ t z, |deriv (deriv (F k t)) z| ≤ C₂
  third_bound : ∀ k < N, ∀ t z, |iteratedDeriv 3 (F k t) z| ≤ C₃
  rate_measurable : ∀ k t, Measurable (D k t)
  rate_bound : ∀ k < N, ∀ t z, |D k t z| ≤ Ct
  time_derivative : ∀ k < N, ∀ r ∈ Set.Icc ((k:ℝ)*(h:ℝ)) (((k:ℝ)+1)*(h:ℝ)), ∀ z,
      HasDerivWithinAt (fun t => F k t z) (D k r z)
        (Set.Icc ((k:ℝ)*(h:ℝ)) (((k:ℝ)+1)*(h:ℝ))) r
  rate_joint : ∀ k < N, ∀ r ∈ Set.Icc ((k:ℝ)*(h:ℝ)) (((k:ℝ)+1)*(h:ℝ)),
      ∀ s ∈ Set.Icc ((k:ℝ)*(h:ℝ)) (((k:ℝ)+1)*(h:ℝ)), ∀ z y,
      |D k r z-D k s y| ≤ (L:ℝ)*(|r-s|+|z-y|)
  pde : ∀ k < N, ∀ t ∈ Set.Icc ((k:ℝ)*(h:ℝ)) (((k:ℝ)+1)*(h:ℝ)), ∀ z,
      D k t z+(1/2:ℝ)*deriv (deriv (F k t)) z+(c k:ℝ)/2*(deriv (F k t) z)^2 = 0

noncomputable def cellHeat_stepData {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N : ℕ) :
    StepData N h c (cellHeat c h f N) (cellRate c h f N) := by
  classical
  have hd (k : ℕ) := cellHeat_verificationData hf hLip c h N k
  have hb (k : ℕ) := (hd k).bounds
  choose C₂ C₃ Ct L H using hb
  refine ⟨(Finset.range N).sup C₂, (Finset.range N).sup C₃,
    (Finset.range N).sup Ct, (Finset.range N).sup L, (Finset.range N).sup c,
    fun k => (hd k).smooth, fun k => (hd k).gradient_bound,
    cellHeat_seam hf hLip c h N, ?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro k hk
    exact Finset.le_sup (f := c) (Finset.mem_range.mpr hk)
  · intro k hk t z
    exact ((H k).1 t z).trans (by exact_mod_cast Finset.le_sup (f := C₂) (Finset.mem_range.mpr hk))
  · intro k hk t z
    exact ((H k).2.1 t z).trans (by exact_mod_cast Finset.le_sup (f := C₃) (Finset.mem_range.mpr hk))
  · exact fun k => (H k).2.2.1
  · intro k hk t z
    exact ((H k).2.2.2.1 t z).trans (by exact_mod_cast Finset.le_sup (f := Ct) (Finset.mem_range.mpr hk))
  · intro k hk r hr z
    have hs : Set.Icc ((k:ℝ)*(h:ℝ)) (((k:ℝ)+1)*(h:ℝ)) ⊆
        Set.Icc (0:ℝ) ((min (k+1) N:ℕ)*h) := by
      intro s hs
      rw [Nat.min_eq_left (by omega : k+1 ≤ N)]
      constructor
      · exact le_trans (mul_nonneg (Nat.cast_nonneg k) h.coe_nonneg) hs.1
      · simpa only [Nat.cast_add, Nat.cast_one] using hs.2
    exact ((H k).2.2.2.2.1 r (hs hr) z).mono hs
  · intro k hk r hr s hs z y
    have hsub : Set.Icc ((k:ℝ)*(h:ℝ)) (((k:ℝ)+1)*(h:ℝ)) ⊆
        Set.Icc (0:ℝ) ((min (k+1) N:ℕ)*h) := by
      intro t ht
      rw [Nat.min_eq_left (by omega : k+1 ≤ N)]
      constructor
      · exact le_trans (mul_nonneg (Nat.cast_nonneg k) h.coe_nonneg) ht.1
      · simpa only [Nat.cast_add, Nat.cast_one] using ht.2
    exact ((H k).2.2.2.2.2.1 r (hsub hr) s (hsub hs) z y).trans (by
      gcongr
      exact_mod_cast Finset.le_sup (f := L) (Finset.mem_range.mpr hk))
  · intro k hk t ht z
    apply (H k).2.2.2.2.2.2 t
    · rw [Nat.min_eq_left (by omega : k+1 ≤ N)]
      constructor
      · exact le_trans (mul_nonneg (Nat.cast_nonneg k) h.coe_nonneg) ht.1
      · simpa only [Nat.cast_add, Nat.cast_one] using ht.2

def profit (B : ℝ≥0 → Ω → ℝ) (α : ℝ≥0 → Ω → ℝ) (h : ℝ≥0) (c : ℕ → ℝ≥0)
    (f : ℝ → ℝ) (x : ℝ) (N : ℕ) : ℝ :=
  (∫ ξ, f (controlledGrid B α h c x N ξ) ∂P)-
    ∑ k ∈ Finset.range N, ∫ ξ, stepCost (fun r => α (Real.toNNReal r)) ((k:ℝ≥0)*h) h (c k) ξ ∂P

def objectives (hm : ∀ t, Measurable (B t)) (h : ℝ≥0) (c : ℕ → ℝ≥0)
    (f : ℝ → ℝ) (x : ℝ) (N : ℕ) : Set ℝ :=
  {v | ∃ α : ℝ≥0 → Ω → ℝ,
    IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α ∧
    (∀ t ξ, |α t ξ| ≤ 1) ∧ v = profit (P := P) B α h c f x N}

lemma objectives_nonempty (hm : ∀ t, Measurable (B t)) (h : ℝ≥0) (c : ℕ → ℝ≥0)
    (f : ℝ → ℝ) (x : ℝ) (N : ℕ) : (objectives (P := P) hm h c f x N).Nonempty := by
  exact ⟨_, fun _ _ => 0, isProgressive_const _ _, by simp, rfl⟩

lemma profit_refinement [IsProbabilityMeasure P] {α : ℝ≥0 → Ω → ℝ}
    (ham : Measurable (fun p : ℝ≥0 × Ω => α p.1 p.2)) (hab : ∀ t ξ, |α t ξ| ≤ 1)
    (h : ℝ≥0) (c : ℕ → ℝ≥0) (f : ℝ → ℝ) (x : ℝ) (N m : ℕ) (hmpos : 0 < m) :
    profit (P := P) B α (h/(m:ℝ≥0)) (fun j => c (j/m)) f x (N*m) =
      profit (P := P) B α h c f x N := by
  have ham' : Measurable (fun p : ℝ × Ω => α (Real.toNNReal p.1) p.2) :=
    ham.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  unfold profit
  congr 1
  · apply integral_congr_ae
    filter_upwards [] with ξ
    rw [controlledGrid_refinement B ham hab h c x N m hmpos ξ]
  · have hi (d a : ℝ≥0) (s : ℝ) : Integrable (stepCost (fun r => α (Real.toNNReal r)) s d a) P :=
      stepCost_integrable (α := fun r => α (Real.toNNReal r)) ham' (fun r ξ => hab _ ξ) s d a d.coe_nonneg a.coe_nonneg
    rw [← integral_finsetSum (Finset.range (N*m)) (fun j _ => hi _ _ _),
      ← integral_finsetSum (Finset.range N) (fun k _ => hi _ _ _)]
    apply integral_congr_ae
    filter_upwards [] with ξ
    exact grid_cost_refinement (α := fun r => α (Real.toNNReal r)) ham' (fun r ξ => hab _ ξ) h c N m hmpos ξ

noncomputable def StepData.refine {N : ℕ} {h : ℝ≥0} {c : ℕ → ℝ≥0}
    {F D : ℕ → ℝ → ℝ → ℝ} (sd : StepData N h c F D) (m : ℕ) (hm : 0 < m) :
    StepData (N*m) (h/(m:ℝ≥0)) (fun j => c (j/m)) (fun j => F (j/m)) (fun j => D (j/m)) := by
  have hq (j : ℕ) (hj : j < N*m) : j/m < N := (Nat.div_lt_iff_lt_mul hm).mpr hj
  have hsub (j : ℕ) : Set.Icc ((j:ℝ)*(↑(h/(m:ℝ≥0)):ℝ)) (((j:ℝ)+1)*(↑(h/(m:ℝ≥0)):ℝ)) ⊆
      Set.Icc ((j/m:ℕ)*(h:ℝ)) (((j/m:ℕ)+1)*(h:ℝ)) := by
    simpa only [NNReal.coe_div, NNReal.coe_natCast] using refined_cell_subset h hm j
  refine ⟨sd.C₂,sd.C₃,sd.Ct,sd.L,sd.Γ,
    fun j => sd.smooth (j/m), fun j => sd.gradient_bound (j/m), ?_,
    fun j hj => sd.coefficient_bound _ (hq j hj),
    fun j hj => sd.second_bound _ (hq j hj),
    fun j hj => sd.third_bound _ (hq j hj), fun j => sd.rate_measurable (j/m),
    fun j hj => sd.rate_bound _ (hq j hj), ?_,?_,?_⟩
  · intro j hj
    rcases refinement_successor hm j with he | ⟨he, hde⟩
    · rw [he]
    · rw [he]
      have ht : (((j+1:ℕ):ℝ)*(↑(h/(m:ℝ≥0)):ℝ)) = (((j/m+1:ℕ):ℝ)*(h:ℝ)) := by
        rw [hde]
        have hh := congrArg NNReal.toReal (refined_time h hm (j/m+1) 0)
        simpa only [Nat.add_zero, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div,
          NNReal.coe_natCast, Nat.cast_zero, zero_mul, add_zero] using hh
      rw [ht]
      exact sd.seam (j/m) (hq j hj)
  · intro j hj r hr z
    exact (sd.time_derivative _ (hq j hj) r (hsub j hr) z).mono (hsub j)
  · intro j hj r hr s hs z y
    exact sd.rate_joint _ (hq j hj) r (hsub j hr) s (hsub j hs) z y
  · intro j hj t ht z
    exact sd.pde _ (hq j hj) t (hsub j ht) z

lemma StepData.mesh_upper (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    {α : ℝ≥0 → Ω → ℝ}
    (hap : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α)
    (hab : ∀ t ξ, |α t ξ| ≤ 1)
    {N : ℕ} {h : ℝ≥0} {c : ℕ → ℝ≥0} {F D : ℕ → ℝ → ℝ → ℝ}
    (sd : StepData N h c F D) (x : ℝ) :
    profit (P := P) B α h c (F N ((N:ℝ)*(h:ℝ))) x N-F 0 0 x ≤
      (N:ℝ)*verificationError sd.Γ sd.C₂ sd.C₃ sd.L h := by
  have hleft (k : ℕ) : (k:ℝ)*(h:ℝ) ∈ Set.Icc ((k:ℝ)*(h:ℝ)) (((k:ℝ)+1)*(h:ℝ)) :=
    ⟨le_rfl, by nlinarith [h.coe_nonneg]⟩
  have hu := variable_grid_verification_upper hB hm hap hab h c x N
    (fun _ => sd.C₂) (fun _ => sd.C₃) (fun _ => sd.Ct) (fun _ => sd.L)
    (fun k _ => sd.smooth k) (fun k _ => sd.gradient_bound k)
    sd.second_bound sd.third_bound (fun k _ => sd.rate_measurable k _)
    (fun k hk => sd.rate_bound k hk _) sd.time_derivative
    (fun k hk r hr z y => by
      simpa only [NNReal.coe_mul, NNReal.coe_natCast] using
        sd.rate_joint k hk r hr ((k:ℝ)*(h:ℝ)) (hleft k) z y)
    (fun k hk z => by
      simpa only [NNReal.coe_mul, NNReal.coe_natCast] using
        sd.pde k hk ((k:ℝ)*(h:ℝ)) (hleft k) z) sd.seam
    (fun k hk => verificationError_mono (c k) sd.Γ sd.C₂ sd.C₂ sd.C₃ sd.C₃ sd.L sd.L h
      (sd.coefficient_bound k hk) le_rfl le_rfl le_rfl)
  dsimp only [profit]
  linarith

lemma StepData.mesh_lower (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    {N : ℕ} {h : ℝ≥0} {c : ℕ → ℝ≥0} {F D : ℕ → ℝ → ℝ → ℝ}
    (sd : StepData N h c F D) (x : ℝ) :
    ∃ α : ℝ≥0 → Ω → ℝ,
      IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α ∧
      (∀ t ξ, |α t ξ| ≤ 1) ∧
      F 0 0 x-(N:ℝ)*verificationError sd.Γ sd.C₂ sd.C₃ sd.L h ≤
        profit (P := P) B α h c (F N ((N:ℝ)*(h:ℝ))) x N := by
  have hleft (k : ℕ) : (k:ℝ)*(h:ℝ) ∈ Set.Icc ((k:ℝ)*(h:ℝ)) (((k:ℝ)+1)*(h:ℝ)) :=
    ⟨le_rfl, by nlinarith [h.coe_nonneg]⟩
  exact variable_grid_verification_lower hB hm h c x N
    (fun _ => sd.C₂) (fun _ => sd.C₃) (fun _ => sd.Ct) (fun _ => sd.L)
    sd.smooth sd.gradient_bound sd.second_bound sd.third_bound
    (fun k _ => sd.rate_measurable k _) (fun k hk => sd.rate_bound k hk _) sd.time_derivative
    (fun k hk r hr z y => by
      simpa only [NNReal.coe_mul, NNReal.coe_natCast] using
        sd.rate_joint k hk r hr ((k:ℝ)*(h:ℝ)) (hleft k) z y)
    (fun k hk z => by
      simpa only [NNReal.coe_mul, NNReal.coe_natCast] using
        sd.pde k hk ((k:ℝ)*(h:ℝ)) (hleft k) z) sd.seam
    (fun k hk => verificationError_mono (c k) sd.Γ sd.C₂ sd.C₂ sd.C₃ sd.C₃ sd.L sd.L h
      (sd.coefficient_bound k hk) le_rfl le_rfl le_rfl)

lemma refinement_endpoint (h : ℝ≥0) (N m : ℕ) (hm : 0 < m) :
    (((N*m:ℕ):ℝ)*((h/(m:ℝ≥0)):ℝ)) = (N:ℝ)*(h:ℝ) := by
  have he := congrArg NNReal.toReal (refined_time h hm N 0)
  simpa only [Nat.add_zero, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div,
    NNReal.coe_natCast, Nat.cast_zero, zero_mul, add_zero] using he

lemma StepData.control_upper (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    {α : ℝ≥0 → Ω → ℝ}
    (hap : IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) α)
    (hab : ∀ t ξ, |α t ξ| ≤ 1)
    {N : ℕ} {h : ℝ≥0} {c : ℕ → ℝ≥0} {F D : ℕ → ℝ → ℝ → ℝ}
    (sd : StepData N h c F D) (x : ℝ) :
    profit (P := P) B α h c (F N ((N:ℝ)*(h:ℝ))) x N ≤ F 0 0 x := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hlim : Tendsto (fun m : ℕ => (N*m:ℕ)*verificationError sd.Γ sd.C₂ sd.C₃ sd.L
      ((h:ℝ)/(m:ℝ))) atTop (𝓝 0) := by
    convert (verificationError_limit h sd.Γ sd.C₂ sd.C₃ sd.L).const_mul (N:ℝ) using 1
    · funext m; push_cast; ring
    · simp
  have hh : profit (P := P) B α h c (F N ((N:ℝ)*(h:ℝ))) x N-F 0 0 x ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm1
    have hmpos : 0 < m := by omega
    have hu := (sd.refine m hmpos).mesh_upper hB hm hap hab x
    have hdiv : N*m/m = N := by rw [Nat.mul_comm, Nat.mul_div_cancel_left _ hmpos]
    change profit (P := P) B α (h/(m:ℝ≥0)) (fun j => c (j/m))
      (F (N*m/m) (((N*m:ℕ):ℝ)*(h/(m:ℝ≥0)))) x (N*m)-F (0/m) 0 x ≤
      ((N*m:ℕ):ℝ)*verificationError sd.Γ sd.C₂ sd.C₃ sd.L (h/(m:ℝ≥0)) at hu
    rw [hdiv, refinement_endpoint h N m hmpos, Nat.zero_div,
      profit_refinement (progressive_joint_measurable _ hap) hab h c _ x N m hmpos] at hu
    simpa only [NNReal.coe_div, NNReal.coe_natCast] using hu
  linarith

lemma StepData.control_lower (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    {N : ℕ} {h : ℝ≥0} {c : ℕ → ℝ≥0} {F D : ℕ → ℝ → ℝ → ℝ}
    (sd : StepData N h c F D) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ v ∈ objectives (P := P) hm h c (F N ((N:ℝ)*(h:ℝ))) x N, F 0 0 x-ε ≤ v := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hlim : Tendsto (fun m : ℕ => (N*m:ℕ)*verificationError sd.Γ sd.C₂ sd.C₃ sd.L
      ((h:ℝ)/(m:ℝ))) atTop (𝓝 0) := by
    convert (verificationError_limit h sd.Γ sd.C₂ sd.C₃ sd.L).const_mul (N:ℝ) using 1
    · funext m; push_cast; ring
    · simp
  obtain ⟨m,hm1,he⟩ := ((eventually_ge_atTop (1:ℕ)).and
    (hlim.eventually (gt_mem_nhds hε))).exists
  have hmpos : 0 < m := by omega
  obtain ⟨α,hap,hab,hl⟩ := (sd.refine m hmpos).mesh_lower hB hm x
  have hdiv : N*m/m = N := by rw [Nat.mul_comm, Nat.mul_div_cancel_left _ hmpos]
  change F (0/m) 0 x-((N*m:ℕ):ℝ)*verificationError sd.Γ sd.C₂ sd.C₃ sd.L (h/(m:ℝ≥0)) ≤
    profit (P := P) B α (h/(m:ℝ≥0)) (fun j => c (j/m))
      (F (N*m/m) (((N*m:ℕ):ℝ)*(h/(m:ℝ≥0)))) x (N*m) at hl
  rw [hdiv, refinement_endpoint h N m hmpos, Nat.zero_div,
    profit_refinement (progressive_joint_measurable _ hap) hab h c _ x N m hmpos] at hl
  refine ⟨_, ⟨α,hap,hab,rfl⟩, ?_⟩
  simp only [NNReal.coe_natCast] at hl
  linarith

theorem cascade_eq_control_sup (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N : ℕ) (x : ℝ) :
    cascade c h f N 0 x = sSup (objectives (P := P) hm h c f x N) := by
  let sd := cellHeat_stepData hf hLip c h N
  have hend : cellHeat c h f N N ((N:ℝ)*(h:ℝ)) = f := by
    rw [cellHeat_left hf hLip c h N N le_rfl]
    simp [cascadeAt, cascade]
  have hstart : cellHeat c h f N 0 0 x = cascade c h f N 0 x := by
    have he := congrFun (cellHeat_left hf hLip c h N 0 (Nat.zero_le N)) x
    simpa only [Nat.cast_zero, zero_mul, cascadeAt, Nat.sub_zero] using he
  have hu : ∀ v ∈ objectives (P := P) hm h c f x N, v ≤ cascade c h f N 0 x := by
    intro v hv
    obtain ⟨α,hap,hab,hv⟩ := hv
    rw [hv]
    have hh := sd.control_upper hB hm hap hab x
    change profit (P := P) B α h c (cellHeat c h f N N ((N:ℝ)*(h:ℝ))) x N ≤
      cellHeat c h f N 0 0 x at hh
    rwa [hend,hstart] at hh
  have hb : BddAbove (objectives (P := P) hm h c f x N) := ⟨_,hu⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hh := sd.control_lower hB hm x hε
    change ∃ v ∈ objectives (P := P) hm h c (cellHeat c h f N N ((N:ℝ)*(h:ℝ))) x N,
      cellHeat c h f N 0 0 x-ε ≤ v at hh
    rw [hend,hstart] at hh
    obtain ⟨v,hv,hl⟩ := hh
    have hs := le_csSup hb hv
    linarith
  · exact csSup_le (objectives_nonempty hm h c f x N) hu

end ZeroTemperatureSK.FiniteVerification

end
end
end
end
end

end OAI
