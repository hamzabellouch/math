import OAI.NumberTheory.Jacobsthal.Renewal.RawHitRegeneration

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.TransitionKernels

lemma actualCostKernel_strict (z : CostState) : ∀ᵐ y ∂costKernel z, z.2 < y.2 := by
  have hm : MeasurableSet {y : CostState | z.2 < y.2} := measurableSet_lt measurable_const measurable_snd
  apply (ae_mem_iff_measure_eq hm.nullMeasurableSet).mpr
  rw [costKernel_apply z hm]
  have he : {s : State | z.2 < (s,z.2+cost (stateRatio s)).2}=univ := by
    apply eq_univ_of_forall
    intro s
    have hp := cost_pos (valid_pos (stateRatio_valid s))
    exact lt_add_of_pos_right z.2 hp
  simp only [mem_ofPred_eq]
  rw [he]
  simp

lemma rawExtension_strict_step (k : ℕ) (h : RawHistory k) :
    ∀ᵐ y ∂rawExtension k (k+1) h,
      (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩).2 < (rawLast (k+1) y).2 := by
  have hs : ∀ᵐ y ∂rawExtension k (k+1) h, (rawLast k h).2 < (rawLast (k+1) y).2 := by
    apply (ae_map_iff (rawLast_measurable (k+1)).aemeasurable
      (measurableSet_lt measurable_const measurable_snd)).mp
    rw [rawExtension_last_step]
    exact actualCostKernel_strict _
  filter_upwards [hs,rawExtension_retains_prefix (show k ≤ k+1 by omega) h] with y hy hp
  have he := congrFun hp (⟨k,by simp⟩ : Finset.Iic k)
  change y ⟨k,_⟩=rawLast k h at he
  rw [he]
  exact hy

lemma rawExtension_strict_coordinate {a b k : ℕ} (hak : a ≤ k) (hkb : k < b) (h : RawHistory a) :
    ∀ᵐ y ∂rawExtension a b h,
      (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩).2 <
        (y ⟨k+1,Finset.mem_Iic.mpr (by omega)⟩).2 := by
  have hm : MeasurableSet {y : RawHistory (k+1) |
      (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩).2 < (rawLast (k+1) y).2} :=
    measurableSet_lt (measurable_snd.comp (measurable_pi_apply _))
      (measurable_snd.comp (rawLast_measurable _))
  have he : (rawExtension a b h).map (rawPrefix (show k+1 ≤ b by omega))=rawExtension a (k+1) h :=
    Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ => CostState) (κ := historyKernel) h (show k+1 ≤ b by omega)
  have ht : ∀ᵐ y ∂rawExtension a (k+1) h,
      (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩).2 < (rawLast (k+1) y).2 := by
    have hc : rawExtension a (k+1)=rawExtension k (k+1) ∘ₖ rawExtension a k :=
      (Kernel.partialTraj_comp_partialTraj hak (by omega)).symm
    rw [hc]
    exact Kernel.ae_comp_of_ae_ae hm (Eventually.of_forall (rawExtension_strict_step k))
  rw [← he] at ht
  exact (ae_map_iff (rawPrefix_measurable (show k+1 ≤ b by omega)).aemeasurable hm).mp ht

noncomputable def increasingCosts (a b : ℕ) : Set (RawHistory b) :=
  {h | ∀ i j : Finset.Iic b, a ≤ i.1 → i.1 ≤ j.1 → (h i).2 ≤ (h j).2}

lemma increasingCosts_measurable (a b : ℕ) : MeasurableSet (increasingCosts a b) := by
  unfold increasingCosts
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _hi
  apply MeasurableSet.iInter
  intro _hij
  exact measurableSet_le (measurable_snd.comp (measurable_pi_apply i))
    (measurable_snd.comp (measurable_pi_apply j))

lemma increasingCosts_of_steps {a b : ℕ} (h : RawHistory b)
    (hs : ∀ k : Fin b, a ≤ k.1 →
      (h ⟨k.1,Finset.mem_Iic.mpr (by have hk:=k.2; omega)⟩).2 ≤
        (h ⟨k.1+1,Finset.mem_Iic.mpr (by have hk:=k.2; omega)⟩).2) :
    h ∈ increasingCosts a b := by
  intro i j hai hij
  have aux : ∀ m, i.1 ≤ m → ∀ hm : m ≤ b, (h i).2 ≤ (h ⟨m,Finset.mem_Iic.mpr hm⟩).2 := by
    intro m him
    induction m,him using Nat.le_induction with
    | base => intro hm; exact le_rfl
    | succ m him ih =>
      intro hmb
      have hmb' : m < b := by omega
      exact (ih (by omega)).trans (hs ⟨m,hmb'⟩ (hai.trans him))
  exact aux j.1 hij (Finset.mem_Iic.mp j.2)

theorem rawExtension_increasingCosts (a b : ℕ) (h : RawHistory a) :
    ∀ᵐ y ∂rawExtension a b h, y ∈ increasingCosts a b := by
  have hs : ∀ᵐ y ∂rawExtension a b h, ∀ k : Fin b, a ≤ k.1 →
      (y ⟨k.1,Finset.mem_Iic.mpr (by have hk:=k.2; omega)⟩).2 <
        (y ⟨k.1+1,Finset.mem_Iic.mpr (by have hk:=k.2; omega)⟩).2 := by
    rw [ae_all_iff]
    intro k
    by_cases hak : a ≤ k.1
    · filter_upwards [rawExtension_strict_coordinate hak k.2 h] with y hy
      exact fun _ => hy
    · exact Eventually.of_forall (fun _ hy => (hak hy).elim)
  filter_upwards [hs] with y hy
  exact increasingCosts_of_steps y (fun k hk => (hy k hk).le)

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures

lemma increasingCosts_at_start (a : ℕ) (h : RawHistory a) : h ∈ increasingCosts a a := by
  intro i j hai hij
  have hi : i.1=a := by have := Finset.mem_Iic.mp i.2; omega
  have hj : j.1=a := by have := Finset.mem_Iic.mp j.2; omega
  have he : i=j := Subtype.ext (hi.trans hj.symm)
  rw [he]

lemma increasingCosts_extend {a b c : ℕ} (hbc : b ≤ c) (h : RawHistory b) (y : RawHistory c)
    (hOld : h ∈ increasingCosts a b) (hNew : y ∈ increasingCosts b c) (hp : rawPrefix hbc y=h) :
    y ∈ increasingCosts a c := by
  intro i j hai hij
  have hv (k : Finset.Iic b) : y ⟨k.1,Finset.mem_Iic.mpr ((Finset.mem_Iic.mp k.2).trans hbc)⟩=h k :=
    congrFun hp k
  by_cases hjb : j.1 ≤ b
  · have hib : i.1 ≤ b := hij.trans hjb
    have he := hOld ⟨i.1,Finset.mem_Iic.mpr hib⟩ ⟨j.1,Finset.mem_Iic.mpr hjb⟩ hai hij
    simpa only [← hv] using he
  · by_cases hib : b ≤ i.1
    · exact hNew i j hib hij
    · have hib' : i.1 ≤ b := by omega
      have h1 := hOld ⟨i.1,Finset.mem_Iic.mpr hib'⟩ ⟨b,by simp⟩ hai hib'
      have h2 := hNew ⟨b,Finset.mem_Iic.mpr hbc⟩ j le_rfl (show b ≤ j.1 by omega)
      have h1' : (y i).2 ≤ (y ⟨b,Finset.mem_Iic.mpr hbc⟩).2 := by
        simpa only [← hv] using h1
      exact h1'.trans h2

lemma rawExtension_preserves_increasing {a b c : ℕ} (hbc : b ≤ c) (h : RawHistory b)
    (hh : h ∈ increasingCosts a b) :
    ∀ᵐ y ∂rawExtension b c h, y ∈ increasingCosts a c := by
  filter_upwards [rawExtension_increasingCosts b c h,rawExtension_retains_prefix hbc h] with y hy hp
  exact increasingCosts_extend hbc h y hh hy hp

noncomputable def returnIncreasing (a b : ℕ) : Set (RawReturnTrace b) :=
  {r | r.2 ∈ increasingCosts a (b+2*(r.1+1))}

lemma returnIncreasing_measurable (a b : ℕ) : MeasurableSet (returnIncreasing a b) := by
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  exact increasingCosts_measurable a (b+2*(n+1))

lemma rawReturn_increasing (a b : ℕ) (h : RawHistory b) (hh : h ∈ increasingCosts a b) :
    ∀ᵐ r ∂rawReturnTraceKernel b h, r ∈ returnIncreasing a b := by
  rw [rawReturnTraceKernel,Kernel.sum_apply,Measure.ae_sum_iff]
  intro n
  rw [Kernel.map_apply _ (rawReturnTrace_mk_measurable b n)]
  apply (ae_map_iff (rawReturnTrace_mk_measurable b n).aemeasurable (returnIncreasing_measurable a b)).mpr
  rw [firstReturnHistory,Kernel.restrict_apply]
  exact ae_restrict_of_ae (rawExtension_preserves_increasing (by omega) h hh)

lemma rawBranchReturn_increasing (a b : ℕ) (c : Bool) (h : RawHistory b) (hh : h ∈ increasingCosts a b) :
    ∀ᵐ r ∂rawBranchReturnKernel b c h, r ∈ returnIncreasing a b := by
  rw [rawBranchReturnKernel,Kernel.restrict_apply]
  exact ae_restrict_of_ae (rawReturn_increasing a b h hh)

noncomputable def selectedIncreasing (a : ℕ) : Set (Σ t : ℕ, RawReturnTrace t) :=
  {r | r.2 ∈ returnIncreasing a r.1}

lemma selectedIncreasing_measurable (a : ℕ) : MeasurableSet (selectedIncreasing a) := by
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro b
  exact returnIncreasing_measurable a b

lemma lastRawCycle_increasing (a : ℕ) (w : List Bool) : ∀ b c h,
    h ∈ increasingCosts a b →
    ∀ᵐ r ∂rawMarkedWordKernel b (w++[c]) h, lastRawCycle b w c r ∈ selectedIncreasing a := by
  induction w with
  | nil =>
    intro b c h hh
    apply rawMarkedWord_cons_ae b c [] h
      ((selectedIncreasing_measurable a).preimage (lastRawCycle_measurable [] b c))
    filter_upwards [rawBranchReturn_increasing a b c h hh] with r hr
    exact Eventually.of_forall (fun _ => hr)
  | cons d w ih =>
    intro b c h hh
    apply rawMarkedWord_cons_ae b d (w++[c]) h
      ((selectedIncreasing_measurable a).preimage (lastRawCycle_measurable (d::w) b c))
    filter_upwards [rawBranchReturn_increasing a b d h hh] with r hr
    exact ih _ c r.2 hr

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
