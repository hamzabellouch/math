import Mathlib
import OAI.Probability.Perceptron.Pressure.PressureTransport

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma integral_finite_label {I : Type*} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (a : Time → I) (ha : Measurable a) (F : I → ℝ) :
    (∫ u, F (a u) ∂timeLaw)=∑ i, timeLaw.real (a ⁻¹' {i})*F i := by
  classical
  have he (u : Time) : F (a u)=∑ i, (if a u=i then F i else 0) := by simp
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    change (∫ u, (a ⁻¹' {i}).indicator (fun _ => F i) u ∂timeLaw)=_
    rw [integral_indicator (ha (measurableSet_singleton i)),integral_const]
    simp only [Measure.restrict_apply_univ,smul_eq_mul,Measure.real]
  · intro i _
    exact (integrable_const (F i)).indicator (ha (measurableSet_singleton i))

structure FiniteFieldModel (f : Time → ℝ) where
  depth : ℕ
  value : Fin (depth+1) → ℝ
  label : Time → Fin (depth+1)
  measurable_label : Measurable label
  positive : ∀ i, 0 < timeLaw.real (label ⁻¹' {i})
  monotone_value : Monotone value
  agrees : (fun u => value (label u)) =ᵐ[timeLaw] f

def FiniteFieldModel.weight {f : Time → ℝ} (M : FiniteFieldModel f) (i : Fin (M.depth+1)) : ℝ :=
  timeLaw.real (M.label ⁻¹' {i})

lemma FiniteFieldModel.weight_pos {f : Time → ℝ} (M : FiniteFieldModel f) (i : Fin (M.depth+1)) :
    0 < M.weight i := M.positive i

lemma FiniteFieldModel.weight_sum {f : Time → ℝ} (M : FiniteFieldModel f) : ∑ i, M.weight i=1 := by
  have h := integral_finite_label M.label M.measurable_label (fun _ => 1)
  simpa [FiniteFieldModel.weight] using h.symm

lemma FiniteFieldModel.integral {f : Time → ℝ} (M : FiniteFieldModel f) (F : ℝ → ℝ) :
    (∫ u, F (f u) ∂timeLaw)=∑ i, M.weight i*F (M.value i) := by
  unfold FiniteFieldModel.weight
  rw [← integral_finite_label M.label M.measurable_label (fun i => F (M.value i))]
  apply integral_congr_ae
  filter_upwards [M.agrees] with u hu
  rw [hu]

def FiniteFieldModel.coupling {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g)
    (a : Fin (M.depth+1)×Fin (N.depth+1)) : ℝ :=
  timeLaw.real ((fun u => (M.label u,N.label u)) ⁻¹' {a})

lemma FiniteFieldModel.coupling_nonneg {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g)
    (a : Fin (M.depth+1)×Fin (N.depth+1)) : 0 ≤ M.coupling N a := measureReal_nonneg

lemma FiniteFieldModel.coupling_fst {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g)
    (i : Fin (M.depth+1)) : ∑ j, M.coupling N (i,j)=M.weight i := by
  classical
  have h := integral_finite_label (fun u => (M.label u,N.label u))
    (M.measurable_label.prodMk N.measurable_label) (fun a => if a.1=i then 1 else 0)
  have he := integral_finite_label M.label M.measurable_label (fun a => if a=i then 1 else 0)
  simp only [FiniteFieldModel.coupling,FiniteFieldModel.weight] at *
  simp only [Fintype.sum_prod_type,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at h he
  rw [Finset.sum_comm] at h
  simpa only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h.symm.trans he

lemma FiniteFieldModel.coupling_snd {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g)
    (j : Fin (N.depth+1)) : ∑ i, M.coupling N (i,j)=N.weight j := by
  classical
  have h := integral_finite_label (fun u => (M.label u,N.label u))
    (M.measurable_label.prodMk N.measurable_label) (fun a => if a.2=j then 1 else 0)
  have he := integral_finite_label N.label N.measurable_label (fun a => if a=j then 1 else 0)
  simp only [FiniteFieldModel.coupling,FiniteFieldModel.weight] at *
  simp only [Fintype.sum_prod_type,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at h he
  exact h.symm.trans he

lemma FiniteFieldModel.coupling_cost {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g) :
    (∑ a, M.coupling N a*|M.value a.1-N.value a.2|)=∫ u, |f u-g u| ∂timeLaw := by
  unfold FiniteFieldModel.coupling
  rw [← integral_finite_label (fun u => (M.label u,N.label u))
    (M.measurable_label.prodMk N.measurable_label) (fun a => |M.value a.1-N.value a.2|)]
  apply integral_congr_ae
  filter_upwards [M.agrees,N.agrees] with u hu hv
  rw [hu,hv]

lemma FiniteFieldModel.values_mem {f : Time → ℝ} (M : FiniteFieldModel f)
    {H : ℝ} (hf : ∀ᵐ u ∂timeLaw, f u ∈ Icc (0:ℝ) H) (i : Fin (M.depth+1)) :
    M.value i ∈ Icc (0:ℝ) H := by
  have hi : timeLaw (M.label ⁻¹' {i}) ≠ 0 := by
    intro hi
    have hp := M.positive i
    change 0 < (timeLaw (M.label ⁻¹' {i})).toReal at hp
    rw [hi] at hp
    simp at hp
  have hne : ∃ u, M.label u=i ∧ M.value (M.label u) ∈ Icc (0:ℝ) H := by
    by_contra! hn
    have hzero : ∀ᵐ u ∂timeLaw, u ∉ M.label ⁻¹' {i} := by
      filter_upwards [M.agrees,hf] with u hu hv
      intro hm
      exact hn u hm (hu ▸ hv)
    exact hi (by simpa only [not_not,Set.ofPred_mem_eq] using ae_iff.mp hzero)
  obtain ⟨u,hu,hv⟩ := hne
  simpa [hu] using hv

def FiniteFieldModel.pressure {f : Time → ℝ} (M : FiniteFieldModel f) (n : ℕ) : ℝ :=
  finiteSphericalFieldValue n M.depth M.weight M.value

lemma FiniteFieldModel.pressure_bound {f g : Time → ℝ} (M : FiniteFieldModel f) (N : FiniteFieldModel g)
    {H : ℝ} (hH : 0 ≤ H) (hf : ∀ᵐ u ∂timeLaw, f u ∈ Icc (0:ℝ) H)
    (hg : ∀ᵐ u ∂timeLaw, g u ∈ Icc (0:ℝ) H) (n : ℕ) :
    |M.pressure n-N.pressure n| ≤ sphericalContinuityConstant n H*(∫ u, |f u-g u| ∂timeLaw) := by
  have h := finiteSphericalFieldValue_coupling_bound M.weight M.value N.weight N.value (M.coupling N)
    M.weight_pos M.weight_sum N.weight_pos N.weight_sum M.monotone_value (M.values_mem hf 0).1
    N.monotone_value (N.values_mem hg 0).1 (M.coupling_nonneg N) (M.coupling_fst N) (M.coupling_snd N)
    H hH (M.values_mem hf _).2 (N.values_mem hg _).2 n
  rwa [M.coupling_cost N] at h

theorem exists_finiteFieldModel (f : Time → ℝ) (hf : Measurable f)
    (hfin : (Set.range f).Finite) : Nonempty (FiniteFieldModel f) := by
  classical
  let S := hfin.toFinset
  let T := S.filter (fun r => 0 < timeLaw.real (f ⁻¹' {r}))
  have hae : ∀ᵐ u ∂timeLaw, f u ∈ T := by
    have hnull : ∀ r ∈ S, ∀ᵐ u ∂timeLaw, f u=r → 0 < timeLaw.real (f ⁻¹' {r}) := by
      intro r _hr
      by_cases hp : 0 < timeLaw.real (f ⁻¹' {r})
      · exact ae_of_all _ (fun _ _ => hp)
      · have hz : timeLaw (f ⁻¹' {r})=0 := by
          have hz : (timeLaw (f ⁻¹' {r})).toReal=0 := le_antisymm (le_of_not_gt hp) ENNReal.toReal_nonneg
          have hp := (ENNReal.toReal_eq_zero_iff _).mp hz
          rcases hp with hp | hp
          · exact hp
          · exact (measure_ne_top _ _ hp).elim
        have hnot : ∀ᵐ u ∂timeLaw, f u ≠ r := by
          apply ae_iff.mpr
          simpa only [Set.preimage,Set.mem_singleton_iff,not_not] using hz
        filter_upwards [hnot] with u hu
        exact fun h => (hu h).elim
    have hall := (S.eventually_all).mpr hnull
    filter_upwards [hall] with u hu
    have hmem : f u ∈ S := hfin.mem_toFinset.mpr (mem_range_self u)
    exact Finset.mem_filter.mpr ⟨hmem,hu (f u) hmem rfl⟩
  have hT : T.Nonempty := by
    obtain ⟨u,hu⟩ := hae.exists
    exact ⟨f u,hu⟩
  obtain ⟨d,hd⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hT)
  let e := T.orderIsoOfFin hd
  let v : Fin (d+1) → ℝ := fun i => e i
  have hv : StrictMono v := fun i j hij => e.strictMono hij
  have hve : MeasurableEmbedding v := ⟨hv.injective,measurable_of_finite _,fun _ _ => (Set.toFinite _).measurableSet⟩
  let a : Time → Fin (d+1) := fun u => hve.invFun (f u)
  have hag : (fun u => v (a u)) =ᵐ[timeLaw] f := by
    filter_upwards [hae] with u hu
    have hx : f u=v (e.symm ⟨f u,hu⟩) := congrArg Subtype.val (e.apply_symm_apply ⟨f u,hu⟩) |>.symm
    dsimp only [a]
    rw [hx,hve.leftInverse_invFun]
  refine ⟨⟨d,v,a,hve.measurable_invFun.comp hf,?_,hv.monotone,hag⟩⟩
  intro i
  have he : a ⁻¹' {i}=ᵐ[timeLaw] f ⁻¹' {v i} := by
    filter_upwards [hag] with u hu
    apply propext
    change (a u=i) ↔ f u=v i
    rw [← hu]
    exact hv.injective.eq_iff.symm
  change 0 < (timeLaw (a ⁻¹' {i})).toReal
  rw [measure_congr he]
  exact (Finset.mem_filter.mp (e i).2).2

end SphericalPerceptronFreeEnergy

end

end OAI
