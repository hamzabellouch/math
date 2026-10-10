import Mathlib
import OAI.Probability.Ballisticity.Stationary.ArrayMap
import OAI.Probability.Ballisticity.Estimates.AnchorMoments

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical Topology
namespace DirectionalTransience

noncomputable def finiteOffsetTest {H : Type*} (z : H) (o : OnePoint H) : ℝ :=
  if o=(z:OnePoint H) then 1 else 0

lemma finiteOffsetTest_continuous {H : Type*} [TopologicalSpace H] [DiscreteTopology H]
    (z : H) : Continuous (finiteOffsetTest z) := by
  have ho : IsOpen ({(z:OnePoint H)} : Set (OnePoint H)) := by
    simpa only [Set.image_singleton] using OnePoint.isOpenMap_coe {z} (isOpen_discrete _)
  have hc : IsClosed ({(z:OnePoint H)} : Set (OnePoint H)) := isClosed_singleton
  apply continuous_iff_continuousAt.mpr
  intro o
  by_cases h : o=(z:OnePoint H)
  · apply (continuousAt_const (y:=(1:ℝ))).congr_of_eventuallyEq
    filter_upwards [ho.mem_nhds h] with x hx
    simp [finiteOffsetTest,Set.mem_singleton_iff.mp hx]
  · apply (continuousAt_const (y:=(0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hc.isOpen_compl.mem_nhds h] with x hx
    have hx' : x≠(z:OnePoint H) := hx
    simp [finiteOffsetTest,hx']

noncomputable def arrayOffsetTest {d : ℕ} (e : Direction d)
    (p q : ℤ×ℕ) (z : HorizontalSpace e) : C(ActualEpisodeArray e,ℝ) :=
  ⟨fun X => finiteOffsetTest z (X.2.1 (p,q)),
    (finiteOffsetTest_continuous z).comp ((continuous_apply _).comp (continuous_fst.comp continuous_snd))⟩

noncomputable def arrayProfileTest {d : ℕ} (e : Direction d)
    (j : ℤ) (p : ℤ×ℕ) (z : HorizontalSpace e) : C(ActualEpisodeArray e,ℝ) :=
  ⟨fun X => (X.2.2.1 (j,p,z)).val,by fun_prop⟩

noncomputable def arraySamplingError {d : ℕ} (e : Direction d)
    (p : ℤ×ℕ) (j : ℤ) (z : HorizontalSpace e) (n : ℕ) : C(ActualEpisodeArray e,ℝ) :=
  ⟨fun X => (n:ℝ)⁻¹*(∑ b∈Finset.range n, arrayOffsetTest e p (j,b) z X)-arrayProfileTest e j p z X,
    by fun_prop⟩

lemma arrayOffsetTest_mem {d : ℕ} (e : Direction d) (p q : ℤ×ℕ) (z : HorizontalSpace e)
    (X : ActualEpisodeArray e) : arrayOffsetTest e p q z X∈Set.Icc (0:ℝ) 1 := by
  change (if _ then (1:ℝ) else 0)∈Set.Icc (0:ℝ) 1
  split_ifs <;> norm_num

lemma arrayProfileTest_mem {d : ℕ} (e : Direction d) (j : ℤ) (p : ℤ×ℕ) (z : HorizontalSpace e)
    (X : ActualEpisodeArray e) : arrayProfileTest e j p z X∈Set.Icc (0:ℝ) 1 := (X.2.2.1 (j,p,z)).property

lemma arraySamplingError_bound {d : ℕ} (e : Direction d) (p : ℤ×ℕ) (j : ℤ)
    (z : HorizontalSpace e) (n : ℕ) (X : ActualEpisodeArray e) : ‖arraySamplingError e p j z n X‖≤1 := by
  have hsum0 : 0≤∑ b∈Finset.range n, arrayOffsetTest e p (j,b) z X :=
    Finset.sum_nonneg (fun b _ => (arrayOffsetTest_mem e p (j,b) z X).1)
  have hsum1 : (∑ b∈Finset.range n, arrayOffsetTest e p (j,b) z X)≤(n:ℝ) := by
    calc _ ≤ ∑ _b∈Finset.range n, (1:ℝ) :=
      Finset.sum_le_sum fun b _ => (arrayOffsetTest_mem e p (j,b) z X).2
    _ = _ := by simp
  have ha0 : 0≤(n:ℝ)⁻¹*∑ b∈Finset.range n, arrayOffsetTest e p (j,b) z X :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) hsum0
  have ha1 : (n:ℝ)⁻¹*∑ b∈Finset.range n, arrayOffsetTest e p (j,b) z X≤1 := by
    apply (mul_le_mul_of_nonneg_left hsum1 (inv_nonneg.mpr (Nat.cast_nonneg n))).trans
    by_cases hn : n=0
    · simp [hn]
    · rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn)]
  have hw := arrayProfileTest_mem e j p z X
  change |(n:ℝ)⁻¹*(∑ b∈Finset.range n, arrayOffsetTest e p (j,b) z X)-arrayProfileTest e j p z X|≤1
  rw [abs_le]
  constructor <;> linarith [hw.1,hw.2]

lemma actual_array_error_atom {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (X : EpisodeInput e) (p : ℤ×ℕ) (j : ℤ)
    (z : HorizontalSpace e) (n : ℕ) (hn : 0<n) :
    arraySamplingError e p j z n (actualArrayMap e t J X) =
      (n:ℝ)⁻¹*∑ b∈Finset.range n,
        AnchorSampling.atomError (episodeProfile e t X.1.1 j) (fun u => u+z) (X.1.2 p) (X.1.2 (j,b)) := by
  have he b : arrayOffsetTest e p (j,b) z (actualArrayMap e t J X) =
      (if X.1.2 (j,b)=X.1.2 p+z then (1:ℝ) else 0) := by
    simp only [arrayOffsetTest,ContinuousMap.coe_mk,actualArrayMap,finiteOffsetTest,OnePoint.coe_injective.eq_iff]
    congr 1
    apply propext
    constructor
    · intro h
      exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
    · intro h
      exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))
  have hw : arrayProfileTest e j p z (actualArrayMap e t J X)=
      (episodeProfile e t X.1.1 j).real {X.1.2 p+z} := rfl
  change (n:ℝ)⁻¹*(∑ b∈Finset.range n, arrayOffsetTest e p (j,b) z (actualArrayMap e t J X))-
    arrayProfileTest e j p z (actualArrayMap e t J X)=_
  simp_rw [he,hw,AnchorSampling.atomError,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  rw [mul_sub,←mul_assoc,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'),one_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> rfl

lemma actual_array_sampling_sq_conditional {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (ω : Environment d) (ξ : EpisodeAuxiliary e) (p : ℤ×ℕ) (j : ℤ)
    (z : HorizontalSpace e) (n : ℕ) (hn : 0<n) :
    (∫ U, (arraySamplingError e p j z n (actualArrayMap e t J ((ω,U),ξ)))^2
      ∂globalEpisodeAnchors e t ht ω)≤(n:ℝ)⁻¹ := by
  let f : ℕ ↪ ℤ×ℕ := ⟨fun b => (j,b),fun a b h => (Prod.mk.inj h).2⟩
  let S := (Finset.range n).map f
  have hcard : S.card=n := by simp [S]
  have hh := AnchorSampling.infinitePi_sample_average_sq
    (fun q : ℤ×ℕ => episodeProfile e t ω q.1) (episodeProfile e t ω j) p S
    (fun b hb => by obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hb; rfl) (fun u => u+z)
  simp only [hcard] at hh
  simp only [globalEpisodeAnchors,AnchorSampling.anchorKernel,Kernel.coe_mk]
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [] with U
  rw [actual_array_error_atom e t J _ p j z n hn]
  simp only [S,Finset.sum_map,f]
  rfl

lemma actual_array_offset {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (X : EpisodeInput e) (p q : ℤ×ℕ)
    (z : HorizontalSpace e) :
    arrayOffsetTest e p q z (actualArrayMap e t J X) =
      (if X.1.2 q=X.1.2 p+z then (1:ℝ) else 0) := by
  simp only [arrayOffsetTest,ContinuousMap.coe_mk,actualArrayMap,finiteOffsetTest,
    OnePoint.coe_injective.eq_iff]
  congr 1
  apply propext
  constructor
  · intro h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  · intro h
    exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

lemma actual_array_profile {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (X : EpisodeInput e) (p : ℤ×ℕ) (j : ℤ)
    (z : HorizontalSpace e) :
    arrayProfileTest e j p z (actualArrayMap e t J X)=
      (episodeProfile e t X.1.1 j).real {X.1.2 p+z} := rfl

lemma actual_array_sampling_test_conditional {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (ω : Environment d) (ξ : EpisodeAuxiliary e) (p q : ℤ×ℕ) (hpq : p≠q)
    (z : HorizontalSpace e) (g : C(ℝ,ℝ)) :
    (∫ U, g (arrayProfileTest e q.1 p z (actualArrayMap e t J ((ω,U),ξ)))*
      (arrayOffsetTest e p q z (actualArrayMap e t J ((ω,U),ξ))-
        arrayProfileTest e q.1 p z (actualArrayMap e t J ((ω,U),ξ)))
      ∂globalEpisodeAnchors e t ht ω)=0 := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f:=fun x : ℝ => g x) g.continuous.continuousOn
  have hG (u : HorizontalSpace e) :
      ‖g ((episodeProfile e t ω q.1).real {u+z})‖≤C := by
    apply hC
    exact ⟨measureReal_nonneg,measureReal_le_one⟩
  have hh := AnchorSampling.infinitePi_sampling_test
    (fun q : ℤ×ℕ => episodeProfile e t ω q.1) p q hpq (fun u => u+z)
    (fun u => g ((episodeProfile e t ω q.1).real {u+z})) C hG
  simp only [globalEpisodeAnchors,AnchorSampling.anchorKernel,Kernel.coe_mk]
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [] with U
  rw [actual_array_offset,actual_array_profile]
  unfold AnchorSampling.atomError
  congr 2
  split_ifs <;> rfl

end DirectionalTransience

end

end OAI
