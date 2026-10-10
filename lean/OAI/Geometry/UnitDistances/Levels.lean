import OAI.Geometry.UnitDistances.States

namespace OAI

namespace PlanarUnitDistances.LevelStates
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels FiniteStates CrossStructure
open scoped Classical NNReal ENNReal
noncomputable section
variable {K V E : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E]

def state (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (a : Place K S × ℝ) (x : V) :
    (V → Bool)×(V → Bool) := match a.1 with
  | .inl σ => archState (fun x => σ (z x)) (fun x => σ (w x)) (u σ) a.2 x
  | .inr v => finiteState z w (WeightedAbsoluteValues.finiteEntry K v.val.1 v.val.2)
      (WeightedAbsoluteValues.finiteEntry_nonarch K v.val.1 v.val.2) a.2 x

omit [Fintype V] in
lemma state_measurable (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (x : V) :
    Measurable (fun a => state S z w u a x) := by
  change Measurable (fun a : Place K S × ℝ => (fun v s => state S z w u (v,s) x) a.1 a.2)
  refine FiniteLevels.measurable_pieces (J := Place K S) (fun v s => state S z w u (v,s) x) ?_
  intro v
  cases v with
  | inl σ => exact archState_measurable _ _ _ _
  | inr v => exact finiteState_measurable _ _ _ _ _

def bit (S : Finset K) (z : V → K) (src tgt : E → V) (a : Place K S × ℝ) (e : E) : Bool :=
  decide (a.2 < -log (av K a.1 (z (src e)-z (tgt e))))

omit [Fintype V] [Fintype E] in
lemma bit_measurable (S : Finset K) (z : V → K) (src tgt : E → V) (e : E) :
    Measurable (fun a => bit S z src tgt a e) := by
  have he : (fun a => bit S z src tgt a e) =
      (fun a => if a.2 < -log (av K a.1 (z (src e)-z (tgt e))) then true else false) := by
    funext a; unfold bit; split_ifs <;> simp_all
  rw [he]
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_lt measurable_snd ((measurable_of_finite (fun v : Place K S => -log (av K v (z (src e)-z (tgt e))))).comp measurable_fst)

def edgeError (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (a : Place K S × ℝ) (e : E) : ℝ :=
  if Consistent (bit S z src tgt a e) (state S z w u a (src e)) (state S z w u a (tgt e)) then 0 else 1

omit [Fintype E] in
lemma edgeError_measurable (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (e : E) :
    Measurable (fun a => edgeError S z w src tgt u a e) := by
  exact (measurable_of_finite (fun bxy : Bool × ((V→Bool)×(V→Bool)) × ((V→Bool)×(V→Bool)) =>
    if Consistent bxy.1 bxy.2.1 bxy.2.2 then (0:ℝ) else 1)).comp
    ((bit_measurable S z src tgt e).prodMk
      ((state_measurable S z w u (src e)).prodMk (state_measurable S z w u (tgt e))))
omit [Fintype V] [Fintype E] in
lemma edgeError_bounds (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (a : Place K S × ℝ) (e : E) :
    0≤edgeError S z w src tgt u a e ∧ edgeError S z w src tgt u a e≤1 := by
  unfold edgeError; split_ifs <;> norm_num

def meanError (μ : Law E) (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (a : Place K S × ℝ) : ℝ :=
  avg μ (edgeError S z w src tgt u a)
lemma meanError_measurable (μ : Law E) (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) : Measurable (meanError μ S z w src tgt u) := by
  exact Finset.measurable_sum _ (fun e _ => measurable_const.mul (edgeError_measurable S z w src tgt u e))
omit [Fintype V] in
lemma meanError_bounds (μ : Law E) (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (a : Place K S × ℝ) :
    0 ≤ meanError μ S z w src tgt u a ∧ meanError μ S z w src tgt u a≤1 := by
  constructor
  · exact avg_nonneg μ (fun e => (edgeError_bounds S z w src tgt u a e).1)
  · exact (avg_mono μ (fun e => (edgeError_bounds S z w src tgt u a e).2)).trans_eq (avg_const _ _)

omit [Fintype V] [Fintype E] in
lemma edgeError_arch (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (σ : K →ₐ[ℚ] ℂ) (s : ℝ) (e : E) :
    edgeError S z w src tgt u (.inl σ,s) e =
      StateConsistency.error (-log ‖σ (z (src e))-σ (z (tgt e))‖) s
        (σ (z (src e))) (σ (z (tgt e))) (σ (w (src e))) (σ (w (tgt e))) (u σ) := by
  simp only [edgeError,bit,state,av,WeightedAbsoluteValues.infiniteEntry_apply,map_sub,
    archState_consistent_iff,StateConsistency.error]

omit [Fintype V] [Fintype E] in
lemma edgeError_finite_ae (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : ↥(finiteSupport K S))
    (e : E) (hu : (z (src e)-z (tgt e))*(w (src e)-w (tgt e))=1) :
    (fun s => edgeError S z w src tgt u (.inr v,s) e) =ᵐ[volume] 0 := by
  filter_upwards [volume.ae_ne (-log (WeightedAbsoluteValues.finiteEntry K v.val.1 v.val.2
    (z (src e)-z (tgt e))))] with s hs
  have hc := finiteState_consistent z w _
    (WeightedAbsoluteValues.finiteEntry_nonarch K v.val.1 v.val.2) hu hs
  exact ite_eq_left hc

lemma integral_meanError (μ : Law E) (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (v : Place K S) (l r : ℝ) :
    (∫s in Icc l r,meanError μ S z w src tgt u (v,s)) =
      ∑e,μ.val e*∫s in Icc l r,edgeError S z w src tgt u (v,s) e := by
  have hi (e : E) : Integrable (fun s => edgeError S z w src tgt u (v,s) e)
      (volume.restrict (Icc l r)) := by
    apply Integrable.mono' (integrable_const (1:ℝ))
      ((edgeError_measurable S z w src tgt u e).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun s => by
      change ‖edgeError S z w src tgt u (v,s) e‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg (edgeError_bounds S z w src tgt u (v,s) e).1]
      exact (edgeError_bounds S z w src tgt u (v,s) e).2
  unfold meanError avg
  rw [integral_finsetSum _ (fun e _ => (hi e).const_mul (μ.val e))]
  simp only [integral_const_mul]

theorem exists_bounded_states (μ : Law E) (S : Finset K) (z w : V → K) (src tgt : E → V)
    (hu : ∀e,(z (src e)-z (tgt e))*(w (src e)-w (tgt e))=1) :
    ∃u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts,
      (∀σ,StateConsistency.Fractional (u σ)) ∧
      (∫a,meanError μ S z w src tgt u a ∂FiniteLevels.measure
        (⟨(Module.finrank ℚ K : ℝ)⁻¹,inv_nonneg.mpr (Nat.cast_nonneg _)⟩ : ℝ≥0)
        (fun v => -radius K S v) (radius K S)) ≤ 2*log 2+4 := by
  have hh (σ : K →ₐ[ℚ] ℂ) := StateConsistency.exists_fractionalShifts μ.val μ.nonneg μ.total
    (fun e => σ (z (src e))) (fun e => σ (z (tgt e)))
    (fun e => σ (w (src e))) (fun e => σ (w (tgt e)))
    (fun e => by simpa only [map_mul,map_sub,map_one] using congrArg σ (hu e))
    (-radius K S (.inl σ)) (radius K S (.inl σ))
  choose u hf hb using hh
  refine ⟨u,hf,?_⟩
  refine (FiniteLevels.integral_eq (J := Place K S)
    (⟨(Module.finrank ℚ K : ℝ)⁻¹,inv_nonneg.mpr (Nat.cast_nonneg _)⟩ : ℝ≥0)
    (fun v => -radius K S v) (radius K S) _ (meanError_measurable μ S z w src tgt u) 1
    (fun a => by
      rw [abs_of_nonneg (meanError_bounds μ S z w src tgt u a).1]
      exact (meanError_bounds μ S z w src tgt u a).2)).trans_le ?_
  have hv (v : ↥(finiteSupport K S)) : (∫s in Icc (-radius K S (.inr v)) (radius K S (.inr v)),
      meanError μ S z w src tgt u (.inr v,s))=0 := by
    rw [integral_meanError]
    apply sum_eq_zero
    intro e _
    rw [integral_congr_ae (ae_restrict_of_ae (edgeError_finite_ae S z w src tgt u v e (hu e)))]
    simp only [Pi.zero_apply,integral_zero,mul_zero]
  change (Module.finrank ℚ K:ℝ)⁻¹ * (∑v : (K →ₐ[ℚ] ℂ) ⊕ ↥(finiteSupport K S),_)≤_
  rw [Fintype.sum_sum_type]
  simp only [hv,sum_const_zero,add_zero]
  have hm := sum_le_sum (s:=univ) (fun σ _ => hb σ)
  simp only [sum_const,card_univ,nsmul_eq_mul,WeightedAbsoluteValues.infiniteEntry_count] at hm
  have harch (σ : K →ₐ[ℚ] ℂ) := integral_meanError μ S z w src tgt u (.inl σ)
    (-radius K S (.inl σ)) (radius K S (.inl σ))
  simp only [edgeError_arch] at harch
  simp_rw [harch]
  have hd : 0<(Module.finrank ℚ K:ℝ) := by exact_mod_cast (Module.finrank_pos : 0<Module.finrank ℚ K)
  calc
    _ ≤ (Module.finrank ℚ K:ℝ)⁻¹*((Module.finrank ℚ K:ℝ)*(2*log 2+4)) :=
      mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hd.le)
    _ = _ := by field_simp
end
end PlanarUnitDistances.LevelStates

namespace PlanarUnitDistances.ThresholdProfiles
open MeasureTheory Set
open scoped BigOperators
noncomputable section

def bit (a s : ℝ) : ℝ := if s < a then 1 else 0

lemma bit_nonneg (a s : ℝ) : 0 ≤ bit a s := by unfold bit; split <;> norm_num
lemma bit_le_one (a s : ℝ) : bit a s ≤ 1 := by unfold bit; split <;> norm_num
lemma bit_measurable (a : ℝ) : Measurable (bit a) :=
  Measurable.ite measurableSet_Iio measurable_const measurable_const

lemma bit_integrableOn (a l u : ℝ) : IntegrableOn (bit a) (Icc l u) := by
  have he : bit a = (Iio a).indicator (fun _ => (1 : ℝ)) := by
    funext s; simp [bit,Set.indicator]
  rw [he]
  exact (show Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc l u))
    from continuous_const.integrableOn_Icc).indicator measurableSet_Iio

lemma abs_bit_sub_eq (a b s : ℝ) :
    |bit a s - bit b s| = (Ico (min a b) (max a b)).indicator (fun _ => (1 : ℝ)) s := by
  by_cases ha : s < a <;> by_cases hb : s < b <;>
    simp [bit,ha,hb,Set.indicator,mem_Ico]

lemma bit_sub_integral {l u a b : ℝ} (hla : l ≤ a) (hua : a ≤ u)
    (hlb : l ≤ b) (hub : b ≤ u) :
    ∫ s in Icc l u, |bit a s - bit b s| = |a-b| := by
  simp_rw [abs_bit_sub_eq]
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ico]
  rw [measureReal_restrict_apply measurableSet_Ico]
  have hsub : Ico (min a b) (max a b) ⊆ Icc l u := by
    intro s hs
    exact ⟨(le_min hla hlb).trans hs.1, hs.2.le.trans (max_le hua hub)⟩
  rw [inter_eq_left.mpr hsub,Real.volume_real_Ico]
  simp [smul_eq_mul,max_sub_min_eq_abs,abs_sub_comm]

lemma bit_mismatch (a b s : ℝ) :
    |bit a s - bit b s| = bit a s + bit b s - 2*bit a s*bit b s := by
  unfold bit
  split <;> split <;> norm_num

variable {E : Type*} [Fintype E]

def frequency (p : E → ℝ) (a : E → ℝ) (s : ℝ) : ℝ := ∑ e, p e * bit (a e) s

def minority (p : E → ℝ) (a : E → ℝ) (s : ℝ) : ℝ :=
  min (frequency p a s) (1-frequency p a s)

lemma frequency_nonneg (p : E → ℝ) (hp : ∀ e, 0 ≤ p e) (a : E → ℝ) (s : ℝ) :
    0 ≤ frequency p a s := Finset.sum_nonneg fun e _ => mul_nonneg (hp e) (bit_nonneg _ _)

lemma frequency_le_one (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hs : ∑ e, p e = 1) (a : E → ℝ) (s : ℝ) : frequency p a s ≤ 1 := by
  unfold frequency
  calc
    _ ≤ ∑ e, p e := Finset.sum_le_sum fun e _ => mul_le_of_le_one_right (hp e) (bit_le_one _ _)
    _ = 1 := hs

lemma frequency_measurable (p : E → ℝ) (a : E → ℝ) : Measurable (frequency p a) := by
  unfold frequency
  exact Finset.measurable_sum Finset.univ fun e _ =>
    measurable_const.mul (bit_measurable (a e))

lemma minority_integrableOn (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hs : ∑ e, p e = 1) (a : E → ℝ) (l u : ℝ) :
    IntegrableOn (minority p a) (Icc l u) := by
  have hm : Measurable (minority p a) :=
    (frequency_measurable p a).min (measurable_const.sub (frequency_measurable p a))
  apply Integrable.of_bound hm.aestronglyMeasurable (1 : ℝ)
  filter_upwards [] with s
  change |min (frequency p a s) (1-frequency p a s)| ≤ 1
  rw [abs_of_nonneg (le_min (frequency_nonneg p hp a s)
    (sub_nonneg.mpr (frequency_le_one p hp hs a s)))]
  exact (min_le_left _ _).trans (frequency_le_one p hp hs a s)

lemma independent_mismatch (p : E → ℝ) (hs : ∑ e, p e = 1) (a : E → ℝ) (s : ℝ) :
    (∑ e, ∑ f, p e*p f*|bit (a e) s-bit (a f) s|) =
      2*frequency p a s*(1-frequency p a s) := by
  simp_rw [bit_mismatch]
  simp_rw [mul_sub,mul_add]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have h₁ : (∑ e, ∑ f, p e*p f*bit (a e) s) = frequency p a s := by
    simp_rw [mul_right_comm (p _) (p _) (bit _ _),← Finset.mul_sum,hs,mul_one]
    rfl
  have h₂ : (∑ e, ∑ f, p e*p f*bit (a f) s) = frequency p a s := by
    simp_rw [mul_assoc,← Finset.mul_sum,← Finset.sum_mul,hs,one_mul]
    rfl
  have h₃ : (∑ e, ∑ f, p e*p f*(2*bit (a e) s*bit (a f) s)) =
      2*frequency p a s*frequency p a s := by
    have he (e f : E) : p e*p f*(2*bit (a e) s*bit (a f) s) =
        (2*(p e*bit (a e) s))*(p f*bit (a f) s) := by ring
    simp_rw [he,← Finset.mul_sum,← Finset.sum_mul]
    unfold frequency
    rw [← Finset.mul_sum]
  rw [h₁,h₂,h₃]
  ring

lemma mismatch_le_twice_minority (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hs : ∑ e, p e = 1) (a : E → ℝ) (s : ℝ) :
    (∑ e, ∑ f, p e*p f*|bit (a e) s-bit (a f) s|) ≤ 2*minority p a s := by
  rw [independent_mismatch p hs a s,minority,mul_min_of_nonneg _ _ (by norm_num)]
  have h0 := frequency_nonneg p hp a s
  have h1 := frequency_le_one p hp hs a s
  apply le_min <;> nlinarith [sq_nonneg (frequency p a s),sq_nonneg (1-frequency p a s)]

lemma pair_integrableOn (c a b l u : ℝ) :
    IntegrableOn (fun s => c * |bit a s-bit b s|) (Icc l u) :=
  ((bit_integrableOn a l u).sub (bit_integrableOn b l u)).abs.const_mul c

lemma mismatch_integrableOn (p a : E → ℝ) (l u : ℝ) :
    IntegrableOn (fun s => ∑ e, ∑ f, p e*p f*|bit (a e) s-bit (a f) s|) (Icc l u) := by
  exact integrable_finsetSum Finset.univ fun e _ =>
    integrable_finsetSum Finset.univ fun f _ => pair_integrableOn _ _ _ _ _

lemma integrated_mismatch (p a : E → ℝ) {l u : ℝ}
    (hla : ∀ e, l ≤ a e) (hua : ∀ e, a e ≤ u) :
    (∫ s in Icc l u, ∑ e, ∑ f, p e*p f*|bit (a e) s-bit (a f) s|) =
      ∑ e, ∑ f, p e*p f*|a e-a f| := by
  rw [integral_finsetSum Finset.univ (fun e _ =>
    integrable_finsetSum Finset.univ fun f _ => pair_integrableOn _ _ _ _ _)]
  apply Finset.sum_congr rfl
  intro e _
  rw [integral_finsetSum Finset.univ (fun f _ => pair_integrableOn _ _ _ _ _)]
  apply Finset.sum_congr rfl
  intro f _
  rw [integral_const_mul,bit_sub_integral (hla e) (hua e) (hla f) (hua f)]

lemma expected_distance_identity (p a : E → ℝ) (hs : ∑ e, p e = 1) {l u : ℝ}
    (hla : ∀ e, l ≤ a e) (hua : ∀ e, a e ≤ u) :
    (∑ e, ∑ f, p e*p f*|a e-a f|) =
      2 * ∫ s in Icc l u, frequency p a s * (1-frequency p a s) := by
  rw [← integrated_mismatch p a hla hua]
  simp_rw [independent_mismatch p hs,mul_assoc (2 : ℝ)]
  exact integral_const_mul _ _

lemma expected_distance_le (p a : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hs : ∑ e, p e = 1) {l u : ℝ} (hla : ∀ e, l ≤ a e) (hua : ∀ e, a e ≤ u) :
    (∑ e, ∑ f, p e*p f*|a e-a f|) ≤ 2 * ∫ s in Icc l u, minority p a s := by
  rw [← integrated_mismatch p a hla hua,← integral_const_mul]
  exact integral_mono (mismatch_integrableOn p a l u)
    ((minority_integrableOn p hp hs a l u).const_mul 2)
    (mismatch_le_twice_minority p hp hs a)

lemma minority_of_constant (p : E → ℝ) (hs : ∑ e, p e = 1) (c s : ℝ) :
    minority p (fun _ => c) s = 0 := by
  simp only [minority,frequency,← Finset.sum_mul,hs,one_mul]
  unfold bit
  split <;> norm_num

end
end PlanarUnitDistances.ThresholdProfiles

namespace PlanarUnitDistances.ThresholdProfiles
open MeasureTheory Set
open scoped BigOperators
noncomputable section

lemma finiteSupport_profile {V E : Type*} [Finite E] (a : E → V → ℝ)
    (ha : ∀ e, Function.HasFiniteSupport (a e)) (F : V → (E → ℝ) → ℝ)
    (hF : ∀ v, F v (fun _ => 0) = 0) :
    Function.HasFiniteSupport (fun v => F v (fun e => a e v)) := by
  classical
  apply (Set.finite_iUnion fun e => ha e).subset
  intro v hv
  by_contra hn
  have hz : (fun e => a e v) = fun _ => 0 := by
    funext e
    by_contra he
    exact hn (Set.mem_iUnion.mpr ⟨e,he⟩)
  exact hv (by change F v (fun e => a e v) = 0; rw [hz,hF])

lemma finiteSupport_minorIntegral {V E : Type*} [Fintype E]
    (p : E → ℝ) (hs : ∑ e, p e = 1) (a : E → V → ℝ)
    (ha : ∀ e, Function.HasFiniteSupport (a e)) (l u : V → ℝ) :
    Function.HasFiniteSupport (fun v => ∫ s in Icc (l v) (u v),
      minority p (fun e => a e v) s) := by
  apply finiteSupport_profile a ha (fun v a => ∫ s in Icc (l v) (u v), minority p a s)
  intro v
  simp only [minority_of_constant p hs,integral_zero]

end
end PlanarUnitDistances.ThresholdProfiles

namespace PlanarUnitDistances.WeightedAbsoluteValues
open MeasureTheory Set Finset Real
open scoped BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
variable {E : Type*} [Fintype E]

def archThreshold (d : E → K) (σ : K →ₐ[ℚ] ℂ) (e : E) : ℝ :=
  -log (infiniteEntry K σ (d e))
def finiteThreshold (d : E → K) (v : Nat.Primes × Gal(K/ℚ)) (e : E) : ℝ :=
  -log (finiteEntry K v.1 v.2 (d e))

def profileScale (p : E → ℝ) (d : E → K)
    (la ua : (K →ₐ[ℚ] ℂ) → ℝ) (lf uf : Nat.Primes × Gal(K/ℚ) → ℝ) : ℝ :=
  ((∑ σ : K →ₐ[ℚ] ℂ, ∫ s in Icc (la σ) (ua σ),
      ThresholdProfiles.minority p (archThreshold K d σ) s) +
    (∑ᶠ v : Nat.Primes × Gal(K/ℚ), ∫ s in Icc (lf v) (uf v),
      ThresholdProfiles.minority p (finiteThreshold K d v) s)) / (Module.finrank ℚ K : ℝ)

omit [Fintype E] in
omit [IsGalois ℚ K] in
lemma finiteThreshold_support (d : E → K) (e : E) :
    Function.HasFiniteSupport (fun v => finiteThreshold K d v e) :=
  (finite_log_support K (d e)).neg

omit [IsGalois ℚ K] in
lemma finiteProfile_integral_support (p : E → ℝ) (hs : ∑ e, p e = 1)
    (d : E → K) (lf uf : Nat.Primes × Gal(K/ℚ) → ℝ) :
    Function.HasFiniteSupport (fun v => ∫ s in Icc (lf v) (uf v),
      ThresholdProfiles.minority p (finiteThreshold K d v) s) :=
  ThresholdProfiles.finiteSupport_minorIntegral p hs (fun e v => finiteThreshold K d v e)
    (finiteThreshold_support K d) lf uf

omit [IsGalois ℚ K] in
lemma finiteProfile_pair_support (p : E → ℝ) (d : E → K) (e f : E) :
    Function.HasFiniteSupport (fun v => p e*p f*
      |finiteThreshold K d v e-finiteThreshold K d v f|) := by
  apply ThresholdProfiles.finiteSupport_profile (fun e v => finiteThreshold K d v e)
    (finiteThreshold_support K d) (fun _ a => p e*p f*|a e-a f|)
  intro v
  simp

omit [NumberField K] [IsGalois ℚ K] in
lemma log_quotient_distance (v : AbsoluteValue K ℝ) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    |-log (v x) - -log (v y)| = |log (v (x/y))| := by
  rw [map_div₀,log_div ((v.pos hx).ne') ((v.pos hy).ne')]
  rw [show -log (v x) - -log (v y) = -(log (v x)-log (v y)) by ring,abs_neg]

omit [Fintype E] in
lemma profile_pair_height (d : E → K) (hd : ∀ e, d e ≠ 0) (e f : E) :
    ((∑ σ : K →ₐ[ℚ] ℂ, |archThreshold K d σ e-archThreshold K d σ f|) +
      (∑ᶠ v : Nat.Primes × Gal(K/ℚ), |finiteThreshold K d v e-finiteThreshold K d v f|)) /
      (Module.finrank ℚ K : ℝ) = 2*exactHeight K (d e/d f) := by
  simp only [archThreshold,finiteThreshold,log_quotient_distance K _ (hd e) (hd f)]
  exact weighted_abs_log_eq_twice K (div_ne_zero (hd e) (hd f))

lemma weighted_height_profile_identity (p : E → ℝ) (d : E → K) (hd : ∀ e, d e ≠ 0) :
    2 * (∑ e, ∑ f, p e*p f*exactHeight K (d e/d f)) =
      ((∑ σ : K →ₐ[ℚ] ℂ, ∑ e, ∑ f, p e*p f*
        |archThreshold K d σ e-archThreshold K d σ f|) +
       (∑ᶠ v : Nat.Primes × Gal(K/ℚ), ∑ e, ∑ f, p e*p f*
        |finiteThreshold K d v e-finiteThreshold K d v f|)) / (Module.finrank ℚ K : ℝ) := by
  classical
  have ha : (∑ σ : K →ₐ[ℚ] ℂ, ∑ e, ∑ f, p e*p f*
      |archThreshold K d σ e-archThreshold K d σ f|) =
      ∑ e, ∑ f, p e*p f*∑ σ : K →ₐ[ℚ] ℂ,
        |archThreshold K d σ e-archThreshold K d σ f| := by
    rw [sum_comm]
    apply sum_congr rfl
    intro e _
    rw [sum_comm]
    simp only [mul_sum]
  have hf : (∑ᶠ v : Nat.Primes × Gal(K/ℚ), ∑ e, ∑ f, p e*p f*
      |finiteThreshold K d v e-finiteThreshold K d v f|) =
      ∑ e, ∑ f, p e*p f*∑ᶠ v : Nat.Primes × Gal(K/ℚ),
        |finiteThreshold K d v e-finiteThreshold K d v f| := by
    rw [finsum_sum_comm univ _ (fun e _ => Function.HasFiniteSupport.sum
      (fun f => finiteProfile_pair_support K p d e f) univ)]
    apply sum_congr rfl
    intro e _
    rw [finsum_sum_comm univ _ (fun f _ => finiteProfile_pair_support K p d e f)]
    apply sum_congr rfl
    intro f _
    exact (mul_finsum _ _).symm
  rw [ha,hf,← sum_add_distrib,sum_div,mul_sum]
  apply sum_congr rfl
  intro e _
  rw [← sum_add_distrib,sum_div,mul_sum]
  apply sum_congr rfl
  intro f _
  rw [← mul_add,mul_div_assoc,profile_pair_height K d hd]
  ring

lemma expected_height_le_profileScale (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hs : ∑ e, p e = 1) (d : E → K) (hd : ∀ e, d e ≠ 0)
    (la ua : (K →ₐ[ℚ] ℂ) → ℝ) (lf uf : Nat.Primes × Gal(K/ℚ) → ℝ)
    (hla : ∀ σ e, la σ ≤ archThreshold K d σ e)
    (hua : ∀ σ e, archThreshold K d σ e ≤ ua σ)
    (hlf : ∀ v e, lf v ≤ finiteThreshold K d v e)
    (huf : ∀ v e, finiteThreshold K d v e ≤ uf v) :
    (∑ e, ∑ f, p e*p f*exactHeight K (d e/d f)) ≤ profileScale K p d la ua lf uf := by
  have ha := sum_le_sum (s := univ) (fun (σ : K →ₐ[ℚ] ℂ) _ =>
    ThresholdProfiles.expected_distance_le p (archThreshold K d σ) hp hs (hla σ) (hua σ))
  have hf := finsum_le_finsum
    (Function.HasFiniteSupport.sum (fun e => Function.HasFiniteSupport.sum
      (fun f => finiteProfile_pair_support K p d e f) univ) univ)
    ((finiteProfile_integral_support K p hs d lf uf).mul_right (fun _ => (2 : ℝ)))
    (fun v => ThresholdProfiles.expected_distance_le p (finiteThreshold K d v) hp hs (hlf v) (huf v))
  have h := div_le_div_of_nonneg_right (add_le_add ha hf) (finrank_pos K).le
  rw [← weighted_height_profile_identity K p d hd] at h
  dsimp only [Pi.mul_apply] at h
  rw [← mul_sum,← mul_finsum,← mul_add,mul_div_assoc] at h
  unfold profileScale
  linarith only [h]

omit [IsGalois ℚ K] in
lemma exists_normalizing_edge (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hs : ∑ e, p e = 1) (d : E → K) {S : ℝ}
    (hS : (∑ e, ∑ f, p e*p f*exactHeight K (d e/d f)) ≤ S) :
    ∃ f, (∑ e, p e*exactHeight K (d e/d f)) ≤ S := by
  classical
  have hne : Nonempty E := by
    by_contra h
    have : IsEmpty E := not_nonempty_iff.mp h
    simp at hs
  obtain ⟨f,_,hf⟩ := exists_min_image univ (fun f => ∑ e, p e*exactHeight K (d e/d f))
    univ_nonempty
  refine ⟨f,le_trans ?_ hS⟩
  calc
    _ = ∑ j, p j * (∑ e, p e*exactHeight K (d e/d f)) := by rw [← sum_mul,hs,one_mul]
    _ ≤ ∑ j, p j * (∑ e, p e*exactHeight K (d e/d j)) :=
      sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hf j (mem_univ _)) (hp j)
    _ = _ := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro e _
      apply sum_congr rfl
      intro j _
      ring

end
end PlanarUnitDistances.WeightedAbsoluteValues

namespace PlanarUnitDistances.LevelScale
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels
open scoped Classical NNReal
noncomputable section
variable {K E : Type*} [Field K] [NumberField K] [Fintype E]

def weight (K : Type*) [Field K] [NumberField K] : ℝ≥0 :=
  ⟨(Module.finrank ℚ K : ℝ)⁻¹,inv_nonneg.mpr (Nat.cast_nonneg _)⟩
def measure (S : Finset K) : Measure (Place K S × ℝ) :=
  FiniteLevels.measure (weight K) (fun v => -radius K S v) (radius K S)
instance (S : Finset K) : IsFiniteMeasure (measure S) := by unfold measure; infer_instance

def cut (S : Finset K) (d : E → K) (v : Place K S) (e : E) := -log (av K v (d e))
def prob (μ : Law E) (S : Finset K) (d : E → K) (a : Place K S × ℝ) : ℝ :=
  ThresholdProfiles.frequency μ.val (cut S d a.1) a.2
def minority (μ : Law E) (S : Finset K) (d : E → K) (a : Place K S × ℝ) : ℝ :=
  min (prob μ S d a) (1-prob μ S d a)
def scale (μ : Law E) (S : Finset K) (d : E → K) : ℝ :=
  ∫a,minority μ S d a ∂measure S

lemma prob_bounds (μ : Law E) (S : Finset K) (d : E → K) (a : Place K S × ℝ) :
    0 ≤ prob μ S d a ∧ prob μ S d a ≤ 1 :=
  ⟨ThresholdProfiles.frequency_nonneg _ μ.nonneg _ _,
   ThresholdProfiles.frequency_le_one _ μ.nonneg μ.total _ _⟩
lemma prob_measurable (μ : Law E) (S : Finset K) (d : E → K) : Measurable (prob μ S d) := by
  exact FiniteLevels.measurable_pieces (fun v => ThresholdProfiles.frequency μ.val (cut S d v))
    (fun v => ThresholdProfiles.frequency_measurable _ _)
lemma minority_measurable (μ : Law E) (S : Finset K) (d : E → K) : Measurable (minority μ S d) :=
  (prob_measurable μ S d).min (measurable_const.sub (prob_measurable μ S d))
lemma minority_bounds (μ : Law E) (S : Finset K) (d : E → K) (a : Place K S × ℝ) :
    0 ≤ minority μ S d a ∧ minority μ S d a ≤ 1 := by
  have h := prob_bounds μ S d a
  unfold minority
  exact ⟨le_min h.1 (sub_nonneg.mpr h.2),(min_le_left _ _).trans h.2⟩
lemma scale_nonneg (μ : Law E) (S : Finset K) (d : E → K) : 0 ≤ scale μ S d :=
  integral_nonneg (fun a => (minority_bounds μ S d a).1)
lemma scale_eq (μ : Law E) (S : Finset K) (d : E → K) :
    scale μ S d = (Module.finrank ℚ K : ℝ)⁻¹ *
      ∑v : Place K S,∫s in Icc (-radius K S v) (radius K S v),
        ThresholdProfiles.minority μ.val (cut S d v) s := by
  exact FiniteLevels.integral_eq (weight K) _ _ _ (minority_measurable μ S d) 1
    (fun a => by rw [abs_of_nonneg (minority_bounds μ S d a).1]; exact (minority_bounds μ S d a).2)

omit [Fintype E] in
lemma pair_distance [IsGalois ℚ K] (S : Finset K) (d : E → K) (hd : ∀e,d e≠0)
    (hm : ∀e,d e∈S) (e f : E) :
    (∑v : Place K S,|cut S d v e-cut S d v f|)/(Module.finrank ℚ K : ℝ) =
      2*WeightedAbsoluteValues.exactHeight K (d e/d f) := by
  have hf : (∑v : ↥(finiteSupport K S),
      |cut S d (.inr v) e-cut S d (.inr v) f|) =
      ∑ᶠv : Nat.Primes × Gal(K/ℚ),
        |WeightedAbsoluteValues.finiteThreshold K d v e-WeightedAbsoluteValues.finiteThreshold K d v f| := by
    change (∑v : ↥(finiteSupport K S),
      |WeightedAbsoluteValues.finiteThreshold K d v.val e-WeightedAbsoluteValues.finiteThreshold K d v.val f|)=_
    rw [Finset.sum_coe_sort (finiteSupport K S) (fun v =>
      |WeightedAbsoluteValues.finiteThreshold K d v e-WeightedAbsoluteValues.finiteThreshold K d v f|)]
    symm
    apply finsum_eq_sum_of_support_subset
    intro v hv
    by_contra hn
    apply hv
    simp only [WeightedAbsoluteValues.finiteThreshold,log_off_support K (hm e) hn,
      log_off_support K (hm f) hn,neg_zero,sub_self,abs_zero]
  rw [Fintype.sum_sum_type,hf]
  exact WeightedAbsoluteValues.profile_pair_height K d hd e f

theorem expected_height_le_scale [IsGalois ℚ K] (μ : Law E) (S : Finset K) (d : E → K)
    (hd : ∀e,d e≠0) (hm : ∀e,d e∈S) :
    avg (pair μ μ) (fun ef => WeightedAbsoluteValues.exactHeight K (d ef.1/d ef.2)) ≤
      scale μ S d := by
  have he (v : Place K S) := ThresholdProfiles.expected_distance_le μ.val (cut S d v)
    μ.nonneg μ.total (fun e => (threshold_in_range K (hm e) v).1)
      (fun e => (threshold_in_range K (hm e) v).2)
  have h := sum_le_sum (s:=univ) (fun v _ => he v)
  have hi : 0≤ (Module.finrank ℚ K : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have h := mul_le_mul_of_nonneg_left h hi
  have hp : (Module.finrank ℚ K : ℝ)⁻¹ *
      (∑v : Place K S,∑e,∑f,μ.val e*μ.val f*|cut S d v e-cut S d v f|) =
      2*avg (pair μ μ) (fun ef => WeightedAbsoluteValues.exactHeight K (d ef.1/d ef.2)) := by
    have hs : (∑v : Place K S,∑e,∑f,μ.val e*μ.val f*|cut S d v e-cut S d v f|) =
        ∑e,∑f,μ.val e*μ.val f*∑v : Place K S,|cut S d v e-cut S d v f| := by
      rw [sum_comm]
      apply sum_congr rfl
      intro e _
      rw [sum_comm]
      simp only [mul_sum]
    rw [hs,pair_avg]
    unfold avg
    simp_rw [mul_sum,← mul_assoc]
    apply sum_congr rfl
    intro e _
    apply sum_congr rfl
    intro f _
    have ht := pair_distance S d hd hm e f
    rw [div_eq_mul_inv] at ht
    calc
      _ = μ.val e*μ.val f*((∑v : Place K S,|cut S d v e-cut S d v f|)*(Module.finrank ℚ K:ℝ)⁻¹) := by simp only [sum_mul,mul_sum]; apply sum_congr rfl; intro v _; ring
      _ = _ := by rw [ht]; ring
  rw [hp,← mul_sum] at h
  rw [scale_eq]
  nlinarith only [h]

lemma exists_normalizing_edge [IsGalois ℚ K] (μ : Law E) (S : Finset K) (d : E → K)
    (hd : ∀e,d e≠0) (hm : ∀e,d e∈S) :
    ∃f,avg μ (fun e => WeightedAbsoluteValues.exactHeight K (d e/d f))≤ scale μ S d := by
  apply WeightedAbsoluteValues.exists_normalizing_edge K μ.val μ.nonneg μ.total d
  have h := expected_height_le_scale μ S d hd hm
  rw [pair_avg] at h
  unfold avg at h
  simp_rw [mul_sum,← mul_assoc] at h
  exact h
end
end PlanarUnitDistances.LevelScale

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X : Type*} [Fintype X]

def support (μ : Law X) : Law {x : X // 0<μ.val x} where
  val := fun x => μ.val x.val
  nonneg := fun x => μ.nonneg x.val
  total := by
    rw [←sum_subtype (univ.filter (fun x => 0<μ.val x)) (fun x => by simp)]
    rw [sum_filter]
    convert μ.total using 1
    apply sum_congr rfl
    intro x _
    split_ifs with hx
    · rfl
    · exact (le_antisymm (le_of_not_gt hx) (μ.nonneg x)).symm

lemma support_avg (μ : Law X) (f : X → ℝ) : avg (support μ) (fun x => f x.val)=avg μ f := by
  change (∑x : {x : X // 0<μ.val x},μ.val x.val*f x.val) = ∑x,μ.val x*f x
  rw [←sum_subtype (univ.filter (fun x => 0<μ.val x)) (fun x => by simp) (fun x => μ.val x*f x),sum_filter]
  apply sum_congr rfl
  intro x _
  split_ifs with hx
  · rfl
  · rw [le_antisymm (le_of_not_gt hx) (μ.nonneg x),zero_mul]
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.LevelScale
open FiniteLaw MeasureTheory PlaceLevels
open scoped Classical
noncomputable section
variable {K E : Type*} [Field K] [NumberField K] [Fintype E]

lemma scale_support (μ : Law E) (S : Finset K) (d : E → K) :
    scale (support μ) S (fun e => d e.val)=scale μ S d := by
  unfold scale
  apply integral_congr_ae
  filter_upwards [] with a
  have hf : prob (support μ) S (fun e => d e.val) a=prob μ S d a :=
    support_avg μ (fun e => ThresholdProfiles.bit (cut S d a.1 e) a.2)
  simp only [minority,hf]

theorem exists_normalizing_edge_support [IsGalois ℚ K] (μ : Law E) (S : Finset K) (d : E → K)
    (hd : ∀e,0<μ.val e → d e≠0) (hm : ∀e,0<μ.val e → d e∈S) :
    ∃f,0<μ.val f ∧ avg μ (fun e => WeightedAbsoluteValues.exactHeight K (d e/d f))≤ scale μ S d := by
  obtain ⟨f,hf⟩ := exists_normalizing_edge (support μ) S (fun e => d e.val)
    (fun e => hd e.val e.property) (fun e => hm e.val e.property)
  rw [support_avg μ (fun e => WeightedAbsoluteValues.exactHeight K (d e/d f.val)),scale_support] at hf
  exact ⟨f.val,f.property,hf⟩

lemma expected_height_le_scale_support [IsGalois ℚ K] (μ : Law E) (S : Finset K) (d : E → K)
    (hd : ∀e,0<μ.val e → d e≠0) (hm : ∀e,0<μ.val e → d e∈S) :
    avg (pair μ μ) (fun ef => WeightedAbsoluteValues.exactHeight K (d ef.1/d ef.2))≤ scale μ S d := by
  have hh:=expected_height_le_scale (support μ) S (fun e => d e.val)
    (fun e => hd e.val e.property) (fun e => hm e.val e.property)
  rw [scale_support] at hh
  have he : avg (pair (support μ) (support μ))
      (fun ef => WeightedAbsoluteValues.exactHeight K (d ef.1.val/d ef.2.val))=
      avg (pair μ μ) (fun ef => WeightedAbsoluteValues.exactHeight K (d ef.1/d ef.2)) := by
    rw [pair_avg,pair_avg]
    calc
      _ = avg (support μ) (fun e => avg μ (fun f => WeightedAbsoluteValues.exactHeight K (d e.val/d f))) :=
        avg_congr (support μ) (fun e => support_avg μ (fun f => WeightedAbsoluteValues.exactHeight K (d e.val/d f)))
      _ = _ := support_avg μ (fun e => avg μ (fun f => WeightedAbsoluteValues.exactHeight K (d e/d f)))
  rwa [he] at hh
end
end PlanarUnitDistances.LevelScale

namespace PlanarUnitDistances.NormalizedScale
open FiniteLaw FiniteStarCoupling WeightedAbsoluteValues
open scoped Classical
noncomputable section
variable {P Q : Type} [Fintype P] [Fintype Q]
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

lemma avg_congr_support {X : Type*} [Fintype X] (μ : Law X) {f g : X → ℝ}
    (h : ∀x,0<μ.val x → f x=g x) : avg μ f=avg μ g := by
  unfold avg
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : 0<μ.val x
  · rw [h x hx]
  · rw [le_antisymm (le_of_not_gt hx) (μ.nonneg x),zero_mul,zero_mul]

theorem coordinates (π : Law (P×Q)) (z w : P⊕Q → K) (E : P → Q → Prop)
    (hE : ∀p q,0<π.val (p,q) → E p q)
    (hu : ∀p q,E p q → (z (.inl p)-z (.inr q))*(w (.inl p)-w (.inr q))=1)
    (hzi : Function.Injective (z ∘ Sum.inl)) (hzq : Function.Injective (z ∘ Sum.inr))
    (S : Finset K) (hS : ∀p q,E p q → z (.inl p)-z (.inr q)∈S)
    {C R : ℝ} (hc : LocalHeightTransfer.LabelControl C (fun p q => π.val (p,q)))
    (hR : LevelScale.scale π S (fun pq => z (.inl pq.1)-z (.inr pq.2)) ≤ R) :
    ∃(Z W : P → K) (a b : Q → K),
      (∀p q,E p q → (Z p-a q)*(W p-b q)=1) ∧
      Function.Injective Z ∧ Function.Injective a ∧
      let A := 4*((C+1)*(Real.log 2+2))*(R+1)+4*R+2*Real.log 2
      avg (left π) (fun p => exactHeight K (Z p)) ≤ A ∧
      avg (left π) (fun p => exactHeight K (W p)) ≤ A ∧
      avg (right π) (fun q => exactHeight K (a q)) ≤ A ∧
      avg (right π) (fun q => exactHeight K (b q)) ≤ A ∧
      avg π (fun pq => exactHeight K (Z pq.1-a pq.2)) ≤ A := by
  let d : P×Q → K := fun pq => z (.inl pq.1)-z (.inr pq.2)
  have hn : ∀pq,0<π.val pq → d pq≠0 := by
    intro pq hp hz
    have hh := hu pq.1 pq.2 (hE pq.1 pq.2 hp)
    change d pq*(w (.inl pq.1)-w (.inr pq.2))=1 at hh
    rw [hz,zero_mul] at hh
    exact zero_ne_one hh
  obtain ⟨e,he,havg⟩ := LevelScale.exists_normalizing_edge_support π S d hn
    (fun pq hp => hS pq.1 pq.2 (hE pq.1 pq.2 hp))
  have hθ := hn e he
  let z₀ : P⊕Q → K := fun v => z v/d e
  let w₀ : P⊕Q → K := fun v => w v*d e
  have huz : ∀p q,E p q → (z₀ (.inl p)-z₀ (.inr q))*(w₀ (.inl p)-w₀ (.inr q))=1 := by
    intro p q hp
    dsimp only [z₀,w₀]
    rw [←sub_div,←sub_mul]
    field_simp
    exact hu p q hp
  have hZ : avg π (fun pq => exactHeight K (z₀ (.inl pq.1)-z₀ (.inr pq.2))) ≤ R := by
    simpa only [z₀,←sub_div,d] using havg.trans hR
  have hW : avg π (fun pq => exactHeight K (w₀ (.inl pq.1)-w₀ (.inr pq.2))) ≤ R := by
    have hh : avg π (fun pq => exactHeight K (w₀ (.inl pq.1)-w₀ (.inr pq.2)))=
        avg π (fun pq => exactHeight K (z₀ (.inl pq.1)-z₀ (.inr pq.2))) := by
      apply avg_congr_support
      intro pq hp
      have hh := huz pq.1 pq.2 (hE pq.1 pq.2 hp)
      have heq := eq_inv_of_mul_eq_one_left hh
      rw [heq,exactHeight_inv]
    rwa [hh]
  obtain ⟨p₀,hp₀⟩ := NormalizedCoordinates.translate K π hc z₀ w₀ hZ hW
  let Z : P → K := fun p => z₀ (.inl p)-z₀ (.inl p₀)
  let W : P → K := fun p => w₀ (.inl p)-w₀ (.inl p₀)
  let a : Q → K := fun q => z₀ (.inr q)-z₀ (.inl p₀)
  let b : Q → K := fun q => w₀ (.inr q)-w₀ (.inl p₀)
  have heq (p : P) (q : Q) : Z p-a q=z₀ (.inl p)-z₀ (.inr q) := by dsimp [Z,a]; ring
  have hfq (p : P) (q : Q) : W p-b q=w₀ (.inl p)-w₀ (.inr q) := by dsimp [W,b]; ring
  refine ⟨Z,W,a,b,fun p q hp => by rw [heq,hfq]; exact huz p q hp,?_,?_,?_⟩
  · intro p r hpr
    apply hzi
    have hh : z (.inl p)/d e=z (.inl r)/d e := sub_left_inj.mp hpr
    exact (div_left_inj' hθ).mp hh
  · intro p r hpr
    apply hzq
    have hh : z (.inr p)/d e=z (.inr r)/d e := sub_left_inj.mp hpr
    exact (div_left_inj' hθ).mp hh
  · simp only [avg_add] at hp₀
    change avg (left π) (fun p => exactHeight K (Z p))+avg (left π) (fun p => exactHeight K (W p))+
      (avg (right π) (fun q => exactHeight K (a q))+avg (right π) (fun q => exactHeight K (b q)))+
      (avg π (fun pq => exactHeight K (z₀ (.inl pq.1)-z₀ (.inr pq.2)))+
        avg π (fun pq => exactHeight K (w₀ (.inl pq.1)-w₀ (.inr pq.2)))) ≤ _ at hp₀
    have hz := avg_nonneg (left π) (fun p => exactHeight_nonneg K (Z p))
    have hw := avg_nonneg (left π) (fun p => exactHeight_nonneg K (W p))
    have ha := avg_nonneg (right π) (fun q => exactHeight_nonneg K (a q))
    have hb := avg_nonneg (right π) (fun q => exactHeight_nonneg K (b q))
    have hd := avg_nonneg π (fun pq => exactHeight_nonneg K (z₀ (.inl pq.1)-z₀ (.inr pq.2)))
    have he := avg_nonneg π (fun pq => exactHeight_nonneg K (w₀ (.inl pq.1)-w₀ (.inr pq.2)))
    dsimp only
    simp_rw [heq]
    refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith
end
end PlanarUnitDistances.NormalizedScale

end OAI
