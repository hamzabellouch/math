import OAI.Analysis.AncientFlat.Evolution.StrongClassicalEvolution
import OAI.Analysis.AncientFlat.Evolution.EvolutionUniqueness

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParametrixEvolution
open ParametrixVolterra FrozenParametrix StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma exists_uniform_evolves (T α β L B : ℝ) (_hT : 0<T) (hT1 : T≤1)
    (hα : 0<α) (hL : 0≤L) (hB : 0≤B)
    (A : C(ℝ,V →ᵇ Icc α β)) (b : C(ℝ,V →ᵇ ℂ))
    (hb : ∀ s ∈ Icc 0 T, ‖b s‖≤B)
    (hLip : ∀ s ∈ Icc 0 T, ∀ r ∈ Icc 0 T, ∀ x z : V,
      |(A s x).val-(A r z).val|≤L*(‖x-z‖+|s-r|))
    (hLipb : ∀ s ∈ Icc 0 T, ∀ x z : V, ‖b s x-b s z‖≤L*‖x-z‖)
    (hA : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (fun x => (A s x).val)) :
    ∃ K : ℝ, 0≤K ∧ ∀ s ∈ Icc 0 T, ∀ d : C₀(V,ℂ),
      ∃ u : ℝ → C₀(V,ℂ), Evolves A b s T d u ∧ ∀ t ∈ Icc s T, ‖u t‖≤K*‖d‖ := by
  let : NormedAddCommGroup (V →ᵇ ℂ) := inferInstance
  let : NormedSpace ℝ (V →ᵇ ℂ) := inferInstance
  obtain ⟨K,hK,he⟩ := exists_uniform_strong_classical_evolution (V := V) (β := β) hα L B hL hB
  refine ⟨K,hK,fun s hs d => ?_⟩
  let shift : C(Slab (T-s),ℝ) := ⟨fun r => s+r.val,continuous_const.add continuous_subtype_val⟩
  have hshift (r : Slab (T-s)) : shift r ∈ Icc 0 T := by
    change 0 ≤ s+r.val ∧ s+r.val ≤ T
    exact ⟨by linarith [r.property.1,hs.1],by linarith [r.property.2]⟩
  have hLip' : ∀ r q : Slab (T-s), ∀ x z : V,
      |((A.comp shift) r x).val-((A.comp shift) q z).val|≤L*(‖x-z‖+|r.val-q.val|) := by
    intro r q x z
    have hh := hLip _ (hshift r) _ (hshift q) x z
    simpa only [ContinuousMap.comp_apply,shift,ContinuousMap.coe_mk,add_sub_add_left_eq_sub] using hh
  obtain ⟨w,hw0,hwc,hwb,hws,hwj,hwt⟩ := he (T-s) (sub_nonneg.mpr hs.2)
    (by linarith [hs.1]) (A.comp shift) (b.comp shift)
    (fun r => hb _ (hshift r)) hLip' (fun r => hLipb _ (hshift r))
    (fun r => hA _ (hshift r)) d
  let u : ℝ → C₀(V,ℂ) := fun t => w (t-s)
  have htshift (t : ℝ) (ht : t ∈ Icc s T) : t-s ∈ Icc 0 (T-s) :=
    ⟨sub_nonneg.mpr ht.1,sub_le_sub_right ht.2 s⟩
  refine ⟨u,⟨?_,?_,?_,?_,?_⟩,fun t ht => hwb _ (htshift t ht)⟩
  · simpa only [u,sub_self] using hw0
  · exact hwc.comp (continuous_id.sub continuous_const).continuousOn htshift
  · intro t ht
    exact hws _ ⟨sub_pos.mpr ht.1,sub_lt_sub_right ht.2 s⟩
  · intro t ht n hn
    exact hwj _ ⟨sub_pos.mpr ht.1,sub_lt_sub_right ht.2 s⟩ n hn
  · intro t ht
    let q : Time (T-s) := ⟨t-s,sub_pos.mpr ht.1,sub_le_sub_right ht.2.le s⟩
    obtain ⟨v,hv,hve⟩ := hwt q (sub_lt_sub_right ht.2 s)
    refine ⟨v,?_,fun x => ?_⟩
    · have ha : HasDerivAt (fun r : ℝ => r-s) 1 t := (hasDerivAt_id t).sub_const s
      convert hv.scomp t ha using 1 <;> first | rfl | simp only [one_smul]
    · have heq : s+(t-s)=t := by ring
      simpa only [ContinuousMap.comp_apply,shift,ContinuousMap.coe_mk,now,q,heq,u] using hve x
end ParametrixEvolution

end

end OAI
