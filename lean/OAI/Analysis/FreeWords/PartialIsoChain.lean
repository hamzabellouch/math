import Mathlib
import OAI.Analysis.FreeWords.PartialIsoAlgebra
import OAI.Analysis.FreeWords.WeakCompact

namespace OAI

noncomputable section

open scoped ComplexConjugate InnerProductSpace BoundedContinuousFunction

namespace UniversalStrongKK

section OperatorMean

variable {G H : Type*} [TopologicalSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (m : ScalarMean G)

variable [CompleteSpace H]

end OperatorMean

end UniversalStrongKK

open scoped Topology

namespace UniversalStrongKK

section UltraMean

variable {I : Type*} [TopologicalSpace I]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end UltraMean

end UniversalStrongKK

namespace KKProjectionSupport

noncomputable section

variable {A : Type*} [CStarAlgebra A]

end

end KKProjectionSupport

namespace KKProjectionSupport

open Filter Topology

open UniversalStrongKK

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_bounded_wot_ultralimit {I : Type*} (ω : Ultrafilter I)
    (f : I → (H →L[ℂ] H)) (hf : ∀ i, ‖f i‖ ≤ 1) :
    ∃ V : H →L[ℂ] H, Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (f i))
      (ω : Filter I) (𝓝 (ContinuousLinearMapWOT.ofCLM V)) := by
  let : TopologicalSpace I := ⊥
  let : DiscreteTopology I := ⟨rfl⟩
  let F : I →ᵇ (H →L[ℂ] H) := BoundedContinuousFunction.ofNormedAddCommGroup f
    continuous_of_discreteTopology 1 hf
  exact ⟨operatorMean (ultrafilterMean ω) F, tendsto_operatorMean ω F⟩

omit [CompleteSpace H] in
theorem wot_mul_const {I : Type*} {l : Filter I} {f : I → (H →L[ℂ] H)}
    {V : H →L[ℂ] H} (h : Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (f i)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM V))) (a : H →L[ℂ] H) :
    Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (f i*a)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM (V*a))) := by
  simpa only [ContinuousLinearMapWOT.ofCLM_mul] using h.mul_const (ContinuousLinearMapWOT.ofCLM a)

omit [CompleteSpace H] in
theorem wot_const_mul {I : Type*} {l : Filter I} {f : I → (H →L[ℂ] H)}
    {V : H →L[ℂ] H} (h : Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (f i)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM V))) (a : H →L[ℂ] H) :
    Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (a*f i)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM (a*V))) := by
  simpa only [ContinuousLinearMapWOT.ofCLM_mul] using h.const_mul (ContinuousLinearMapWOT.ofCLM a)

omit [CompleteSpace H] in
theorem wot_limit_eq {I : Type*} {l : Filter I} [l.NeBot]
    {f : I → (H →L[ℂ] H)} {V W : H →L[ℂ] H}
    (h : Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (f i)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM V))) (he : ∀ᶠ i in l, f i = W) : V=W := by
  have h' : (fun i => ContinuousLinearMapWOT.ofCLM (f i)) =ᶠ[l]
      (fun _ => ContinuousLinearMapWOT.ofCLM W) := he.mono (fun i hi => congrArg _ hi)
  exact congrArg ContinuousLinearMapWOT.toCLM (tendsto_nhds_unique h (tendsto_const_nhds.congr' h'.symm))

theorem partialIso_directed_limit {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (f : I → PartialIso (H →L[ℂ] H)) (hf : Monotone f) :
    ∃ V : PartialIso (H →L[ℂ] H), (∀ i, f i ≤ V) ∧
      ∃ ω : Ultrafilter I, (ω : Filter I) ≤ atTop ∧
        Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (f i).value) (ω : Filter I)
          (𝓝 (ContinuousLinearMapWOT.ofCLM V.value)) := by
  let ω : Ultrafilter I := Ultrafilter.of atTop
  have hω : (ω : Filter I) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨V, hV⟩ := exists_bounded_wot_ultralimit ω (fun i => (f i).value)
    (fun i => partial_norm (f i).isPartial)
  let p (i : I) := star (f i).value*(f i).value
  obtain ⟨P, hP⟩ := exists_bounded_wot_ultralimit ω p
    (fun i => (partial_initial (f i).isPartial).norm_le)
  have hVi (i : I) : V*p i=(f i).value := by
    apply wot_limit_eq (wot_mul_const hV (p i))
    filter_upwards [(eventually_ge_atTop i).filter_mono hω] with j hij
    exact (hf hij).1
  have hiV (i : I) : star (f i).value*V=p i := by
    apply wot_limit_eq (wot_const_mul hV (star (f i).value))
    filter_upwards [(eventually_ge_atTop i).filter_mono hω] with j hij
    exact (hf hij).2
  have hsVi (i : I) : star V*(f i).value=p i := by
    simpa only [star_mul, star_star, p] using congrArg star (hiV i)
  have hVV : star V*V=P := by
    have ht := wot_const_mul hV (star V)
    have hh : (fun i => ContinuousLinearMapWOT.ofCLM (star V*(f i).value)) =
        (fun i => ContinuousLinearMapWOT.ofCLM (p i)) := funext (fun i => congrArg _ (hsVi i))
    rw [hh] at ht
    exact congrArg ContinuousLinearMapWOT.toCLM (tendsto_nhds_unique ht hP)
  have hVP : V*P=V := by
    have ht := wot_const_mul hP V
    have hh : (fun i => ContinuousLinearMapWOT.ofCLM (V*p i)) =
        (fun i => ContinuousLinearMapWOT.ofCLM (f i).value) := funext (fun i => congrArg _ (hVi i))
    rw [hh] at ht
    exact congrArg ContinuousLinearMapWOT.toCLM (tendsto_nhds_unique ht hV)
  refine ⟨⟨V, ?_⟩, (fun i => ⟨hVi i, hiV i⟩), ω, hω, hV⟩
  change V*star V*V=V
  rw [mul_assoc, hVV, hVP]

theorem exists_maximal_partialIso (M : VonNeumannAlgebra H) (p q : H →L[ℂ] H) :
    ∃ V : PartialIso (H →L[ℂ] H), Maximal
      (fun v : PartialIso (H →L[ℂ] H) => v.value ∈ M ∧ v.value*p=v.value ∧ q*v.value=v.value) V := by
  let S := {v : PartialIso (H →L[ℂ] H) | v.value ∈ M ∧ v.value*p=v.value ∧ q*v.value=v.value}
  let z : PartialIso (H →L[ℂ] H) := ⟨0, by simp [Partial]⟩
  have hz : z ∈ S := ⟨zero_mem M, by simp [z], by simp [z]⟩
  obtain ⟨V, hzV, hV⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    let : Nonempty c := ⟨⟨y, hy⟩⟩
    let : IsDirectedOrder c := ⟨fun a b => by
      obtain ⟨k, hk, hak, hbk⟩ := hchain.directedOn a.val a.property b.val b.property
      exact ⟨⟨k,hk⟩,hak,hbk⟩⟩
    obtain ⟨W, hW, ω, hω, hlim⟩ := partialIso_directed_limit (fun i : c => i.val)
      (fun _ _ hij => hij)
    refine ⟨W, ⟨mem_of_wot_tendsto M hlim (Eventually.of_forall fun i => (hc i.property).1), ?_, ?_⟩,
      fun j hj => hW ⟨j,hj⟩⟩
    · have he := wot_mul_const hlim p
      have hh : (fun i : c => ContinuousLinearMapWOT.ofCLM (i.val.value*p)) =
          (fun i : c => ContinuousLinearMapWOT.ofCLM i.val.value) := by
        funext i; rw [(hc i.property).2.1]
      rw [hh] at he
      exact congrArg ContinuousLinearMapWOT.toCLM (tendsto_nhds_unique he hlim)
    · have he := wot_const_mul hlim q
      have hh : (fun i : c => ContinuousLinearMapWOT.ofCLM (q*i.val.value)) =
          (fun i : c => ContinuousLinearMapWOT.ofCLM i.val.value) := by
        funext i; rw [(hc i.property).2.2]
      rw [hh] at he
      exact congrArg ContinuousLinearMapWOT.toCLM (tendsto_nhds_unique he hlim)) z hz
  exact ⟨V,hV⟩

end

end KKProjectionSupport
end

end OAI
