import OAI.Analysis.AncientFlat.Evolution.SourceInitialDerivative
import OAI.Analysis.AncientFlat.Evolution.SimilarityCovariance

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology
namespace ParametrixEvolution
open ParametrixVolterra FrozenParametrix StrongWeightedVolterra ParametrixDilation
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {α β : ℝ}
lemma exists_source_evolves (hα : 0<α) (L B : ℝ) (hL : 0≤L) (hB : 0≤B)
    (A : C(ℝ,V →ᵇ Icc α β)) (b : C(ℝ,V →ᵇ ℂ))
    (R : ℝ) (hR0 : 0≤R) (hR : R≤1)
    (hb : ∀ s ∈ Icc 0 R, ‖b s‖≤B)
    (hLip : ∀ s ∈ Icc 0 R, ∀ r ∈ Icc 0 R, ∀ x z : V,
      |(A s x).val-(A r z).val|≤L*(‖x-z‖+|s-r|))
    (hLipb : ∀ s ∈ Icc 0 R, ∀ x z : V, ‖b s x-b s z‖≤L*‖x-z‖)
    (hA : ∀ s ∈ Icc 0 R, ContDiff ℝ ∞ (fun x => (A s x).val))
    (γ : ℝ) (hγ : 0<γ) (hγ1 : γ≤1) (f : ℝ →ᵇ C₀(V,ℂ))
    (hf : ∃ H : ℝ, 0≤H ∧ ∀ t ∈ Icc 0 R, ∀ x y, ‖f t x-f t y‖≤H*‖x-y‖^γ)
    (d : C₀(V,ℂ)) : ∃ u : ℝ → C₀(V,ℂ), SourceEvolves A b f 0 R d u := by
  let incl : C(Slab R,ℝ) := ⟨Subtype.val,continuous_subtype_val⟩
  let l : Time R →ᵇ C₀(V,ℂ) := f.compContinuous ⟨Subtype.val,continuous_subtype_val⟩
  obtain ⟨K,hK,hs⟩ := exists_classical_source_evolution hα (A.comp incl) (b.comp incl)
    hR0 hR L B hL hB (fun r => hb r.val r.property)
    (fun s r x z => hLip s.val s.property r.val r.property x z)
    (fun s x z => hLipb s.val s.property x z) (fun s => hA s.val s.property)
  obtain ⟨H,hH,hf⟩ := hf
  obtain ⟨u,hu0,huc,_,huJ,huB,hut⟩ := hs γ hγ hγ1 d l
    ⟨H,hH,fun t x y => hf t.val ⟨t.property.1.le,t.property.2⟩ x y⟩
  refine ⟨u,hu0,huc,huJ,huB,fun t ht => ?_⟩
  exact hut ⟨t,ht.1,ht.2.le⟩ ht.2

variable {A : C(ℝ,V →ᵇ Icc α β)} {b : C(ℝ,V →ᵇ ℂ)}
  {d : C₀(V,ℂ)} {u f : ℝ → C₀(V,ℂ)}
omit [MeasurableSpace V] [BorelSpace V] in
lemma SourceEvolves.dilate_shift (hu : SourceEvolves A b f 0 1 d u)
    (Af : V → ℝ) (Bf : V → ℂ)
    (hmoveA : ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      (A t x).val=Real.exp (-t)/16*Af (Real.exp (t/4) • x))
    (hmoveb : ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      b t x=1/2+Bf (Real.exp (t/4) • x))
    {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    SourceEvolves A b (fun t => dil s (f (s+t))) 0 (1-s) (dil s (u s))
      (fun t => dil s (u (s+t))) := by
  let : NormedAddCommGroup C₀(V,ℂ) := inferInstance
  let : NormedSpace ℂ C₀(V,ℂ) := inferInstance
  let : NormedAddCommGroup (V →ᵇ ℂ) := inferInstance
  let : NormedSpace ℝ (V →ᵇ ℂ) := inferInstance
  have hst (t : ℝ) (ht : t ∈ Ioo (0:ℝ) (1-s)) : s+t ∈ Ioo (0:ℝ) 1 :=
    ⟨by linarith [hs.1,ht.1],by linarith [ht.2]⟩
  refine ⟨by simp,?_,?_,?_,?_⟩
  · apply (dil s).continuous.comp_continuousOn
    apply hu.2.1.comp (continuous_const.add continuous_id).continuousOn
    intro t ht
    change s+t ∈ Icc (0:ℝ) 1
    exact ⟨by linarith [hs.1,ht.1],by linarith [ht.2]⟩
  · intro t ht
    exact (hu.2.2.1 _ (hst t ht)).comp (contDiff_const.smul contDiff_id)
  · intro t ht
    exact bounded_jets_scale _ _ (hu.2.2.1 _ (hst t ht)) (hu.2.2.2.1 _ (hst t ht))
  · intro t ht
    obtain ⟨p,hp,hpe⟩ := hu.2.2.2.2 _ (hst t ht)
    let Q : (V →ᵇ ℂ) →L[ℝ] (V →ᵇ ℂ) := BoundedContinuousFunction.compContinuousCLM ℂ ℝ (dilMap s)
    have ht' : HasDerivAt (fun r => (u (s+r)).toBCF) p t := by
      have ha : HasDerivAt (fun r : ℝ => s+r) 1 t := (hasDerivAt_id t).const_add s
      convert hp.scomp t ha using 1 <;> first | rfl | simp only [one_smul]
    refine ⟨Q p,?_,?_⟩
    · convert Q.hasFDerivAt.comp_hasDerivAt t ht' using 1
      rfl
    · intro x
      change p (Real.exp (-s/4) • x)=_
      rw [hpe]
      have hc := moving_covariance Af Bf hmoveA hmoveb hs.1 ht.1.le (by linarith [ht.2]) x
      rw [hc.1,hc.2]
      change _=f (s+t) (Real.exp (-s/4) • x)-((A t x).val : ℂ)*
        Δ (Δ (fun y => u (s+t) (Real.exp (-s/4) • y))) x-
        b t x*u (s+t) (Real.exp (-s/4) • x)
      rw [bilaplacian_scale _ _ (hu.2.2.1 _ (hst t ht)),exp_quarter_four]
      simp only [Complex.ofReal_mul,Complex.real_smul]
      ring
end ParametrixEvolution

end

end OAI
