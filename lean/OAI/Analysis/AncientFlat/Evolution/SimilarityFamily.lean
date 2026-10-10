import OAI.Analysis.AncientFlat.Evolution.SimilarityCovariance
import OAI.Analysis.AncientFlat.Evolution.DilationContinuity

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
open ParametrixDilation
namespace ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem exists_local_similarity_family (α β C L B : ℝ)
    (hα : 0<α) (hC : 0≤C) (hL : 0≤L) (hB : 0≤B)
    (A : C(ℝ,V →ᵇ Icc α β)) (b : C(ℝ,V →ᵇ ℂ))
    (Af : V → ℝ) (Bf : V → ℂ)
    (hmoveA : ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      (A t x).val=Real.exp (-t)/16*Af (Real.exp (t/4) • x))
    (hmoveb : ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      b t x=1/2+Bf (Real.exp (t/4) • x))
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ‖b t‖≤B)
    (hLip : ∀ t ∈ Icc (0:ℝ) 1, ∀ r ∈ Icc (0:ℝ) 1, ∀ x z : V,
      |(A t x).val-(A r z).val|≤L*(‖x-z‖+|t-r|))
    (hLipb : ∀ t ∈ Icc (0:ℝ) 1, ∀ x z : V, ‖b t x-b t z‖≤L*‖x-z‖)
    (hA : ∀ t ∈ Icc (0:ℝ) 1, ContDiff ℝ ∞ (fun x => (A t x).val))
    (hAj : ∀ t ∈ Icc (0:ℝ) 1, ∀ n : ℕ, n≤2 → ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => (A t y).val) x‖≤C) :
    ∃ K : ℝ, 0≤K ∧ ∃ S : ℝ → (C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)),
      S 0=ContinuousLinearMap.id ℂ C₀(V,ℂ) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ‖S t‖≤K) ∧
      (∀ d : C₀(V,ℂ), ContinuousOn (fun t => S t d) (Icc (0:ℝ) 1)) ∧
      (∀ d : C₀(V,ℂ), ∃ u : ℝ → C₀(V,ℂ), Evolves A b 0 1 d u ∧
        ∀ t ∈ Icc (0:ℝ) 1, ∀ x, S t d x=u t (Real.exp (-t/4) • x)) ∧
      (∀ s t : ℝ, 0 ≤ s → 0≤t → s+t≤1 → S (s+t)=(S t).comp (S s)) := by
  classical
  let : NormedAddCommGroup C₀(V,ℂ) := inferInstance
  let : NormedSpace ℂ C₀(V,ℂ) := inferInstance
  obtain ⟨K,hK,E,hE0,hEn,hEv,hEc⟩ := exists_evolution_family (V := V) 1 α β C L B
    zero_lt_one le_rfl hα hC hL hB A b hb hLip hLipb hA hAj
  let S : ℝ → (C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)) := fun t => (dil t).comp (E t 0)
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl,zero_le_one⟩
  refine ⟨K,hK,S,?_,?_,?_,?_,?_⟩
  · change (dil 0).comp (E 0 0)=_
    rw [dil_zero,hE0 0 h0]
    rfl
  · intro t ht
    calc
      ‖S t‖≤‖dil (V := V) t‖*‖E t 0‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _≤1*K := mul_le_mul (opNorm_dil_le t) (hEn 0 h0 t ht) (norm_nonneg _) zero_le_one
      _=K := one_mul _
  · intro d
    exact continuousOn_dil_apply (hEv 0 h0 d).2.1
  · intro d
    refine ⟨fun t => E t 0 d,hEv 0 h0 d,fun t ht x => rfl⟩
  · intro s t hs ht hst
    have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs,by linarith⟩
    have ht' : t ∈ Icc (0:ℝ) (1-s) := ⟨ht,by linarith⟩
    apply ContinuousLinearMap.ext
    intro d
    have hu := (hEv 0 h0 d).dilate_shift Af Bf hmoveA hmoveb hs'
    have hv := (hEv 0 h0 (S s d)).end_mono (by linarith : 1-s≤1)
    have hh := hv.unique hu (by linarith [hs'.2]) hα hC hB
      (fun r hr => hb r ⟨hr.1,by linarith [hr.2]⟩)
      (fun r hr => (hA r ⟨hr.1,by linarith [hr.2]⟩).of_le (by decide))
      (fun r hr => hAj r ⟨hr.1,by linarith [hr.2]⟩) t ht'
    change dil (s+t) (E (s+t) 0 d)=dil t (E t 0 (S s d))
    rw [hh]
    rw [add_comm s t,dil_add]
    rfl
end ParametrixEvolution

end

end OAI
