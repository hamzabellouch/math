import OAI.Analysis.AncientFlat.Evolution.ShiftedEvolution

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace ParametrixEvolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {α β s T : ℝ} {A : C(ℝ,V →ᵇ Icc α β)} {b : C(ℝ,V →ᵇ ℂ)}
  {d : C₀(V,ℂ)} {u v : ℝ → C₀(V,ℂ)}
omit [MeasurableSpace V] [BorelSpace V] in
lemma Evolves.congr (hu : Evolves A b s T d u) (hsT : s≤T)
    (he : ∀ t ∈ Icc s T, v t=u t) : Evolves A b s T d v := by
  refine ⟨(he s ⟨le_rfl,hsT⟩).trans hu.1,hu.2.1.congr he,?_,?_,?_⟩
  · intro t ht
    rw [he t ⟨ht.1.le,ht.2.le⟩]
    exact hu.2.2.1 t ht
  · intro t ht n hn
    rw [he t ⟨ht.1.le,ht.2.le⟩]
    exact hu.2.2.2.1 t ht n hn
  · intro t ht
    obtain ⟨p,hp,hpe⟩ := hu.2.2.2.2 t ht
    refine ⟨p,hp.congr_of_eventuallyEq ?_,?_⟩
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
      rw [he r ⟨hr.1.le,hr.2.le⟩]
    · rw [he t ⟨ht.1.le,ht.2.le⟩]
      exact hpe

theorem exists_evolution_family (T α β C L B : ℝ) (hT : 0<T) (hT1 : T≤1)
    (hα : 0<α) (hC : 0≤C) (hL : 0≤L) (hB : 0≤B)
    (A : C(ℝ,V →ᵇ Icc α β)) (b : C(ℝ,V →ᵇ ℂ))
    (hb : ∀ s ∈ Icc 0 T, ‖b s‖≤B)
    (hLip : ∀ s ∈ Icc 0 T, ∀ r ∈ Icc 0 T, ∀ x z : V,
      |(A s x).val-(A r z).val|≤L*(‖x-z‖+|s-r|))
    (hLipb : ∀ s ∈ Icc 0 T, ∀ x z : V, ‖b s x-b s z‖≤L*‖x-z‖)
    (hA : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (fun x => (A s x).val))
    (hAj : ∀ s ∈ Icc 0 T, ∀ n : ℕ, n≤2 → ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => (A s y).val) x‖≤C) :
    ∃ K : ℝ, 0≤K ∧ ∃ E : ℝ → ℝ → (C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)),
      (∀ s ∈ Icc 0 T, E s s=ContinuousLinearMap.id ℂ C₀(V,ℂ)) ∧
      (∀ s ∈ Icc 0 T, ∀ t ∈ Icc s T, ‖E t s‖≤K) ∧
      (∀ s ∈ Icc 0 T, ∀ d : C₀(V,ℂ), Evolves A b s T d (fun t => E t s d)) ∧
      (∀ s ∈ Icc 0 T, ∀ r ∈ Icc s T, ∀ t ∈ Icc r T,
        (E t r).comp (E r s)=E t s) := by
  classical
  obtain ⟨K,hK,hex⟩ := exists_uniform_evolves T α β L B hT hT1 hα hL hB A b hb hLip hLipb hA
  choose u hu hn using hex
  have huc (s : ℝ) (hs : s ∈ Icc 0 T) {d : C₀(V,ℂ)} {u v : ℝ → C₀(V,ℂ)}
      (hu : Evolves A b s T d u) (hv : Evolves A b s T d v) :
      ∀ t ∈ Icc s T, u t=v t :=
    hu.unique hv hs.2 hα hC hB
      (fun t ht => hb t ⟨hs.1.trans ht.1,ht.2⟩)
      (fun t ht => (hA t ⟨hs.1.trans ht.1,ht.2⟩).of_le (by decide))
      (fun t ht => hAj t ⟨hs.1.trans ht.1,ht.2⟩)
  let F (s : ℝ) (hs : s ∈ Icc 0 T) (t : ℝ) (ht : t ∈ Icc s T) : C₀(V,ℂ) →ₗ[ℂ] C₀(V,ℂ) :=
    { toFun := fun d => u s hs d t
      map_add' := fun d e => huc s hs (hu s hs (d+e)) ((hu s hs d).add (hu s hs e)) t ht
      map_smul' := fun c d => huc s hs (hu s hs (c•d)) ((hu s hs d).smul c) t ht }
  let G (s : ℝ) (hs : s ∈ Icc 0 T) (t : ℝ) (ht : t ∈ Icc s T) : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ) :=
    (F s hs t ht).mkContinuous K (fun d => hn s hs d t ht)
  let E : ℝ → ℝ → (C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)) := fun t s =>
    if hs : s ∈ Icc 0 T then if ht : t ∈ Icc s T then G s hs t ht else 0 else 0
  have hE (s : ℝ) (hs : s ∈ Icc 0 T) (t : ℝ) (ht : t ∈ Icc s T) (d : C₀(V,ℂ)) :
      E t s d=u s hs d t := by
    simp only [E,dite_eq_left hs,dite_eq_left ht,G,LinearMap.mkContinuous_apply,F]
    rfl
  have hsol (s : ℝ) (hs : s ∈ Icc 0 T) (d : C₀(V,ℂ)) : Evolves A b s T d (fun t => E t s d) :=
    (hu s hs d).congr hs.2 (fun t ht => hE s hs t ht d)
  refine ⟨K,hK,E,?_,?_,hsol,?_⟩
  · intro s hs
    apply ContinuousLinearMap.ext
    intro d
    exact (hE s hs s ⟨le_rfl,hs.2⟩ d).trans (hu s hs d).1
  · intro s hs t ht
    rw [show E t s=G s hs t ht by simp only [E,dite_eq_left hs,dite_eq_left ht]]
    exact LinearMap.mkContinuous_norm_le _ hK _
  · intro s hs r hr t ht
    have hr' : r ∈ Icc 0 T := ⟨hs.1.trans hr.1,hr.2⟩
    apply ContinuousLinearMap.ext
    intro d
    exact huc r hr' (hsol r hr' (E r s d)) ((hsol s hs d).restrict hr.1) t ht
end ParametrixEvolution

end

end OAI
