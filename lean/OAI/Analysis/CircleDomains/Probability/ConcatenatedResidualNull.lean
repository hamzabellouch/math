import OAI.Analysis.CircleDomains.Selection.ConcatenatedTags

namespace OAI

/-! Countably many junction times and null residual images in the open
pieces give a null residual image for the concatenated path. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {ι X : Type*} [Encodable ι] [MetricSpace X]

theorem residualImage_concatenated_subset (B : Set X)
    (γ : C(PathTime, X)) (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ioo (a i) (b i))))
    (Γ : ι → TaggedPath X)
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t) :
    residualImage B (concatenatedTaggedPath γ a b Γ) ⊆
      γ '' (⋃ i, Ioo (a i) (b i))ᶜ ∪ ⋃ i, residualImage B (Γ i) := by
  rintro x ⟨t, ht, rfl⟩
  by_cases hpiece : t ∈ ⋃ i, Ioo (a i) (b i)
  · right
    obtain ⟨i, hi⟩ := mem_iUnion.mp hpiece
    apply mem_iUnion.mpr
    refine ⟨i, rescalePathTime (a i) (b i) t, ?_, ?_⟩
    · exact (residualTimes_concatenated_piece B γ a b hab hdis Γ hmatch i hi).mp ht
    · have he := hmatch i _ (rescalePathTime_mem_Ioo (hab i) hi)
      rw [affine_rescalePathTime (hab i) ⟨hi.1.le, hi.2.le⟩] at he
      exact he.symm
  · exact Or.inl ⟨t, hpiece, rfl⟩

theorem residualImage_concatenated_null [MeasurableSpace X] [MeasurableSingletonClass X]
    (B : Set X) (ν : Measure X) [NullSingletonClass ν]
    (γ : C(PathTime, X)) (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ioo (a i) (b i))))
    (hcount : (⋃ i, Ioo (a i) (b i))ᶜ.Countable)
    (Γ : ι → TaggedPath X)
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t)
    (hnull : ∀ i, ν (residualImage B (Γ i)) = 0) :
    ν (residualImage B (concatenatedTaggedPath γ a b Γ)) = 0 :=
  measure_mono_null (residualImage_concatenated_subset B γ a b hab hdis Γ hmatch)
    (measure_union_null ((hcount.image γ).measure_zero ν) (measure_iUnion_null hnull))

end CircleDomainRigidity

end

end OAI
