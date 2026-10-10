import OAI.Analysis.FreeEntropy.GUECovariance

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter
open scoped Classical Topology
namespace FiniteEntropySeparation
 theorem matrixTraceWord_cyclic {α : Type u1} {d : ℕ} (A : α → Matrix (Fin d) (Fin d) ℂ) (u v : List α) :
    matrixTraceWord A (u++v) = matrixTraceWord A (v++u) := by
  simp only [matrixTraceWord, matrixWord_append]
  rw [Matrix.trace_mul_comm]
 theorem matrixWord_map {α : Type u2} {β : Type u3} {d : ℕ} (A : β → Matrix (Fin d) (Fin d) ℂ) (f : α → β) (w : List α) :
    matrixWord A (w.map f) = matrixWord (A ∘ f) w := by simp [matrixWord,List.map_map]
 theorem matrixTraceWord_map {α : Type u4} {β : Type u5} {d : ℕ} (A : β → Matrix (Fin d) (Fin d) ℂ) (f : α → β) (w : List α) :
    matrixTraceWord A (w.map f) = matrixTraceWord (A ∘ f) w := by simp [matrixTraceWord,matrixWord_map]
 theorem sum_word_left_or_noise {α : Type u6} {β : Type u7} (w : List (α ⊕ β)) :
    (∃ u : List α, w=u.map Sum.inl) ∨ (∃ u i v, w=u++Sum.inr i::v) := by
  induction w with
  | nil => exact Or.inl ⟨[],rfl⟩
  | cons a w ih =>
    cases a with
    | inl a =>
      rcases ih with ⟨u,rfl⟩ | ⟨u,i,v,rfl⟩
      · exact Or.inl ⟨a::u,rfl⟩
      · exact Or.inr ⟨Sum.inl a::u,i,v,rfl⟩
    | inr i => exact Or.inr ⟨[],i,w,rfl⟩
 theorem tendsto_of_sub_zero {f g : ℕ → ℂ} {z : ℂ} (hfg : Tendsto (fun k => f k-g k) atTop (𝓝 0))
    (hg : Tendsto g atTop (𝓝 z)) : Tendsto f atTop (𝓝 z) := by
  simpa only [sub_add_cancel, zero_add] using hfg.add hg
 variable {α : Type u8} {n : ℕ} {D : ℕ → ℕ}
 def expectedMatrixWord (A : (k : ℕ) → α → Matrix (Fin (D k)) (Fin (D k)) ℂ) (k : ℕ) (w : List (α ⊕ Fin n)) : ℂ :=
   ∫ x, matrixTraceWord (jointMatrix (A k) x) w ∂productGaussian (MatrixIndex n (D k))
 theorem matrixTraceWord_covariance_tendsto (hD0 : ∀ k, 0 < D k) (hD : Tendsto D atTop atTop)
    (A : (k : ℕ) → α → Matrix (Fin (D k)) (Fin (D k)) ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hA : ∀ k a, matrixOpNorm (A k a) ≤ R) (u v : List (α ⊕ Fin n)) :
    Tendsto (fun k => (∫ x, matrixTraceWord (jointMatrix (A k) x) u*matrixTraceWord (jointMatrix (A k) x) v ∂productGaussian (MatrixIndex n (D k)))-
      expectedMatrixWord A k u*expectedMatrixWord A k v) atTop (𝓝 0) := by
  apply tendsto_zero_of_norm_bound_inv_sq hD (C := ((u.length:ℝ)^2*jointMomentBound n R (2*(u.length-1))+(v.length:ℝ)^2*jointMomentBound n R (2*(v.length-1)))/2)
  intro k
  convert matrixTraceWord_covariance_bound (hD0 k) (A k) hR (hA k) u v using 1
  · rfl
  · ring
 theorem expectedMatrixWord_tendsto (hD0 : ∀ k, 0 < D k) (hD : Tendsto D atTop atTop)
    (A : (k : ℕ) → α → Matrix (Fin (D k)) (Fin (D k)) ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hA : ∀ k a, matrixOpNorm (A k a) ≤ R) (M : List (α ⊕ Fin n) → ℂ)
    (hcyclic : ∀ u v, M (u++v)=M (v++u))
    (hbase : ∀ u : List α, Tendsto (fun k => matrixTraceWord (A k) u) atTop (𝓝 (M (u.map Sum.inl))))
    (hrec : ∀ (i : Fin n) (w : List (α ⊕ Fin n)), M (Sum.inr i::w) =
      ∑ r : Fin w.length, if w[r.val]=Sum.inr i then M (w.take r.val)*M (w.drop (r.val+1)) else 0)
    (w : List (α ⊕ Fin n)) : Tendsto (fun k => expectedMatrixWord A k w) atTop (𝓝 (M w)) := by
  induction w using (measure List.length).wf.induction with
  | h w ih =>
    rcases sum_word_left_or_noise w with ⟨u,rfl⟩ | ⟨u,i,v,rfl⟩
    · simpa [expectedMatrixWord,matrixTraceWord_map,jointMatrix,Function.comp_def] using hbase u
    · have hrecLimit : Tendsto (fun k => expectedMatrixWord A k (Sum.inr i::(v++u))) atTop (𝓝 (M (Sum.inr i::(v++u)))) := by
        simp only [expectedMatrixWord, gueTraceWord_stein (hD0 _), hrec]
        apply tendsto_finsetSum
        intro r _
        split_ifs with hr
        · apply tendsto_of_sub_zero (matrixTraceWord_covariance_tendsto hD0 hD A hR hA _ _)
          apply Tendsto.mul
          · exact ih ((v++u).take r.val) (by change ((v++u).take r.val).length < (u++Sum.inr i::v).length; have hh:=r.isLt; simp only [List.length_take,List.length_append,List.length_cons] at *; omega)
          · exact ih ((v++u).drop (r.val+1)) (by change ((v++u).drop (r.val+1)).length < (u++Sum.inr i::v).length; simp only [List.length_drop,List.length_append,List.length_cons]; omega)
        · exact tendsto_const_nhds
      convert hrecLimit using 1
      · funext k
        exact congrArg (fun f => ∫ x, f x ∂productGaussian (MatrixIndex n (D k))) (funext (fun x => matrixTraceWord_cyclic (jointMatrix (A k) x) u (Sum.inr i::v)))
      · exact congrArg (fun z : ℂ => 𝓝 z) (hcyclic u (Sum.inr i::v))
end FiniteEntropySeparation

end

end OAI
