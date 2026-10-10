import OAI.Probability.ClassicalON.ExpMoments

namespace OAI

universe uI uJ uX

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

def MomentCone {X : Type uX} {I : Type uI} (a : I → X → ℝ) (f : X → ℝ) : Prop :=
  ∃ (k : ℕ) (c : Fin k → ℝ) (p : Fin k → List I),
    (∀ j,0≤c j) ∧ ∀ x,f x=∑ j,c j*((p j).map (fun i => a i x)).prod

variable {X : Type uX} {I : Type uI} {a : I → X → ℝ}

theorem momentCone_const {c : ℝ} (hc : 0≤c) : MomentCone a (fun _ => c) := by
  refine ⟨1,fun _ => c,fun _ => [],fun _ => hc,?_⟩
  intro x; simp

theorem momentCone_coordinate (i : I) : MomentCone a (a i) := by
  refine ⟨1,fun _ => 1,fun _ => [i],fun _ => by norm_num,?_⟩
  intro x; simp

theorem momentCone_add {f g : X → ℝ} (hf : MomentCone a f) (hg : MomentCone a g) :
    MomentCone a (fun x => f x+g x) := by
  rcases hf with ⟨k,c,p,hc,hf⟩
  rcases hg with ⟨l,d,q,hd,hg⟩
  refine ⟨k+l,Fin.append c d,Fin.append p q,?_,?_⟩
  · intro j; cases j using Fin.addCases <;> simp_all
  · intro x
    change f x+g x=_
    rw [hf,hg,Fin.sum_univ_add]
    simp

theorem momentCone_mul {f g : X → ℝ} (hf : MomentCone a f) (hg : MomentCone a g) :
    MomentCone a (fun x => f x*g x) := by
  classical
  rcases hf with ⟨k,c,p,hc,hf⟩
  rcases hg with ⟨l,d,q,hd,hg⟩
  let e := (finProdFinEquiv : Fin k × Fin l ≃ Fin (k*l)).symm
  refine ⟨k*l,fun j => c (e j).1*d (e j).2,
    fun j => p (e j).1 ++ q (e j).2,
    fun j => mul_nonneg (hc _) (hd _),?_⟩
  intro x
  simp only [List.map_append,List.prod_append]
  rw [Equiv.sum_comp e (fun z : Fin k × Fin l => c z.1*d z.2*
    ((List.map (fun i => a i x) (p z.1)).prod*(List.map (fun i => a i x) (q z.2)).prod))]
  simp only [Fintype.sum_prod_type]
  rw [hf,hg,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem momentCone_finsetProd {J : Type uJ} (s : Finset J) (f : J → X → ℝ)
    (hf : ∀ j∈s,MomentCone a (f j)) : MomentCone a (fun x => ∏ j∈s,f j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (momentCone_const (a := a) (by norm_num : (0 : ℝ)≤1))
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      momentCone_mul (hf i (by simp)) (ih (fun j hj => hf j (by simp [hj])))

section Integral
variable [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

theorem momentCone_integral_nonneg (ha : ∀ i,Continuous (a i))
    (hm : ∀ (k : ℕ) (p : Fin k → I),0≤∫ x,∏ i,a (p i) x ∂μ)
    {f : X → ℝ} (hf : MomentCone a f) : 0≤∫ x,f x ∂μ := by
  rcases hf with ⟨k,c,p,hc,hf⟩
  simp_rw [hf]
  have hp : ∀ l : List I,Continuous (fun x => (l.map (fun i => a i x)).prod) := by
    intro l
    induction l with
    | nil => simpa using (continuous_const : Continuous (fun _ : X => (1 : ℝ)))
    | cons i l ih =>
      simp only [List.map_cons,List.prod_cons]
      apply Continuous.mul
      · exact ha i
      · exact ih
  have hI (j : Fin k) : Integrable (fun x => c j*(List.map (fun i => a i x) (p j)).prod) μ :=
    compact_integrable (by
      apply Continuous.mul
      · exact continuous_const
      · exact hp (p j))
  rw [integral_finsetSum _ (fun j _ => hI j)]
  apply Finset.sum_nonneg
  intro j _
  rw [integral_const_mul]
  apply mul_nonneg (hc j)
  have he (x : X) : (List.map (fun i => a i x) (p j)).prod =
      ∏ i : Fin (p j).length,a ((p j).get i) x := by
    have hh := List.ofFn_comp' (List.get (p j)) (fun i => a i x)
    rw [List.ofFn_get] at hh
    rw [← hh,List.prod_ofFn]
  simp_rw [he]
  exact hm (p j).length (fun i => (p j).get i)

end Integral
end ClassicalON

end

end OAI
