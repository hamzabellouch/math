import OAI.Geometry.PinnedDistances.PartitionIntegrals

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11

section
noncomputable section
open scoped BigOperators Topology ZeroAtInfty
open Filter MeasureTheory
namespace WeakPinned.Bounded

lemma test_bound_rate (D V A : ℕ → ℝ) (H M : ℝ)
    (hD : ∀ n,0≤ D n) (hH : 0≤ H)
    (hV : Tendsto V atTop (𝓝 0)) (hA : Tendsto A atTop (𝓝 0))
    (h : ∀ η,0<η → ∃ N : ℝ,0≤ N ∧ ∀ δ,0<δ →
      ∀ n,D n≤ 2*η+H*(V n/δ+N*(δ+(M+1)*A n))) :
    Tendsto D atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (hD n))
  · intro b hb
    obtain ⟨N,hN,h⟩ := h (b/8) (by positivity)
    let δ := b/(4*(H*N+1))
    have hδ : 0<δ := by dsimp [δ]; positivity
    have he : (H*N+1)*δ=b/4 := by dsimp [δ]; field_simp
    have hNd : H*N*δ≤ b/4 := by nlinarith
    have hlt : 2*(b/8)+H*(0/δ+N*(δ+(M+1)*0))<b := by simp only [zero_div,mul_zero,add_zero]; nlinarith
    have ht := (tendsto_const_nhds.add ((hV.div_const δ).add
      ((tendsto_const_nhds.add (hA.const_mul (M+1))).const_mul N) |>.const_mul H)).eventually
      (eventually_lt_nhds hlt)
    exact ht.mono (fun n hn => (h δ hδ n).trans_lt hn)

lemma zeroAtInfty_tail (f : C₀(ℂ,ℝ)) (η : ℝ) (hη : 0<η) :
    ∃ R : ℝ,0≤ R ∧ ∀ z,R<‖z‖ → |f z|≤ η := by
  have hf := (Metric.tendsto_nhds.mp (zero_at_infty f) η hη)
  obtain ⟨K,hK,hsub⟩ := mem_cocompact.mp hf
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0:ℂ)
  refine ⟨max R 0,le_max_right _ _,?_⟩
  intro z hz
  have hzK : z∉K := by
    intro hzK
    have hh := Metric.mem_closedBall.mp (hR hzK)
    simp only [dist_zero_right] at hh
    exact (not_le_of_gt (lt_of_le_of_lt (le_max_left _ _) hz)) hh
  simpa only [Real.dist_eq,sub_zero] using (show dist (f z) 0<η from hsub hzK).le

lemma zeroAtInfty_modulus (f : C₀(ℂ,ℝ)) (η : ℝ) (hη : 0<η) :
    ∃ ε : ℝ,0<ε ∧ ∀ z w,‖z-w‖<2*ε → |f z-f w|≤ η := by
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp (ZeroAtInftyContinuousMap.uniformContinuous f) η hη
  refine ⟨δ/2,by positivity,?_⟩
  intro z w hzw
  have hh := hd (show dist z w<δ by rw [dist_eq_norm]; linarith)
  exact (by simpa only [Real.dist_eq] using hh.le)

local instance : MeasurableSpace Sphere := borel Sphere
local instance : BorelSpace Sphere := ⟨rfl⟩

def sphereTest (f : C(Sphere,ℝ)) : C₀(ℂ,ℝ) where
  toFun := fun z => f (z:Sphere)-f OnePoint.infty
  continuous_toFun := (f.continuous.comp OnePoint.continuous_coe).sub continuous_const
  zero_at_infty' := by
    have hco : Tendsto ((↑) : ℂ → Sphere) (cocompact ℂ) (𝓝 OnePoint.infty) :=
      OnePoint.tendsto_coe_infty.mono_left cocompact_le_coclosedCompact
    simpa using ((f.continuous.tendsto OnePoint.infty).comp hco).sub_const (f OnePoint.infty)

lemma sphereTest_bound (f : C(Sphere,ℝ)) (z : ℂ) : |sphereTest f z|≤ 2*‖f‖ := by
  have h₁ := f.norm_coe_le_norm (z:Sphere)
  have h₂ := f.norm_coe_le_norm OnePoint.infty
  change |f (z:Sphere)-f OnePoint.infty|≤ 2*‖f‖
  simpa only [Real.norm_eq_abs,two_mul] using
    (norm_sub_le (f (z:Sphere)) (f OnePoint.infty)).trans (add_le_add h₁ h₂)

end WeakPinned.Bounded

end
end
section
noncomputable section
open scoped BigOperators Topology ZeroAtInfty
open Filter MeasureTheory
namespace WeakPinned.Bounded
open Hierarchy Variance Global NumberField
variable {P : Type u1} {I : Type u2} [Fintype P] [DecidableEq P] [Fintype I]

lemma testDiscrep_sub_const (w : I → ℝ) (B : I → Finset P) (f : P → ℝ) (c : ℝ)
    (hn : 0<Fintype.card P) (hB : ∀ i,(B i).Nonempty) :
    testDiscrep w B (fun x => f x-c)=testDiscrep w B f := by
  have hh (S : Finset P) (hS : S.Nonempty) :
      (∑ x,prob S x*(f x-c))=(∑ x,prob S x*f x)-c := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,sum_prob S hS,one_mul]
  unfold testDiscrep
  simp_rw [hh _ (hB _),hh Finset.univ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hn))]
  simp only [sub_sub_sub_cancel_right]

variable {V : ℕ → Type u3} {J : ℕ → Type u4} {K : ℕ → Type u5}
  [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)] [∀ n,Fintype (J n)]
  [∀ n,Field (K n)] [∀ n,NumberField (K n)]

omit [∀ (n : ℕ), NumberField (K n)] in
lemma C0_arch_test_rate (Z₁ Z₂ : ∀ n,V n → K n)
    (h₁ : ∀ n,Function.Injective (Z₁ n)) (h₂ : ∀ n,Function.Injective (Z₂ n))
    (v : ∀ n,InfinitePlace (K n)) (m : ℕ → ℝ) (b : ℕ → ℂ)
    (w : ∀ n,J n → ℝ) (B : ∀ n,J n → Finset (V n)) (T : ℕ → ℝ) (M H : ℝ)
    (hn : ∀ n,2≤ Fintype.card (V n)) (hT : ∀ n,1≤ T n) (hM : 0≤ M) (hH : 0≤ H)
    (hw : ∀ n i,0≤ w n i) (hW : ∀ n,∑ i,w n i≤ 1) (hB : ∀ n i,2≤ (B n i).card)
    (hdom : ∀ n x,(∑ i,w n i*prob (B n i) x)≤ M*prob Finset.univ x)
    (hvar : Tendsto (fun n => archMean (Z₁ n) (Z₂ n) (massEval (varianceCell (w n) (B n) (T n))) (v n)) atTop (𝓝 0))
    (hsmall : Tendsto (fun n => T n/Fintype.card (V n)) atTop (𝓝 0))
    (f : C₀(ℂ,ℝ)) (hbound : ∀ z,|f z|≤ H) :
    Tendsto (fun n => testDiscrep (w n) (B n)
      (fun x => f ((Real.exp (m n):ℂ)*(v n).embedding (Z₁ n x)+b n))) atTop (𝓝 0) := by
  apply test_bound_rate _ _ _ H M (fun n => testDiscrep_nonneg _ _ _ (hw n)) hH hvar hsmall
  intro η hη
  obtain ⟨R,hR,hout⟩ := zeroAtInfty_tail f η hη
  obtain ⟨ε,hε,hcont⟩ := zeroAtInfty_modulus f η hη
  obtain ⟨N,hN⟩ := exists_nat_ge (2*R/(ε/(2*Real.exp 1))+1)
  refine ⟨((2*N+1)^2:ℕ),by positivity,?_⟩
  intro δ hδ n
  have hh := arch_test_bound (Z₁ n) (Z₂ n) (h₁ n) (h₂ n) (v n) (m n) (b n) (hn n)
    R ε η H M (T n) δ N hR hε hN hη.le hH hM (hT n) hδ
    (w n) (B n) (hw n) (hW n) (hB n) (hdom n) f hbound hcont hout
  convert hh using 1
  ring

local instance : MeasurableSpace Sphere := borel Sphere
local instance : BorelSpace Sphere := ⟨rfl⟩

omit [∀ (n : ℕ), NumberField (K n)] in
lemma sphere_arch_test_rate (Z₁ Z₂ : ∀ n,V n → K n)
    (h₁ : ∀ n,Function.Injective (Z₁ n)) (h₂ : ∀ n,Function.Injective (Z₂ n))
    (v : ∀ n,InfinitePlace (K n)) (m : ℕ → ℝ) (b : ℕ → ℂ)
    (w : ∀ n,J n → ℝ) (B : ∀ n,J n → Finset (V n)) (T : ℕ → ℝ) (M : ℝ)
    (hn : ∀ n,2≤ Fintype.card (V n)) (hT : ∀ n,1≤ T n) (hM : 0≤ M)
    (hw : ∀ n i,0≤ w n i) (hW : ∀ n,∑ i,w n i≤ 1) (hB : ∀ n i,2≤ (B n i).card)
    (hdom : ∀ n x,(∑ i,w n i*prob (B n i) x)≤ M*prob Finset.univ x)
    (hvar : Tendsto (fun n => archMean (Z₁ n) (Z₂ n) (massEval (varianceCell (w n) (B n) (T n))) (v n)) atTop (𝓝 0))
    (hsmall : Tendsto (fun n => T n/Fintype.card (V n)) atTop (𝓝 0))
    (f : C(Sphere,ℝ)) :
    Tendsto (fun n => testDiscrep (w n) (B n)
      (fun x => f (((Real.exp (m n):ℂ)*(v n).embedding (Z₁ n x)+b n):Sphere))) atTop (𝓝 0) := by
  have ht := C0_arch_test_rate Z₁ Z₂ h₁ h₂ v m b w B T M (2*‖f‖) hn hT hM (by positivity)
    hw hW hB hdom hvar hsmall (sphereTest f) (sphereTest_bound f)
  convert ht using 1
  funext n
  symm
  apply testDiscrep_sub_const _ _ _ _ (by have := hn n; omega)
  intro i
  exact Finset.card_pos.mp (by have := hB n i; omega)

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace WeakPinned.Bounded
open Variance
variable {V : Type u6} {I : Type u7} [Fintype V] [DecidableEq V] [Fintype I]
variable (G : Core.Fibers V I)

omit [Fintype I] in
lemma incoming_discrep_bound (T H : ℝ) (hT : 0<T) (hn : 2≤Fintype.card V)
    (f : V → ℝ) (hf : ∀ x,|f x|≤H) :
    (∑ y,G.incomingWeight y*|(∑ x,G.conditionalSource y x*f x)-∑ x,prob Finset.univ x*f x|)≤
      testDiscrep (G.retainedWeight T) (G.retainedSet T) f+2*H*G.omittedMass T := by
  have hA : |∑ x,prob (Finset.univ : Finset V) x*f x|≤H :=
    avg_abs_bound _ _ _ (Core.Fibers.prob_nn _) (sum_prob _
      (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))) hf
  unfold testDiscrep Core.Fibers.omittedMass
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : T≤((G.incoming y).card:ℝ)
  · have hne : (G.incoming y).Nonempty := Finset.card_pos.mp (by exact_mod_cast hT.trans_le hy)
    simp only [Core.Fibers.retainedWeight,Core.Fibers.retainedSet,Core.Fibers.conditionalSource,
      ite_eq_left hy,ite_eq_left hne,not_lt_of_ge hy,ite_false,mul_zero,add_zero]
    exact le_rfl
  · have hbound : |(∑ x,G.conditionalSource y x*f x)-∑ x,prob Finset.univ x*f x|≤2*H := by
      have hh := avg_abs_bound _ _ _ (G.conditionalSource_nonneg y) (G.conditionalSource_sum hn y) hf
      exact (abs_sub _ _).trans (by linarith)
    simp only [Core.Fibers.retainedWeight,ite_eq_right hy,lt_of_not_ge hy,ite_true,zero_mul,zero_add]
    nlinarith [mul_le_mul_of_nonneg_left hbound (G.incomingWeight_nonneg y)]

lemma incoming_test_bound (T H C : ℝ) (hT : 0<T) (hn : 2≤Fintype.card V)
    (f g : V → ℝ) (hf : ∀ x,|f x|≤H) (hg : ∀ y,|g y|≤C) :
    |(∑ e,G.fiberWeight e*∑ y,prob (G.targets e) y*(f (G.source e)*g y))-
      (∑ x,prob Finset.univ x*f x)*(∑ y,G.incomingWeight y*g y)|≤
      C*(testDiscrep (G.retainedWeight T) (G.retainedSet T) f+2*H*G.omittedMass T) := by
  have hC : 0≤C := (abs_nonneg (g (Classical.choice (Fintype.card_pos_iff.mp (by omega))))).trans (hg _)
  rw [← G.incoming_eval (fun x y => f x*g y)]
  have he : (∑ y,G.incomingWeight y*∑ x,G.conditionalSource y x*(f x*g y))-
      (∑ x,prob Finset.univ x*f x)*(∑ y,G.incomingWeight y*g y)=
      ∑ y,G.incomingWeight y*((∑ x,G.conditionalSource y x*f x)-∑ x,prob Finset.univ x*f x)*g y := by
    simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he]
  calc
    _ ≤ ∑ y,|G.incomingWeight y*((∑ x,G.conditionalSource y x*f x)-∑ x,prob Finset.univ x*f x)*g y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ C*(∑ y,G.incomingWeight y*|(∑ x,G.conditionalSource y x*f x)-∑ x,prob Finset.univ x*f x|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y _
      rw [abs_mul,abs_mul,abs_of_nonneg (G.incomingWeight_nonneg y)]
      nlinarith [mul_le_mul_of_nonneg_left (hg y) (mul_nonneg (G.incomingWeight_nonneg y) (abs_nonneg ((∑ x,G.conditionalSource y x*f x)-∑ x,prob Finset.univ x*f x)))]
    _ ≤ _ := mul_le_mul_of_nonneg_left (incoming_discrep_bound G T H hT hn f hf) hC

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace WeakPinned.Bounded
open Variance
local instance : MeasurableSpace Sphere := borel Sphere
local instance : BorelSpace Sphere := ⟨rfl⟩
local instance : MeasurableSingletonClass (Quad Sphere) := inferInstance
local instance : MeasurableSingletonClass ((Sphere × Sphere) × (Sphere × Sphere)) := inferInstance
local instance : MeasurableSingletonClass (Expanded Sphere) := Prod.instMeasurableSingletonClass
variable {V : Type u8} {I : Type u9} [Fintype V] [DecidableEq V] [Fintype I]
variable (G : Core.Fibers V I)

omit G [Fintype I] in
lemma integral_uniformLaw (U : V → Sphere) (f : Sphere → ℝ) :
    (∫ z,f z ∂  uniformLaw U)=∑ x,prob Finset.univ x*f (U x) := by
  rw [uniformLaw,integral_finiteLaw _ _ (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))]
  simp only [prob,Finset.mem_univ,ite_true,Finset.card_univ,one_div]

lemma integral_edgeProbability (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) (f : Quad Sphere → ℝ) :
    (∫ q,f q ∂ (edgeProbability G U₁ U₂ hG hB:Measure (Quad Sphere)))=
      ∑ e,G.fiberWeight e*∑ y,prob (G.targets e) y*f (edgeValue G.source U₁ U₂ (e,y)) := by
  change (∫ q,f q ∂ finiteLaw _ _)=_
  rw [integral_finiteLaw _ _ (graph_edgeWeight_nonneg G)]
  simp only [edgeWeight,Fintype.sum_prod_type,mul_assoc,← Finset.mul_sum]

lemma integral_expandedProbability (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) (f : Expanded Sphere → ℝ) :
    (∫ r,f r ∂ (expandedProbability G U₁ U₂ hG hB:Measure (Expanded Sphere)))=
      ∑ r,tripleWeight G.fiberWeight (fun e => prob (G.targets e)) r*f (tripleValue G.source U₁ U₂ r) := by
  change (∫ r,f r ∂ finiteLaw (tripleWeight G.fiberWeight (fun e => prob (G.targets e))) (tripleValue G.source U₁ U₂))=_
  exact integral_finiteLaw _ _ (graph_tripleWeight_nonneg G) f

lemma expanded_test_bound (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) (hn : 2≤Fintype.card V)
    (π : Sphere × Sphere → Sphere) (f : Quad Sphere → ℝ) (g h : Sphere → ℝ) (C H₁ H₂ : ℝ)
    (hC : 0≤C) (hf : ∀ q,|f q|≤C) (hg : ∀ z,|g z|≤H₁) (hh : ∀ z,|h z|≤H₂) :
    |(∫ r,f r.1*g (π r.2.1)*h (π r.2.2) ∂ (expandedProbability G U₁ U₂ hG hB:Measure (Expanded Sphere)))-
      (∫ q,f q ∂ (edgeProbability G U₁ U₂ hG hB:Measure (Quad Sphere)))*
        (∫ z,g z ∂ uniformLaw (fun x => π (U₁ x,U₂ x)))*(∫ z,h z ∂ uniformLaw (fun x => π (U₁ x,U₂ x)))|≤
      C*(H₂*testDiscrep G.fiberWeight G.targets (fun x => g (π (U₁ x,U₂ x)))+
        H₁*testDiscrep G.fiberWeight G.targets (fun x => h (π (U₁ x,U₂ x)))) := by
  rw [integral_expandedProbability,integral_edgeProbability,integral_uniformLaw,integral_uniformLaw]
  have hA : |∑ x,prob (Finset.univ : Finset V) x*g (π (U₁ x,U₂ x))|≤H₁ := by
    exact avg_abs_bound _ _ _ (Core.Fibers.prob_nn _) (sum_prob _
      (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))) (fun x => hg _)
  have hb := mixture_pair_test_bound G.fiberWeight (fun e => prob (G.targets e))
    (fun e y => f (edgeValue G.source U₁ U₂ (e,y))) (fun x => g (π (U₁ x,U₂ x))) (fun x => h (π (U₁ x,U₂ x)))
    (∑ x,prob Finset.univ x*g (π (U₁ x,U₂ x))) (∑ x,prob Finset.univ x*h (π (U₁ x,U₂ x)))
    C H₁ H₂ G.fiberWeight_nonneg (fun e => Core.Fibers.prob_nn _) (fun e => sum_prob _ (hB e))
    hC (fun e y => hf _) (fun x => hh _) hA
  simpa only [tripleValue,testDiscrep,edgeWeight,Fintype.sum_prod_type,mul_assoc,← Finset.mul_sum] using hb

lemma integral_target (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) (g : Sphere × Sphere → ℝ) :
    (∫ q,g q.2.2 ∂ (edgeProbability G U₁ U₂ hG hB:Measure (Quad Sphere)))=
      ∑ y,G.incomingWeight y*g (U₁ y,U₂ y) := by
  rw [integral_edgeProbability]
  simp only [edgeValue,Finset.mul_sum,← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.sum_mul,G.fiber_marginal,G.incoming_marginal]

lemma incoming_law_test_bound (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) (hn : 2≤Fintype.card V) (T H C : ℝ) (hT : 0<T)
    (f : Sphere → ℝ) (g : Sphere × Sphere → ℝ) (hf : ∀ z,|f z|≤H) (hg : ∀ z,|g z|≤C) :
    |(∫ q,f q.1*g q.2.2 ∂ (edgeProbability G U₁ U₂ hG hB:Measure (Quad Sphere)))-
      (∫ z,f z ∂ uniformLaw U₁)*(∫ q,g q.2.2 ∂ (edgeProbability G U₁ U₂ hG hB:Measure (Quad Sphere)))|≤
      C*(testDiscrep (G.retainedWeight T) (G.retainedSet T) (fun x => f (U₁ x))+2*H*G.omittedMass T) := by
  rw [integral_target,integral_edgeProbability,integral_uniformLaw]
  exact incoming_test_bound G T H C hT hn (fun x => f (U₁ x)) (fun x => g (U₁ x,U₂ x))
    (fun x => hf _) (fun x => hg _)

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace WeakPinned.Bounded
local instance : MeasurableSpace Sphere := borel Sphere
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {V : ℕ → Type u10} {I : ℕ → Type u11} [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)] [∀ n,Fintype (I n)]
variable (G : ∀ n,Core.Fibers (V n) (I n)) (U₁ U₂ : ∀ n,V n → Sphere)
  (hG : ∀ n,0<(G n).edgeCount) (hB : ∀ n e,((G n).targets e).Nonempty)
  (hn : ∀ n,2≤Fintype.card (V n))

include hn
lemma expanded_test_rate (π : Sphere × Sphere → Sphere)
    (hd : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep (G n).fiberWeight (G n).targets
      (fun x => f (π (U₁ n x,U₂ n x)))) atTop (𝓝 0))
    (f : Quad Sphere →ᵇ ℝ) (g h : Sphere →ᵇ ℝ) :
    Tendsto (fun n => (∫ r,f r.1*g (π r.2.1)*h (π r.2.2)
      ∂ (expandedProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n):Measure (Expanded Sphere)))-
      (∫ q,f q ∂ (edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n):Measure (Quad Sphere)))*
        (∫ z,g z ∂ uniformLaw (fun x => π (U₁ n x,U₂ n x)))*
        (∫ z,h z ∂ uniformLaw (fun x => π (U₁ n x,U₂ n x)))) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have ht := ((hd g.toContinuousMap).const_mul ‖h‖ |>.add
    ((hd h.toContinuousMap).const_mul ‖g‖)).const_mul ‖f‖
  simp only [mul_zero,zero_add] at ht
  apply squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) ht
  exact expanded_test_bound (G n) (U₁ n) (U₂ n) (hG n) (hB n) (hn n) π f g h
    ‖f‖ ‖g‖ ‖h‖ (norm_nonneg _) (fun q => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm q)
    (fun z => by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm z)
    (fun z => by simpa only [Real.norm_eq_abs] using h.norm_coe_le_norm z)

lemma incoming_law_test_rate (T : ℕ → ℝ) (hT : ∀ n,0<T n)
    (hd : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep ((G n).retainedWeight (T n))
      ((G n).retainedSet (T n)) (fun x => f (U₁ n x))) atTop (𝓝 0))
    (ho : Tendsto (fun n => (G n).omittedMass (T n)) atTop (𝓝 0))
    (f : Sphere →ᵇ ℝ) (g : Sphere × Sphere →ᵇ ℝ) :
    Tendsto (fun n => (∫ q,f q.1*g q.2.2 ∂ (edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n):Measure (Quad Sphere)))-
      (∫ z,f z ∂ uniformLaw (U₁ n))*(∫ q,g q.2.2 ∂ (edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n):Measure (Quad Sphere))))
      atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have ht := ((hd f.toContinuousMap).add (ho.const_mul (2*‖f‖))).const_mul ‖g‖
  simp only [mul_zero,zero_add] at ht
  apply squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) ht
  exact incoming_law_test_bound (G n) (U₁ n) (U₂ n) (hG n) (hB n) (hn n) (T n) ‖f‖ ‖g‖ (hT n) f g
    (fun z => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm z)
    (fun z => by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm z)

end WeakPinned.Bounded

end
end

end OAI
