import Mathlib
import OAI.Probability.Contingency.LawComposition

namespace OAI

/-! Dense Regularity. -/

noncomputable section

open scoped BigOperators
open scoped BigOperators
namespace Contingency.Dense
noncomputable section
variable {a c : ℕ}

theorem scaled_affine (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (u v : Fin a×Fin c → ℝ) (α β : ℝ) (hab : α+β=1)
    (i : Fin (a+1)) (j : Fin (c+1)) :
    scaled R P w (α • u+β • v) i j=α*scaled R P w u i j+β*scaled R P w v i j := by
  have hs (i j) : w i j*(α*u (i,j)+β*v (i,j))=α*(w i j*u (i,j))+β*(w i j*v (i,j)) := by ring
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j
  all_goals simp only [scaled,complete_corner,complete_bottom,complete_right,complete_free,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,hs,Finset.sum_add_distrib,← Finset.mul_sum]
  all_goals have hb : β=1-α := by linarith only [hab]
  all_goals rw [hb]; ring

theorem normalized_affine (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (u v : Fin a×Fin c → ℝ) (α β : ℝ) (hab : α+β=1)
    (i : Fin (a+1)) (j : Fin (c+1)) :
    normalized R P w (α • u+β • v) i j=α*normalized R P w u i j+β*normalized R P w v i j := by
  simp only [normalized,scaled_affine R P w u v α β hab]
  ring

theorem polytope_convex (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ) (w : Fin a → Fin c → ℝ) :
    Convex ℝ (polytope R P w) := by
  intro u hu v hv α β hα hβ hab i j
  rw [normalized_affine R P w u v α β hab]
  exact add_nonneg (mul_nonneg hα (hu i j)) (mul_nonneg hβ (hv i j))

 

def coefficient (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ) (w : Fin a → Fin c → ℝ)
    (i : Fin (a+1)) (j : Fin (c+1)) (k : Fin a) (l : Fin c) : ℝ :=
  Fin.lastCases
    (Fin.lastCases (w k l/scale R P (Fin.last a) (Fin.last c))
      (fun j => if l=j then -(w k l/scale R P (Fin.last a) j.castSucc) else 0) j)
    (fun i => Fin.lastCases (if k=i then -(w k l/scale R P i.castSucc (Fin.last c)) else 0)
      (fun j => if k=i ∧ l=j then w k l/scale R P i.castSucc j.castSucc else 0) j) i

theorem normalized_difference (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (u v : Fin a×Fin c → ℝ) (i : Fin (a+1)) (j : Fin (c+1)) :
    normalized R P w u i j-normalized R P w v i j=
      ∑ k,∑ l,coefficient R P w i j k l*(u (k,l)-v (k,l)) := by
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j
  all_goals simp only [normalized,scaled,complete_corner,complete_bottom,complete_right,
    complete_free,coefficient,Fin.lastCases_last,Fin.lastCases_castSucc]
  · simp only [div_mul_eq_mul_div,mul_sub,Finset.sum_sub_distrib,← Finset.sum_div]
    ring
  · simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    simp only [neg_mul,div_mul_eq_mul_div,mul_sub,Finset.sum_sub_distrib,← Finset.sum_div,Finset.sum_neg_distrib]
    ring
  · simp only [ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    simp only [neg_mul,div_mul_eq_mul_div,mul_sub,Finset.sum_sub_distrib,← Finset.sum_div,Finset.sum_neg_distrib]
    ring
  · simp only [ite_and,ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    ring

theorem normalized_width_bound (w s t B : ℝ) (hw0 : 0 ≤ w) (hB : 0<B) (ht : 0<t)
    (hws : w ≤ s/B) (hst : s ≤ t) : |w/t| ≤ 1/B := by
  rw [abs_of_nonneg (div_nonneg hw0 ht.le)]
  apply (div_le_iff₀ ht).mpr
  calc
    w  ≤  s/B := hws
    _  ≤  t/B := div_le_div_of_nonneg_right hst hB.le
    _ = 1/B*t := by ring

theorem coefficient_bound (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B : ℝ) (hB : 0<B)
    (hR : ∀ i,0<R i) (hP : ∀ j,0<P j)
    (hRmax : ∀ i,R i ≤ R (Fin.last a)) (hPmax : ∀ j,P j ≤ P (Fin.last c))
    (hw0 : ∀ i j,0 ≤ w i j) (hw : ∀ i j,w i j ≤ scale R P i.castSucc j.castSucc/B)
    (i : Fin (a+1)) (j : Fin (c+1)) (k : Fin a) (l : Fin c) :
    |coefficient R P w i j k l| ≤ 1/B := by
  have hs (i j) : 0<scale R P i j := lt_min (hR i) (hP j)
  have hbase (i j) (hh : scale R P k.castSucc l.castSucc ≤ scale R P i j) : |w k l/scale R P i j| ≤ 1/B :=
    normalized_width_bound _ _ _ _ (hw0 k l) hB (hs i j) (hw k l) hh
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j
  all_goals simp only [coefficient,Fin.lastCases_last,Fin.lastCases_castSucc]
  · exact hbase _ _ (min_le_min (hRmax _) (hPmax _))
  · split_ifs with h
    · subst l; rw [abs_neg]; exact hbase _ _ (min_le_min_right _ (hRmax _))
    · simp only [abs_zero]; positivity
  · split_ifs with h
    · subst k; rw [abs_neg]; exact hbase _ _ (min_le_min_left _ (hPmax _))
    · simp only [abs_zero]; positivity
  · split_ifs with h
    · rcases h with ⟨rfl,rfl⟩; exact hbase _ _ le_rfl
    · simp only [abs_zero]; positivity

 

theorem normalized_lipschitz (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B d : ℝ) (hB : 0<B) (he : (a*c:ℕ) ≤ d)
    (hR : ∀ i,0<R i) (hP : ∀ j,0<P j)
    (hRmax : ∀ i,R i ≤ R (Fin.last a)) (hPmax : ∀ j,P j ≤ P (Fin.last c))
    (hw0 : ∀ i j,0 ≤ w i j) (hw : ∀ i j,w i j ≤ scale R P i.castSucc j.castSucc/B)
    (u v : Fin a×Fin c → ℝ) (i : Fin (a+1)) (j : Fin (c+1)) :
    |normalized R P w u i j-normalized R P w v i j| ≤ d/B*‖u-v‖ := by
  rw [normalized_difference]
  calc
    _  ≤  ∑ k,∑ l,|coefficient R P w i j k l*(u (k,l)-v (k,l))| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _)
    _  ≤  ∑ k : Fin a,∑ l : Fin c,(1/B)*‖u-v‖ := by
      apply Finset.sum_le_sum; intro k _
      apply Finset.sum_le_sum; intro l _
      rw [abs_mul]
      apply mul_le_mul (coefficient_bound R P w B hB hR hP hRmax hPmax hw0 hw i j k l)
      · simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm (u-v) (k,l)
      · exact abs_nonneg _
      · positivity
    _ = (a*c:ℕ)/B*‖u-v‖ := by simp; ring
    _  ≤  d/B*‖u-v‖ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right he hB.le) (norm_nonneg _)

end
end Contingency.Dense

 

 

open scoped BigOperators
namespace Contingency.Dense
noncomputable section
variable {a c : ℕ}

 
def penalty (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B d : ℝ) (u : Fin a×Fin c → ℝ) : ℝ :=
  max 0 (Finset.univ.sup' Finset.univ_nonempty fun s : Fin (a+1)×Fin (c+1) =>
    -normalized R P w u s.1 s.2-d/B)

theorem penalty_nonneg (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B d : ℝ) (u : Fin a×Fin c → ℝ) :
    0 ≤ penalty R P w B d u := le_max_left _ _

theorem le_penalty (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B d : ℝ) (u : Fin a×Fin c → ℝ) (i j) :
    -normalized R P w u i j-d/B ≤ penalty R P w B d u := by
  exact (Finset.le_sup' (fun s : Fin (a+1)×Fin (c+1) =>
    -normalized R P w u s.1 s.2-d/B) (Finset.mem_univ (i,j))).trans (le_max_right _ _)

theorem penalty_le_iff (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B d : ℝ) (u : Fin a×Fin c → ℝ) (z : ℝ) :
    penalty R P w B d u ≤ z ↔ 0 ≤ z ∧ ∀ i j,-normalized R P w u i j-d/B ≤ z := by
  simp only [penalty,max_le_iff,Finset.sup'_le_iff,Finset.mem_univ,forall_const]
  exact and_congr_right (fun _ => ⟨fun h i j => h (i,j),fun h s => h s.1 s.2⟩)

theorem penalty_convex (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B d : ℝ) : ConvexOn ℝ Set.univ (penalty R P w B d) := by
  refine ⟨convex_univ,?_⟩
  intro u _ v _ α β ha hb hab
  rw [smul_eq_mul,smul_eq_mul,penalty_le_iff]
  constructor
  · exact add_nonneg (mul_nonneg ha (penalty_nonneg _ _ _ _ _ _))
      (mul_nonneg hb (penalty_nonneg _ _ _ _ _ _))
  · intro i j
    rw [normalized_affine R P w u v α β hab]
    have h1 := mul_le_mul_of_nonneg_left (le_penalty R P w B d u i j) ha
    have h2 := mul_le_mul_of_nonneg_left (le_penalty R P w B d v i j) hb
    have h3 := congrArg (fun t : ℝ => t*(d/B)) hab
    nlinarith only [h1,h2,h3]

theorem penalty_zero_of_slack (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B d : ℝ) (u : Fin a×Fin c → ℝ)
    (hu : ∀ i j,-d/B ≤ normalized R P w u i j) : penalty R P w B d u=0 := by
  apply le_antisymm _ (penalty_nonneg _ _ _ _ _ _)
  rw [penalty_le_iff]
  exact ⟨le_rfl,fun i j => by have hh := hu i j; rw [neg_div] at hh; linarith only [hh]⟩

theorem penalty_difference (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B d K : ℝ) (hK : 0 ≤ K)
    (u v : Fin a×Fin c → ℝ)
    (hv : ∀ i j,|normalized R P w u i j-normalized R P w v i j| ≤ K) :
    |penalty R P w B d u-penalty R P w B d v| ≤ K := by
  have h (u v : Fin a×Fin c → ℝ)
      (hh : ∀ i j,normalized R P w v i j-normalized R P w u i j ≤ K) :
      penalty R P w B d u ≤ penalty R P w B d v+K := by
    rw [penalty_le_iff]
    refine ⟨add_nonneg (penalty_nonneg _ _ _ _ _ _) hK,fun i j => ?_⟩
    linarith only [hh i j,le_penalty R P w B d v i j]
  rw [abs_le]
  constructor
  · have hv' := h v u (fun i j => (abs_le.mp (hv i j)).2)
    linarith only [hv']
  · have hu' := h u v (fun i j => by have := (abs_le.mp (hv i j)).1; linarith)
    linarith only [hu']

 

def density (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B d A : ℝ) (u : Fin a×Fin c → ℝ) : ℝ :=
  (2:ℝ)^(-A*penalty R P w B d u)

theorem density_pos (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B d A : ℝ) (u : Fin a×Fin c → ℝ) :
    0<density R P w B d A u := Real.rpow_pos_of_pos (by norm_num) _

theorem density_logconcave (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B d A : ℝ) (hA : 0 ≤ A)
    (u v : Fin a×Fin c → ℝ) (α β : ℝ) (ha : 0 ≤ α) (hb : 0 ≤ β) (hab : α+β=1) :
    density R P w B d A u^α*density R P w B d A v^β ≤
      density R P w B d A (α • u+β • v) := by
  have h := (penalty_convex R P w B d).2 (Set.mem_univ u) (Set.mem_univ v) ha hb hab
  simp only [smul_eq_mul] at h
  unfold density
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  nlinarith only [mul_le_mul_of_nonneg_left h hA]

end
end Contingency.Dense

 

 

open Set MeasureTheory
open scoped Pointwise
namespace Contingency.Interpolation

structure OpenBox (q : ℕ) where
  lower : Fin q → ℝ
  upper : Fin q → ℝ

def OpenBox.carrier {q : ℕ} (B : OpenBox q) : Set (Fin q → ℝ) :=
  Set.pi Set.univ fun i => Ioo (B.lower i) (B.upper i)

def boxUnion {q : ℕ} (S : Finset (OpenBox q)) : Set (Fin q → ℝ) :=
  ⋃ B∈S, B.carrier

 

def FiniteBoxInterpolation : Prop :=
  ∀ (q : ℕ) (S₁ S₂ S₀ : Finset (OpenBox q)) (t : ℝ), 0<t → t<1 →
  ∀ (l u : Fin q → ℝ),
    closure (boxUnion S₁ ∪ boxUnion S₂ ∪ boxUnion S₀) ⊆ Icc l u →
  ∀ (f₁ f₂ f₀ : (Fin q → ℝ) → ℝ),
    ContinuousOn f₁ (Icc l u) → ContinuousOn f₂ (Icc l u) → ContinuousOn f₀ (Icc l u) →
    (∀ x∈Icc l u, 0<f₁ x ∧ 0<f₂ x ∧ 0<f₀ x) →
    (∀ x∈boxUnion S₁, ∀ y∈boxUnion S₂, (1-t) • x+t • y∈boxUnion S₀) →
    (∀ x∈boxUnion S₁, ∀ y∈boxUnion S₂, f₁ x^(1-t)*f₂ y^t≤f₀ ((1-t) • x+t • y)) →
    (∫ x in boxUnion S₁,f₁ x)^(1-t)*(∫ x in boxUnion S₂,f₂ x)^t≤∫ x in boxUnion S₀,f₀ x

end Contingency.Interpolation

 

 

open Set MeasureTheory
open scoped Topology
namespace Contingency.Interpolation
noncomputable section

variable {q : ℕ}

@[simp] theorem mem_boxUnion (S : Finset (OpenBox q)) (x : Fin q → ℝ) :
    x∈boxUnion S ↔ ∃ B∈S,∀ i,B.lower i<x i ∧ x i<B.upper i := by
  simp [boxUnion,OpenBox.carrier]

theorem OpenBox.isOpen (B : OpenBox q) : IsOpen B.carrier :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

theorem OpenBox.isBounded (B : OpenBox q) : Bornology.IsBounded B.carrier := by
  exact (Bornology.isBounded_pi).mpr (Or.inr fun _ => Metric.isBounded_Ioo _ _)

theorem boxUnion_isOpen (S : Finset (OpenBox q)) : IsOpen (boxUnion S) :=
  isOpen_iUnion fun B => isOpen_iUnion fun _ => B.isOpen

theorem boxUnion_isBounded (S : Finset (OpenBox q)) : Bornology.IsBounded (boxUnion S) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [boxUnion]
  | @insert B S hB ih =>
    have he : boxUnion (insert B S)=B.carrier ∪ boxUnion S := by simp [boxUnion]
    rw [he]
    exact B.isBounded.union ih

theorem boxUnion_measurable (S : Finset (OpenBox q)) : MeasurableSet (boxUnion S) :=
  (boxUnion_isOpen S).measurableSet

theorem boxUnion_volume_finite (S : Finset (OpenBox q)) : volume (boxUnion S)<⊤ :=
  (boxUnion_isBounded S).measure_lt_top

theorem boxUnion_volume_pos (S : Finset (OpenBox q)) (hS : (boxUnion S).Nonempty) :
    0<volume (boxUnion S) := (boxUnion_isOpen S).measure_pos volume hS

def OpenBox.tail (B : OpenBox (q+1)) : OpenBox q :=
  ⟨fun i => B.lower i.succ,fun i => B.upper i.succ⟩

def slices (S : Finset (OpenBox (q+1))) (x : ℝ) : Finset (OpenBox q) := by
  classical
  exact (S.filter (fun B => B.lower 0<x ∧ x<B.upper 0)).image OpenBox.tail

@[simp] theorem mem_slices (S : Finset (OpenBox (q+1))) (x : ℝ) (y : Fin q → ℝ) :
    y∈boxUnion (slices S x) ↔ Fin.cons x y∈boxUnion S := by
  classical
  simp [mem_boxUnion,slices,Fin.forall_fin_succ,OpenBox.tail]
  constructor
  · rintro ⟨B,⟨hB,hx⟩,hy⟩
    exact ⟨B,hB,hx,hy⟩
  · rintro ⟨B,hB,hx,hy⟩
    exact ⟨B,⟨hB,hx⟩,hy⟩

def endpoints (S : Finset (OpenBox (q+1))) : Finset ℝ := by
  classical
  exact S.biUnion fun B => {B.lower 0,B.upper 0}

theorem lower_mem_endpoints (S : Finset (OpenBox (q+1))) (B : OpenBox (q+1)) (hB : B∈S) :
    B.lower 0∈endpoints S := by
  classical
  simp only [endpoints,Finset.mem_biUnion,Finset.mem_insert,Finset.mem_singleton]
  exact ⟨B,hB,Or.inl rfl⟩

theorem upper_mem_endpoints (S : Finset (OpenBox (q+1))) (B : OpenBox (q+1)) (hB : B∈S) :
    B.upper 0∈endpoints S := by
  classical
  simp only [endpoints,Finset.mem_biUnion,Finset.mem_insert,Finset.mem_singleton]
  exact ⟨B,hB,Or.inr rfl⟩

 

structure GoodWeight (q : ℕ) where
  f : (Fin q → ℝ) → ℝ
  continuous : Continuous f
  positive : ∀ x,0<f x
  bound : ℝ
  bounded : ∀ x,‖f x‖ ≤ bound

namespace GoodWeight

theorem integrable (F : GoodWeight q) (S : Finset (OpenBox q)) :
    IntegrableOn F.f (boxUnion S) :=
  IntegrableOn.of_bound (boxUnion_volume_finite S) F.continuous.aestronglyMeasurable F.bound
    (Filter.Eventually.of_forall F.bounded)

theorem integral_nonneg (F : GoodWeight q) (S : Finset (OpenBox q)) :
    0 ≤ ∫ x in boxUnion S,F.f x := MeasureTheory.integral_nonneg fun x => (F.positive x).le

theorem integral_pos (F : GoodWeight q) (S : Finset (OpenBox q)) (hS : (boxUnion S).Nonempty) :
    0 < ∫ x in boxUnion S,F.f x := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (F.positive x).le) (F.integrable S)).mpr
  have he : Function.support F.f=univ := by ext x; simp [Function.mem_support,(F.positive x).ne']
  rw [he,Measure.restrict_apply_univ]
  exact boxUnion_volume_pos S hS

def slice (F : GoodWeight (q+1)) (x : ℝ) : GoodWeight q :=
  ⟨fun y => F.f (Fin.cons x y),F.continuous.comp (continuous_const.finCons continuous_id),
    fun point => F.positive (Fin.cons x point),F.bound,fun point => F.bounded (Fin.cons x point)⟩

 

theorem marginal_continuous (F : GoodWeight (q+1)) (S : Finset (OpenBox q)) :
    Continuous (fun x : ℝ => ∫ y in boxUnion S,F.f (Fin.cons x y)) := by
  apply continuous_of_dominated (bound := fun _ => F.bound)
  · intro x
    exact (F.slice x).continuous.aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall fun y => F.bounded _
  · exact integrableOn_const (boxUnion_volume_finite S).ne
  · exact Filter.Eventually.of_forall fun y =>
      F.continuous.comp (by fun_prop)

end GoodWeight
end
end Contingency.Interpolation

 

 

open Set MeasureTheory
namespace Contingency.Interpolation
noncomputable section
variable {q : ℕ}

 
def marginal (S : Finset (OpenBox (q+1))) (F : GoodWeight (q+1)) (x : ℝ) : ℝ :=
  ∫ y in boxUnion (slices S x),F.f (Fin.cons x y)

theorem marginal_nonneg (S : Finset (OpenBox (q+1))) (F : GoodWeight (q+1)) (x : ℝ) :
    0 ≤ marginal S F x := (F.slice x).integral_nonneg _

 
theorem marginal_fubini (S : Finset (OpenBox (q+1))) (F : GoodWeight (q+1)) :
    Integrable (marginal S F) ∧ (∫ x,marginal S F x)=∫ z in boxUnion S,F.f z := by
  classical
  let e : ℝ × (Fin q → ℝ) ≃ᵐ (Fin (q+1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm
  have hp : MeasurePreserving e := (volume_preserving_piFinSuccAbove (fun _ : Fin (q+1) => ℝ) 0).symm _
  have he (p : ℝ × (Fin q → ℝ)) : e p=Fin.cons p.1 p.2 := by
    simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
  let I := (boxUnion S).indicator F.f
  have hi : Integrable I := (F.integrable S).integrable_indicator (boxUnion_measurable S)
  have hpull : Integrable (fun p : ℝ × (Fin q → ℝ) => I (Fin.cons p.1 p.2)) (volume.prod volume) := by
    simpa only [Function.comp_def,he,Measure.volume_eq_prod] using (hp.integrable_comp_emb e.measurableEmbedding).mpr hi
  have hind (x : ℝ) : (fun y => I (Fin.cons x y))=
      (boxUnion (slices S x)).indicator (fun y => F.f (Fin.cons x y)) := by
    funext y
    by_cases hy : y∈boxUnion (slices S x)
    · simp only [I,Set.indicator_of_mem hy,Set.indicator_of_mem ((mem_slices S x y).mp hy)]
    · simp only [I,Set.indicator_of_notMem hy,Set.indicator_of_notMem (mt (mem_slices S x y).mpr hy)]
  have hm (x : ℝ) : (∫ y,I (Fin.cons x y))=marginal S F x := by
    rw [hind x,integral_indicator (boxUnion_measurable _)]; rfl
  refine ⟨?_,?_⟩
  · simpa only [hm] using hpull.integral_prod_left
  · have hprod := integral_prod (fun p : ℝ × (Fin q → ℝ) => I (Fin.cons p.1 p.2)) hpull
    simp only [hm] at hprod
    rw [← hprod]
    have heq := hp.integral_comp' I
    simp only [he,Measure.volume_eq_prod] at heq
    rw [heq,integral_indicator (boxUnion_measurable S)]

end
end Contingency.Interpolation

 

 

open Set
namespace Contingency.Interpolation
noncomputable section

 

def nextEndpoint (E : Finset ℝ) (x : ℝ) : ℝ :=
  if h : (E.filter (x < ·)).Nonempty then (E.filter (x < ·)).min' h else x

theorem nextEndpoint_le (E : Finset ℝ) (x y : ℝ) (hy : y∈E) (hxy : x<y) :
    nextEndpoint E x ≤ y := by
  classical
  have h : (E.filter (x < ·)).Nonempty := ⟨y,Finset.mem_filter.mpr ⟨hy,hxy⟩⟩
  simp only [nextEndpoint,dite_eq_left h]
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hy,hxy⟩)

theorem nextEndpoint_gt (E : Finset ℝ) (x : ℝ) (h : ∃ y∈E,x<y) :
    x < nextEndpoint E x := by
  classical
  have hh : (E.filter (x < ·)).Nonempty := by simpa only [Finset.nonempty_def,Finset.mem_filter] using h
  simp only [nextEndpoint,dite_eq_left hh]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ hh)).2

theorem nextEndpoint_mem (E : Finset ℝ) (x : ℝ) (h : x < nextEndpoint E x) :
    nextEndpoint E x∈E := by
  classical
  unfold nextEndpoint at *
  split_ifs at * with hh
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hh)).1
  · exact False.elim (lt_irrefl _ h)

theorem endpoint_not_between (E : Finset ℝ) (l e : ℝ) (he : e∈E) :
    e ≤ l ∨ nextEndpoint E l ≤ e := by
  rcases le_or_gt e l with hh|hh
  · exact Or.inl hh
  · exact Or.inr (nextEndpoint_le E l e he hh)

 
theorem endpoint_comparisons (E : Finset ℝ) (l x y e : ℝ)
    (hx : x∈Ioo l (nextEndpoint E l)) (hy : y∈Ioo l (nextEndpoint E l)) (he : e∈E) :
    (e<x ↔ e<y) ∧ (x<e ↔ y<e) := by
  rcases hx with ⟨hxl,hxu⟩
  rcases hy with ⟨hyl,hyu⟩
  rcases endpoint_not_between E l e he with hh|hh <;> constructor <;> constructor <;> intro h <;> linarith

 

theorem grid_covers (E : Finset ℝ) (x a b : ℝ) (ha : a∈E) (hb : b∈E)
    (hax : a<x) (hxb : x<b) (hx : x∉E) :
    ∃ l∈E,x∈Ioo l (nextEndpoint E l) := by
  classical
  let L := E.filter (· < x)
  have hL : L.Nonempty := ⟨a,Finset.mem_filter.mpr ⟨ha,hax⟩⟩
  let l := L.max' hL
  have hl : l∈E ∧ l<x := Finset.mem_filter.mp (Finset.max'_mem _ hL)
  have hnext : l<nextEndpoint E l := nextEndpoint_gt E l ⟨b,hb,hl.2.trans hxb⟩
  refine ⟨l,hl.1,hl.2,?_⟩
  by_contra hh
  have hnle : nextEndpoint E l ≤ x := le_of_not_gt hh
  have hnmem := nextEndpoint_mem E l hnext
  have hnlt : nextEndpoint E l<x := lt_of_le_of_ne hnle (by intro he; exact hx (he ▸ hnmem))
  have hmax : nextEndpoint E l ≤ l := Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hnmem,hnlt⟩)
  exact not_lt_of_ge hmax hnext

end
end Contingency.Interpolation

 

 

open Set MeasureTheory Filter
open scoped Topology
namespace Contingency.Interpolation
noncomputable section

 

theorem interval_inverse (C C' : ℝ → ℝ) (a b : ℝ) (hab : a<b)
    (hc : ContinuousOn C (Icc a b)) (hm : StrictMonoOn C (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt C (C' x) x)
    (hp : ∀ x ∈ Ioo a b, 0<C' x) :
    ∃ Q : ℝ → ℝ,
      StrictMonoOn Q (Ioo (C a) (C b)) ∧
      Q '' Ioo (C a) (C b)=Ioo a b ∧
      (∀ y ∈ Ioo (C a) (C b), C (Q y)=y ∧ Q y∈Ioo a b ∧
        HasDerivAt Q (C' (Q y))⁻¹ y) := by
  have hi := hc.image_Ioo_of_strictMonoOn hab.le hm
  let Q := Function.invFunOn C (Ioo a b)
  have hq y (hy : y∈Ioo (C a) (C b)) : Q y∈Ioo a b ∧ C (Q y)=y := by
    rw [← hi] at hy
    exact Function.invFunOn_pos hy
  have hmono : StrictMonoOn Q (Ioo (C a) (C b)) := by
    intro x hx y hy hxy
    have hxq := hq x hx
    have hyq := hq y hy
    apply (hm.lt_iff_lt (Ioo_subset_Icc_self hxq.1) (Ioo_subset_Icc_self hyq.1)).mp
    simpa only [hxq.2,hyq.2] using hxy
  have himage : Q '' Ioo (C a) (C b)=Ioo a b := by
    apply Subset.antisymm
    · rintro _ ⟨y,hy,rfl⟩; exact (hq y hy).1
    · intro x hx
      have hcx : C x∈Ioo (C a) (C b) := hi ▸ mem_image_of_mem C hx
      refine ⟨C x,hcx,?_⟩
      exact hm.injOn (Ioo_subset_Icc_self (hq (C x) hcx).1) (Ioo_subset_Icc_self hx) (hq _ hcx).2
  refine ⟨Q,hmono,himage,fun y hy => ?_⟩
  obtain ⟨hyq,heq⟩ := hq y hy
  have hcont : ContinuousAt Q y := by
    apply hmono.continuousAt_of_image_mem_nhds (isOpen_Ioo.mem_nhds hy)
    rw [himage]
    exact isOpen_Ioo.mem_nhds hyq
  refine ⟨heq,hyq,?_⟩
  apply (hd _ hyq).of_local_left_inverse hcont (hp _ hyq).ne'
  filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
  exact (hq z hz).2

 

theorem positive_quantile (F : ℝ → ℝ) (a b : ℝ) (hab : a<b)
    (hc : ContinuousOn F (Icc a b)) (hp : ∀ x∈Icc a b,0<F x) :
    let M := ∫ x in a..b,F x
    0<M ∧ ∃ Q : ℝ → ℝ,
      StrictMonoOn Q (Ioo 0 1) ∧ Q '' Ioo 0 1=Ioo a b ∧
      ∀ y∈Ioo 0 1, Q y∈Ioo a b ∧ HasDerivAt Q (M/F (Q y)) y := by
  let M := ∫ x in a..b,F x
  have hM : 0<M := intervalIntegral.integral_pos hab hc
    (fun x hx => (hp x (Ioc_subset_Icc_self hx)).le) ⟨a,left_mem_Icc.mpr hab.le,hp a (left_mem_Icc.mpr hab.le)⟩
  let C := fun x => (∫ t in a..x,F t)/M
  have hi : IntervalIntegrable F volume a b := hc.intervalIntegrable_of_Icc hab.le
  have hci : ContinuousOn (fun x => ∫ t in a..x,F t) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using intervalIntegral.continuousOn_primitive_interval' hi (left_mem_uIcc : a∈uIcc a b)
  have hC : ContinuousOn C (Icc a b) := hci.div_const M
  have hmono : StrictMonoOn C (Icc a b) := by
    intro x hx y hy hxy
    apply (div_lt_div_iff_of_pos_right hM).mpr
    have hxint : IntervalIntegrable F volume a x := hi.mono_set (by
      simp only [uIcc_of_le hab.le,uIcc_of_le hx.1]; exact Icc_subset_Icc le_rfl hx.2)
    have hyint : IntervalIntegrable F volume x y := hi.mono_set (by
      simp only [uIcc_of_le hab.le,uIcc_of_le hxy.le]; exact Icc_subset_Icc hx.1 hy.2)
    have he := intervalIntegral.integral_add_adjacent_intervals hxint hyint
    have hpos : 0<∫ t in x..y,F t := intervalIntegral.integral_pos hxy
      (hc.mono (Icc_subset_Icc hx.1 hy.2))
      (fun z hz => (hp z ⟨hx.1.trans hz.1.le,hz.2.trans hy.2⟩).le)
      ⟨x,left_mem_Icc.mpr hxy.le,hp x hx⟩
    linarith only [he,hpos]
  have hder (x) (hx : x∈Ioo a b) : HasDerivAt C (F x/M) x := by
    have hint : IntervalIntegrable F volume a x := hi.mono_set (by
      simp only [uIcc_of_le hab.le,uIcc_of_le hx.1.le]; exact Icc_subset_Icc le_rfl hx.2.le)
    have hfc : ContinuousAt F x := hc.continuousAt (Icc_mem_nhds hx.1 hx.2)
    apply HasDerivAt.div_const
    exact intervalIntegral.integral_hasDerivAt_right hint
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hc.mono Ioo_subset_Icc_self) x hx) hfc
  have hCa : C a=0 := by simp [C]
  have hCb : C b=1 := by simp [C,M,hM.ne']
  obtain ⟨Q,hqm,hqi,hqd⟩ := interval_inverse C (fun x => F x/M) a b hab hC hmono hder
    (fun x hx => div_pos (hp x (Ioo_subset_Icc_self hx)) hM)
  rw [hCa,hCb] at hqm hqi hqd
  refine ⟨hM,Q,hqm,hqi,fun y hy => ?_⟩
  have hh := hqd y hy
  refine ⟨hh.2.1,?_⟩
  simpa only [inv_div] using hh.2.2

 

theorem transport_amgm (M N F G α β : ℝ) (hM : 0<M) (hN : 0<N)
    (hF : 0<F) (hG : 0<G) (ha : 0 ≤ α) (hb : 0 ≤ β) (hab : α+β=1) :
    M^α*N^β ≤ F^α*G^β*(α*(M/F)+β*(N/G)) := by
  have hh := Real.geom_mean_le_arith_mean2_weighted ha hb
    (div_pos hM hF).le (div_pos hN hG).le hab
  have havehe : F^α*G^β*((M/F)^α*(N/G)^β)=M^α*N^β := by
    rw [Real.div_rpow hM.le hF.le,Real.div_rpow hN.le hG.le]
    field_simp [(Real.rpow_pos_of_pos hF α).ne',(Real.rpow_pos_of_pos hG β).ne']
  rw [← havehe]
  exact mul_le_mul_of_nonneg_left hh (mul_nonneg (Real.rpow_nonneg hF.le _) (Real.rpow_nonneg hG.le _))

end
end Contingency.Interpolation

 

 

open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Contingency.Interpolation
noncomputable section
variable {n : ℕ}

def prefixMass (m : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => j < i), m j

def totalMass (m : Fin n → ℝ) : ℝ := ∑ i,m i

theorem prefix_nonneg (m : Fin n → ℝ) (hm : ∀ i,0 ≤ m i) (i : Fin n) :
    0 ≤ prefixMass m i := Finset.sum_nonneg fun j _ => hm j

theorem prefix_next_le (m : Fin n → ℝ) (hm : ∀ i,0 ≤ m i) (i j : Fin n) (hij : i<j) :
    prefixMass m i+m i ≤ prefixMass m j := by
  classical
  have he : prefixMass m i+m i=∑ k ∈ insert i (Finset.univ.filter fun k => k < i),m k := by
    rw [Finset.sum_insert (by simp)]
    simp only [prefixMass]; ring
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    rcases Finset.mem_insert.mp hk with rfl|hk
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hk).2.trans hij⟩
  · intro k _ _; exact hm k

theorem prefix_add_le_total (m : Fin n → ℝ) (hm : ∀ i,0 ≤ m i) (i : Fin n) :
    prefixMass m i+m i ≤ totalMass m := by
  classical
  have he : prefixMass m i+m i=∑ k ∈ insert i (Finset.univ.filter fun k => k < i),m k := by
    rw [Finset.sum_insert (by simp)]
    simp only [prefixMass]; ring
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hm k)

def probabilityPiece (m : Fin n → ℝ) (i : Fin n) : Set ℝ :=
  Ioo (prefixMass m i/totalMass m) ((prefixMass m i+m i)/totalMass m)

theorem probabilityPiece_subset (m : Fin n → ℝ) (hm : ∀ i,0 ≤ m i)
    (hM : 0<totalMass m) (i : Fin n) : probabilityPiece m i ⊆ Ioo 0 1 := by
  intro t ht
  refine ⟨(div_nonneg (prefix_nonneg m hm i) hM.le).trans_lt ht.1,ht.2.trans_le ?_⟩
  exact (div_le_one hM).mpr (prefix_add_le_total m hm i)

theorem probabilityPiece_disjoint (m : Fin n → ℝ) (hm : ∀ i,0 ≤ m i)
    (hM : 0<totalMass m) : Pairwise (fun i j => Disjoint (probabilityPiece m i) (probabilityPiece m j)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij|hij
  · apply disjoint_left.mpr
    intro t ht1 ht2
    have hh := div_le_div_of_nonneg_right (prefix_next_le m hm i j hij) hM.le
    exact not_lt_of_ge (ht1.2.le.trans hh) ht2.1
  · apply disjoint_left.mpr
    intro t ht1 ht2
    have hh := div_le_div_of_nonneg_right (prefix_next_le m hm j i hij) hM.le
    exact not_lt_of_ge (ht2.2.le.trans hh) ht1.1

 

theorem probabilityPieces_volume (m : Fin n → ℝ) (hm : ∀ i,0 ≤ m i)
    (hM : 0<totalMass m) : volume (⋃ i,probabilityPiece m i)=1 := by
  rw [measure_iUnion (probabilityPiece_disjoint m hm hM) (fun i => measurableSet_Ioo)]
  simp only [tsum_fintype,probabilityPiece,Real.volume_Ioo]
  have he (i) : (prefixMass m i+m i)/totalMass m-prefixMass m i/totalMass m=m i/totalMass m := by ring
  simp only [he]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (hm i) hM.le),← Finset.sum_div]
  change ENNReal.ofReal (totalMass m / totalMass m) = 1
  rw [div_self hM.ne', ENNReal.ofReal_one]

end
end Contingency.Interpolation

end

end OAI
