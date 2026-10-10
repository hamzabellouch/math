import Mathlib
import OAI.Algebra.FiniteTensor.ComplementaryGraphs

namespace OAI

/-! Formal graph charts, compatible moving coordinates and actual gradient ideals. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (K ι υ σ τ : Type*) [Field K] [Fintype ι]
  [Fintype υ] [DecidableEq υ] [Fintype σ] [Fintype τ]
  (a : ι → ℕ) (p : ℕ) [Fact p.Prime] [CharP K p]
  (ha : ∀ i,0<a i) (hap : ∀ i,a i≤p) (e : υ ≃ σ ⊕ τ)

include hap in
 

theorem exists_formal_left_chart
    (H : υ → MvPowerSeries σ (Ring K ι a))
    (G : υ → MvPowerSeries τ (Ring K ι a))
    (hH : ∀ i,constantMap K ι a ha (MvPowerSeries.constantCoeff (H i))=0)
    (hG : ∀ i,MvPowerSeries.constantCoeff (G i)=0)
    (hdet : Matrix.det (fun i j => constantMap K ι a ha
      (MvPowerSeries.coeff (Finsupp.single j 1) (combinedGraph (Ring K ι a) υ σ τ e H G i)))≠0) :
    ∃ q : Ring (Ring K ι a) υ (fun _ => p) ≃ₐ[Ring K ι a] Ring (Ring K ι a) υ (fun _ => p),
      ∀ i, splitRestriction (Fact.out : p.Prime).pos e q
        (coord (Ring K ι a) υ (fun _ => p) i)=
        nilEval (Ring K ι a) (coord (Ring K ι a) σ (fun _ => p))
          (fun j => ⟨p,coord_pow _ _ _ j⟩) (H i) := by
  let c := combinedGraph (Ring K ι a) υ σ τ e H G
  have hc (i : υ) : constantMap K ι a ha (MvPowerSeries.constantCoeff (c i))=0 := by
    simp only [c,combinedGraph_constantCoeff,hG,add_zero,hH]
  let q := AlgEquiv.ofBijective (movingSubst K ι υ a p ha hap c hc)
    (movingSubst_bijective K ι υ a p ha hap c hc hdet)
  refine ⟨q,?_⟩
  intro i
  change planeRestriction (Ring K ι a) υ σ τ p e (Fact.out : p.Prime).pos
    (movingSubst K ι υ a p ha hap c hc (coord (Ring K ι a) υ (fun _ => p) i))=_
  rw [movingSubst_coord]
  exact combinedGraph_eval_left (Ring K ι a) υ σ τ p e (Fact.out : p.Prime).pos H G hG i

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (K R S υ : Type*) [Field K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] (a : υ → ℕ)

theorem substitution_specialization (r : R →ₐ[K] S)
    (f : Ring R υ a →ₐ[R] Ring R υ a) (g : Ring S υ a →ₐ[S] Ring S υ a)
    (h : ∀ i, coefficientHom K R S υ a r (f (coord R υ a i))=
      g (coord S υ a i)) (v : Ring R υ a) :
    coefficientHom K R S υ a r (f v)=g (coefficientHom K R S υ a r v) := by
  have heq : (coefficientHom K R S υ a r).comp (f.restrictScalars K)=
      (g.restrictScalars K).comp (coefficientHom K R S υ a r) := by
    apply Ideal.Quotient.algHom_ext
    apply AlgHom.coe_ringHom_injective
    apply MvPolynomial.ringHom_ext
    · intro b
      change coefficientHom K R S υ a r (f (algebraMap R (Ring R υ a) b))=
        g (coefficientHom K R S υ a r (algebraMap R (Ring R υ a) b))
      rw [f.commutes,coefficientHom_scalar,g.commutes]
    · intro i
      change coefficientHom K R S υ a r (f (coord R υ a i))=
        g (coefficientHom K R S υ a r (coord R υ a i))
      rw [coefficientHom_coord]
      exact h i
  exact AlgHom.congr_fun heq v

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (K ι υ : Type*) [Field K] [Fintype ι]
  [Fintype υ] [DecidableEq υ] (a : ι → ℕ) (p : ℕ) [Fact p.Prime] [CharP K p]
  (ha : ∀ i,0<a i) (hap : ∀ i,a i≤p)
  (c : υ → MvPowerSeries υ (Ring K ι a))
  (hc : ∀ i, constantMap K ι a ha (MvPowerSeries.constantCoeff (c i))=0)
  (hM : Matrix.det (fun i j => constantMap K ι a ha
    (MvPowerSeries.coeff (Finsupp.single j 1) (c i)))≠0)

def movingChart : Ring (Ring K ι a) υ (fun _ => p) ≃ₐ[Ring K ι a]
    Ring (Ring K ι a) υ (fun _ => p) :=
  AlgEquiv.ofBijective (movingSubst K ι υ a p ha hap c hc)
    (movingSubst_bijective K ι υ a p ha hap c hc hM)

def centralChart : Ring K υ (fun _ => p) ≃ₐ[K] Ring K υ (fun _ => p) :=
  AlgEquiv.ofBijective (FrobeniusTruncation.formalSubst K υ p
    (fun i => MvPowerSeries.map (constantMap K ι a ha).toRingHom (c i)) hc)
    (FrobeniusTruncation.formalSubst_bijective K υ p _ hc hM)

 
theorem movingChart_specialization (v : Ring (Ring K ι a) υ (fun _ => p)) :
    coefficientHom K (Ring K ι a) K υ (fun _ => p) (constantMap K ι a ha)
      (movingChart K ι υ a p ha hap c hc hM v)=
    centralChart K ι υ a p ha c hc hM
      (coefficientHom K (Ring K ι a) K υ (fun _ => p) (constantMap K ι a ha) v) := by
  refine substitution_specialization K (Ring K ι a) K υ (fun _ => p)
    (constantMap K ι a ha) (movingChart K ι υ a p ha hap c hc hM).toAlgHom
    (centralChart K ι υ a p ha c hc hM).toAlgHom ?_ v
  intro i
  change coefficientHom K (Ring K ι a) K υ (fun _ => p) (constantMap K ι a ha)
    (movingSubst K ι υ a p ha hap c hc (coord (Ring K ι a) υ (fun _ => p) i))=
    FrobeniusTruncation.formalSubst K υ p _ hc (coord K υ (fun _ => p) i)
  rw [←specialization_eq_coefficientHom,movingSubst_central]
  exact (FrobeniusTruncation.formalSubst_coord K υ p
    (fun i => MvPowerSeries.map (constantMap K ι a ha).toRingHom (c i)) hc i).symm

include ha in
omit [Fintype ι] [Fintype υ] [DecidableEq υ] [Fact p.Prime] in
theorem coefficientRingCharP : CharP (Ring K ι a) p := by
  apply charP_of_injective_ringHom (f:=algebraMap K (Ring K ι a))
  apply Function.LeftInverse.injective (g:=constantMap K ι a ha)
  intro b
  exact (constantMap K ι a ha).commutes b

variable [CharP (Ring K ι a) p] {σ : Type*} {d : ℕ}

theorem movingChart_normal_specialization (e : υ ≃ σ ⊕ Fin d) :
    Forms.mapCoefficients K (Ring (Ring K ι a) υ (fun _ => p)) (Ring K υ (fun _ => p)) υ
      (coefficientHom K (Ring K ι a) K υ (fun _ => p) (constantMap K ι a ha))
      (chartNormal K (Ring K ι a) υ p e (movingChart K ι υ a p ha hap c hc hM))=
    chartNormal K K υ p e (centralChart K ι υ a p ha c hc hM) := by
  apply chartNormal_specialization
  exact movingChart_specialization K ι υ a p ha hap c hc hM

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (R S υ σ τ : Type*) [CommRing R] [CommRing S] [Fintype σ] [Fintype τ]
  (e : υ ≃ σ ⊕ τ)

theorem combinedGraph_map (r : R →+* S) (H : υ → MvPowerSeries σ R)
    (G : υ → MvPowerSeries τ R) (i : υ) :
    MvPowerSeries.map r (combinedGraph R υ σ τ e H G i)=
      combinedGraph S υ σ τ e (fun i => MvPowerSeries.map r (H i))
        (fun i => MvPowerSeries.map r (G i)) i := by
  simp only [combinedGraph,map_add,←MvPowerSeries.rename_map]

theorem combinedGraph_swap (H : υ → MvPowerSeries σ R) (G : υ → MvPowerSeries τ R) :
    combinedGraph R υ τ σ (e.trans (Equiv.sumComm _ _)) G H=
      combinedGraph R υ σ τ e H G := by
  funext i
  change MvPowerSeries.rename (fun j => e.symm (Sum.inr j)) (G i)+
    MvPowerSeries.rename (fun j => e.symm (Sum.inl j)) (H i)=_
  exact add_comm _ _

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (K υ : Type*) [Field K] [Fintype υ] [DecidableEq υ] (p : ℕ)
  [Fact p.Prime] [CharP K p]

 
def fixedChart (c0 : υ → MvPowerSeries υ K)
    (h0 : ∀ i,MvPowerSeries.constantCoeff (c0 i)=0)
    (hM : Matrix.det (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (c0 i))≠0) :
    Ring K υ (fun _ => p) ≃ₐ[K] Ring K υ (fun _ => p) :=
  AlgEquiv.ofBijective (FrobeniusTruncation.formalSubst K υ p c0 h0)
    (FrobeniusTruncation.formalSubst_bijective K υ p c0 h0 hM)

@[simp] theorem fixedChart_coord (c0 : υ → MvPowerSeries υ K)
    (h0 : ∀ i,MvPowerSeries.constantCoeff (c0 i)=0)
    (hM : Matrix.det (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (c0 i))≠0) (i : υ) :
    fixedChart K υ p c0 h0 hM (coord K υ (fun _ => p) i)=
      nilEval K (coord K υ (fun _ => p)) (fun j => ⟨p,coord_pow _ _ _ j⟩) (c0 i) := by
  exact FrobeniusTruncation.formalSubst_coord K υ p c0 h0 i

variable (ι : Type*) [Fintype ι] (a : ι → ℕ)
  (ha : ∀ i,0<a i) (hap : ∀ i,a i≤p)

include hap in
 

theorem compatible_moving_chart
    (c0 : υ → MvPowerSeries υ K)
    (h0 : ∀ i,MvPowerSeries.constantCoeff (c0 i)=0)
    (hM : Matrix.det (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (c0 i))≠0)
    (c : υ → MvPowerSeries υ (Ring K ι a))
    (hc : ∀ i,MvPowerSeries.map (constantMap K ι a ha).toRingHom (c i)=c0 i) :
    ∃ q : Ring (Ring K ι a) υ (fun _ => p) ≃ₐ[Ring K ι a] Ring (Ring K ι a) υ (fun _ => p),
      (∀ i,q (coord (Ring K ι a) υ (fun _ => p) i)=
        nilEval (Ring K ι a) (coord (Ring K ι a) υ (fun _ => p))
          (fun j => ⟨p,coord_pow _ _ _ j⟩) (c i)) ∧
      ∀ v,coefficientHom K (Ring K ι a) K υ (fun _ => p) (constantMap K ι a ha) (q v)=
        fixedChart K υ p c0 h0 hM
          (coefficientHom K (Ring K ι a) K υ (fun _ => p) (constantMap K ι a ha) v) := by
  have hcz (i : υ) : constantMap K ι a ha (MvPowerSeries.constantCoeff (c i))=0 := by
    have hh := congrArg MvPowerSeries.constantCoeff (hc i)
    exact hh.trans (h0 i)
  have hcM : Matrix.det (fun i j => constantMap K ι a ha
      (MvPowerSeries.coeff (Finsupp.single j 1) (c i)))≠0 := by
    convert hM using 1
    congr 1
    funext i j
    exact congrArg (MvPowerSeries.coeff (Finsupp.single j 1)) (hc i)
  let q := movingChart K ι υ a p ha hap c hcz hcM
  refine ⟨q,?_,?_⟩
  · intro i
    exact movingSubst_coord K ι υ a p ha hap c hcz i
  · intro v
    refine substitution_specialization K (Ring K ι a) K υ (fun _ => p)
      (constantMap K ι a ha) q.toAlgHom (fixedChart K υ p c0 h0 hM).toAlgHom ?_ v
    intro i
    change coefficientHom K (Ring K ι a) K υ (fun _ => p) (constantMap K ι a ha)
      (q (coord (Ring K ι a) υ (fun _ => p) i))=
      fixedChart K υ p c0 h0 hM (coord K υ (fun _ => p) i)
    change coefficientHom K (Ring K ι a) K υ (fun _ => p) (constantMap K ι a ha)
      (movingSubst K ι υ a p ha hap c hcz (coord (Ring K ι a) υ (fun _ => p) i))=_
    rw [←specialization_eq_coefficientHom,movingSubst_central,hc i]
    exact (fixedChart_coord K υ p c0 h0 hM i).symm

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (K υ σ τ : Type*) [Field K] [Fintype υ] [DecidableEq υ]
  [Fintype σ] [Fintype τ]
  (p : ℕ) [Fact p.Prime] [CharP K p]
  (ι : Type*) [Fintype ι] (a : ι → ℕ)
  (ha : ∀ i,0<a i) (hap : ∀ i,a i≤p) (e : υ ≃ σ ⊕ τ)

include hap in
 

theorem compatible_graph_charts
    (H0 : υ → MvPowerSeries σ K) (G : υ → MvPowerSeries τ K)
    (hH0 : ∀ i,MvPowerSeries.constantCoeff (H0 i)=0)
    (hG : ∀ i,MvPowerSeries.constantCoeff (G i)=0)
    (hL : Function.Injective (Matrix.mulVecLin
      (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (H0 i))))
    (hR : Function.Injective (Matrix.mulVecLin
      (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (G i))))
    (hcomp : IsCompl (Matrix.mulVecLin
      (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (H0 i))).range
      (Matrix.mulVecLin (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (G i))).range) :
    ∃ q0 : Ring K υ (fun _ => p) ≃ₐ[K] Ring K υ (fun _ => p),
      (∀ i,splitRestriction (Fact.out : p.Prime).pos e q0 (coord K υ (fun _ => p) i)=
        nilEval K (coord K σ (fun _ => p)) (fun j => ⟨p,coord_pow _ _ _ j⟩) (H0 i)) ∧
      (∀ i,splitRestriction (Fact.out : p.Prime).pos (e.trans (Equiv.sumComm _ _)) q0
          (coord K υ (fun _ => p) i)=
        nilEval K (coord K τ (fun _ => p)) (fun j => ⟨p,coord_pow _ _ _ j⟩) (G i)) ∧
      ∀ H : υ → MvPowerSeries σ (Ring K ι a),
        (∀ i,MvPowerSeries.map (constantMap K ι a ha).toRingHom (H i)=H0 i) →
        ∃ q : Ring (Ring K ι a) υ (fun _ => p) ≃ₐ[Ring K ι a] Ring (Ring K ι a) υ (fun _ => p),
          (∀ i,splitRestriction (Fact.out : p.Prime).pos e q
              (coord (Ring K ι a) υ (fun _ => p) i)=
            nilEval (Ring K ι a) (coord (Ring K ι a) σ (fun _ => p))
              (fun j => ⟨p,coord_pow _ _ _ j⟩) (H i)) ∧
          ∀ v,coefficientHom K (Ring K ι a) K υ (fun _ => p) (constantMap K ι a ha) (q v)=
            q0 (coefficientHom K (Ring K ι a) K υ (fun _ => p) (constantMap K ι a ha) v) := by
  let c0 := combinedGraph K υ σ τ e H0 G
  have hz (i : υ) : MvPowerSeries.constantCoeff (c0 i)=0 := by
    simp only [c0,combinedGraph_constantCoeff,hH0,hG,add_zero]
  have hM : Matrix.det (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (c0 i))≠0 :=
    combinedGraph_central_tangent K υ σ τ e (RingHom.id K) H0 G hL hR hcomp
  let q0 := fixedChart K υ p c0 hz hM
  refine ⟨q0,?_,?_,?_⟩
  · intro i
    change planeRestriction K υ σ τ p e (Fact.out : p.Prime).pos
      (q0 (coord K υ (fun _ => p) i))=_
    rw [fixedChart_coord]
    exact combinedGraph_eval_left K υ σ τ p e (Fact.out : p.Prime).pos H0 G hG i
  · intro i
    change planeRestriction K υ τ σ p (e.trans (Equiv.sumComm _ _)) (Fact.out : p.Prime).pos
      (q0 (coord K υ (fun _ => p) i))=_
    rw [fixedChart_coord]
    change planeRestriction K υ τ σ p (e.trans (Equiv.sumComm _ _)) (Fact.out : p.Prime).pos
      (nilEval K (coord K υ (fun _ => p)) _ (combinedGraph K υ σ τ e H0 G i))=_
    rw [←combinedGraph_swap K υ σ τ e H0 G]
    exact combinedGraph_eval_left K υ τ σ p (e.trans (Equiv.sumComm _ _))
      (Fact.out : p.Prime).pos G H0 hH0 i
  · intro H hH
    let G' := fun i => MvPowerSeries.map (algebraMap K (Ring K ι a)) (G i)
    let c := combinedGraph (Ring K ι a) υ σ τ e H G'
    have hG' (i : υ) : MvPowerSeries.constantCoeff (G' i)=0 := by
      simp only [G',MvPowerSeries.constantCoeff_map,hG,map_zero]
    have hc (i : υ) : MvPowerSeries.map (constantMap K ι a ha).toRingHom (c i)=c0 i := by
      rw [combinedGraph_map]
      have hh : (fun i => MvPowerSeries.map (constantMap K ι a ha).toRingHom (H i))=H0 := funext hH
      rw [hh]
      congr 1
      funext j
      ext d
      simp only [G',MvPowerSeries.coeff_map]
      exact (constantMap K ι a ha).commutes (MvPowerSeries.coeff d (G j))
    obtain ⟨q,hq,hs⟩ := compatible_moving_chart K υ p ι a ha hap c0 hz hM c hc
    refine ⟨q,?_,hs⟩
    intro i
    change planeRestriction (Ring K ι a) υ σ τ p e (Fact.out : p.Prime).pos
      (q (coord (Ring K ι a) υ (fun _ => p) i))=_
    rw [hq]
    exact combinedGraph_eval_left (Ring K ι a) υ σ τ p e (Fact.out : p.Prime).pos H G' hG' i

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (K : Type*) [Field K] (m : ℕ)

 

theorem constantMap_parameters :
    constantMap K (Fin m) (fun _ => 2) (fun _ => by decide)=augmentationAlg K m := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change constantMap K (Fin m) (fun _ => 2) (fun _ => by decide)
    (coord K (Fin m) (fun _ => 2) i)=augmentation K m (t K m i)
  rw [constantMap_coord,augmentation_t]

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor
noncomputable section
variable (K : Type*) [Field K] (m : ℕ) {υ σ : Type*} [Finite υ]

 
theorem parameter_hasSubst (H : υ → MvPowerSeries σ (T K m))
    (hH : ∀ i,augmentation K m (MvPowerSeries.constantCoeff (H i))=0) :
    MvPowerSeries.HasSubst H := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
  intro i
  apply mem_nilradical.mp
  apply parameterIdeal_le_nilradical
  have hh := sub_constant_mem K m (MvPowerSeries.constantCoeff (H i))
  simpa only [hH,map_zero,sub_zero] using hh

end
end PD4Tensor

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (K R υ σ τ : Type*) [Field K] [CommRing R] [Algebra K R]
  [Fintype υ] [DecidableEq υ] [Fintype σ] (p : ℕ)

 
theorem graph_zero (hp : 0<p) (e : υ ≃ σ ⊕ τ)
    (q : Ring R υ (fun _ => p) ≃ₐ[R] Ring R υ (fun _ => p))
    (H : υ → MvPowerSeries σ R) (hH : MvPowerSeries.HasSubst H)
    (hq : ∀ i,splitRestriction hp e q (coord R υ (fun _ => p) i)=
      nilEval R (coord R σ (fun _ => p)) (fun j => ⟨p,coord_pow _ _ _ j⟩) (H i))
    (S : MvPowerSeries υ R) (hS : MvPowerSeries.subst H S=0) :
    splitRestriction hp e q
      (nilEval R (coord R υ (fun _ => p)) (fun j => ⟨p,coord_pow _ _ _ j⟩) S)=0 := by
  rw [graph_eval H hH _ _ (splitRestriction hp e q) hq,hS,map_zero]

variable [CharP R p]

theorem graph_gradient (hp : 0<p) (e : υ ≃ σ ⊕ τ)
    (q : Ring R υ (fun _ => p) ≃ₐ[R] Ring R υ (fun _ => p))
    (H : υ → MvPowerSeries σ R) (hH : MvPowerSeries.HasSubst H)
    (hq : ∀ i,splitRestriction hp e q (coord R υ (fun _ => p) i)=
      nilEval R (coord R σ (fun _ => p)) (fun j => ⟨p,coord_pow _ _ _ j⟩) (H i))
    (S a : MvPowerSeries υ R)
    (ha : MvPowerSeries.subst H a∈Ideal.span
      (Set.range (fun i => MvPowerSeries.subst H (MvPowerSeries.pderiv i S)))) :
    splitRestriction hp e q
      (nilEval R (coord R υ (fun _ => p)) (fun j => ⟨p,coord_pow _ _ _ j⟩) a) ∈
      Ideal.span (Set.range (fun i => splitRestriction hp e q
        (chartDerivative K R υ p i
          (nilEval R (coord R υ (fun _ => p)) (fun j => ⟨p,coord_pow _ _ _ j⟩) S)))) := by
  have hh := ideal_span_range_map
    (nilEval R (coord R σ (fun _ => p)) (fun j => ⟨p,coord_pow _ _ _ j⟩)).toRingHom
    _ _ ha
  change nilEval R (coord R σ (fun _ => p)) _ (MvPowerSeries.subst H a) ∈
    Ideal.span (Set.range (fun i =>
      nilEval R (coord R σ (fun _ => p)) _ (MvPowerSeries.subst H (MvPowerSeries.pderiv i S)))) at hh
  change splitRestriction hp e q (nilEval R (coord R υ (fun _ => p)) _ a) ∈
    Ideal.span (Set.range (fun i => splitRestriction hp e q
      (relativeDeriv R υ p i (nilEval R (coord R υ (fun _ => p)) _ S))))
  simp only [partial_nilEval,graph_eval H hH _ _ (splitRestriction hp e q) hq]
  exact hh

end
end PD4Tensor.FiniteCoordinates
end

end OAI
