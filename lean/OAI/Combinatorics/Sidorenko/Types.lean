import OAI.Combinatorics.Sidorenko.Coefficients

namespace OAI


section

namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section MatrixActivation
variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]

noncomputable def sampleMatrixKernel (r : ℕ) (z : Activation K)
    (x y : K → SymMatrix F (2*r)) : ℝ :=
  ∏ κ∈z.1,rankKernel F (2*r) r (if z.2 κ then 1 else -1) (x κ-y κ)
noncomputable def activationMatrixKernel (r : ℕ) (p : FiniteLaw (Activation K))
    (x y : K → SymMatrix F (2*r)) : ℝ := p.mean (fun z => sampleMatrixKernel r z x y)
noncomputable def matrixSampleProduct (r : ℕ) (z : ActCorner → Activation K)
    (x : Fin 13 → K → SymMatrix F (2*r)) (y : Fin 22 → K → SymMatrix F (2*r)) : ℝ :=
  ∏ k,sampleMatrixKernel r (z k) (x (cornerPoint k)) (y k.1)
noncomputable def conditionalMatrixMoment (r : ℕ) (p : ActCorner → FiniteLaw (Activation K)) : ℝ :=
  uniformMean (fun xy : (Fin 13 → K → SymMatrix F (2*r)) × (Fin 22 → K → SymMatrix F (2*r)) =>
    ∏ k,activationMatrixKernel r (p k) (xy.1 (cornerPoint k)) (xy.2 k.1))

lemma matrixSampleProduct_coordinates (r : ℕ) (z : ActCorner → Activation K)
    (x : Fin 13 → K → SymMatrix F (2*r)) (y : Fin 22 → K → SymMatrix F (2*r)) :
    matrixSampleProduct r z x y=∏ κ,∏ j,∏ k∈coordinateActive z κ j,
      rankKernel F (2*r) r (coordinateSigns z κ j k) (x (faceVertex j k) κ-y j κ) := by
  unfold matrixSampleProduct sampleMatrixKernel
  have he (k : ActCorner) :
      (∏ κ∈(z k).1,rankKernel F (2*r) r (if (z k).2 κ then 1 else -1) (x (cornerPoint k) κ-y k.1 κ))=
      ∏ κ,if κ∈(z k).1 then rankKernel F (2*r) r (if (z k).2 κ then 1 else -1) (x (cornerPoint k) κ-y k.1 κ) else 1 := by
    simp only [Finset.prod_ite_mem,Finset.univ_inter]
  simp_rw [he]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl; intro κ _
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl; intro j _
  rw [coordinateActive,Finset.prod_filter]
  rfl

lemma coordinateMatrixIntegral (r : ℕ) (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ) :
    uniformMean (fun xy : (Fin 13 → SymMatrix F (2*r)) × (Fin 22 → SymMatrix F (2*r)) =>
      ∏ j,∏ k∈T j,rankKernel F (2*r) r (ξ j k) (xy.1 (faceVertex j k)-xy.2 j))=
      uniformMean (configurationProduct (K := F) r T ξ) := by
  rw [uniformMean_prod]
  apply uniformMean_congr; intro X
  rw [uniformMean_pi_product (fun j Y => ∏ k∈T j,rankKernel F (2*r) r (ξ j k) (X (faceVertex j k)-Y))]
  rfl

lemma matrixSampleProduct_mean (r : ℕ) (z : ActCorner → Activation K) :
    uniformMean (fun xy : (Fin 13 → K → SymMatrix F (2*r)) × (Fin 22 → K → SymMatrix F (2*r)) =>
      matrixSampleProduct r z xy.1 xy.2)=
      ∏ κ,uniformMean (configurationProduct (K := F) r (coordinateActive z κ) (coordinateSigns z κ)) := by
  simp_rw [matrixSampleProduct_coordinates]
  rw [uniformMean_coordinate_factor (fun κ X Y => ∏ j,∏ k∈coordinateActive z κ j,
    rankKernel F (2*r) r (coordinateSigns z κ j k) (X (faceVertex j k)-Y j))]
  simp_rw [coordinateMatrixIntegral]

lemma conditionalMatrixMoment_law (r : ℕ) (p : ActCorner → FiniteLaw (Activation K)) :
    conditionalMatrixMoment (F := F) r p=(FiniteLaw.independent p).mean (fun z =>
      ∏ κ,uniformMean (configurationProduct (K := F) r (coordinateActive z κ) (coordinateSigns z κ))) := by
  unfold conditionalMatrixMoment activationMatrixKernel
  simp_rw [←FiniteLaw.independent_mean_product]
  rw [uniformMean_law_swap]
  apply FiniteLaw.mean_congr; intro z
  exact matrixSampleProduct_mean r z

omit [Fintype K] [DecidableEq K] in
lemma sampleMatrixKernel_nonneg (r : ℕ) (z : Activation K) (x y : K → SymMatrix F (2*r)) :
    0≤ sampleMatrixKernel r z x y := Finset.prod_nonneg (fun _ _ => rankKernel_nonneg ..)
lemma activationMatrixKernel_nonneg (r : ℕ) (p : FiniteLaw (Activation K)) (x y : K → SymMatrix F (2*r)) :
    0≤activationMatrixKernel r p x y := p.mean_nonneg (fun z => sampleMatrixKernel_nonneg r z x y)
end MatrixActivation

lemma configuration_even_rank_limit (r : ℕ) (hl : singularTailThreshold≤2*(2*r))
    (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
    (hξ : ∀ j k,ξ j k=1 ∨ ξ j k= -1) : Tendsto
    (fun q : OddPrime => uniformMean (configurationProduct (K := ZMod q.val) (2*r) T ξ))
    primeInfinity (nhds (uniformMean (boolConfiguration 1 T ξ))) := by
  have hch (q : OddPrime) : (quadraticChar (ZMod q.val) ((-1:ZMod q.val)^(2*r)):ℝ)=1 := by
    rw [Even.neg_one_pow (even_two_mul r)]; simp
  have h₁ := configuration_bool_tendsto (2*r) T ξ hξ hl
  have h₂ := boolTestError_tendsto (2*r) (by have := singularTailThreshold_large; omega) T ξ 1
  simp_rw [hch] at h₁
  have h := (h₁.add h₂).add_const (uniformMean (boolConfiguration 1 T ξ))
  simp only [zero_add,add_zero] at h
  convert h using 1
  funext q
  unfold boolTestError
  ring

lemma conditionalMatrixMoment_tendsto {K : Type*} [Fintype K] [DecidableEq K]
    (r : ℕ) (hl : singularTailThreshold≤2*(2*r)) (p : ActCorner → FiniteLaw (Activation K))
    (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0) : Tendsto
    (fun q : OddPrime => conditionalMatrixMoment (F := ZMod q.val) (2*r) p) primeInfinity
    (nhds (1+activeCoefficient (fun k => activationMoment (p k)))) := by
  have h (z : ActCorner → Activation K) := tendsto_finsetProd Finset.univ (fun κ _ =>
    configuration_even_rank_limit r hl (coordinateActive z κ) (coordinateSigns z κ) (coordinateSigns_good z κ))
  have ht := FiniteLaw.mean_tendsto (FiniteLaw.independent p) _ _ h
  simp only [coordinateModels_product,expandedModel_mean p hp] at ht
  simpa only [conditionalMatrixMoment_law] using ht
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Types
variable {K : Type*} [Fintype K] [DecidableEq K]
noncomputable def inactiveLaw : FiniteLaw (Activation K) := FiniteLaw.dirac (∅,fun _ => false)
omit [Fintype K] in
lemma inactivePhi (α : Finset K) : activationPhi α (∅,fun _ => false)=if α=∅ then 1 else 0 := by
  by_cases he : α=∅
  · subst α; simp
  · simp [activationPhi,Finset.subset_empty,he]
lemma inactiveLaw_zero (α : Finset K) (hα : α≠∅) : inactiveLaw.mean (activationPhi α)=0 := by
  simp only [inactiveLaw,FiniteLaw.mean_dirac,inactivePhi,ite_eq_right hα]
lemma inactiveLaw_moment (α β : Finset K) : activationMoment inactiveLaw α β=if α=∅ ∧ β=∅ then 1 else 0 := by
  simp only [activationMoment,inactiveLaw,FiniteLaw.mean_dirac,inactivePhi]
  by_cases hα : α=∅ <;> by_cases hβ : β=∅ <;> simp [hα,hβ]
noncomputable def thinnedLaw (p : FiniteLaw (Activation K)) (lam : ℝ) (hlam : 0≤lam) (hlam1 : lam≤1) :=
  FiniteLaw.mixture p inactiveLaw lam hlam hlam1
lemma thinnedLaw_zero (p : FiniteLaw (Activation K)) (hp : ∀ α,α≠∅ → p.mean (activationPhi α)=0)
    (lam : ℝ) (hlam : 0≤lam) (hlam1 : lam≤1) (α : Finset K) (hα : α≠∅) :
    (thinnedLaw p lam hlam hlam1).mean (activationPhi α)=0 := by
  rw [thinnedLaw,FiniteLaw.mean_mixture,hp α hα,inactiveLaw_zero α hα]; ring
lemma thinnedLaw_active (p : FiniteLaw (Activation K)) (lam : ℝ) (hlam : 0≤lam) (hlam1 : lam≤1)
    (α β : Finset K) (hα : α≠∅) :
    activationMoment (thinnedLaw p lam hlam hlam1) α β=lam*activationMoment p α β := by
  unfold activationMoment thinnedLaw
  rw [FiniteLaw.mean_mixture]
  have hz : inactiveLaw.mean (fun z : Activation K => activationPhi α z*activationPhi β z)=0 := by
    change activationMoment inactiveLaw α β=0
    simp only [inactiveLaw_moment,hα,false_and,ite_false]
  rw [hz]; ring
lemma activeCoefficient_scaling (p : ActCorner → FiniteLaw (Activation K)) (lam : ActCorner → ℝ)
    (hlam : ∀ k,0≤lam k) (hlam1 : ∀ k,lam k≤1) :
    activeCoefficient (fun k => activationMoment (thinnedLaw (p k) (lam k) (hlam k) (hlam1 k)))=
      (∏ k,lam k)*activeCoefficient (fun k => activationMoment (p k)) := by
  unfold activeCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro α hα
  have ha := (mem_nonemptyLabels α).mp hα
  unfold labelProduct
  simp_rw [thinnedLaw_active _ _ _ _ _ _ (ha _),Finset.prod_mul_distrib]
lemma activeCoefficient_inactive (p : ActCorner → FiniteLaw (Activation K)) (k : ActCorner)
    (hk : p k=inactiveLaw) : activeCoefficient (fun k => activationMoment (p k))=0 := by
  unfold activeCoefficient
  apply Finset.sum_eq_zero; intro α hα
  have ha := (mem_nonemptyLabels α).mp hα
  unfold labelProduct
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  dsimp only
  rw [hk,inactiveLaw_moment]
  simp only [ha,false_and,ite_false]
end Types
noncomputable def basePairLaw (a : Fin 13) (b : Fin 22) : FiniteLaw (Activation ActCorner) :=
  if a=faceVertex b 0 then cornerLaw (b,0) else
    if a=faceVertex b 1 then cornerLaw (b,1) else
      if a=faceVertex b 2 then cornerLaw (b,2) else inactiveLaw
lemma basePairLaw_corner (k : ActCorner) : basePairLaw (cornerPoint k) k.1=cornerLaw k := by
  obtain ⟨j,k⟩ := k
  have hinj := faceVertex_injective j
  have h01 : faceVertex j 1≠faceVertex j 0 := fun h => (by decide : (1:Fin 3)≠0) (hinj h)
  have h20 : faceVertex j 2≠faceVertex j 0 := fun h => (by decide : (2:Fin 3)≠0) (hinj h)
  have h21 : faceVertex j 2≠faceVertex j 1 := fun h => (by decide : (2:Fin 3)≠1) (hinj h)
  fin_cases k <;> simp [basePairLaw,cornerPoint,h01,h20,h21]
lemma basePairLaw_zero (a : Fin 13) (b : Fin 22) (α : Finset ActCorner) (hα : α≠∅) :
    (basePairLaw a b).mean (activationPhi α)=0 := by
  unfold basePairLaw; split
  · exact cornerLaw_zero _ α hα
  · split
    · exact cornerLaw_zero _ α hα
    · split
      · exact cornerLaw_zero _ α hα
      · exact inactiveLaw_zero α hα
lemma basePairLaw_identity : activeCoefficient (fun k => activationMoment (basePairLaw (cornerPoint k) k.1))= -(1/4:ℝ)^66 := by
  simp only [basePairLaw_corner]
  exact identity_activeCoefficient
lemma cornerPoint_surjective : Function.Surjective cornerPoint := by decide
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Typed
variable {A B K : Type*} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
noncomputable def typedCoefficient (p : A → B → FiniteLaw (Activation K)) (a : Fin 13 → A) (b : Fin 22 → B) : ℝ :=
  activeCoefficient (fun k => activationMoment (p (a (cornerPoint k)) (b k.1)))
noncomputable def typeMapLaw (π : FiniteLaw A) (ν : FiniteLaw B) : FiniteLaw ((Fin 13 → A) × (Fin 22 → B)) :=
  (FiniteLaw.independent (fun _ => π)).prod (FiniteLaw.independent (fun _ => ν))
noncomputable def averagedCoefficient (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K)) : ℝ :=
  (typeMapLaw π ν).mean (fun ab => typedCoefficient p ab.1 ab.2)
omit [Fintype A] [Fintype B] in
lemma typedCoefficient_thinned (p : A → B → FiniteLaw (Activation K)) (lam : A → B → ℝ)
    (h0 : ∀ a b,0≤lam a b) (h1 : ∀ a b,lam a b≤1) (a : Fin 13 → A) (b : Fin 22 → B) :
    typedCoefficient (fun a b => thinnedLaw (p a b) (lam a b) (h0 a b) (h1 a b)) a b=
      (∏ k : ActCorner,lam (a (cornerPoint k)) (b k.1))*typedCoefficient p a b :=
  activeCoefficient_scaling _ _ _ _
omit [Fintype A] [Fintype B] in
lemma typedCoefficient_inactive_left (p : A → B → FiniteLaw (Activation K)) (a : Fin 13 → A)
    (b : Fin 22 → B) (i : Fin 13) (hi : ∀ j,p (a i) j=inactiveLaw) : typedCoefficient p a b=0 := by
  obtain ⟨k,hk⟩ := cornerPoint_surjective i
  exact activeCoefficient_inactive _ k (by rw [hk]; exact hi _)
omit [Fintype A] [Fintype B] in
lemma typedCoefficient_inactive_right (p : A → B → FiniteLaw (Activation K)) (a : Fin 13 → A)
    (b : Fin 22 → B) (j : Fin 22) (hj : ∀ i,p i (b j)=inactiveLaw) : typedCoefficient p a b=0 :=
  activeCoefficient_inactive _ (j,0) (hj _)
end Typed
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Kernel
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
noncomputable def kernelMean (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) : ℝ :=
  π.mean (fun x => ν.mean (W x))
noncomputable def bipartiteMoment (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) : ℝ :=
  (FiniteLaw.independent (fun _ : Fin 13 => π)).mean (fun x =>
    (FiniteLaw.independent (fun _ : Fin 22 => ν)).mean (fun y =>
      ∏ k : ActCorner,W (x (cornerPoint k)) (y k.1)))
lemma bipartiteMoment_nonneg (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ)
    (hW : ∀ x y,0≤W x y) : 0≤bipartiteMoment π ν W :=
  FiniteLaw.mean_nonneg _ (fun _ => FiniteLaw.mean_nonneg _ (fun _ => Finset.prod_nonneg (fun _ _ => hW _ _)))
lemma bipartiteMoment_congr (π : FiniteLaw X) (ν : FiniteLaw Y) {W Z : X → Y → ℝ}
    (h : ∀ x y,W x y=Z x y) : bipartiteMoment π ν W=bipartiteMoment π ν Z := by
  unfold bipartiteMoment
  apply FiniteLaw.mean_congr; intro x
  apply FiniteLaw.mean_congr; intro y
  exact Finset.prod_congr rfl fun k _ => h _ _
lemma bipartiteMoment_typed (π : FiniteLaw A) (ν : FiniteLaw B) (σ : FiniteLaw X) (τ : FiniteLaw Y)
    (W : A × X → B × Y → ℝ) :
    bipartiteMoment (π.prod σ) (ν.prod τ) W=
      (typeMapLaw π ν).mean (fun ab => (FiniteLaw.independent (fun _ : Fin 13 => σ)).mean (fun x =>
        (FiniteLaw.independent (fun _ : Fin 22 => τ)).mean (fun y =>
          ∏ k : ActCorner,W (ab.1 (cornerPoint k),x (cornerPoint k)) (ab.2 k.1,y k.1)))) := by
  unfold bipartiteMoment typeMapLaw
  rw [FiniteLaw.mean_prod,independent_mean_prod]
  apply FiniteLaw.mean_congr; intro a
  simp_rw [independent_mean_prod]
  exact FiniteLaw.mean_swap _ _ _
lemma kernelMean_prod (π : FiniteLaw A) (ν : FiniteLaw B) (σ : FiniteLaw X) (τ : FiniteLaw Y)
    (W : A × X → B × Y → ℝ) : kernelMean (π.prod σ) (ν.prod τ) W=
      π.mean (fun a => ν.mean (fun b => σ.mean (fun x => τ.mean (fun y => W (a,x) (b,y))))) := by
  unfold kernelMean
  rw [FiniteLaw.mean_prod]
  apply FiniteLaw.mean_congr; intro a
  simp_rw [FiniteLaw.mean_prod]
  exact FiniteLaw.mean_swap _ _ _
end Kernel
namespace FiniteLaw
lemma independent_uniform_mean {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
    (f : (I → A) → ℝ) : (independent (fun _ : I => (uniform : FiniteLaw A))).mean f=uniformMean f := by
  unfold mean independent uniform uniformMean
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fun,Nat.cast_pow,←inv_pow,←Finset.mul_sum,div_eq_mul_inv]
  ring
end FiniteLaw
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section MatrixMean
variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
lemma uniformMean_sub_right {A : Type*} [AddGroup A] [Fintype A] (y : A) (f : A → ℝ) :
    uniformMean (fun x => f (x-y))=uniformMean f := uniformMean_equiv (Equiv.subRight y) f
lemma sampleMatrixKernel_mean (r : ℕ) (hr : 0<r) (hF : ringChar F≠2)
    (z : Activation K) (y : K → SymMatrix F (2*r)) :
    uniformMean (fun x => sampleMatrixKernel r z x y)=1 := by
  have he (x : K → SymMatrix F (2*r)) : sampleMatrixKernel r z x y=
      ∏ κ,if κ∈z.1 then rankKernel F (2*r) r (if z.2 κ then 1 else -1) (x κ-y κ) else 1 := by
    simp only [sampleMatrixKernel,Finset.prod_ite_mem,Finset.univ_inter]
  simp only [he]
  rw [uniformMean_pi_product (fun κ x => if κ∈z.1 then rankKernel F (2*r) r (if z.2 κ then 1 else -1) (x-y κ) else 1)]
  have hm (κ : K) : uniformMean (fun x : SymMatrix F (2*r) =>
      if κ∈z.1 then rankKernel F (2*r) r (if z.2 κ then 1 else -1) (x-y κ) else 1)=1 := by
    by_cases hκ : κ∈z.1
    · simp only [hκ,ite_true,uniformMean_sub_right]
      exact uniformMean_rankKernel (2*r) r hr (by omega) hF (by split <;> simp)
    · simp only [hκ,ite_false,uniformMean_const]
  simp only [hm,Finset.prod_const_one]
lemma activationMatrixKernel_mean (r : ℕ) (hr : 0<r) (hF : ringChar F≠2)
    (p : FiniteLaw (Activation K)) (y : K → SymMatrix F (2*r)) :
    uniformMean (fun x => activationMatrixKernel r p x y)=1 := by
  unfold activationMatrixKernel
  rw [uniformMean_law_swap]
  simp only [sampleMatrixKernel_mean r hr hF,FiniteLaw.mean_const]
omit [Fintype K] [DecidableEq K] in
lemma sampleMatrixKernel_symm (r : ℕ) (z : Activation K) (x y : K → SymMatrix F (2*(2*r))) :
    sampleMatrixKernel (2*r) z x y=sampleMatrixKernel (2*r) z y x := by
  unfold sampleMatrixKernel
  apply Finset.prod_congr rfl; intro κ _
  have hc : quadraticChar F ((-1:F)^(2*r))=1 := by rw [Even.neg_one_pow (even_two_mul r)]; simp
  rw [←neg_sub (x κ) (y κ),rankKernel_neg,hc,one_mul]
lemma activationMatrixKernel_symm (r : ℕ) (p : FiniteLaw (Activation K)) (x y : K → SymMatrix F (2*(2*r))) :
    activationMatrixKernel (2*r) p x y=activationMatrixKernel (2*r) p y x := by
  apply FiniteLaw.mean_congr; intro z; exact sampleMatrixKernel_symm r z x y
end MatrixMean
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section TypedMatrix
variable {A B K F : Type*} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
  [Field F] [Fintype F] [DecidableEq F]
noncomputable def typedMatrixLaw (r : ℕ) (π : FiniteLaw A) : FiniteLaw (A × (K → SymMatrix F (2*r))) :=
  π.prod FiniteLaw.uniform
noncomputable def typedMatrixKernel (r : ℕ) (p : A → B → FiniteLaw (Activation K))
    (x : A × (K → SymMatrix F (2*r))) (y : B × (K → SymMatrix F (2*r))) : ℝ :=
  activationMatrixKernel r (p x.1 y.1) x.2 y.2
omit [Fintype A] [Fintype B] in
lemma typedMatrixKernel_nonneg (r : ℕ) (p : A → B → FiniteLaw (Activation K))
    (x : A × (K → SymMatrix F (2*r))) (y : B × (K → SymMatrix F (2*r))) :
    0≤typedMatrixKernel r p x y := activationMatrixKernel_nonneg r _ _ _
lemma typedMatrixKernel_moment (r : ℕ) (π : FiniteLaw A) (ν : FiniteLaw B)
    (p : A → B → FiniteLaw (Activation K)) :
    bipartiteMoment (typedMatrixLaw (F := F) (K := K) r π) (typedMatrixLaw r ν) (typedMatrixKernel r p)=
      (typeMapLaw π ν).mean (fun ab => conditionalMatrixMoment (F := F) r (fun k => p (ab.1 (cornerPoint k)) (ab.2 k.1))) := by
  rw [typedMatrixLaw,typedMatrixLaw,bipartiteMoment_typed]
  apply FiniteLaw.mean_congr; intro ab
  simp_rw [FiniteLaw.independent_uniform_mean]
  rw [conditionalMatrixMoment,uniformMean_prod]
  rfl
lemma typedMatrixKernel_mean (r : ℕ) (hr : 0<r) (hF : ringChar F≠2)
    (π : FiniteLaw A) (ν : FiniteLaw B) (p : A → B → FiniteLaw (Activation K)) :
    kernelMean (typedMatrixLaw (F := F) (K := K) r π) (typedMatrixLaw r ν) (typedMatrixKernel r p)=1 := by
  rw [typedMatrixLaw,typedMatrixLaw,kernelMean_prod]
  have h (a : A) (b : B) :
      (FiniteLaw.uniform : FiniteLaw (K → SymMatrix F (2*r))).mean (fun x =>
        FiniteLaw.uniform.mean (fun y => typedMatrixKernel r p (a,x) (b,y)))=1 := by
    rw [FiniteLaw.mean_swap]
    simp only [FiniteLaw.mean_uniform,typedMatrixKernel,activationMatrixKernel_mean r hr hF,uniformMean_const]
  simp only [h,FiniteLaw.mean_const]
omit [Fintype A] [Fintype B] in
lemma typedMatrixKernel_transpose (r : ℕ) (p : A → B → FiniteLaw (Activation K))
    (x : A × (K → SymMatrix F (2*(2*r)))) (y : B × (K → SymMatrix F (2*(2*r)))) :
    typedMatrixKernel (2*r) p x y=typedMatrixKernel (2*r) (fun b a => p a b) y x :=
  activationMatrixKernel_symm r _ _ _
end TypedMatrix
lemma typedMatrixKernel_tendsto {A B K : Type*} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
    (r : ℕ) (hl : singularTailThreshold≤2*(2*r)) (π : FiniteLaw A) (ν : FiniteLaw B)
    (p : A → B → FiniteLaw (Activation K))
    (hp : ∀ a b α,α≠∅ → (p a b).mean (activationPhi α)=0) :
    Tendsto (fun q : OddPrime => bipartiteMoment
      (typedMatrixLaw (F := ZMod q.val) (K := K) (2*r) π) (typedMatrixLaw (2*r) ν) (typedMatrixKernel (2*r) p))
      primeInfinity (nhds (1+averagedCoefficient π ν p)) := by
  have ht := FiniteLaw.mean_tendsto (typeMapLaw π ν)
    (fun q : OddPrime => fun ab => conditionalMatrixMoment (F := ZMod q.val) (2*r) (fun k => p (ab.1 (cornerPoint k)) (ab.2 k.1)))
    (fun ab => 1+typedCoefficient p ab.1 ab.2)
    (fun ab => conditionalMatrixMoment_tendsto r hl _ (fun k => hp _ _))
  simp only [FiniteLaw.mean_add,FiniteLaw.mean_const] at ht
  simpa only [typedMatrixKernel_moment,averagedCoefficient] using ht
end SidorenkoCounterexample

end

end OAI
