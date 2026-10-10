import Mathlib
import OAI.Algebra.FiniteTensor.TensorKernels

namespace OAI

/-! Liftable pure tensors, deformation cycles and the finite pairing obstruction. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor
noncomputable section
open scoped TensorProduct
open SuperReduction CohomologyTensor
variable {K ι : Type*} [Field K] [Invertible (2:K)] [Fintype ι] [LinearOrder ι]
variable {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]

 

theorem exists_liftable_pure_tensor
    (C : ∀ i, SuperReduction K (E i)) (d b : ∀ i, E i →ₗ[K] E i)
    (hdd : ∀ i v, d i (d i v)=0)
    (hdg : ∀ i v, d i ((C i).g v) = -(C i).g (d i v))
    (hδd : ∀ i v, (C i).d (d i v) = -d i ((C i).d v))
    (hδb : ∀ i v, (C i).d (b i v) = b i ((C i).d v))
    (hbg : ∀ i v, b i ((C i).g v) = (C i).g (b i v))
    (α : ⨂[K] i, E i)
    (hαδ : finiteD C α=0)
    (hαd : oddTensor (fun i => (C i).g) d α=0)
    (htrip : ∀ S : Finset ι, S.card=3 → partialTensor E b S α ∈ LinearMap.range (finiteD C))
    (L : (⨂[K] i, E i) →ₗ[K] K)
    (hLδ : ∀ v, L (finiteD C v)=0)
    (hLd : ∀ v, L (oddTensor (fun i => (C i).g) d v)=0)
    (hLα : L α ≠ 0) :
    ∃ (a : ∀ i, E i) (S : Finset ι), S.card ≤ 2 ∧
      (∀ i, (C i).d (a i)=0) ∧
      (∀ i, d i (a i) ∈ LinearMap.range (C i).d) ∧
      (∀ i ∉ S, b i (a i) ∈ LinearMap.range (C i).d) ∧
      L (PiTensorProduct.tprod K a) ≠ 0 := by
  let D := oddTensor (fun i => (C i).g) d
  let Q := CohomologyTensor.project C
  let I := CohomologyTensor.embed C
  let u := Q α
  let Dbar := oddTensor (fun i => repMap (C i) (C i).g) (fun i => repMap (C i) (d i))
  let bbar := fun i => repMap (C i) (b i)
  let Lbar := L.comp I
  have hanti (v : ⨂[K] i, E i) : finiteD C (D v) + D (finiteD C v)=0 :=
    oddTensor_anticommute (fun i => (C i).g) (fun i => (C i).d) d
      (fun i => (C i).dg) hdg hδd v
  have hDδ (v : ⨂[K] i, E i) : D (finiteD C v) = -finiteD C (D v) :=
    eq_neg_of_add_eq_zero_right (hanti v)
  have hδD (v : ⨂[K] i, E i) : finiteD C (D v) = -D (finiteD C v) :=
    eq_neg_of_add_eq_zero_left (hanti v)
  have hQDδ (v : ⨂[K] i, E i) : Q (D (finiteD C v))=0 := by
    rw [hDδ,map_neg,CohomologyTensor.project_d,neg_zero]
  have huD : Dbar u=0 := by
    change Dbar (CohomologyTensor.project C α)=0
    rw [← odd_sandwich C d,operator_projection C D hQDδ α hαδ,hαd,map_zero]
  have htr (S : Finset ι) (hS : S.card=3) :
      partialTensor (fun i => ↥(Factors C i)) bbar S u=0 := by
    change partialTensor (fun i => ↥(Factors C i)) bbar S (CohomologyTensor.project C α)=0
    rw [← partial_sandwich C b S]
    have hpres (v : ⨂[K] i, E i) :
        CohomologyTensor.project C (partialTensor E b S (finiteD C v))=0 := by
      rw [partial_commute C b (fun i v => (hδb i v).symm) hbg,CohomologyTensor.project_d]
    rw [operator_projection C (partialTensor E b S) hpres α hαδ]
    obtain ⟨v,hv⟩ := htrip S hS
    rw [← hv,CohomologyTensor.project_d]
  have hLbarD (v : ⨂[K] i, Factors C i) : Lbar (Dbar v)=0 := by
    change L (I (Dbar v))=0
    rw [← odd_sandwich C d]
    have hcy : finiteD C (D (I v))=0 := by
      rw [hδD,CohomologyTensor.d_include,map_zero,neg_zero]
    exact (pairing_projection C L hLδ (D (I v)) hcy).trans (hLd (I v))
  have huL : Lbar u ≠ 0 := by
    change L (I (Q α)) ≠ 0
    rw [pairing_projection C L hLδ α hαδ]
    exact hLα
  choose R hRd hRg hRp using fun i => exists_induced_reduction (C i) (d i) (b i) (C i).g
    (hdd i) (C i).gg (hdg i) (hδd i) (C i).dg (hδb i) (hbg i)
  have htotal : finiteD R = Dbar := by
    unfold finiteD Dbar oddTensor
    congr 1
    funext i
    congr 1
    funext j
    simp only [dcoord,oddCoordinate,hRd,hRg]
  have huR : finiteD R u=0 := by rw [htotal]; exact huD
  have huKer : u ∈ kernelSupport (fun i => ↥(Factors C i)) bbar 2 :=
    triple_kernel_support (fun i => ↥(Factors C i)) bbar u htr
  let Good : Set (⨂[K] i, Factors C i) := {v | ∃ (f : ∀ i, Factors C i) (S : Finset ι),
    S.card ≤ 2 ∧ (∀ i, (R i).d (f i)=0) ∧ (∀ i ∉ S, bbar i (f i)=0) ∧
    PiTensorProduct.tprod K f=v}
  have hspan : kernelSupport (fun i => ↥(Factors C i)) bbar 2 ≤
      (Submodule.span K Good).comap (finiteP R) := by
    apply Submodule.span_le.mpr
    rintro v ⟨f,S,hS,hb,hf⟩
    subst v
    change finiteP R (PiTensorProduct.tprod K f) ∈ Submodule.span K Good
    rw [finiteP,PiTensorProduct.map_tprod]
    apply Submodule.subset_span
    refine ⟨fun i => (R i).p (f i),S,hS,?_,?_,rfl⟩
    · intro i; exact (R i).dp (f i)
    · intro i hi; exact hRp i (f i) (hb i hi)
  have hvGood : finiteP R u ∈ Submodule.span K Good := hspan huKer
  have hvL : Lbar (finiteP R u) ≠ 0 := by
    obtain ⟨v,hv⟩ := finite_cycle_mod_projection R u huR
    have hh := congrArg Lbar hv
    rw [htotal,hLbarD,map_sub] at hh
    rw [← sub_eq_zero.mp hh.symm]
    exact huL
  have hex : ∃ v ∈ Good, Lbar v ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hker : Submodule.span K Good ≤ LinearMap.ker Lbar := by
      apply Submodule.span_le.mpr
      intro v hv
      exact hnone v hv
    exact hvL (hker hvGood)
  obtain ⟨v,⟨f,S,hS,hfd,hfb,hfv⟩,hLv⟩ := hex
  subst v
  refine ⟨fun i => repInclude (C i) (f i),S,hS,?_,?_,?_,?_⟩
  · intro i; exact SuperReduction.d_include (C i) (f i)
  · intro i
    apply cycle_of_project_zero (C i)
    · rw [hδd,SuperReduction.d_include,map_zero,neg_zero]
    · change repMap (C i) (d i) (f i)=0
      rw [← hRd]; exact hfd i
  · intro i hi
    apply cycle_of_project_zero (C i)
    · rw [hδb,SuperReduction.d_include,map_zero]
    · exact hfb i hi
  · simpa only [Lbar,I,CohomologyTensor.embed,LinearMap.comp_apply,
      PiTensorProduct.map_tprod] using hLv

end
end PD4Tensor

 

namespace PD4Tensor
noncomputable section
open scoped TensorProduct BigOperators
variable {K R ι : Type*} [Field K] [CommRing R] [Algebra K R]
variable [Fintype ι] [LinearOrder ι]
variable {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]

 
def deformedTensor (g δ k : ∀ i, E i →ₗ[K] E i) (t : ι → R) :
    R ⊗[K] (⨂[K] i, E i) →ₗ[K] R ⊗[K] (⨂[K] i, E i) :=
  TensorProduct.map LinearMap.id (oddTensor g δ) +
    ∑ i, TensorProduct.map (LinearMap.mulLeft K (t i))
      (PiTensorProduct.map (oddCoordinate g k i))

 
def tensorLift (a c : ∀ i, E i) (t : ι → R) : R ⊗[K] (⨂[K] i, E i) :=
  ∑ S : Finset ι, (∏ i∈S, t i) ⊗ₜ[K] PiTensorProduct.tprod K (S.piecewise c a)

 
theorem sum_finsets_split {M : Type*} [AddCommMonoid M] (f : Finset ι → M) (i : ι) :
    ∑ S : Finset ι, f S = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i∉S),
      (f S + f (insert i S)) := by
  classical
  rw [Finset.sum_add_distrib]
  have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun S : Finset ι => i∉S) f
  rw [← h]
  congr 1
  symm
  apply Finset.sum_bij (fun S hS => insert i S)
  · intro S hS
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hS ⊢
    simp
  · intro S hS T hT heq
    have hs : i∉S := (Finset.mem_filter.mp hS).2
    have ht : i∉T := (Finset.mem_filter.mp hT).2
    simpa only [Finset.erase_insert hs,Finset.erase_insert ht] using
      congrArg (fun U : Finset ι => U.erase i) heq
  · intro S hS
    have hs : i∈S := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hS
    refine ⟨S.erase i,by simp,Finset.insert_erase hs⟩
  · intro S hS; rfl

def deformedCoordinate (g δ k : ∀ i, E i →ₗ[K] E i) (t : ι → R) (i : ι) :
    R ⊗[K] (⨂[K] i, E i) →ₗ[K] R ⊗[K] (⨂[K] i, E i) :=
  TensorProduct.map LinearMap.id (PiTensorProduct.map (oddCoordinate g δ i)) +
    TensorProduct.map (LinearMap.mulLeft K (t i))
      (PiTensorProduct.map (oddCoordinate g k i))

theorem deformedTensor_eq_sum (g δ k : ∀ i, E i →ₗ[K] E i) (t : ι → R) :
    deformedTensor g δ k t = ∑ i, deformedCoordinate g δ k t i := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro r
  apply LinearMap.ext
  intro v
  change deformedTensor g δ k t (r ⊗ₜ[K] v) = (∑ i, deformedCoordinate g δ k t i) (r ⊗ₜ[K] v)
  simp only [deformedTensor,deformedCoordinate,oddTensor,LinearMap.sum_apply,
    LinearMap.add_apply,TensorProduct.map_tmul,LinearMap.id_apply,
    LinearMap.mulLeft_apply,TensorProduct.tmul_sum,Finset.sum_add_distrib]

 

theorem tensorLift_cycle (g δ k : ∀ i, E i →ₗ[K] E i) (a c : ∀ i, E i)
    (ha : ∀ i, δ i (a i)=0) (hc : ∀ i, δ i (c i)= -k i (a i))
    (t : ι → R) (ht : ∀ i, t i * t i=0) :
    deformedTensor g δ k t (tensorLift a c t)=0 := by
  rw [deformedTensor_eq_sum,LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  simp only [tensorLift,map_sum]
  rw [sum_finsets_split _ i]
  apply Finset.sum_eq_zero
  intro S hS
  have hi : i∉S := (Finset.mem_filter.mp hS).2
  have hzero : PiTensorProduct.map (oddCoordinate g δ i)
      (PiTensorProduct.tprod K (S.piecewise c a))=0 := by
    rw [PiTensorProduct.map_tprod]
    apply (PiTensorProduct.tprod K).map_coord_zero i
    simp [oddCoordinate,hi,ha]
  have hneg : PiTensorProduct.map (oddCoordinate g δ i)
      (PiTensorProduct.tprod K ((insert i S).piecewise c a)) =
      -PiTensorProduct.map (oddCoordinate g k i)
        (PiTensorProduct.tprod K (S.piecewise c a)) := by
    simp only [PiTensorProduct.map_tprod]
    let factors : ∀ j, E j := fun j => oddCoordinate g k i j (S.piecewise c a j)
    have hcoords : (fun j => oddCoordinate g δ i j ((insert i S).piecewise c a j)) =
        Function.update factors i (-factors i) := by
      funext j
      by_cases hji : j=i
      · subst j; simp [factors,oddCoordinate,hi,hc]
      · simp only [Function.update_of_ne hji,factors]
        simp only [Finset.piecewise]
        by_cases hlt : j < i
        · simp [oddCoordinate,hlt,hji]
        · simp [oddCoordinate,hlt,hji]
    rw [hcoords,(PiTensorProduct.tprod K).map_update_neg,Function.update_eq_self]
  have hsq : t i * (t i * ∏ j∈S,t j)=0 := by rw [← mul_assoc,ht,zero_mul]
  simp only [deformedCoordinate,LinearMap.add_apply,TensorProduct.map_tmul,
    LinearMap.id_apply,LinearMap.mulLeft_apply,Finset.prod_insert hi,hzero,hneg,
    TensorProduct.tmul_zero,zero_add,TensorProduct.tmul_neg,hsq,
    TensorProduct.zero_tmul,add_zero,add_neg_cancel]

variable {V : Type*} [AddCommGroup V] [Module K V]

 
def specializeTensor (ε : R →ₐ[K] K) : R ⊗[K] V →ₗ[K] V :=
  (TensorProduct.lid K V).toLinearMap.comp (TensorProduct.map ε.toLinearMap LinearMap.id)

@[simp] theorem specializeTensor_tmul (ε : R →ₐ[K] K) (r : R) (v : V) :
    specializeTensor ε (r ⊗ₜ[K] v) = ε r • v := by
  simp [specializeTensor]

 
theorem specialize_tensorLift (a c : ∀ i, E i) (t : ι → R) (ε : R →ₐ[K] K)
    (ht : ∀ i, ε (t i)=0) :
    specializeTensor ε (tensorLift a c t) = PiTensorProduct.tprod K a := by
  rw [tensorLift,map_sum]
  rw [Finset.sum_eq_single (∅ : Finset ι)]
  · simp
  · intro S _ hS
    obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    rw [specializeTensor_tmul,map_prod]
    have hz : ∏ j∈S, ε (t j)=0 := Finset.prod_eq_zero hi (ht i)
    rw [hz,zero_smul]
  · simp

end
end PD4Tensor

 

noncomputable section

namespace PD4Tensor
noncomputable section
open scoped TensorProduct BigOperators
open SuperReduction CohomologyTensor
variable {K ι : Type*} [Field K] [Invertible (2:K)] [Fintype ι] [LinearOrder ι]
variable {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]

 
 
omit [Invertible (2:K)] in
theorem selective_tensorLift_cycle
    (g δ k : ∀ i, E i →ₗ[K] E i) (a c : ∀ i,E i) (q : Fin 3 ↪ ι)
    (ha : ∀ i, δ i (a i)=0)
    (hc : ∀ i∈Set.range q, δ i (c i)= -k i (a i))
    (hz : ∀ i∉Set.range q, c i=0) :
    deformedTensor g δ k (threeParameters (K:=K) q)
      (tensorLift a c (threeParameters (K:=K) q))=0 := by
  classical
  let k' : ∀ i,E i →ₗ[K] E i := fun i => if i∈Set.range q then k i else 0
  have hcorr (i : ι) : δ i (c i)= -k' i (a i) := by
    by_cases hi : i∈Set.range q
    · simpa only [k',ite_eq_left hi] using hc i hi
    · simp only [k',ite_eq_right hi,hz i hi,map_zero,LinearMap.zero_apply,neg_zero]
  have hd : deformedTensor g δ k (threeParameters (K:=K) q) =
      deformedTensor g δ k' (threeParameters (K:=K) q) := by
    unfold deformedTensor
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i∈Set.range q
    · congr 1
      congr 1
      funext j
      simp only [oddCoordinate]
      split_ifs with hji hji
      · rfl
      · subst j; simp only [k',ite_eq_left hi]
      · rfl
    · rw [threeParameters_other q i hi]
      simp
  rw [hd]
  exact tensorLift_cycle g δ k' a c ha hcorr _ (threeParameters_sq q)

 

theorem exists_three_deformed_cycle
    (C : ∀ i, SuperReduction K (E i)) (d b : ∀ i, E i →ₗ[K] E i)
    (hdd : ∀ i v, d i (d i v)=0)
    (hdg : ∀ i v, d i ((C i).g v) = -(C i).g (d i v))
    (hδd : ∀ i v, (C i).d (d i v) = -d i ((C i).d v))
    (hδb : ∀ i v, (C i).d (b i v) = b i ((C i).d v))
    (hbg : ∀ i v, b i ((C i).g v) = (C i).g (b i v))
    (A : Finset ι) (hA : 5 ≤ A.card)
    (α : ⨂[K] i, E i)
    (hαδ : finiteD C α=0)
    (hαd : oddTensor (fun i => (C i).g) d α=0)
    (htrip : ∀ S : Finset ι, S.card=3 → partialTensor E b S α ∈ LinearMap.range (finiteD C))
    (L : (⨂[K] i, E i) →ₗ[K] K)
    (hLδ : ∀ v, L (finiteD C v)=0)
    (hLd : ∀ v, L (oddTensor (fun i => (C i).g) d v)=0)
    (hLα : L α ≠ 0) :
    ∃ (q : Fin 3 ↪ ι) (κ : T K 3 ⊗[K] (⨂[K] i,E i)),
      (∀ j, q j∈A) ∧
      deformedTensor (fun i => (C i).g) (fun i => (C i).d)
        (fun i => (d i).comp (b i) - (b i).comp (d i))
        (threeParameters (K:=K) q) κ=0 ∧
      L (specializeTensor (augmentationAlg K 3) κ) ≠ 0 := by
  classical
  obtain ⟨a,S,hS,ha,had,hab,hLa⟩ := exists_liftable_pure_tensor C d b hdd hdg hδd hδb hbg
    α hαδ hαd htrip L hLδ hLd hLα
  have hsd : 2 < (A\S).card := by
    have h := Finset.card_le_card (Finset.inter_subset_right (s₁:=A) (s₂:=S))
    have h' := Finset.card_sdiff_add_card_inter A S
    omega
  obtain ⟨i,j,k,hi,hj,hk,hij,hik,hjk⟩ := Finset.two_lt_card_iff.mp hsd
  let q : Fin 3 ↪ ι := ⟨![i,j,k],by
    intro r s hrs
    fin_cases r <;> fin_cases s <;> simp_all⟩
  have hq (r : Fin 3) : q r∈A\S := by fin_cases r <;> assumption
  choose β hβ using had
  have hgam : ∀ u∈Set.range q, ∃ γ, (C u).d γ=b u (a u) := by
    rintro u ⟨r,rfl⟩
    exact hab _ (Finset.mem_sdiff.mp (hq r)).2
  choose γ hγ using hgam
  let c : ∀ u,E u := fun u => if hu : u∈Set.range q then d u (γ u hu) + b u (β u) else 0
  refine ⟨q,tensorLift a c (threeParameters (K:=K) q),?_,?_,?_⟩
  · intro r; exact (Finset.mem_sdiff.mp (hq r)).1
  · apply selective_tensorLift_cycle _ _ _ a c q ha
    · intro u hu
      simp only [c,dite_eq_left hu,map_add,hδd,hδb,hγ,hβ,
        LinearMap.sub_apply,LinearMap.comp_apply]
      abel
    · intro u hu; simp only [c,dite_eq_right hu]
  · rw [specialize_tensorLift]
    · exact hLa
    · intro u; exact augmentation_threeParameters q u

end
end PD4Tensor

namespace PD4Tensor
noncomputable section
open scoped TensorProduct BigOperators
open SuperReduction CohomologyTensor
variable {K ι : Type*} [Field K] [Invertible (2:K)] [Fintype ι] [LinearOrder ι]
variable {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]

 

theorem finite_tensor_pairing_obstruction
    (C : ∀ i, SuperReduction K (E i)) (d b : ∀ i, E i →ₗ[K] E i)
    (hdd : ∀ i v, d i (d i v)=0)
    (hdg : ∀ i v, d i ((C i).g v) = -(C i).g (d i v))
    (hδd : ∀ i v, (C i).d (d i v) = -d i ((C i).d v))
    (hδb : ∀ i v, (C i).d (b i v) = b i ((C i).d v))
    (hbg : ∀ i v, b i ((C i).g v) = (C i).g (b i v))
    (A : Finset ι) (hA : 5 ≤ A.card)
    (α : ⨂[K] i, E i)
    (hαδ : finiteD C α=0)
    (hαd : oddTensor (fun i => (C i).g) d α=0)
    (htrip : ∀ S : Finset ι, S.card=3 → partialTensor E b S α ∈ LinearMap.range (finiteD C))
    (L : (⨂[K] i, E i) →ₗ[K] K)
    (hLδ : ∀ v, L (finiteD C v)=0)
    (hLd : ∀ v, L (oddTensor (fun i => (C i).g) d v)=0)
    (hLα : L α ≠ 0)
    (W : Type*) [AddCommGroup W] [Module K W] [Module (T K 3) W]
    (left : (Fin 3 ↪ ι) → W)
    (Δ : (Fin 3 ↪ ι) → W →ₗ[K] W)
    (B : (Fin 3 ↪ ι) → W →ₗ[T K 3] (T K 3 ⊗[K] (⨂[K] i, E i)) →ₗ[T K 3] T K 3)
    (hcentral : ∀ q v, augmentation K 3 (B q (left q) v) =
      L (specializeTensor (augmentationAlg K 3) v))
    (hboundary : ∀ q u v,
      deformedTensor (fun i => (C i).g) (fun i => (C i).d)
        (fun i => (d i).comp (b i) - (b i).comp (d i))
        (threeParameters (K:=K) q) v=0 → B q (Δ q u) v=0)
    (hleft : ∀ q, (∀ j, q j∈A) → ∃ u, Δ q u=
      (t K 3 0 * t K 3 1 * t K 3 2) • left q) : False := by
  obtain ⟨q,κ,hq,hκ,hLκ⟩ := exists_three_deformed_cycle C d b hdd hdg hδd hδb hbg
    A hA α hαδ hαd htrip L hLδ hLd hLα
  have hunit : IsUnit (B q (left q) κ) := by
    apply isUnit_of_augmentation_ne_zero
    rw [hcentral]
    exact hLκ
  obtain ⟨u,hu⟩ := hleft q hq
  have hzero := hboundary q u κ hκ
  rw [hu,LinearMap.map_smul,LinearMap.smul_apply,smul_eq_mul] at hzero
  exact triple_mul_unit_ne_zero K 3 0 1 2 (by decide) (by decide) (by decide) hunit hzero

end
end PD4Tensor
end

end

end OAI
