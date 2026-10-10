import Mathlib

namespace OAI

section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
universe u v w u' v' i j
variable {K : Type u} [Field K]
variable {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
variable [Module K M] [Module K N]

lemma basisLeft_natural {N' : Type w} [AddCommGroup N'] [Module K N']
    {ι : Type i} [DecidableEq ι] (b : Module.Basis ι K M) (g : N →ₗ[K] N')
    (x : M ⊗[K] N) (k : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (TensorProduct.map LinearMap.id g x) k =
      g (TensorProduct.equivFinsuppOfBasisLeft b x k) := by
  induction x using TensorProduct.inductionOn with
  | tmul m n => simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul]
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]

lemma basisRight_natural {M' : Type v} [AddCommGroup M'] [Module K M']
    {ι : Type i} [DecidableEq ι] (b : Module.Basis ι K N) (f : M →ₗ[K] M')
    (x : M ⊗[K] N) (k : ι) :
    TensorProduct.equivFinsuppOfBasisRight b (TensorProduct.map f LinearMap.id x) k =
      f (TensorProduct.equivFinsuppOfBasisRight b x k) := by
  induction x using TensorProduct.inductionOn with
  | tmul m n => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul]
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]

theorem tensor_right_detect {ι : Type i} {N' : ι → Type w}
    [∀ i, AddCommGroup (N' i)] [∀ i, Module K (N' i)]
    (g : ∀ i, N →ₗ[K] N' i)
    (hg : ∀ y, (∀ i, g i y=0) → y=0) (x : M ⊗[K] N)
    (hx : ∀ i, TensorProduct.map LinearMap.id (g i) x=0) : x=0 := by
  classical
  let b := Module.Free.chooseBasis K M
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  rw [map_zero]
  ext k
  apply hg
  intro i
  rw [← basisLeft_natural b (g i),hx i,map_zero,Finsupp.zero_apply]

theorem tensor_left_detect {ι : Type i} {M' : ι → Type v}
    [∀ i, AddCommGroup (M' i)] [∀ i, Module K (M' i)]
    (f : ∀ i, M →ₗ[K] M' i)
    (hf : ∀ x, (∀ i, f i x=0) → x=0) (x : M ⊗[K] N)
    (hx : ∀ i, TensorProduct.map (f i) LinearMap.id x=0) : x=0 := by
  classical
  let b := Module.Free.chooseBasis K N
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  rw [map_zero]
  ext k
  apply hf
  intro i
  rw [← basisRight_natural b (f i),hx i,map_zero,Finsupp.zero_apply]

theorem tensor_detect {ι : Type i} {κ : Type j} {M' : ι → Type v} {N' : κ → Type w}
    [∀ i, AddCommGroup (M' i)] [∀ i, Module K (M' i)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module K (N' j)]
    (f : ∀ i, M →ₗ[K] M' i) (g : ∀ j, N →ₗ[K] N' j)
    (hf : ∀ x, (∀ i, f i x=0) → x=0)
    (hg : ∀ y, (∀ j, g j y=0) → y=0)
    (x : M ⊗[K] N) (hx : ∀ i j, TensorProduct.map (f i) (g j) x=0) : x=0 := by
  apply tensor_left_detect f hf x
  intro i
  apply tensor_right_detect g hg (TensorProduct.map (f i) LinearMap.id x)
  intro j
  have hcomp : (TensorProduct.map LinearMap.id (g j)).comp
      (TensorProduct.map (f i) (LinearMap.id : N →ₗ[K] N)) =
      TensorProduct.map (f i) (g j) := by
    ext m n
    simp
  change ((TensorProduct.map LinearMap.id (g j)).comp
      (TensorProduct.map (f i) (LinearMap.id : N →ₗ[K] N))) x=0
  rw [hcomp,hx i j]

theorem tensor_map_zero_of_test_kernels
    {ι : Type i} {κ : Type j} {M' : ι → Type v} {N' : κ → Type w}
    [∀ i, AddCommGroup (M' i)] [∀ i, Module K (M' i)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module K (N' j)]
    (t : ∀ i, M →ₗ[K] M' i) (s : ∀ j, N →ₗ[K] N' j)
    (f : M →ₗ[K] M) (g : N →ₗ[K] N)
    (hf : (⨅ i, LinearMap.ker (t i)) ≤ LinearMap.ker f)
    (hg : (⨅ j, LinearMap.ker (s j)) ≤ LinearMap.ker g)
    (x : M ⊗[K] N) (hx : ∀ i j, TensorProduct.map (t i) (s j) x=0) :
    TensorProduct.map f g x=0 := by
  let P : Submodule K M := ⨅ i, LinearMap.ker (t i)
  let Q : Submodule K N := ⨅ j, LinearMap.ker (s j)
  let t' := fun i => P.liftQ (t i) (iInf_le _ i)
  let s' := fun j => Q.liftQ (s j) (iInf_le _ j)
  have ht : ∀ y, (∀ i, t' i y=0) → y=0 := by
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      apply (Submodule.Quotient.mk_eq_zero P).mpr
      simpa only [P,t',Submodule.mem_iInf,LinearMap.mem_ker,Submodule.liftQ_apply] using hy
  have hs : ∀ y, (∀ j, s' j y=0) → y=0 := by
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      apply (Submodule.Quotient.mk_eq_zero Q).mpr
      simpa only [Q,s',Submodule.mem_iInf,LinearMap.mem_ker,Submodule.liftQ_apply] using hy
  have hquot : TensorProduct.map P.mkQ Q.mkQ x=0 := by
    apply tensor_detect t' s' ht hs
    intro i j
    have hc : (TensorProduct.map (t' i) (s' j)).comp
        (TensorProduct.map P.mkQ Q.mkQ) = TensorProduct.map (t i) (s j) := by
      ext m n
      simp [t',s']
    change ((TensorProduct.map (t' i) (s' j)).comp
      (TensorProduct.map P.mkQ Q.mkQ)) x=0
    rw [hc,hx i j]
  have hc : (TensorProduct.map (P.liftQ f hf) (Q.liftQ g hg)).comp
      (TensorProduct.map P.mkQ Q.mkQ) = TensorProduct.map f g := by
    ext m n
    simp
  rw [← hc,LinearMap.comp_apply,hquot,map_zero]

end ElementaryPositivity.LinearDetection

end
section
namespace ElementaryPositivity.LinearDetection
open scoped TensorProduct
universe u v w i j
variable {K : Type u} [Field K]
variable {M : Type v} [AddCommGroup M] [Module K M]
variable {N : Type w} [AddCommGroup N] [Module K N]

noncomputable def retract (P : Submodule K M) : M →ₗ[K] M :=
  P.projection (Classical.choose P.exists_isCompl) (Classical.choose_spec P.exists_isCompl)

lemma retract_mem (P : Submodule K M) (x : M) : retract P x∈P :=
  P.projection_apply_mem _ x

lemma retract_eq_self (P : Submodule K M) {x : M} (hx : x∈P) : retract P x=x :=
  P.projection_apply_of_mem_left _ hx

lemma retract_top : retract (⊤ : Submodule K M)=LinearMap.id := by
  ext x
  exact retract_eq_self _ trivial

noncomputable def filtrationPiece (F : ℕ → Submodule K M) (n : ℕ) (i : Fin (n+1)) :
    M →ₗ[K] M :=
  if i.val<n then retract (F i.val)-retract (F (i.val+1)) else retract (F n)

lemma filtrationPiece_mem (F : ℕ → Submodule K M) (hF : Antitone F)
    (n : ℕ) (i : Fin (n+1)) (x : M) : filtrationPiece F n i x∈F i.val := by
  unfold filtrationPiece
  split_ifs with hi
  · exact (F i.val).sub_mem (retract_mem _ _) (hF (Nat.le_succ _) (retract_mem _ _))
  · have he : i.val=n := by omega
    rw [he]
    exact retract_mem _ _

lemma filtrationPiece_kernel (F : ℕ → Submodule K M) (hF : Antitone F)
    (n : ℕ) (i : Fin (n+1)) (hi : i.val<n) :
    F (i.val+1)≤LinearMap.ker (filtrationPiece F n i) := by
  intro x hx
  change filtrationPiece F n i x=0
  simp only [filtrationPiece,ite_eq_left hi,LinearMap.sub_apply]
  rw [retract_eq_self _ (hF (Nat.le_succ _) hx),retract_eq_self _ hx,sub_self]

lemma filtrationPiece_sum (F : ℕ → Submodule K M) (hF : F 0=⊤) (n : ℕ) :
    ∑ i : Fin (n+1),filtrationPiece F n i = LinearMap.id := by
  classical
  rw [Fin.sum_univ_castSucc]
  have hs : (∑ i : Fin n, filtrationPiece F n i.castSucc) =
      retract (F 0)-retract (F n) := by
    simp only [filtrationPiece,Fin.val_castSucc,Fin.is_lt,ite_true]
    change (∑ i : Fin n, (fun k : ℕ=>retract (F k)-retract (F (k+1))) i.val) = _
    exact (Fin.sum_univ_eq_sum_range (fun k=>retract (F k)-retract (F (k+1))) n).trans
      (Finset.sum_range_sub' (fun i=>retract (F i)) n)
  rw [hs]
  simp only [filtrationPiece,Fin.val_last,lt_self_iff_false,ite_false,sub_add_cancel,hF,retract_top]

lemma tensor_map_sum_left {α : Type*} (s : Finset α) (f : α → M →ₗ[K] M)
    (g : N →ₗ[K] N) :
    TensorProduct.map (∑ i∈s,f i) g = ∑ i∈s,TensorProduct.map (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs => simp [hi,TensorProduct.map_add_left,hs]

lemma tensor_map_sum_right {α : Type*} (s : Finset α) (f : M →ₗ[K] M)
    (g : α → N →ₗ[K] N) :
    TensorProduct.map f (∑ i∈s,g i) = ∑ i∈s,TensorProduct.map f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs => simp [hi,TensorProduct.map_add_right,hs]

lemma tensor_sum_pieces (F : ℕ → Submodule K M) (G : ℕ → Submodule K N)
    (hF : F 0=⊤) (hG : G 0=⊤) (n : ℕ) (x : M ⊗[K] N) :
    ∑ i : Fin (n+1), ∑ j : Fin (n+1),
      TensorProduct.map (filtrationPiece F n i) (filtrationPiece G n j) x = x := by
  have he : (∑ i : Fin (n+1),∑ j : Fin (n+1),
      TensorProduct.map (filtrationPiece F n i) (filtrationPiece G n j))=
      TensorProduct.map LinearMap.id LinearMap.id := by
    rw [← filtrationPiece_sum F hF n,← filtrationPiece_sum G hG n]
    rw [tensor_map_sum_left]
    apply Finset.sum_congr rfl
    intro i hi
    rw [tensor_map_sum_right]
  simpa only [LinearMap.sum_apply,TensorProduct.map_id,LinearMap.id_apply] using LinearMap.congr_fun he x

noncomputable def testFiltration {ι : Type i} {D : ι → Type v}
    [∀ i,AddCommGroup (D i)] [∀ i,Module K (D i)]
    (t : ∀ i,M →ₗ[K] D i) (wt : ι → ℤ) (W : ℤ) : Submodule K M :=
  ⨅ i, ⨅ (_ : wt i<W), LinearMap.ker (t i)

lemma mem_testFiltration {ι : Type i} {D : ι → Type v}
    [∀ i,AddCommGroup (D i)] [∀ i,Module K (D i)]
    (t : ∀ i,M →ₗ[K] D i) (wt : ι → ℤ) (W : ℤ) (x : M) :
    x∈testFiltration t wt W ↔ ∀ i,wt i<W → t i x=0 := by
  simp only [testFiltration,Submodule.mem_iInf,LinearMap.mem_ker]

lemma testFiltration_antitone {ι : Type i} {D : ι → Type v}
    [∀ i,AddCommGroup (D i)] [∀ i,Module K (D i)]
    (t : ∀ i,M →ₗ[K] D i) (wt : ι → ℤ) : Antitone (testFiltration t wt) := by
  intro u v huv x hx
  rw [mem_testFiltration] at hx ⊢
  exact fun i hi=>hx i (lt_of_lt_of_le hi huv)

noncomputable def additiveTensorFiltration (F : ℤ → Submodule K M)
    (G : ℤ → Submodule K N) (W : ℤ) : Submodule K (M ⊗[K] N) :=
  Submodule.span K {z | ∃ u v x y, W≤u+v ∧ x∈F u ∧ y∈G v ∧ z=x⊗ₜ[K]y}

lemma tmul_mem_additiveTensorFiltration (F : ℤ → Submodule K M)
    (G : ℤ → Submodule K N) {W u v : ℤ} (h : W≤u+v)
    {x : M} {y : N} (hx : x∈F u) (hy : y∈G v) :
    x⊗ₜ[K]y ∈ additiveTensorFiltration F G W :=
  Submodule.subset_span ⟨u,v,x,y,h,hx,hy,rfl⟩

lemma map_mem_additiveTensorFiltration (F : ℤ → Submodule K M)
    (G : ℤ → Submodule K N) {W u v : ℤ} (h : W≤u+v)
    (f : M →ₗ[K] M) (g : N →ₗ[K] N)
    (hf : ∀ x,f x∈F u) (hg : ∀ y,g y∈G v) (z : M⊗[K]N) :
    TensorProduct.map f g z ∈ additiveTensorFiltration F G W := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact tmul_mem_additiveTensorFiltration F G h (hf x) (hg y)
  | add x y hx hy =>
    rw [map_add]
    exact (additiveTensorFiltration F G W).add_mem hx hy

theorem additiveTensorFiltration_iff_tests
    {ι : Type i} {κ : Type j} {D : ι → Type v} {E : κ → Type w}
    [∀ i,AddCommGroup (D i)] [∀ i,Module K (D i)]
    [∀ j,AddCommGroup (E j)] [∀ j,Module K (E j)]
    (t : ∀ i,M →ₗ[K] D i) (s : ∀ j,N →ₗ[K] E j)
    (wt : ι → ℤ) (ws : κ → ℤ) (L R : ℤ)
    (hL : testFiltration t wt L=⊤) (hR : testFiltration s ws R=⊤)
    (W : ℤ) (z : M⊗[K]N) :
    z∈additiveTensorFiltration (testFiltration t wt) (testFiltration s ws) W ↔
      ∀ i j, wt i+ws j<W → TensorProduct.map (t i) (s j) z=0 := by
  classical
  constructor
  · intro hz i j hij
    have hle : additiveTensorFiltration (testFiltration t wt) (testFiltration s ws) W ≤
        LinearMap.ker (TensorProduct.map (t i) (s j)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨u,v,x,y,huv,hx,hy,rfl⟩
      change TensorProduct.map (t i) (s j) (x⊗ₜ[K]y)=0
      rw [TensorProduct.map_tmul]
      by_cases hi : wt i<u
      · rw [(mem_testFiltration t wt u x).mp hx i hi,TensorProduct.zero_tmul]
      · have hj : ws j<v := by omega
        rw [(mem_testFiltration s ws v y).mp hy j hj,TensorProduct.tmul_zero]
    exact hle hz
  · intro hz
    by_cases hlow : W≤L+R
    · have hx : ∀ x : M,x∈testFiltration t wt L := by simp [hL]
      have hy : ∀ y : N,y∈testFiltration s ws R := by simp [hR]
      have h := map_mem_additiveTensorFiltration (testFiltration t wt) (testFiltration s ws)
        hlow LinearMap.id LinearMap.id hx hy z
      simpa only [TensorProduct.map_id,LinearMap.id_apply] using h
    let n : ℕ := (W-L-R).toNat
    have hn : (n : ℤ)=W-L-R := Int.toNat_of_nonneg (by omega)
    let F : ℕ → Submodule K M := fun i=>testFiltration t wt (L+i)
    let G : ℕ → Submodule K N := fun j=>testFiltration s ws (R+j)
    have hF : Antitone F := by
      intro i j hij
      exact testFiltration_antitone t wt (by omega)
    have hG : Antitone G := by
      intro i j hij
      exact testFiltration_antitone s ws (by omega)
    have hF0 : F 0=⊤ := by simpa only [F,Nat.cast_zero,add_zero] using hL
    have hG0 : G 0=⊤ := by simpa only [G,Nat.cast_zero,add_zero] using hR
    rw [← tensor_sum_pieces F G hF0 hG0 n z]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.sum_mem
    intro j hj
    by_cases hij : i.val+j.val<n
    · have hin : i.val<n := by omega
      have hjn : j.val<n := by omega
      have hiKer : (⨅ a : {a // wt a<L+(i.val : ℤ)+1}, LinearMap.ker (t a.val)) ≤
          LinearMap.ker (filtrationPiece F n i) := by
        intro x hx
        apply filtrationPiece_kernel F hF n i hin
        rw [mem_testFiltration]
        intro a ha
        exact (Submodule.mem_iInf _).mp hx ⟨a,by simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using ha⟩
      have hjKer : (⨅ b : {b // ws b<R+(j.val : ℤ)+1}, LinearMap.ker (s b.val)) ≤
          LinearMap.ker (filtrationPiece G n j) := by
        intro y hy
        apply filtrationPiece_kernel G hG n j hjn
        rw [mem_testFiltration]
        intro b hb
        exact (Submodule.mem_iInf _).mp hy ⟨b,by simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using hb⟩
      have he : TensorProduct.map (filtrationPiece F n i) (filtrationPiece G n j) z=0 := by
        apply tensor_map_zero_of_test_kernels
          (fun a : {a // wt a<L+(i.val : ℤ)+1}=>t a.val)
          (fun b : {b // ws b<R+(j.val : ℤ)+1}=>s b.val)
          _ _ hiKer hjKer
        intro a b
        apply hz
        have ha := a.property
        have hb := b.property
        omega
      rw [he]
      exact Submodule.zero_mem _
    · apply map_mem_additiveTensorFiltration (testFiltration t wt) (testFiltration s ws)
        (u:=L+i.val) (v:=R+j.val) (by omega)
        (filtrationPiece F n i) (filtrationPiece G n j)
      · exact filtrationPiece_mem F hF n i
      · exact filtrationPiece_mem G hG n j

end ElementaryPositivity.LinearDetection

end

end OAI
