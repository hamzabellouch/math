import OAI.Combinatorics.EuclideanRamsey.GramCompletion

namespace OAI

universe uValue

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

open scoped BigOperators RealInnerProductSpace
namespace EuclideanRamsey

def FiniteEuclidean := ℕ →₀ ℝ
namespace FiniteEuclidean
instance : AddCommGroup FiniteEuclidean := inferInstanceAs (AddCommGroup (ℕ →₀ ℝ))
instance : Module ℝ FiniteEuclidean := inferInstanceAs (Module ℝ (ℕ →₀ ℝ))
def coords (x : FiniteEuclidean) : ℕ →₀ ℝ := x

def product (x y : FiniteEuclidean) : ℝ :=
  (coords x).sum (fun n r => r*coords y n)
lemma product_eq_sum (x y : FiniteEuclidean) {s : Finset ℕ}
    (hx : (coords x).support ⊆ s) : product x y=∑ n∈s,coords x n*coords y n :=
  Finsupp.sum_of_support_subset _ hx _ (by simp)
instance core : InnerProductSpace.Core ℝ FiniteEuclidean where
  inner := product
  conj_inner_symm x y := by
    change product y x=product x y
    rw [product_eq_sum y x ((Finset.subset_union_right : (coords y).support ⊆ (coords x).support ∪ (coords y).support)),
      product_eq_sum x y ((Finset.subset_union_left : (coords x).support ⊆ (coords x).support ∪ (coords y).support))]
    apply Finset.sum_congr rfl
    intro n _; ring
  re_inner_nonneg x := by
    change 0 ≤ (coords x).sum (fun n r => r*coords x n)
    exact Finset.sum_nonneg (fun n _ => mul_self_nonneg _)
  add_left x y z := by
    change ((coords x)+(coords y)).sum _ = _
    exact Finsupp.sum_add_index (by simp) (by intro n _ r t; exact add_mul _ _ _)
  smul_left x y r := by
    change (r • coords x).sum (fun n t => t*coords y n)=r*product x y
    rw [Finsupp.sum_smul_index (by simp)]
    simp only [product,Finsupp.mul_sum,mul_assoc]
  definite x h := by
    change (coords x).sum (fun n r => r*coords x n)=0 at h
    have hs : ∀ n∈(coords x).support,coords x n*coords x n=0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun n _ => mul_self_nonneg _)).mp h
    apply Finsupp.ext
    intro n
    by_cases hn : n∈(coords x).support
    · exact mul_self_eq_zero.mp (hs n hn)
    · exact Finsupp.notMem_support_iff.mp hn
instance : NormedAddCommGroup FiniteEuclidean := InnerProductSpace.Core.toNormedAddCommGroup (𝕜:=ℝ)
instance : InnerProductSpace ℝ FiniteEuclidean := InnerProductSpace.ofCore core.toCore
lemma norm_sq (x : FiniteEuclidean) : ‖x‖^2=(coords x).sum (fun _ r => r^2) := by
  rw [← real_inner_self_eq_norm_sq]
  change product x x = _
  simp [product,Finsupp.sum,pow_two]
@[simp] lemma coords_add (x y : FiniteEuclidean) : coords (x+y)=coords x+coords y := rfl
@[simp] lemma coords_sub (x y : FiniteEuclidean) : coords (x-y)=coords x-coords y := rfl
@[simp] lemma coords_smul (c : ℝ) (x : FiniteEuclidean) : coords (c • x)=c • coords x := rfl

def reindex (f : ℕ → ℕ) (hf : Function.Injective f) : FiniteEuclidean →ₗᵢ[ℝ] FiniteEuclidean where
  toLinearMap :=
    { toFun := fun x => (coords x).mapDomain f
      map_add' := fun x y => Finsupp.mapDomain_add
      map_smul' := fun c x => Finsupp.mapDomain_smul c (coords x) }
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq,norm_sq]
    exact Finsupp.sum_mapDomain_index_inj hf

def block (j : ℕ) : FiniteEuclidean →ₗᵢ[ℝ] FiniteEuclidean :=
  reindex (Nat.pair j) (fun _m _n h => (Nat.pair_eq_pair.mp h).2)
end FiniteEuclidean
end EuclideanRamsey
namespace EuclideanRamsey
namespace FiniteEuclidean
open scoped BigOperators RealInnerProductSpace

noncomputable def embed (d : ℕ) : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] FiniteEuclidean where
  toLinearMap :=
    { toFun := fun x => (Finsupp.equivFunOnFinite.symm (fun i => x i)).mapDomain Fin.val
      map_add' := by
        intro x y
        change Finsupp.mapDomain _ _ = _ + _
        rw [← Finsupp.mapDomain_add]
        congr 1
        ext i; simp
      map_smul' := by
        intro r x
        change Finsupp.mapDomain _ _ = r • (_ : ℕ →₀ ℝ)
        rw [← Finsupp.mapDomain_smul]
        congr 1
        ext i; simp }
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq,EuclideanSpace.norm_sq_eq]
    change (Finsupp.mapDomain Fin.val _).sum _ = _
    rw [Finsupp.sum_mapDomain_index_inj Fin.val_injective]
    rw [Finsupp.sum_fintype]
    · simp [Real.norm_eq_abs,sq_abs]
    · intro _; simp

@[simp] lemma embed_apply (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    coords (embed d x) i.val=x i := by
  exact Finsupp.mapDomain_apply_of_injective Fin.val_injective _ i

lemma embed_outside (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) (n : ℕ) (hn : d≤n) :
    coords (embed d x) n=0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨i,rfl⟩
  exact (not_le_of_gt i.isLt) hn

lemma extend_pair {s d : ℕ} (a : Fin s → EuclideanSpace ℝ (Fin d)) (i j : Fin s)
    (z z' : FiniteEuclidean) (h : ‖z'-z‖=‖a j-a i‖) :
    ∃ b : Fin s → FiniteEuclidean,b i=z ∧ b j=z' ∧
      ∀ k l,‖b k-b l‖=‖a k-a l‖ := by
  let e := embed d
  let v := e (a j-a i)
  let w := z'-z
  let R := (ℝ ∙ (v-w))ᗮ.reflection
  refine ⟨fun k => z+R (e (a k-a i)),by simp,?_,?_⟩
  · have he : R v=w := Submodule.reflection_sub (by rw [show ‖v‖=‖a j-a i‖ from e.norm_map _]; exact h.symm)
    simpa [v,w] using congrArg (fun t => z+t) he
  · intro k l
    simp only [add_sub_add_left_eq_sub,← map_sub,sub_sub_sub_cancel_right,
      LinearIsometryEquiv.norm_map,LinearIsometry.norm_map]

lemma inner_reindex (f : ℕ → ℕ) (hf : Function.Injective f) (x y : FiniteEuclidean) :
    ⟪reindex f hf x,reindex f hf y⟫=⟪x,y⟫ :=
  (reindex f hf).inner_map_map x y

lemma inner_block_ne (i j : ℕ) (hij : i≠j) (x y : FiniteEuclidean) :
    ⟪block i x,block j y⟫=0 := by
  change product (block i x) (block j y)=0
  unfold product
  change ((coords x).mapDomain (Nat.pair i)).sum
    (fun n r => r*((coords y).mapDomain (Nat.pair j)) n)=0
  rw [Finsupp.sum_mapDomain_index_inj (fun _ _ h => (Nat.pair_eq_pair.mp h).2)]
  apply Finset.sum_eq_zero
  intro n hn
  dsimp only
  rw [Finsupp.mapDomain_of_notMem_range]
  · simp
  · rintro ⟨m,hm⟩
    exact hij (Nat.pair_eq_pair.mp hm).1.symm

noncomputable def flatten (l : List FiniteEuclidean) : FiniteEuclidean :=
  ∑ i : Fin l.length,block i (l.get i)

lemma norm_sum_blocks {n : ℕ} (x : Fin n → FiniteEuclidean) :
    ‖∑ i : Fin n,block i (x i)‖^2=∑ i,‖x i‖^2 := by
  rw [← real_inner_self_eq_norm_sq,inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sum_inner]
  rw [Finset.sum_eq_single i]
  · exact (block i).inner_map_map _ _ |>.trans (real_inner_self_eq_norm_sq _)
  · intro j _ hji
    exact inner_block_ne j i (fun he => hji (Fin.ext he)) _ _
  · simp

lemma flatten_distance (l k : List FiniteEuclidean) (h : l.length=k.length) :
    ‖flatten l-flatten k‖^2 = ∑ i : Fin l.length,‖l.get i-k.get (i.cast h)‖^2 := by
  have he : flatten l-flatten k = ∑ i : Fin l.length,block i (l.get i-k.get (i.cast h)) := by
    unfold flatten
    have hk : (∑ i : Fin k.length,block i (k.get i))=
        ∑ i : Fin l.length,block i (k.get (i.cast h)) := by
      exact Fintype.sum_equiv (finCongr h).symm _ _ (by intro i; rfl)
    rw [hk,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (map_sub (block i) _ _).symm
  rw [he,norm_sum_blocks]
end FiniteEuclidean
end EuclideanRamsey
namespace EuclideanRamsey
namespace FiniteEuclidean
open scoped BigOperators RealInnerProductSpace

noncomputable def unit (n : ℕ) : FiniteEuclidean := Finsupp.single n 1
lemma norm_unit (n : ℕ) : ‖unit n‖=1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [norm_sq]
  simp [unit,coords]
lemma inner_unit (x : FiniteEuclidean) (n : ℕ) : ⟪x,unit n⟫=coords x n := by
  rw [real_inner_comm]
  change product (unit n) x=coords x n
  simp [product,unit,coords]

lemma common_vertex (r : ℝ) (hr : 0 < r) (x y : FiniteEuclidean) (hxy : ‖y-x‖≤2*r) :
    ∃ z : FiniteEuclidean,‖z-x‖=r ∧ ‖z-y‖=r := by
  classical
  let v := y-x
  obtain ⟨n,hn⟩ := (coords v).support.exists_notMem
  have hz : coords v n=0 := Finsupp.notMem_support_iff.mp hn
  let e := unit n
  have he : ‖e‖=1 := norm_unit n
  have hv : ⟪v,e⟫=0 := by simpa [e] using (inner_unit v n).trans hz
  let t := Real.sqrt (r^2-‖v‖^2/4)
  have ht0 : 0≤r^2-‖v‖^2/4 := by
    have hv0 := norm_nonneg v
    change ‖v‖≤2*r at hxy
    nlinarith [sq_nonneg (2*r-‖v‖)]
  have ht : t^2=r^2-‖v‖^2/4 := Real.sq_sqrt ht0
  refine ⟨x+(1/2:ℝ)•v+t•e,?_,?_⟩
  · apply (sq_eq_sq₀ (norm_nonneg _) hr.le).mp
    have heq : x+(1/2:ℝ)•v+t•e-x=(1/2:ℝ)•v+t•e := by abel
    rw [heq,norm_add_sq_real]
    rw [norm_smul,norm_smul,he,real_inner_smul_left,real_inner_smul_right,hv]
    simp only [Real.norm_eq_abs,sq_abs,mul_pow]
    nlinarith
  · apply (sq_eq_sq₀ (norm_nonneg _) hr.le).mp
    have heq : x+(1/2:ℝ)•v+t•e-y=(-(1/2):ℝ)•v+t•e := by
      have : y=x+v := by dsimp [v]; abel
      rw [this]
      module
    rw [heq,norm_add_sq_real]
    rw [norm_smul,norm_smul,he,real_inner_smul_left,real_inner_smul_right,hv]
    simp only [Real.norm_eq_abs,mul_pow,sq_abs]
    nlinarith

lemma unit_distance_constant {Y : Type uValue} (r : ℝ) (hr : 0 < r)
    (f : FiniteEuclidean → Y) (hf : ∀ x y,‖x-y‖=r → f x=f y) (x y : FiniteEuclidean) :
    f x=f y := by
  have hsmall (x y : FiniteEuclidean) (h : ‖y-x‖≤2*r) : f x=f y := by
    obtain ⟨z,hz,hz'⟩ := common_vertex r hr x y h
    exact (hf z x hz).symm.trans (hf z y hz')
  have hl : IsLocallyConstant f := by
    apply (IsLocallyConstant.iff_exists_open f).mpr
    intro x
    refine ⟨Metric.ball x (2*r),Metric.isOpen_ball,Metric.mem_ball_self (by positivity),?_⟩
    intro y hy
    exact (hsmall x y (by exact (show ‖y-x‖<2*r by simpa only [Metric.mem_ball,dist_eq_norm] using hy).le)).symm
  exact hl.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ x) (Set.mem_univ y)
end FiniteEuclidean
end EuclideanRamsey

end

end OAI
