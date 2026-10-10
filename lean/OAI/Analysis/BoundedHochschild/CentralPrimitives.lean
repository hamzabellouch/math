import Mathlib
import OAI.Analysis.BoundedHochschild.CentralHomotopy
import OAI.Analysis.BoundedHochschild.PathStages

namespace OAI

/-! Central cut primitives and restriction through expected embeddings. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma central_differential_values {n : ℕ} (p : M) (hp : ∀ a, p*a=a*p)
    (f g : Cochain M n) (hfg : ∀ x, p*f x=g x) (x : Fin (n+1) → M) :
    p*differentialValue f x=differentialValue g x := by
  simp only [differentialValue,mul_add,Finset.mul_sum,mul_smul_comm]
  congr 2
  · rw [← mul_assoc,hp (x 0),mul_assoc,hfg]
  · apply Finset.sum_congr rfl
    intro j _
    rw [hfg]
  · rw [← mul_assoc,hfg]

lemma norm_sum_supported_cochains {n : ℕ} (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i*p j=0) (g : I → Cochain M n)
    (hleft : ∀ i x, p i*g i x=g i x) (hright : ∀ i x, g i x*p i=g i x)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ i, ‖g i‖ ≤ C) (s : Finset I) :
    ‖∑ i ∈ s, g i‖ ≤ C := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro x
  rw [sum_apply]
  apply supported_sum_norm_le p (fun i => g i x) hp horth
    (fun i => hleft i x) (fun i => hright i x) s (C*∏ j,‖x j‖)
    (mul_nonneg hC (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  intro i _
  exact (g i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hg i)
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

 

theorem primitive_of_central_pieces
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (hcentral : ∀ i a, p i*a=a*p i)
    (horth : ∀ i j, i ≠ j → p i*p j=0)
    (htotal : ∀ x : M, (∀ i, p i*x=0) → x=0)
    {n : ℕ} (f : Cochain M (n+1)) (g : I → Cochain M n)
    (hleft : ∀ i x, p i*g i x=g i x)
    (hdf : ∀ i x, differentialValue (g i) x=p i*f x)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ i, ‖g i‖ ≤ C) :
    ∃ G : Cochain M n, ‖G‖ ≤ C ∧ ∀ x, differentialValue G x=f x := by
  classical
  let F : Finset I → Cochain M n := fun s => ∑ i ∈ s, g i
  have hF (s : Finset I) : ‖F s‖ ≤ C :=
    norm_sum_supported_cochains p hp horth g hleft
      (fun i x => by rw [← hcentral,hleft]) C hC hg s
  let U : Ultrafilter (Finset I) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset I)) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨G,hG,ht⟩ := bounded_cochain_ultralimit e U F C hC hF
  have hproj (i : I) (x : Fin n → M) : p i*G x=g i x := by
    have hlim := (hL (p i)).tendsto e (ht x)
    have hex : (fun s => p i*F s x) =ᶠ[U] (fun _ => g i x) := by
      apply hU
      filter_upwards [eventually_ge_atTop ({i} : Finset I)] with s hs
      have hi : i ∈ s := hs (Finset.mem_singleton_self i)
      change p i*(∑ j ∈ s,g j) x=g i x
      rw [sum_apply,Finset.mul_sum]
      rw [Finset.sum_eq_single i]
      · exact hleft i x
      · intro j _ hji
        calc
          p i*g j x=p i*(p j*g j x) := by rw [hleft]
          _=0 := by rw [← mul_assoc,horth i j hji.symm,zero_mul]
      · exact fun hh => (hh hi).elim
    apply predual_tendsto_unique e hlim
    intro z
    exact tendsto_const_nhds.congr' (hex.mono fun _ h => congrArg (fun a : M => e.symm a z) h.symm)
  refine ⟨G,hG,fun x => sub_eq_zero.mp (htotal _ fun i => ?_)⟩
  rw [mul_sub,central_differential_values (p i) (hcentral i) G (g i) (hproj i),hdf,sub_self]

end BoundedHochschild

 

open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def centralOutput {n : ℕ} (p : M) (f : Cochain M n) : Cochain M n :=
  (ContinuousLinearMap.mul ℂ M p).compContinuousMultilinearMap f

@[simp] lemma centralOutput_apply {n : ℕ} (p : M) (f : Cochain M n) (x : Fin n → M) :
    centralOutput p f x=p*f x := rfl

lemma norm_centralOutput_le {n : ℕ} (p : M) (hp : ‖p‖ ≤ 1) (f : Cochain M n) :
    ‖centralOutput p f‖ ≤ ‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  exact (norm_mul_le p (f x)).trans ((mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans
    (by simpa only [one_mul] using f.le_opNorm x))

 

theorem primitive_of_central_cut_primitives
    (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
    (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (hcentral : ∀ i a, p i*a=a*p i)
    (horth : ∀ i j, i ≠ j → p i*p j=0)
    (htotal : ∀ x : M, (∀ i, p i*x=0) → x=0)
    {n : ℕ} (f : Cochain M (n+1)) (hf : ∀ x, differentialValue f x=0)
    (b : I → Cochain M n) (hb : ∀ i x, p i*b i x=b i x)
    (hdb : ∀ i x, differentialValue (b i) x=centralCut (p i) (centralOutput (p i) f) x)
    (C : ℝ) (hC : 0 ≤ C) (hbn : ∀ i, ‖b i‖ ≤ C) :
    ∃ G : Cochain M n, ‖G‖ ≤ C+n*‖f‖ ∧ ∀ x, differentialValue G x=f x := by
  have hsupport (i : I) (x : Fin (n+1) → M) :
      p i*centralOutput (p i) f x=centralOutput (p i) f x := by
    simp only [centralOutput_apply,← mul_assoc,(hp i).isIdempotentElem.eq]
  have hcoc (i : I) (x : Fin (n+2) → M) : differentialValue (centralOutput (p i) f) x=0 := by
    rw [← central_differential_values (p i) (hcentral i) f (centralOutput (p i) f)
      (fun _ => rfl),hf,mul_zero]
  choose a han has had using fun i =>
    central_cocycle_correction (p i) (hp i) (hcentral i) (centralOutput (p i) f)
      (hsupport i) (hcoc i)
  let g : I → Cochain M n := fun i => b i+a i
  have hgn (i : I) : ‖g i‖ ≤ C+n*‖f‖ := by
    calc
      ‖g i‖ ≤ ‖b i‖+‖a i‖ := norm_add_le _ _
      _ ≤ C+n*‖centralOutput (p i) f‖ := add_le_add (hbn i) (han i)
      _ ≤ C+n*‖f‖ := add_le_add_right
        (mul_le_mul_of_nonneg_left (norm_centralOutput_le (p i) ((hp i).norm_le) f)
          (Nat.cast_nonneg _)) C
  apply primitive_of_central_pieces e hL p hp hcentral horth htotal f g
    (fun i x => by simp only [g,add_apply,mul_add,hb,has]) _ _ (by positivity) hgn
  intro i x
  simp only [g,differentialValue_add,hdb,had]
  rw [add_sub_cancel,centralOutput_apply]

end BoundedHochschild

 

open Filter Topology
namespace BoundedHochschild
variable {M N : Type*} [CStarAlgebra M] [CStarAlgebra N]

 

structure ExpectedEmbedding (N M : Type*) [CStarAlgebra N] [CStarAlgebra M] where
  includeMap : N →L[ℂ] M
  expectMap : M →L[ℂ] N
  include_mul : ∀ a b, includeMap (a*b)=includeMap a*includeMap b
  include_one : includeMap 1=1
  include_star : ∀ a, includeMap (star a)=star (includeMap a)
  include_norm : ∀ a, ‖includeMap a‖=‖a‖
  expect_norm : ∀ a, ‖expectMap a‖ ≤ ‖a‖
  retract : ∀ a, expectMap (includeMap a)=a
  left_module : ∀ a x, expectMap (includeMap a*x)=a*expectMap x
  right_module : ∀ x a, expectMap (x*includeMap a)=expectMap x*a

namespace ExpectedEmbedding
variable (E : ExpectedEmbedding N M)

def restrict {n : ℕ} (f : Cochain M n) : Cochain N n :=
  E.expectMap.compContinuousMultilinearMap (f.compContinuousLinearMap (fun _ => E.includeMap))

def extend {n : ℕ} (g : Cochain N n) : Cochain M n :=
  E.includeMap.compContinuousMultilinearMap (g.compContinuousLinearMap (fun _ => E.expectMap))

@[simp] lemma restrict_apply {n : ℕ} (f : Cochain M n) (x : Fin n → N) :
    E.restrict f x=E.expectMap (f (fun i => E.includeMap (x i))) := rfl
@[simp] lemma extend_apply {n : ℕ} (g : Cochain N n) (x : Fin n → M) :
    E.extend g x=E.includeMap (g (fun i => E.expectMap (x i))) := rfl

lemma restrict_norm {n : ℕ} (f : Cochain M n) : ‖E.restrict f‖ ≤ ‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  change ‖E.expectMap (f (fun i => E.includeMap (x i)))‖ ≤ _
  exact (E.expect_norm _).trans (by
    simpa only [E.include_norm] using (f.le_opNorm (fun i => E.includeMap (x i))))

lemma extend_norm {n : ℕ} (g : Cochain N n) : ‖E.extend g‖ ≤ ‖g‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  rw [extend_apply,E.include_norm]
  exact (g.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => E.expect_norm _)) (norm_nonneg _))

lemma merge_include {n : ℕ} (x : Fin (n+1) → N) (j : Fin n) :
    mergeInputs (fun i => E.includeMap (x i)) j =
      fun i => E.includeMap (mergeInputs x j i) := by
  funext i
  simp only [mergeInputs]
  split_ifs <;> simp only [E.include_mul]

 

lemma differential_restrict {n : ℕ} (f : Cochain M n) (x : Fin (n+1) → N) :
    differentialValue (E.restrict f) x =
      E.expectMap (differentialValue f (fun i => E.includeMap (x i))) := by
  simp only [differentialValue,restrict_apply,map_add,map_sum,map_smul,
    E.left_module,E.right_module,E.merge_include]

lemma restrict_cocycle {n : ℕ} (f : Cochain M n)
    (hf : ∀ x, differentialValue f x=0) :
    ∀ x, differentialValue (E.restrict f) x=0 := by
  intro x
  rw [E.differential_restrict,hf,map_zero]

 

lemma differential_extend_on_include {n : ℕ} (g : Cochain N n) (x : Fin (n+1) → N) :
    differentialValue (E.extend g) (fun i => E.includeMap (x i))=
      E.includeMap (differentialValue g x) := by
  simp only [differentialValue,extend_apply,E.merge_include,E.retract,map_add,map_sum,
    map_smul,E.include_mul]

 

theorem finite_exactness {n : ℕ} (f : Cochain M (n+1)) (g : Cochain N n)
    (hg : ∀ x, differentialValue g x=E.restrict f x)
    (S : Set M) (hS : ∀ a ∈ S, ∃ b, E.includeMap b=a)
    (hfS : ∀ x : Fin (n+1) → M, (∀ i, x i ∈ S) →
      ∃ b, E.includeMap b=f x)
    (x : Fin (n+1) → M) (hx : ∀ i, x i ∈ S) :
    differentialValue (E.extend g) x=f x := by
  classical
  choose y hy using fun i => hS (x i) (hx i)
  have hxy : (fun i => E.includeMap (y i))=x := funext hy
  obtain ⟨a,ha⟩ := hfS x hx
  rw [← hxy,E.differential_extend_on_include,hg,restrict_apply,hxy,← ha,E.retract]

end ExpectedEmbedding
end BoundedHochschild
end

end OAI
