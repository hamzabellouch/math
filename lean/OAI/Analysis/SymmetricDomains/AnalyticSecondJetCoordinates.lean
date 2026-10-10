import Mathlib
import OAI.Analysis.SymmetricDomains.FieldSecondJet

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
namespace LinearMap
open scoped _root_.LinearMap
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A : Module.End K V) (e : V →ₗ[K] (ι → K)) (w : ι → K)
    (he : ∀ x i, e (A x) i=w i*e x i)
include he

 theorem diagonal_coordinate_pow (n : ℕ) (x : V) (i : ι) :
    e ((A^n) x) i=(w i)^n*e x i := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ',Module.End.mul_apply,he,hn,pow_succ']
    ring

 theorem diagonal_coordinate_aeval (p : K[X]) (x : V) (i : ι) :
    e ((aeval A p) x) i=p.eval (w i)*e x i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add,LinearMap.add_apply,Pi.add_apply,eval_add,hp,hq,add_mul]
  | monomial n a =>
    simp only [aeval_monomial,eval_monomial,Module.End.mul_apply,
      Module.algebraMap_end_apply,map_smul,Pi.smul_apply,smul_eq_mul,
      diagonal_coordinate_pow A e w he,mul_assoc]

 theorem diagonal_faithful_aeval_eq_zero (hinj : Function.Injective e)
    (s : Finset K) (hw : ∀ i, w i∈s) :
    aeval A (∏ a∈s, (X-C a))=0 := by
  classical
  ext x
  apply hinj
  funext i
  rw [diagonal_coordinate_aeval A e w he]
  have hz : (∏ a∈s, (X-C a)).eval (w i)=0 := by
    simp only [eval_prod,eval_sub,eval_X,eval_C]
    exact Finset.prod_eq_zero (hw i) (sub_self (w i))
  simp [hz]

 theorem diagonal_faithful_isSemisimple (hinj : Function.Injective e)
    (s : Finset K) (hw : ∀ i, w i∈s) : A.IsSemisimple := by
  classical
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    ((Polynomial.separable_prod_X_sub_C_iff'.mpr (fun _ _ _ _ h => h)).squarefree)
  exact diagonal_faithful_aeval_eq_zero A e w he hinj s hw

 theorem diagonal_faithful_eigenvalue_mem (hinj : Function.Injective e)
    {μ : K} (hμ : A.HasEigenvalue μ) : ∃ i, w i=μ := by
  classical
  obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff _).mp hμ
  rw [Module.End.mem_eigenspace_iff] at hx
  by_contra! h
  apply hx0
  apply hinj
  funext i
  have hh := he x i
  rw [hx,map_smul,Pi.smul_apply,smul_eq_mul] at hh
  have hi : e x i=0 := by
    have hz : (μ-w i)*e x i=0 := by rw [sub_mul,hh,sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (h i).symm)
  simpa using hi

end LinearMap

open Filter Topology

abbrev SecondJetIndex (ι : Type*) := ι ⊕ ((ι × ι) ⊕ (ι × ι × ι))

def secondJetWeight {ι : Type*} (w : ι → ℂ) : SecondJetIndex ι → ℂ
  | .inl i => -w i
  | .inr (.inl (i,j)) => w j-w i
  | .inr (.inr (i,j,k)) => w j+w k-w i

variable {E V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [AddCommGroup V] [Module ℂ V]
    (F : V →ₗ[ℂ] (E → E)) (p : E) (hF : ∀ X, AnalyticAt ℂ (F X) p)
    (b : Module.Basis ι ℂ E)

def analyticSecondJetCoordinates : V →ₗ[ℂ] (SecondJetIndex ι → ℂ) where
  toFun X j := match j with
    | .inl i => b.repr (F X p) i
    | .inr (.inl (i,j)) => b.repr (fieldFirstJet F p hF X (b j)) i
    | .inr (.inr (i,j,k)) => b.repr (fieldSecondJet F p hF X (b j) (b k)) i
  map_add' X Y := by
    funext j
    rcases j with i | (⟨i,j⟩ | ⟨i,j,k⟩) <;>
      simp only [map_add,Pi.add_apply,add_apply,Finsupp.add_apply]
  map_smul' c X := by
    funext j
    rcases j with i | (⟨i,j⟩ | ⟨i,j,k⟩) <;>
      simp only [map_smul,Pi.smul_apply,smul_apply,Finsupp.smul_apply,
        RingHom.id_apply,smul_eq_mul]

 theorem analyticSecondJetCoordinates_eq_zero_iff (X : V) :
    analyticSecondJetCoordinates F p hF b X=0 ↔ ZeroSecondJet (F X) p := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · apply b.ext_elem
      intro i
      simpa [analyticSecondJetCoordinates,fieldFirstJet,fieldSecondJet] using congrFun h (.inl i)
    · apply ContinuousLinearMap.coe_injective
      apply b.ext
      intro j
      apply b.ext_elem
      intro i
      simpa [analyticSecondJetCoordinates,fieldFirstJet,fieldSecondJet] using congrFun h (.inr (.inl (i,j)))
    · apply ContinuousLinearMap.coe_injective
      apply b.ext
      intro j
      apply ContinuousLinearMap.coe_injective
      apply b.ext
      intro k
      apply b.ext_elem
      intro i
      simpa [analyticSecondJetCoordinates,fieldFirstJet,fieldSecondJet] using congrFun h (.inr (.inr (i,j,k)))
  · rintro ⟨h0,h1,h2⟩
    funext j
    rcases j with i | (⟨i,j⟩ | ⟨i,j,k⟩) <;>
      simp [analyticSecondJetCoordinates,fieldFirstJet,fieldSecondJet,h0,h1,h2]

 theorem analyticSecondJetCoordinates_injective
    (hjet : ∀ X, ZeroSecondJet (F X) p → X=0) :
    Function.Injective (analyticSecondJetCoordinates F p hF b) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro X hX
  exact hjet X ((analyticSecondJetCoordinates_eq_zero_iff F p hF b X).mp hX)

 omit [CompleteSpace E] in
 theorem basis_coordinate_diagonal (A : E →L[ℂ] E) (w : ι → ℂ)
    (hA : ∀ i, A (b i)=w i • b i) (x : E) (i : ι) :
    b.repr (A x) i=w i*b.repr x i := by
  classical
  have he : (b.coord i).comp A.toLinearMap=w i • b.coord i := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply,ContinuousLinearMap.coe_coe,hA,map_smul,
      LinearMap.smul_apply,Module.Basis.coord_apply,Module.Basis.repr_self,Finsupp.single_apply,
      smul_eq_mul]
    split_ifs with h
    · subst j; rfl
    · simp
  exact LinearMap.congr_fun he x

 theorem analyticSecondJetCoordinates_euler (A : E →L[ℂ] E) (w : ι → ℂ)
    (hA : ∀ i, A (b i)=w i • b i) (B : Module.End ℂ V)
    (hB : ∀ X, F (B X) =ᶠ[𝓝 p] VectorField.lieBracket ℂ (fun y => A (y-p)) (F X)) :
    ∀ X j, analyticSecondJetCoordinates F p hF b (B X) j=
      secondJetWeight w j*analyticSecondJetCoordinates F p hF b X j := by
  intro X j
  rcases j with i | (⟨i,j⟩ | ⟨i,j,k⟩)
  · change b.repr (F (B X) p) i=(-w i)*b.repr (F X p) i
    rw [(hB X).eq_of_nhds,lieBracket_centeredLinear_zeroJet,map_neg,Finsupp.neg_apply,
      basis_coordinate_diagonal b A w hA,neg_mul]
  · change b.repr (fderiv ℂ (F (B X)) p (b j)) i=(w j-w i)*b.repr (fderiv ℂ (F X) p (b j)) i
    rw [(hB X).fderiv_eq,lieBracket_centeredLinear_firstJet A p (hF X)]
    simp only [sub_apply,ContinuousLinearMap.comp_apply,hA,map_smul,
      map_sub,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul,basis_coordinate_diagonal b A w hA]
    ring
  · change b.repr (fderiv ℂ (fderiv ℂ (F (B X))) p (b j) (b k)) i=
      (w j+w k-w i)*b.repr (fderiv ℂ (fderiv ℂ (F X)) p (b j) (b k)) i
    rw [(hB X).fderiv.fderiv_eq,lieBracket_centeredLinear_secondJet A p (hF X),hA,hA]
    simp only [map_smul,map_add,map_sub,Finsupp.add_apply,
      Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul,basis_coordinate_diagonal b A w hA]
    rw [((hF X).contDiffAt.isSymmSndFDerivAt_of_omega) (b k) (b j)]
    ring

end

end OAI
