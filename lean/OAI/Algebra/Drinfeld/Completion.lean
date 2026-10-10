import OAI.Algebra.Drinfeld.Categories

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section
namespace LieGrading
open AssociativeElimination UniversalEmbedding WordGrading
variable {R α : Type*} [CommRing R]

def weightSupport (wt : α → ℕ) (p : FreeLieAlgebra R α) : Finset ℕ :=
  (embed p).coeff.support.image (degree wt)

theorem piece_eq_zero_of_not_mem {wt : α → ℕ} {p : FreeLieAlgebra R α} {n : ℕ}
    (hn : n∉weightSupport wt p) : piece wt n p=0 := by
  classical
  apply UniversalEmbedding.injective
  rw [embed_piece,map_zero]
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  rw [WordGrading.piece,project_coeff]
  by_cases hw : degree wt w=n
  · rw [ite_eq_left hw]
    change (embed p).coeff w=0
    by_contra hc
    apply hn
    exact Finset.mem_image.mpr ⟨w,by simpa only [Finsupp.mem_support_iff] using hc,hw⟩
  · rw [ite_eq_right hw]
    rfl

theorem sum_pieces (wt : α → ℕ) (p : FreeLieAlgebra R α) :
    ∑ n∈weightSupport wt p,piece wt n p=p := by
  classical
  apply UniversalEmbedding.injective
  rw [map_sum]
  simp_rw [embed_piece]
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  simp only [MonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,WordGrading.piece,project_coeff]
  by_cases hw : degree wt w∈weightSupport wt p
  · simp only [Finset.sum_ite_eq,hw,ite_true]
  · have hz : (embed p).coeff w=0 := by
      by_contra hc
      apply hw
      exact Finset.mem_image.mpr ⟨w,by simpa only [Finsupp.mem_support_iff] using hc,rfl⟩
    simp [hz]

theorem ext_pieces (wt : α → ℕ) {p q : FreeLieAlgebra R α}
    (h : ∀ n,piece wt n p=piece wt n q) : p=q := by
  have hz : ∀ n,piece wt n (p-q)=0 := by
    intro n
    change projection wt n (p-q)=0
    rw [map_sub]
    change piece wt n p-piece wt n q=0
    rw [h n,sub_self]
  apply sub_eq_zero.mp
  rw [←sum_pieces wt (p-q)]
  simp only [hz,Finset.sum_const_zero]

end LieGrading
namespace PolynomialModuleCoefficients
open Polynomial
variable {M : Type*} [AddCommGroup M] [Module ℚ M]

theorem eq_zero (s : Finset ℕ) (v : ℕ → M)
    (h : ∀ c : ℚ,∑ n∈s,c^n • v n=0) {n : ℕ} (hn : n∈s) : v n=0 := by
  classical
  apply (Module.forall_dual_apply_eq_zero_iff ℚ (v n)).mp
  intro l
  let P : ℚ[X] := ∑ k∈s,Polynomial.monomial k (l (v k))
  have hp : P=0 := by
    apply Polynomial.funext
    intro c
    have he := congrArg l (h c)
    simpa only [P,Polynomial.eval_finsetSum,Polynomial.eval_monomial,map_sum,map_smul,
      map_zero,smul_eq_mul,mul_comm,Polynomial.eval_zero] using he
  have hc := congrArg (fun p : ℚ[X] => p.coeff n) hp
  simpa only [P,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,Polynomial.coeff_zero,
    Finset.sum_ite_eq',hn,ite_true] using hc

theorem mem (E : Submodule ℚ M) (s : Finset ℕ) (v : ℕ → M)
    (h : ∀ c : ℚ,∑ n∈s,c^n • v n∈E) {n : ℕ} (hn : n∈s) : v n∈E := by
  apply (Submodule.Quotient.mk_eq_zero E).mp
  exact eq_zero s (fun n => (Submodule.mkQ E) (v n)) (fun c => by
    have he : E.mkQ (∑ n∈s,c^n • v n)=0 := (Submodule.Quotient.mk_eq_zero E).mpr (h c)
    simpa only [map_sum,map_smul] using he) hn

end PolynomialModuleCoefficients
end

namespace LieGrading
variable {R α β : Type*} [CommRing R]
variable (wa : α → ℕ) (wb : β → ℕ)
variable (f : FreeLieAlgebra R α →ₗ[R] FreeLieAlgebra R β)
variable (hf : ∀ n {p},p∈homogeneousLie wa n → f p∈homogeneousLie wb n)
include hf

theorem map_piece (n : ℕ) (p : FreeLieAlgebra R α) : f (piece wa n p)=piece wb n (f p) := by
  classical
  have he : f p=∑ k∈weightSupport wa p,f (piece wa k p) := by
    rw [←map_sum,sum_pieces]
  rw [he]
  change _=projection wb n (∑ k∈weightSupport wa p,f (piece wa k p))
  rw [map_sum]
  simp only [projection,LinearMap.coe_mk,AddHom.coe_mk]
  simp_rw [piece_homogeneous (hf _ (piece_spec wa _ p).1)]
  by_cases hn : n∈weightSupport wa p
  · simp [hn]
  · rw [piece_eq_zero_of_not_mem hn,map_zero]
    simp [hn]

theorem injective_of_homogeneous
    (hi : ∀ n {p q},p∈homogeneousLie wa n → q∈homogeneousLie wa n → f p=f q → p=q) :
    Function.Injective f := by
  intro p q hpq
  apply ext_pieces wa
  intro n
  apply hi n (piece_spec wa n p).1 (piece_spec wa n q).1
  rw [map_piece wa wb f hf,map_piece wa wb f hf,hpq]

theorem reflects_homogeneous (hi : Function.Injective f) {n : ℕ} {p : FreeLieAlgebra R α}
    (hp : f p∈homogeneousLie wb n) : p∈homogeneousLie wa n := by
  have he : piece wa n p=p := by
    apply hi
    rw [map_piece wa wb f hf,piece_homogeneous hp,ite_eq_left rfl]
  rw [←he]
  exact (piece_spec wa n p).1

end LieGrading

section
namespace SolutionGrading
open LieGrading AssociativeElimination UniversalEmbedding

def dilation (c : ℚ) : L →ₗ⁅ℚ⁆ L := eval (c • x) (c • y)
@[simp] theorem dilation_x (c : ℚ) : dilation c x=c • x := eval_x _ _
@[simp] theorem dilation_y (c : ℚ) : dilation c y=c • y := eval_y _ _

theorem eval_dilation {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (c : ℚ) (a b : M) (p : L) : eval a b (dilation c p)=eval (c • a) (c • b) p := by
  simp only [dilation,map_eval,map_smul,eval_x,eval_y]

def braidDilation (c : ℚ) : T4 →ₗ⁅ℚ⁆ T4 :=
  T4Universal.lift (fun i j => c • t i j)
    (by intros; rw [t_comm]) (by intros; rw [t_self,smul_zero])
    (by intros; rw [smul_lie,lie_smul,t_disjoint _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›,smul_zero,smul_zero])
    (by intros; rw [←smul_add,smul_lie,lie_smul,t_three _ _ _ ‹_› ‹_› ‹_›,smul_zero,smul_zero])

@[simp] theorem braidDilation_t (c : ℚ) (i j : Fin 4) : braidDilation c (t i j)=c • t i j :=
  T4Universal.lift_t _ _ _ _ _ _ _

theorem dilation_W (c : ℚ) {p : L} (hp : p∈W) : dilation c p∈W := by
  change IsSolution (dilation c p)
  constructor
  · have h := congrArg (dilation c) hp.1
    simp only [map_add,map_zero,map_eval,dilation_x,dilation_y] at h
    simpa only [eval_dilation] using h
  constructor
  · have h := congrArg (dilation c) hp.2.1
    simp only [map_add,map_zero,map_eval,map_sub,map_neg,dilation_x,dilation_y,←smul_neg,←smul_sub] at h
    simpa only [eval_dilation] using h
  · have h := congrArg (braidDilation c) hp.2.2
    simp only [map_add,map_eval,braidDilation_t,←smul_add] at h
    simpa only [eval_dilation] using h

theorem dilation_homogeneous (c : ℚ) {n : ℕ} {p : L}
    (hp : p∈homogeneousLie (fun _ => 1) n) : dilation c p=c^n • p := by
  have ht : ∀ t : UniversalEmbedding.Tree Bool,dilation c t.eval=c^(treeDegree (fun _ => 1) t) • t.eval := by
    intro t
    induction t with
    | leaf a => cases a <;> simp [Tree.eval,dilation,x,y,treeDegree_leaf,eval]
    | node t u ht hu =>
      simp only [Tree.eval,LieHom.map_lie,treeDegree_node,ht,hu,smul_lie,lie_smul,smul_smul,←pow_add,Nat.add_comm]
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨t,hn,rfl⟩ := hp; simpa only [hn] using ht t
  | zero => simp
  | add p q _ _ hp hq => simp only [map_add,hp,hq,smul_add]
  | smul a p _ hp => simp only [map_smul,hp,smul_smul,mul_comm]

theorem dilation_sum (c : ℚ) (p : L) :
    dilation c p=∑ n∈weightSupport (fun _ => 1) p,c^n • piece (fun _ => 1) n p := by
  conv_lhs => rw [←sum_pieces (fun _ => 1) p]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact dilation_homogeneous c (piece_spec (fun _ => 1) n p).1

theorem piece_W {p : L} (hp : p∈W) (n : ℕ) : piece (fun _ => 1) n p∈W := by
  classical
  by_cases hn : n∈weightSupport (fun _ => 1) p
  · apply PolynomialModuleCoefficients.mem W (weightSupport (fun _ => 1) p)
      (fun n => piece (fun _ => 1) n p) ?_ hn
    intro c
    rw [←dilation_sum]
    exact dilation_W c hp
  · rw [piece_eq_zero_of_not_mem hn]
    exact W.zero_mem

theorem piece_Wn {p : L} (hp : p∈W) (n : ℕ) : piece (fun _ => 1) n p∈Wn n := by
  exact ⟨piece_W hp n,by change _∈weightPiece (fun _ => 1) n; rw [LieGrading.weightPiece_eq]; exact (piece_spec (fun _ => 1) n p).1⟩

end SolutionGrading

theorem completed_leftInverse (e : OddFree ≃ₗ[ℚ] W) (h : Graded e) :
    Function.LeftInverse (completedInv e h) (completed e h) := by
  intro a
  funext n
  apply Subtype.ext
  change e.symm (e (a n))=(a n : OddFree)
  exact e.symm_apply_apply _

theorem completed_rightInverse (e : OddFree ≃ₗ[ℚ] W) (h : Graded e) :
    Function.RightInverse (completedInv e h) (completed e h) := by
  intro a
  funext n
  apply Subtype.ext
  change (e (e.symm ⟨a n,(a n).property.1⟩) : L)=(a n : L)
  rw [e.apply_symm_apply]

theorem completed_continuous (e : OddFree ≃ₗ[ℚ] W) (h : Graded e) :
    Continuous (completed e h) := by
  let : DiscreteTopology OddFree := ⟨rfl⟩
  apply continuous_pi
  intro n
  let f : Fn n → Wn n := fun p => ⟨e p,(e p).property,(h n p).2 p.property⟩
  exact (continuous_of_discreteTopology (f:=f)).comp (continuous_apply n)

theorem completedInv_continuous (e : OddFree ≃ₗ[ℚ] W) (h : Graded e) :
    Continuous (completedInv e h) := by
  let : DiscreteTopology L := ⟨rfl⟩
  apply continuous_pi
  intro n
  let f : Wn n → Fn n := fun p => ⟨e.symm ⟨p,p.property.1⟩,
    (h n _).1 (by rw [e.apply_symm_apply]; exact p.property.2)⟩
  exact (continuous_of_discreteTopology (f:=f)).comp (continuous_apply n)

theorem completed_bracket (e : OddFree ≃ₗ[ℚ] W) (h : Graded e)
    (he : ∀ a b,(e ⁅a,b⁆ : L)=ihara (e a) (e b))
    (a b : OddCompletion) (n : ℕ) :
    (e (∑ i ∈ Finset.range (n+1),⁅(a i : OddFree),(b (n-i) : OddFree)⁆) : L)=
      ∑ i ∈ Finset.range (n+1),ihara (completed e h a i) (completed e h b (n-i)) := by
  simp only [map_sum,Submodule.coe_sum,he]
  rfl

namespace GradedGeneration
open LieGrading

instance finite_Fn (n : ℕ) : Module.Finite ℚ (Fn n) := by
  change Module.Finite ℚ (weightPiece oddWeight n)
  rw [weightPiece_eq]
  infer_instance

theorem Fn_eq_bot {n : ℕ} (hn : n≤2) : Fn n=⊥ := by
  change weightPiece oddWeight n=⊥
  rw [weightPiece_eq]
  apply le_antisymm ?_ bot_le
  apply Submodule.span_le.mpr
  rintro p ⟨t,ht,rfl⟩
  have h := treeDegree_lower (m:=3) (wt:=oddWeight) (by intro k; simp [oddWeight]) t
  omega

variable (v : ℕ → L) (hv : ∀ k,v k∈Ln (oddWeight k))
include hv

 theorem homogeneous {n : ℕ} {p : OddFree} (hp : p∈Fn n) :
    GenericIhara.evalIhara v p∈Ln n := by
  change _∈weightPiece (fun _ => 1) n
  rw [weightPiece_eq]
  apply homogeneous_iff.mpr
  apply GenericIhara.evalIhara_homogeneous oddWeight v (fun k => ?_) (by
    change p∈weightPiece oddWeight n at hp
    rwa [weightPiece_eq] at hp)
  apply homogeneousLie_embed
  have h := hv k
  change v k∈weightPiece (fun _ => 1) (oddWeight k) at h
  rwa [weightPiece_eq] at h

variable (hW : ∀ p,GenericIhara.evalIhara v p∈W)

def valuePiece (n : ℕ) : Fn n →ₗ[ℚ] Wn n :=
  ((GenericIhara.evalIhara v).comp (Fn n).subtype).codRestrict _
    (fun p => ⟨hW p,homogeneous v hv p.property⟩)

variable (hi : ∀ n,2<n → Function.Injective (valuePiece v hv hW n))
include hW hi

theorem valuePiece_injective (n : ℕ) : Function.Injective (valuePiece v hv hW n) := by
  by_cases hn : 2<n
  · exact hi n hn
  · intro p q _
    have hp := p.property
    have hq := q.property
    simp only [Fn_eq_bot (show n≤2 by omega),Submodule.mem_bot] at hp hq
    exact Subtype.ext (hp.trans hq.symm)

theorem values_injective : Function.Injective (GenericIhara.evalIhara v) := by
  apply injective_of_homogeneous oddWeight (fun _ => 1) _ ?_ ?_
  · intro n p hp
    rw [←weightPiece_eq] at hp ⊢
    exact homogeneous v hv hp
  · intro n p q hp hq he
    rw [←weightPiece_eq] at hp hq
    exact congrArg Subtype.val (valuePiece_injective v hv hW hi n
      (Subtype.ext he : valuePiece v hv hW n ⟨p,hp⟩=valuePiece v hv hW n ⟨q,hq⟩))

theorem valuePiece_surjective (n : ℕ) : Function.Surjective (valuePiece v hv hW n) := by
  by_cases hn : 2<n
  · apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp (hi n hn)
    apply le_antisymm
    · exact LinearMap.finrank_le_finrank_of_injective (hi n hn)
    · exact RationalBound.finrank_Wn_le n hn
  · intro q
    refine ⟨0,?_⟩
    rw [map_zero]
    apply Subtype.ext
    have hq := q.property
    simp only [LowWeight.Wn_eq_bot (show n≤2 by omega),Submodule.mem_bot] at hq
    exact hq.symm

def valueMap : OddFree →ₗ[ℚ] W := (GenericIhara.evalIhara v).codRestrict _ hW

theorem valueMap_bijective : Function.Bijective (valueMap v hW) := by
  constructor
  · intro p q he
    exact values_injective v hv hW hi (congrArg Subtype.val he)
  · intro q
    classical
    have hs : ∀ n,∃ p : Fn n,valuePiece v hv hW n p=⟨piece (fun _ => 1) n q.val,
        SolutionGrading.piece_Wn q.property n⟩ := by
      intro n
      exact valuePiece_surjective v hv hW hi n _
    choose p hp using hs
    refine ⟨∑ n∈weightSupport (fun _ => 1) q.val,(p n).val,?_⟩
    apply Subtype.ext
    change GenericIhara.evalIhara v (∑ n∈weightSupport (fun _ => 1) q.val,(p n).val)=q.val
    rw [map_sum]
    calc
      _ = ∑ n∈weightSupport (fun _ => 1) q.val,piece (fun _ => 1) n q.val := by
        apply Finset.sum_congr rfl
        intro n _
        exact congrArg Subtype.val (hp n)
      _ = q.val := sum_pieces _ _

def equivalence : OddFree ≃ₗ[ℚ] W := LinearEquiv.ofBijective (valueMap v hW) (valueMap_bijective v hv hW hi)

theorem equivalence_graded : Graded (equivalence v hv hW hi) := by
  intro n p
  change GenericIhara.evalIhara v p∈Ln n ↔ p∈Fn n
  constructor
  · intro hp
    change _∈weightPiece oddWeight n
    rw [weightPiece_eq]
    have hhom : ∀ m {q},q∈homogeneousLie oddWeight m →
        GenericIhara.evalIhara v q∈homogeneousLie (fun _ => 1) m := by
      intro m q hq
      rw [←weightPiece_eq] at hq ⊢
      exact homogeneous v hv hq
    have hpx : GenericIhara.evalIhara v p∈homogeneousLie (fun _ => 1) n := by
      change _∈weightPiece (fun _ => 1) n at hp
      rwa [weightPiece_eq] at hp
    exact reflects_homogeneous oddWeight (fun _ => 1) (GenericIhara.evalIhara v)
      (hf := hhom) (values_injective v hv hW hi) hpx
  · exact homogeneous v hv

theorem main_of_values : MainStatement := by
  let e := equivalence v hv hW hi
  have hg : Graded e := equivalence_graded v hv hW hi
  have hb : ∀ a b,(e ⁅a,b⁆ : L)=ihara (e a) (e b) := by
    intro a b
    change GenericIhara.evalIhara v ⁅a,b⁆=ihara (GenericIhara.evalIhara v a) (GenericIhara.evalIhara v b)
    rw [GenericIhara.evalIhara_lie,GenericIhara.rational_ihara]
  exact ⟨e,hg,hb,completed_leftInverse e hg,completed_rightInverse e hg,
    completed_continuous e hg,completedInv_continuous e hg,completed_bracket e hg hb⟩

end GradedGeneration
end

namespace IntegralFamily
open LieGrading
variable {V : Values} (f : Family V)

def rangeValues : Values where
  space := (GenericIhara.evalIhara (cast f ℚ)).range
  le_W := by rintro p ⟨q,rfl⟩; exact V.le_W (rational_mem f q)
  bracket := by
    rintro p q ⟨a,rfl⟩ ⟨b,rfl⟩
    exact ⟨⁅a,b⁆,by rw [GenericIhara.evalIhara_lie,GenericIhara.rational_ihara]⟩

def rangeFamily : Family (rangeValues f) where
  value := f.value
  homogeneous := f.homogeneous
  member k := ⟨FreeLieAlgebra.of ℚ k,GenericIhara.evalIhara_of _ _⟩

def rangePiece (n : ℕ) : homogeneousLie (R:=ℚ) oddWeight n →ₗ[ℚ] piece (rangeValues f) n :=
  { toFun p := ⟨⟨GenericIhara.evalIhara (cast f ℚ) p.val,
      V.le_W (rational_mem f p.val),by
        change _∈weightPiece (fun _ => 1) n
        rw [weightPiece_eq]
        exact eval_homogeneous f ℚ p.property⟩,⟨p.val,rfl⟩⟩
    map_add' p q := by apply Subtype.ext; apply Subtype.ext; exact map_add _ _ _
    map_smul' c p := by apply Subtype.ext; apply Subtype.ext; exact map_smul _ _ _ }

theorem rangePiece_surjective (n : ℕ) : Function.Surjective (rangePiece f n) := by
  intro p
  obtain ⟨q,hq⟩ := p.property
  refine ⟨⟨LieGrading.piece oddWeight n q,(piece_spec oddWeight n q).1⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change GenericIhara.evalIhara (cast f ℚ) (LieGrading.piece oddWeight n q)=p.val.val
  rw [map_piece oddWeight (fun _ => 1) _ (fun _ _ hp => eval_homogeneous f ℚ hp),hq]
  have hp : p.val.val∈homogeneousLie (fun _ => 1) n := by
    have hp := p.val.property.2
    change _∈weightPiece (fun _ => 1) n at hp
    rwa [weightPiece_eq] at hp
  change LieGrading.piece (fun _ => 1) n p.val.val=p.val.val
  rw [piece_homogeneous hp,ite_eq_left rfl]

variable (g : NormalizedFamily.Data) (hg : g.value=cast f K) (ha : ∀ k,g.active k)
include hg ha

theorem range_dimension_lower (n : ℕ) (hn : 2<n) :
    Module.finrank ℚ (homogeneousLie (R:=ℚ) oddWeight n)≤Module.finrank ℚ (piece (rangeValues f) n) := by
  let h : homogeneousLie (R:=K) oddWeight n →ₗ[K]
      SaturatedSolutions.reduction n (piece (rangeValues f) n) :=
    (reducedValue (rangeFamily f) n).codRestrict _ (reduced_mem (rangeFamily f))
  have hi : Function.Injective h := by
    intro p q hpq
    apply NormalizedFamily.valueMap_injective g n (by omega) ha
    apply Subtype.ext
    change GenericIhara.evalIhara g.value p.val=GenericIhara.evalIhara g.value q.val
    rw [hg]
    exact congrArg (fun z => z.val.val) hpq
  have he : Module.finrank ℚ (homogeneousLie (R:=ℚ) oddWeight n)=
      Module.finrank K (homogeneousLie (R:=K) oddWeight n) :=
    (LieDimension.finrank_homogeneous K oddWeight n).symm
  rw [he,←SaturatedSolutions.finrank_reduction n (piece (rangeValues f) n) hn]
  exact LinearMap.finrank_le_finrank_of_injective hi

theorem rangePiece_injective (n : ℕ) (hn : 2<n) : Function.Injective (rangePiece f n) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr (rangePiece_surjective f n)
  exact le_antisymm (range_dimension_lower f g hg ha n hn)
    (LinearMap.finrank_le_finrank_of_surjective (rangePiece_surjective f n))

theorem main_of_normalized : MainStatement := by
  have hv : ∀ k,cast f ℚ k∈Ln (oddWeight k) := by
    intro k
    change _∈weightPiece (fun _ => 1) (oddWeight k)
    rw [weightPiece_eq]
    exact cast_homogeneous f ℚ k
  have hW : ∀ p,GenericIhara.evalIhara (cast f ℚ) p∈W := fun p => V.le_W (rational_mem f p)
  apply GradedGeneration.main_of_values (cast f ℚ) hv hW
  intro n hn p q hpq
  apply Subtype.ext
  have hp : p.val∈homogeneousLie oddWeight n := by
    have hp := p.property
    change _∈weightPiece oddWeight n at hp
    rwa [weightPiece_eq] at hp
  have hq : q.val∈homogeneousLie oddWeight n := by
    have hq := q.property
    change _∈weightPiece oddWeight n at hq
    rwa [weightPiece_eq] at hq
  exact congrArg (fun z : homogeneousLie (R:=ℚ) oddWeight n => z.val) (rangePiece_injective f g hg ha n hn
    (show rangePiece f n ⟨p.val,hp⟩=rangePiece f n ⟨q.val,hq⟩ from
      Subtype.ext (Subtype.ext (congrArg Subtype.val hpq))))

omit hg ha in

theorem main_of_oddValues (V : Values) (h : OddValues V) : MainStatement :=
  main_of_normalized (normalizedFamily V h) (normalizedData V h) rfl (fun _ => True.intro)

end IntegralFamily

namespace CategoricalValues

def OddWitnesses : Prop := ∀ k,∃ w : Witness,
  value w∈Ln (oddWeight k) ∧
  (AssociativeElimination.embed (value w)).coeff (GenericIhara.depthOneWord (oddWeight k-1))≠0

theorem main_of_oddWitnesses (h : OddWitnesses) : MainStatement := by
  apply IntegralFamily.main_of_oddValues values
  intro k
  obtain ⟨w,hw,hc⟩ := h k
  exact ⟨⟨value w,value_mem w,hw⟩,⟨w,rfl⟩,hc⟩

open CategoryGauge

def ofSolution {n : ℕ} {q : L} (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : Witness where
  three := ThreeSolutionCategory.data q
  four := FourSolutionCategory.data hq hqn hn
  swap := ThreeSolutionCategory.swap hq
  rotate := ThreeSolutionCategory.rotate hq hqn hn
  kill_x := by simp [ThreeSolutionCategory.loop_zero,derivation_apply]
  kill_y := by
    simp only [loop_apply,ThreeSolutionCategory.data,Matrix.cons_val_one,Matrix.cons_val_zero,
      derivation_apply,D_y,←lie_skew y q]
    abel
  AD := FourSolutionCategory.AD hq hqn hn
  DE := FourSolutionCategory.DE hq hqn hn
  AB := FourSolutionCategory.AB hq hqn hn
  BC := FourSolutionCategory.BC hq hqn hn
  CE := FourSolutionCategory.CE hq hqn hn

@[simp] theorem value_ofSolution {n : ℕ} {q : L} (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    value (ofSolution hq hqn hn)=q := ThreeSolutionCategory.value q

theorem Wn_le_values (n : ℕ) : Wn n≤values.space := by
  intro q hq
  by_cases hn : 2<n
  · exact ⟨ofSolution hq.1 hq.2 hn,value_ofSolution hq.1 hq.2 hn⟩
  · have he : q=0 := by
      have hh := hq
      rw [LowWeight.Wn_eq_bot (by omega : n≤2)] at hh
      exact hh
    rw [he]
    exact values.space.zero_mem

theorem values_eq_W : values.space=W := by
  apply le_antisymm values.le_W
  intro q hq
  classical
  rw [←LieGrading.sum_pieces (fun _ => 1) q]
  apply Submodule.sum_mem
  intro n hn
  exact Wn_le_values n (SolutionGrading.piece_Wn hq n)

theorem W_ihara_closed {p q : L} (hp : p∈W) (hq : q∈W) : ihara p q∈W := by
  rw [←values_eq_W] at hp hq ⊢
  exact values.bracket hp hq

theorem main_of_oddSolutions
    (h : ∀ k,∃ q : L,q∈Wn (oddWeight k) ∧
      (AssociativeElimination.embed q).coeff (GenericIhara.depthOneWord (oddWeight k-1))≠0) :
    MainStatement := by
  apply main_of_oddWitnesses
  intro k
  obtain ⟨q,hq,hc⟩ := h k
  exact ⟨ofSolution hq.1 hq.2 (by unfold oddWeight; omega),by simpa using hq.2,by simpa using hc⟩

end CategoricalValues

open AssociativeElimination WordGrading
 theorem real_odd_nonzero (k : ℕ) :
    (embed (RealDeligneDrinfeld.KZHomogeneous.q (2*k+3))).coeff (GenericIhara.depthOneWord (2*k+2))≠0 := by
  rw [RealDeligneDrinfeld.KZHomogeneous.q_embed_any (2*k+3) (2*k+3) le_rfl]
  change (piece (fun _ => 1) (2*k+3) _).coeff _≠0
  rw [piece,project_coeff,ite_eq_left (by rw [CutoffDepth.length_depthOne])]
  exact KZComparison.odd_value_nonzero k
 theorem odd_solution (k : ℕ) : ∃ q : L,q∈Wn (oddWeight k) ∧
    (embed q).coeff (GenericIhara.depthOneWord (oddWeight k-1))≠0 := by
  have hh := RationalScalar.descend (RealDeligneDrinfeld.KZHomogeneous.coefficient_solution (2*k+3))
    (RealDeligneDrinfeld.KZHomogeneous.q_homogeneous (2*k+3))
    (GenericIhara.depthOneWord (2*k+2)) (real_odd_nonzero k)
  simpa only [oddWeight,show 2*k+3-1=2*k+2 by omega] using hh
 theorem main : MainStatement := CategoricalValues.main_of_oddSolutions odd_solution

end DeligneDrinfeld

end

end OAI
