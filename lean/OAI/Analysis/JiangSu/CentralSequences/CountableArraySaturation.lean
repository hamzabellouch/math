import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerArrayTest
import OAI.Analysis.JiangSu.Nonunital.SIRepresentatives
import OAI.Analysis.JiangSu.Nonunital.RationalTerms

namespace OAI

section

noncomputable section
namespace NormUltra
open Filter Topology
open scoped ENNReal

variable {A : Type*} [NormedAddCommGroup A]

theorem bounded_countable_array_test {I J : Type*} [Countable I] [Nonempty I]
    [Countable J] [Nonempty J] (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ)≤atTop)
    (C : I→ℝ) (hC : ∀ i,0≤C i) (g : J→ℕ→(I→A)→ℝ)
    (hg : ∀ j k x,0≤g j k x)
    (hsupply : ∀ F : Finset J,∀ ε : ℝ,0<ε → ∀ᶠ k in (U : Filter ℕ),
      ∃ x : I→A,(∀ i,‖x i‖≤C i) ∧ ∀ j∈F,g j k x<ε) :
    ∃ x : I→lp (fun _ : ℕ=>A) ∞,(∀ i k,‖x i k‖≤C i) ∧
      ∀ j,Tendsto (fun k=>g j k (fun i=>x i k)) (U : Filter ℕ) (𝓝 0) := by
  classical
  obtain ⟨e,he⟩ := exists_surjective_nat I
  choose r hr using he
  obtain ⟨x,hxn,hx⟩ := bounded_array_test_countable U hfree (C ∘ e) (fun n=>hC (e n))
    (fun j k y=>g j k (fun i=>y (r i))) (fun j k y=>hg j k (fun i=>y (r i)))
    (fun F ε hε=>by
      filter_upwards [hsupply F ε hε] with k ⟨y,hyn,hy⟩
      refine ⟨y ∘ e,fun i=>hyn (e i),?_⟩
      simpa only [Function.comp_apply,hr] using hy)
  refine ⟨fun i=>x (r i),?_,hx⟩
  intro i k
  simpa only [Function.comp_apply,hr] using hxn (r i) k

end NormUltra

end
end

section

noncomputable section
namespace NonunitalCentralSaturation
open Filter Topology NormUltra NormUltra.QuotientAlgebra NonunitalGamma RationalTerms
open scoped ENNReal CStarAlgebra

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (U : Ultrafilter ℕ)
local notation "N" => QuotientAlgebra (fun _ : ℕ=>A) U
local notation "C" => normCentralizer (A := A) U
local notation "Fω" => CentralSequenceAlgebra (A := A) U
local notation "L" => lp (fun _ : ℕ=>A) ∞
local notation "π" => centralSequenceQuotient (A := A) U

omit [PartialOrder A] [StarOrderedRing A] in
lemma exists_bounded_lift (z : Fω) {ε : ℝ} (hε : 0<ε) :
    ∃ (X : C) (x : L),mk U x=(X:N) ∧ π X=z ∧ ‖x‖<‖z‖+ε := by
  obtain ⟨X,hX,hXn⟩ := NonunitalClosedIdeal.QuotientAlgebra.exists_norm_mk_lt
    (normAnnihilator U) z (half_pos hε)
  obtain ⟨x,hx,hxn⟩ := QuotientAlgebra.exists_norm_mk_lt (X:N) (half_pos hε)
  refine ⟨X,x,hx,hX,?_⟩
  change ‖x‖<‖X‖+ε/2 at hxn
  linarith

omit [PartialOrder A] [StarOrderedRing A] in
lemma central_representative_errors (X : C) (x : L) (hx : mk U x=(X:N)) (a : A) :
    Tendsto (fun k=>‖x k*a-a*x k‖) (U : Filter ℕ) (𝓝 0) := by
  apply (mk_eq_mk_iff (x*boundedConstant (A := A) a) (boundedConstant (A := A) a*x)).mp
  rw [mk_mul,mk_mul,hx]
  exact X.property a

omit [PartialOrder A] [StarOrderedRing A] in
lemma quotient_eq_of_dense_errors (a : ℕ→A) (ha : DenseRange a)
    (X Y : C) (x y : L) (hx : mk U x=(X:N)) (hy : mk U y=(Y:N))
    (hleft : ∀ i,Tendsto (fun k=>‖(x k-y k)*a i‖) (U : Filter ℕ) (𝓝 0))
    (hright : ∀ i,Tendsto (fun k=>‖a i*(x k-y k)‖) (U : Filter ℕ) (𝓝 0)) : π X=π Y := by
  apply (NonunitalClosedIdeal.QuotientAlgebra.mk_eq_mk_iff (normAnnihilator U) X Y).mpr
  have he (i : ℕ) : ((X:N)-(Y:N))*normInclusion U (a i)=0 ∧
      normInclusion U (a i)*((X:N)-(Y:N))=0 := by
    constructor
    · have h := (mk_eq_mk_iff ((x-y)*boundedConstant (A := A) (a i)) 0).mpr
        (by simpa only [BoundedFamilies.mem_vanishing,sub_zero,lp.infty_coeFn_mul,
          lp.coeFn_sub,Pi.mul_apply,Pi.sub_apply,boundedConstant_apply] using hleft i)
      rw [mk_mul,mk_sub,mk_zero,hx,hy] at h
      exact h
    · have h := (mk_eq_mk_iff (boundedConstant (A := A) (a i)*(x-y)) 0).mpr
        (by simpa only [BoundedFamilies.mem_vanishing,sub_zero,lp.infty_coeFn_mul,
          lp.coeFn_sub,Pi.mul_apply,Pi.sub_apply,boundedConstant_apply] using hright i)
      rw [mk_mul,mk_sub,mk_zero,hx,hy] at h
      exact h
  intro b
  exact ha.induction_on b
    ((isClosed_eq (continuous_const.mul (map_continuous (normInclusion U))) continuous_const).inter
      (isClosed_eq ((map_continuous (normInclusion U)).mul continuous_const) continuous_const)) he

end NonunitalCentralSaturation

end
end

section

noncomputable section
namespace NonunitalCentralSaturation
open Filter Topology NormUltra NormUltra.QuotientAlgebra NonunitalGamma RationalTerms
open scoped ENNReal CStarAlgebra

local instance finiteModelRationalAlgebra {E : Type*} [CStarAlgebra E] : NormedAlgebra ℚ E := .restrictScalars ℚ ℂ E
variable {D A : Type} [CStarAlgebra D] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (U : Ultrafilter ℕ) [TopologicalSpace.SeparableSpace A] [Fact ((U : Filter ℕ)≤atTop)]
local notation "N" => QuotientAlgebra (fun _ : ℕ=>A) U
local notation "C" => normCentralizer (A := A) U
local notation "Fω" => CentralSequenceAlgebra (A := A) U
local notation "L" => lp (fun _ : ℕ=>A) ∞
local notation "π" => centralSequenceQuotient (A := A) U
local notation "cu" => centralLocalUnit (A := A) U

abbrev Var := ℕ ⊕ Term ℕ
instance : Nonempty Var := ⟨.inl 0⟩
inductive Test where
 | norm : Term ℕ → Test
 | comm : ℕ → Var → Test
 | left : ℕ → Term ℕ → Test
 | right : ℕ → Term ℕ → Test
 | imagLeft : ℕ → Test
 | imagRight : ℕ → Test
 deriving Encodable
instance : Nonempty Test := ⟨.imagLeft 0⟩

def baseBound (d : ℕ→D) : Var→ℝ
 | .inl j => ‖d j‖
 | .inr e => ‖e.eval d‖
lemma baseBound_nonneg (d : ℕ→D) (v : Var) : 0≤baseBound d v := by cases v <;> exact norm_nonneg _

def FiniteModels (d : ℕ→D) : Prop :=
  ∀ E : Finset (Term ℕ),∃ w : ℕ→Fω,(∀ j,‖w j‖≤‖d j‖) ∧
    w 0=algebraMap ℂ Fω Complex.I ∧ ∀ e∈E,‖e.eval w‖≤‖e.eval d‖

def testValue (d : ℕ→D) (a : ℕ→A) (u : A) : Test→(Var→A)→ℝ
 | .norm e,x => max (‖x (.inr e)‖-‖e.eval d‖) 0
 | .comm i v,x => ‖x v*a i-a i*x v‖
 | .left i e,x => ‖(e.localEval u (fun j=>x (.inl j))-x (.inr e))*a i‖
 | .right i e,x => ‖a i*(e.localEval u (fun j=>x (.inl j))-x (.inr e))‖
 | .imagLeft i,x => ‖(x (.inl 0)-(Complex.I:ℂ)•u)*a i‖
 | .imagRight i,x => ‖a i*(x (.inl 0)-(Complex.I:ℂ)•u)‖
omit [PartialOrder A] [StarOrderedRing A] [TopologicalSpace.SeparableSpace A] in
lemma testValue_nonneg (d : ℕ→D) (a : ℕ→A) (u : A) (t : Test) (x : Var→A) :
    0≤testValue d a u t x := by
  cases t with
  | norm e => exact le_max_right _ _
  | _ => exact norm_nonneg _

def Test.terms : Test→Finset (Term ℕ)
 | .norm e => {e}
 | .left _ e => {e}
 | .right _ e => {e}
 | _ => ∅

theorem finite_models_coordinate_supply (d : ℕ→D) (a : ℕ→A)
    (u : L) (hu : mk U u=(cu:N)) (hmodels : FiniteModels (A := A) U d)
    (F : Finset Test) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k in (U : Filter ℕ),∃ x : Var→A,
      (∀ v,‖x v‖≤baseBound d v+1) ∧ ∀ t∈F,testValue d a (u k) t x<ε := by
  classical
  let E := F.biUnion Test.terms
  obtain ⟨w,hwn,hwI,hwe⟩ := hmodels E
  let z : Var→Fω := fun v=>match v with
    | .inl j => w j
    | .inr e => if e∈E then e.eval w else 0
  have hzn (v : Var) : ‖z v‖≤baseBound d v := by
    cases v with
    | inl j => exact hwn j
    | inr e =>
      dsimp [z,baseBound]
      split_ifs with he
      · exact hwe e he
      · simpa only [norm_zero] using (norm_nonneg (e.eval d))
  let η := min ε 1 / 2
  have hη : 0<η := by dsimp [η]; positivity
  have hηε : η<ε := by have := min_le_left ε (1:ℝ); dsimp [η]; linarith
  have hη1 : η<1 := by have := min_le_right ε (1:ℝ); dsimp [η]; linarith
  choose V x hx hV hxn using fun v=>exists_bounded_lift U (z v) hη
  have hxb (v : Var) : ‖x v‖<baseBound d v+η := by
    have := hxn v
    have := hzn v
    linarith
  have hgen (j : ℕ) : π (V (.inl j))=w j := hV (.inl j)
  have haux (e : Term ℕ) (he : e∈E) : π (V (.inr e))=e.eval w := by
    simpa only [z,ite_eq_left he] using hV (.inr e)
  let W : Term ℕ→C := fun e=>e.localEval cu (fun j=>V (.inl j))
  let y : Term ℕ→L := fun e=>e.localEval u (fun j=>x (.inl j))
  have hy (e : Term ℕ) : mk U (y e)=(W e:N) := by
    dsimp [y,W]
    rw [e.mk_localEval]
    simp_rw [hu,hx]
    exact (e.map_localEval cu (fun j=>V (.inl j)) (normCentralInclusion U)).symm
  have hW (e : Term ℕ) : π (W e)=e.eval w := by
    dsimp [W]
    rw [e.map_localEval]
    change e.localEval 1 (fun j=>π (V (.inl j)))=e.eval w
    simp_rw [hgen]
    exact e.localEval_one w
  have hrels (e : Term ℕ) (he : e∈E) :=
    (NonunitalSI.quotient_eq_iff_two_sided_errors U (y e) (x (.inr e)) (W e) (V (.inr e))
      (hy e) (hx (.inr e))).mp ((hW e).trans (haux e he).symm)
  have hIq : π (V (.inl 0))=π ((Complex.I:ℂ)•cu) := by
    rw [hgen,map_smul,hwI]
    exact Algebra.algebraMap_eq_smul_one Complex.I
  have hIrep : mk U ((Complex.I:ℂ)•u)=(((Complex.I:ℂ)•cu:C):N) := by
    rw [mk_smul,hu]
    rfl
  have hIrels := (NonunitalSI.quotient_eq_iff_two_sided_errors U (x (.inl 0))
    ((Complex.I:ℂ)•u) (V (.inl 0)) ((Complex.I:ℂ)•cu) (hx (.inl 0)) hIrep).mp hIq
  have ht (t : Test) (ht : t∈F) : ∀ᶠ k in (U : Filter ℕ),
      testValue d a (u k) t (fun v=>x v k)<ε := by
    cases t with
    | norm e =>
      filter_upwards [] with k
      apply max_lt_iff.mpr
      refine ⟨?_,hε⟩
      have hh := (BoundedFamilies.norm_coordinate_le (x (.inr e)) k).trans_lt (hxb (.inr e))
      change ‖x (.inr e) k‖-‖e.eval d‖<ε
      change ‖x (.inr e) k‖<‖e.eval d‖+η at hh
      linarith
    | comm i v =>
      exact (central_representative_errors U (V v) (x v) (hx v) (a i)).eventually (gt_mem_nhds hε)
    | left i e =>
      have he : e∈E := Finset.mem_biUnion.mpr ⟨.left i e,ht,Finset.mem_singleton_self e⟩
      have hh := ((hrels e he (a i)).1).eventually (gt_mem_nhds hε)
      simpa only [testValue,y,Term.localEval_apply] using hh
    | right i e =>
      have he : e∈E := Finset.mem_biUnion.mpr ⟨.right i e,ht,Finset.mem_singleton_self e⟩
      have hh := ((hrels e he (a i)).2).eventually (gt_mem_nhds hε)
      simpa only [testValue,y,Term.localEval_apply] using hh
    | imagLeft i => exact ((hIrels (a i)).1).eventually (gt_mem_nhds hε)
    | imagRight i => exact ((hIrels (a i)).2).eventually (gt_mem_nhds hε)
  filter_upwards [(eventually_all_finset F).mpr ht] with k hk
  refine ⟨fun v=>x v k,fun v=>?_,hk⟩
  exact (BoundedFamilies.norm_coordinate_le (x v) k).trans ((hxb v).le.trans (by linarith))

end NonunitalCentralSaturation

end
end

end OAI
