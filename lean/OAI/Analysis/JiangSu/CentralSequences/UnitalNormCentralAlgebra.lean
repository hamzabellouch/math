import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.TracialMatrixModelSaturation
import OAI.Analysis.JiangSu.CentralSequences.SigmaOrderZeroLift
import OAI.Analysis.JiangSu.CStarAlgebras.UnitalKernelCutoff

namespace OAI


noncomputable section
namespace DirectComparison

section

open Pureness CurrentMain Filter Topology NormUltra
open scoped ComplexOrder ENNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "D" => FamilyUltrapower (fun τ : TracialState A => τ) U
local notation "ι" => NonunitalGamma.normInclusion (A := A) U

def unitalNormCentralizer : StarSubalgebra ℂ N where
  carrier := {x | ∀ a : A,x*ι a=ι a*x}
  zero_mem' := by intro a; simp only [zero_mul,mul_zero]
  one_mem' := by intro a; simp only [one_mul,mul_one]
  add_mem' hx hy := by intro a; simp only [add_mul,mul_add,hx a,hy a]
  mul_mem' hx hy := by intro a; rw [mul_assoc,hy a,←mul_assoc,hx a,mul_assoc]
  algebraMap_mem' c := by intro a; exact Algebra.commutes c (ι a)
  star_mem' hx := by
    intro a
    have h := congrArg star (hx (star a))
    simpa only [star_mul,←map_star,star_star] using h.symm

omit [PartialOrder A] [StarOrderedRing A] [Nontrivial A] [Nonempty (TracialState A)] in
instance unitalNormCentralizer_closed : IsClosed (unitalNormCentralizer (A := A) U : Set N) := by
  change IsClosed {x : N | ∀ a : A,x*ι a=ι a*x}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun a => isClosed_eq (by fun_prop) (by fun_prop))

instance : CStarAlgebra (unitalNormCentralizer (A := A) U) := by
  letI : SubringClass (StarSubalgebra ℂ N) N := @StarSubalgebra.subringClass ℂ N _ _ _ _ _ _
  exact StarSubalgebra.cstarAlgebra _
instance (priority := 1100) : LE (unitalNormCentralizer (A := A) U) := (CStarAlgebra.spectralOrder _).toLE
instance (priority := 1100) : Preorder (unitalNormCentralizer (A := A) U) := (CStarAlgebra.spectralOrder _).toPreorder
instance (priority := 1100) : PartialOrder (unitalNormCentralizer (A := A) U) := CStarAlgebra.spectralOrder _
instance : StarOrderedRing (unitalNormCentralizer (A := A) U) := CStarAlgebra.spectralOrderedRing _

def normToTracialUnital : N →⋆ₐ[ℂ] D :=
  { normToTracial (A := A) U with
    map_one' := normToTracial_one U
    commutes' := fun c => by
      change normToTracial (A := A) U (algebraMap ℂ N c)=algebraMap ℂ D c
      rw [Algebra.algebraMap_eq_smul_one,map_smul,normToTracial_one,Algebra.algebraMap_eq_smul_one] }

def unitalCentralToTracial : unitalNormCentralizer (A := A) U →⋆ₐ[ℂ] D :=
  (normToTracialUnital U).comp (StarSubalgebra.subtype _)

omit [PartialOrder A] [StarOrderedRing A] [Nontrivial A] [Nonempty (TracialState A)] in
lemma unitalNormCentralizer_nonneg_iff (x : unitalNormCentralizer (A := A) U) :
    0≤x ↔ 0≤(x:N) := by
  constructor
  · exact map_nonneg (StarSubalgebra.subtype _)
  · intro hx
    let r : unitalNormCentralizer (A := A) U := ⟨CFC.sqrt (x:N),fun a =>
      ((show Commute (x:N) (ι a) from x.property a).cfcₙ_nnreal NNReal.sqrt).eq⟩
    have hr : star r*r=x := by
      apply Subtype.ext
      change star (CFC.sqrt (x:N))*CFC.sqrt (x:N)=(x:N)
      rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self _ hx]
    rw [←hr]
    exact star_mul_self_nonneg r

variable [TopologicalSpace.SeparableSpace A]
theorem unitalNormCentralizer_sigma (hfree : (U : Filter ℕ)≤atTop)
    (x w : ℕ → unitalNormCentralizer (A := A) U)
    (hw : ∀ m,unitalCentralToTracial (A := A) U (w m)=0) :
    ∃ d : unitalNormCentralizer (A := A) U,unitalCentralToTracial (A := A) U d=0 ∧ 0≤d ∧ d≤1 ∧
      (∀ m,d*w m=w m) ∧ (∀ m,x m*d=d*x m) := by
  classical
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq A
  let z : ℕ → N := fun m => (Encodable.decode (α := ℕ⊕ℕ) m).elim 0
    (Sum.elim (fun j => ι (a j)) (fun j => (x j:N)))
  obtain ⟨d,hd,hdp,hdn,hdw,hdz⟩ := trace_kernel_sigma_ideal U hfree z (fun m => (w m:N)) hw
  have hda (m : ℕ) : ι (a m)*d=d*ι (a m) := by
    simpa only [z,Encodable.encodek,Option.elim_some,Sum.elim_inl] using hdz (Encodable.encode (Sum.inl m : ℕ⊕ℕ))
  have hdx (m : ℕ) : (x m:N)*d=d*(x m:N) := by
    simpa only [z,Encodable.encodek,Option.elim_some,Sum.elim_inr] using hdz (Encodable.encode (Sum.inr m : ℕ⊕ℕ))
  have hdc : ∀ b : A,d*ι b=ι b*d := by
    have he := ha.equalizer (show Continuous (fun b => d*ι b) by fun_prop)
      (show Continuous (fun b => ι b*d) by fun_prop) (funext (fun m => (hda m).symm))
    exact fun b => congrFun he b
  let d' : unitalNormCentralizer (A := A) U := ⟨d,hdc⟩
  have hp : 0≤d' := (unitalNormCentralizer_nonneg_iff U d').mpr hdp
  exact ⟨d',hd,hp,(CStarAlgebra.norm_le_one_iff_of_nonneg d' hp).mp hdn,
    fun m => Subtype.ext (hdw m),fun m => Subtype.ext (hdx m)⟩

end

open Pureness CurrentMain Filter Topology NormUltra CompletelyPositiveOperations
open scoped ComplexOrder ENNReal CStarAlgebra

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "C" => unitalNormCentralizer (A := A) U
local notation "D" => FamilyUltrapower (fun τ : TracialState A => τ) U
local notation "ι" => NonunitalGamma.normInclusion (A := A) U
local notation "q" => unitalCentralToTracial (A := A) U
local notation "j" => familyUltrapowerMap (fun τ : TracialState A => τ) U

 theorem unital_central_surjective (hfree : (U : Filter ℕ)≤atTop)
    (y : D) (hy : ∀ a : A,Commute y (j a)) : ∃ v : C,q v=y := by
  obtain ⟨v,hv⟩ := normToTracial_surjective (A := A) U y
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq A
  let x : ℕ → N := fun m => ι (a m)
  let w : ℕ → N := fun m => v*x m-x m*v
  have hj (b : A) : normToTracial (A := A) U (ι b)=j b := rfl
  have hw (m : ℕ) : normToTracial (A := A) U (w m)=0 := by
    simp only [w,x,map_sub,map_mul,hv,hj,(hy _).eq,sub_self]
  obtain ⟨d,hd,_hp,_hn,hdw,hdx⟩ := trace_kernel_sigma_ideal U hfree x w hw
  have hc (m : ℕ) : (v-d*v)*x m=x m*(v-d*v) := by
    apply sub_eq_zero.mp
    calc
      (v-d*v)*x m-x m*(v-d*v)=w m-d*w m+(x m*d-d*x m)*v := by dsimp [w]; noncomm_ring
      _=0 := by rw [hdw m,hdx m,sub_self,sub_self,zero_mul,add_zero]
  have hcc : ∀ b : A,(v-d*v)*ι b=ι b*(v-d*v) := by
    have he := ha.equalizer (show Continuous (fun b => (v-d*v)*ι b) by fun_prop)
      (show Continuous (fun b => ι b*(v-d*v)) by fun_prop) (funext hc)
    exact fun b => congrFun he b
  refine ⟨⟨v-d*v,hcc⟩,?_⟩
  change normToTracial (A := A) U (v-d*v)=y
  simp only [map_sub,map_mul,hd,zero_mul,sub_zero,hv]

 theorem unital_central_matrix_lift (hfree : (U : Filter ℕ)≤atTop)
    (n : ℕ) (hn : 0<n) (η : CStarMatrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] D)
    (hη : ∀ M a,Commute (η M) (j a)) :
    ∃ φ : CStarMatrix (Fin n) (Fin n) ℂ →CP C,
      (∀ M,q (φ M)=η M) ∧ (∀ M,‖φ M‖≤‖M‖) ∧
      (∀ M P,φ M*φ P=φ (M*P)*φ 1) := by
  classical
  let : FiniteDimensional ℂ (CStarMatrix (Fin n) (Fin n) ℂ) :=
    FiniteDimensional.of_injective (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.toLinearMap
      (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.injective
  let p : Fin n := ⟨0,hn⟩
  choose v hv using fun i : Fin n => unital_central_surjective U hfree (η (matrixUnit i p)) (hη _)
  let ψ := matrixKraus p v
  have hψ : ∀ M,q (ψ M)=η M := matrixKraus_lift q η p v hv
  obtain ⟨θ,hθ,hθrel⟩ := sigma_order_zero_lift q η ψ hψ (unitalNormCentralizer_sigma U hfree)
  exact order_zero_contractive_cut q η θ hθ hθrel

 theorem comparison_central_order_zero (hfree : (U : Filter ℕ)≤atTop)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcmp : StrictComparison A) (hnuc : IsNuclear A) (n : ℕ) (hn : 0<n) :
    ∃ (η : CStarMatrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] D)
      (φ : CStarMatrix (Fin n) (Fin n) ℂ →CP C),
      (∀ M,q (φ M)=η M) ∧ (∀ M,‖φ M‖≤‖M‖) ∧
      (∀ M P,φ M*φ P=φ (M*P)*φ 1) := by
  obtain ⟨η,hη⟩ := comparison_central_matrix U hfree hsimple hinf hcmp hnuc n hn
  obtain ⟨φ,hφ⟩ := unital_central_matrix_lift U hfree n hn η hη
  exact ⟨η,φ,hφ⟩

end DirectComparison

end

end OAI
