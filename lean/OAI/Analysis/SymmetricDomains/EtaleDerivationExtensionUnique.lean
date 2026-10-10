import Mathlib
import OAI.Analysis.SymmetricDomains.AnalyticDirectionalDerivationFun

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
namespace Release061

section
open Set Filter Topology
variable {n : ℕ}

noncomputable def analyticCoordinate (i : Fin n) : AnalyticGerm (Fin n → ℂ) :=
  analyticGermOf _ (fun x => x i) ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt _)

theorem analyticGerm_aeval {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ι → E → ℂ) (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (P : MvPolynomial ι ℂ) :
    (MvPolynomial.aeval (fun i => analyticGermOf E (f i) (hf i)) P).val =
      ((fun x => MvPolynomial.eval (fun i => f i x) P) : Filter.Germ (𝓝 (0:E)) ℂ) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.aeval_C,MvPolynomial.eval_C]; rfl
  | add P Q hP hQ =>
    simp only [map_add,Subring.coe_add,hP,hQ]
    rfl
  | mul_X P i hP =>
    simp only [map_mul,MvPolynomial.aeval_X,Subring.coe_mul,hP,MvPolynomial.eval_X]
    rfl

theorem algebraicIndependent_analyticCoordinate :
    AlgebraicIndependent ℂ (analyticCoordinate (n := n)) := by
  rw [algebraicIndependent_iff_ker_eq_bot]
  apply le_antisymm _ bot_le
  intro P hP
  simp only [RingHom.mem_ker,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] at hP
  have he : (fun x : Fin n → ℂ => MvPolynomial.eval x P) =ᶠ[𝓝 0] 0 := by
    apply Filter.Germ.coe_eq.mp
    rw [← analyticGerm_aeval (fun (i : Fin n) (x : Fin n → ℂ) => x i)
      (fun i => (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt _) P]
    exact congrArg Subtype.val hP
  have hzero := (AnalyticOnNhd.eval_mvPolynomial P).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ (0 : Fin n → ℂ)) he
  have : P = 0 := by
    apply MvPolynomial.funext
    intro x
    simpa only [map_zero,Pi.zero_apply] using hzero (mem_univ x)
  simpa only [Ideal.mem_bot] using this

end

open Algebra KaehlerDifferential
open scoped TensorProduct

noncomputable def etaleDerivationExtension
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FormallyEtale A B] (d : Derivation R A B) : Derivation R B B :=
  ((LinearMap.liftBaseChange B d.liftKaehlerDifferential).comp
    (tensorKaehlerEquivOfFormallyEtale R A B).symm.toLinearMap).compDer (D R B)

@[simp] theorem etaleDerivationExtension_algebraMap
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FormallyEtale A B] (d : Derivation R A B) (a : A) :
    etaleDerivationExtension R A B d (algebraMap A B a) = d a := by
  change (LinearMap.liftBaseChange B d.liftKaehlerDifferential)
    ((tensorKaehlerEquivOfFormallyEtale R A B).symm (D R B (algebraMap A B a))) = _
  simp only [tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul,Derivation.liftKaehlerDifferential_comp_D,one_smul]

theorem etaleDerivationExtension_unique
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FormallyEtale A B] (d : Derivation R A B)
    (e : Derivation R B B) (he : ∀ a, e (algebraMap A B a) = d a) :
    e = etaleDerivationExtension R A B d := by
  apply_fun Derivation.liftKaehlerDifferential using fun x y h => by
    ext b
    simpa only [Derivation.liftKaehlerDifferential_comp_D] using congrArg (fun L => L (D R B b)) h
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := (tensorKaehlerEquivOfFormallyEtale R A B).surjective x
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => simpa only [map_add] using congrArg₂ (·+·) hy hz
  | tmul b a =>
    simp only [tensorKaehlerEquivOfFormallyEtale_apply,mapBaseChange_tmul,map_smul]
    congr 1
    have ha : a ∈ Submodule.span A (Set.range (D R A)) := by
      rw [span_range_derivation]; trivial
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨a,rfl⟩ := ha
      simp only [map_D,Derivation.liftKaehlerDifferential_comp_D,
        etaleDerivationExtension_algebraMap,he]
    | zero => simp
    | add a b _ _ ha hb => simp only [map_add,ha,hb]
    | smul c a _ ha => simp only [map_smul,LinearMap.map_smul_of_tower,ha]

end Release061

end

end OAI
