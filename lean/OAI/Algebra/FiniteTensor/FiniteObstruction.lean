import Mathlib
import OAI.Algebra.FiniteTensor.DeformedGraphs
import OAI.Algebra.FiniteTensor.RelativeKoszul

namespace OAI

/-! The finite chart obstruction and formal evaluation of separated potentials. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped TensorProduct BigOperators
open Forms FrobeniusTruncation FiniteCoordinates
attribute [local instance] parameterCharP
universe u
variable (K : Type*) [Field K] (p : ℕ) [CharP K p] [Fact p.Prime] [Invertible (2 : K)]
  {n : ℕ} (σ : Fin (n+1) → Type u) [∀ i,Fintype (σ i)] [∀ i,DecidableEq (σ i)]

 

def sigmaDeformed (S b : ∀ i,A K (σ i) p) (q : Fin 3 ↪ Fin (n+1)) :
    Ring (T K 3) ((i : Fin (n+1)) × σ i) (fun _ => p) :=
  coefficientMap K (T K 3) _ (fun _ => p) (sigmaPotential K p σ S) +
    ∑ i,threeParameters (K:=K) q i •
      coefficientMap K (T K 3) _ (fun _ => p) (sigmaBlock K p σ i (b i))

 

theorem finite_chart_obstruction {d c : ℕ}
    (r : ((i : Fin (n+1)) × σ i) ≃ Fin (c+d))
    (e : ((i : Fin (n+1)) × σ i) ≃ Fin d ⊕ Fin c)
    (q0 : Ring K ((i : Fin (n+1)) × σ i) (fun _ => p) ≃ₐ[K]
      Ring K ((i : Fin (n+1)) × σ i) (fun _ => p))
    (qL : (Fin 3 ↪ Fin (n+1)) →
      Ring (T K 3) ((i : Fin (n+1)) × σ i) (fun _ => p) ≃ₐ[T K 3]
        Ring (T K 3) ((i : Fin (n+1)) × σ i) (fun _ => p))
    (S b : ∀ i,A K (σ i) p) (active : Finset (Fin (n+1)))
    (hb : ∀ i,i∉active → b i=0) (hA : 5≤active.card)
    (hL0 : splitRestriction (Fact.out : p.Prime).pos e q0 (sigmaPotential K p σ S)=0)
    (hR : splitRestriction (Fact.out : p.Prime).pos (e.trans (Equiv.sumComm _ _)) q0
      (sigmaPotential K p σ S)=0)
    (htripR : ∀ s : Finset (Fin (n+1)), s⊆active → s.card=3 →
      splitRestriction (Fact.out : p.Prime).pos (e.trans (Equiv.sumComm _ _)) q0
        (sigmaSelected K p σ b s) ∈ Ideal.span (Set.range (fun i =>
          splitRestriction (Fact.out : p.Prime).pos (e.trans (Equiv.sumComm _ _)) q0
            (chartDerivative K K _ p i (sigmaPotential K p σ S)))))
    (hspecial : ∀ q : Fin 3 ↪ Fin (n+1), (∀ j,q j∈active) → ∀ a,
      coefficientHom K (T K 3) K _ (fun _ => p) (augmentationAlg K 3) (qL q a)=
        q0 (coefficientHom K (T K 3) K _ (fun _ => p) (augmentationAlg K 3) a))
    (hL : ∀ q : Fin 3 ↪ Fin (n+1), (∀ j,q j∈active) →
      splitRestriction (Fact.out : p.Prime).pos e (qL q) (sigmaDeformed K p σ S b q)=0)
    (htripL : ∀ q : Fin 3 ↪ Fin (n+1), (∀ j,q j∈active) →
      splitRestriction (Fact.out : p.Prime).pos e (qL q)
        (algebraMap (T K 3) (Ring (T K 3) ((i : Fin (n+1)) × σ i) (fun _ => p))
          (t K 3 0*t K 3 1*t K 3 2)) ∈ Ideal.span (Set.range (fun i =>
            splitRestriction (Fact.out : p.Prime).pos e (qL q)
              (chartDerivative K (T K 3) _ p i (sigmaDeformed K p σ S b q))))) : False := by
  classical
  obtain ⟨q,κ,hq,hκ,hpair⟩ := exists_three_graph_tensor_cycle K p σ r e q0 S b active hb hA hL0 hR htripR
  let η := sigmaExtendedForms K (T K 3) p σ κ
  let lam := chartNormal K (T K 3) ((i : Fin (n+1)) × σ i) p e (qL q)
  let u : T K 3 := t K 3 0*t K 3 1*t K 3 2
  let J := extendFormFunctional K (T K 3) ((i : Fin (n+1)) × σ i) (fun _ => p)
    (orientedResidue K _ p (Fact.out : p.Prime).pos r)
  have hη : relativeKoszul K (T K 3) _ p (sigmaDeformed K p σ S b q) η=0 := by
    change relativeKoszul K (T K 3) _ p
      (coefficientMap K (T K 3) _ (fun _ => p) (sigmaPotential K p σ S) +
        ∑ i,threeParameters (K:=K) q i •
          coefficientMap K (T K 3) _ (fun _ => p) (sigmaBlock K p σ i (b i)))
        (sigmaExtendedForms K (T K 3) p σ κ)=0
    rw [relativeKoszul_sigmaExtended,hκ]
    exact (sigmaExtendedForms K (T K 3) p σ).map_zero
  have hη' : oneForm K _ _ (fun i =>
      chartDerivative K (T K 3) _ p i (sigmaDeformed K p σ S b q))*η=0 := by
    rw [relativeKoszul_eq] at hη
    exact hη
  have hB := chartNormal_boundary K (T K 3) ((i : Fin (n+1)) × σ i) p
    (Fact.out : p.Prime).pos e (qL q) _ (hL q hq) _ (htripL q hq)
  rw [scalar_parameter_mul] at hB
  have hz : (u • lam)*η=0 := boundary_mul_cycle_zero _ _ _ hB hη'
  have hzero : u * J (lam*η)=0 := by
    change u • J (lam*η)=0
    rw [←map_smul,←smul_mul_assoc,hz,map_zero]
  have hunit : IsUnit (J (lam*η)) := by
    apply isUnit_of_augmentation_ne_zero
    change (augmentationAlg K 3) (extendFormFunctional K (T K 3) _ (fun _ => p)
      (orientedResidue K _ p (Fact.out : p.Prime).pos r) (lam*η))≠0
    rw [extendFormFunctional_specialization,map_mul]
    have hlam := chartNormal_specialization K (T K 3) K ((i : Fin (n+1)) × σ i) p
      (augmentationAlg K 3) e (qL q) q0 (hspecial q hq)
    change mapCoefficients K _ _ _ _ lam=_ at hlam
    rw [hlam]
    change orientedResidue K _ p (Fact.out : p.Prime).pos r
      (chartNormal K K _ p e q0 * mapCoefficients K _ _ _ _
        (sigmaExtendedForms K (T K 3) p σ κ))≠0
    rw [sigmaExtendedForms_specialization]
    exact hpair
  exact triple_mul_unit_ne_zero K 3 0 1 2 (by decide) (by decide) (by decide) hunit hzero

end
end PD4Tensor.TruncatedForms

namespace PD4Tensor.FrobeniusTruncation
noncomputable section
variable (K σ τ : Type*) [Field K] [Fintype σ]
  [Fintype τ] (p : ℕ)

 
theorem formalEval_rename (f : σ → τ) (F : MvPowerSeries σ K) :
    formalEval K τ p (MvPowerSeries.rename f F)=rename K σ p f (formalEval K σ p F) := by
  unfold formalEval
  erw [nilEval_rename]
  have hh := nilEval_map (rename K σ p f) (coord K σ p)
    (fun i => ⟨p,variable_pow K σ p i⟩) F
  simpa only [rename_coord,Function.comp_def] using hh.symm

end
end PD4Tensor.FrobeniusTruncation

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (K R σ : Type*) [CommRing K] [CommRing R] [Algebra K R]
  [Fintype σ] (p : ℕ)

 
theorem nilEval_extension (F : MvPowerSeries σ K) :
    nilEval R (coord R σ (fun _ => p)) (fun j => ⟨p,coord_pow _ _ _ j⟩)
      (MvPowerSeries.map (algebraMap K R) F)=
    coefficientMap K R σ (fun _ => p)
      (nilEval K (coord K σ (fun _ => p)) (fun j => ⟨p,coord_pow _ _ _ j⟩) F) := by
  have hh := nilEval_coefficients (algebraMap K R)
    (coefficientMap K R σ (fun _ => p)).toRingHom
    (fun k => by
      change coefficientMap K R σ (fun _ => p) (algebraMap K (Ring K σ (fun _ => p)) k)=_
      rw [AlgHom.commutes]
      exact IsScalarTower.algebraMap_apply K R (Ring R σ (fun _ => p)) k)
    (coord K σ (fun _ => p)) (fun j => ⟨p,coord_pow _ _ _ j⟩) F
  simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,coefficientMap_coord] at hh
  exact hh.symm

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped BigOperators
open FrobeniusTruncation
universe u
variable (K : Type*) [Field K] (p : ℕ) {n : ℕ}
  (σ : Fin (n+1) → Type u) [∀ i,Fintype (σ i)] [∀ i,DecidableEq (σ i)]

 
 
 
@[simp] theorem formalSigmaPotential_eval (F : ∀ i,MvPowerSeries (σ i) K) :
    formalEval K _ p (formalSigmaPotential K σ F)=
      sigmaPotential K p σ (fun i => formalEval K (σ i) p (F i)) := by
  simp only [formalSigmaPotential,map_sum,formalEval_rename,sigmaPotential]

omit [∀ i,DecidableEq (σ i)] in
@[simp] theorem formalSigmaSelected_eval (b : ∀ i,MvPowerSeries (σ i) K)
    (s : Finset (Fin (n+1))) :
    formalEval K _ p (formalSigmaSelected K σ b s)=
      sigmaSelected K p σ (fun i => formalEval K (σ i) p (b i)) s := by
  simp only [formalSigmaSelected,map_prod,formalEval_rename,sigmaSelected,sigmaBlock]

open FiniteCoordinates in
@[simp] theorem formalSigmaDeformed_eval (F b : ∀ i,MvPowerSeries (σ i) K)
    (q : Fin 3 ↪ Fin (n+1)) :
    nilEval (T K 3) (coord (T K 3) ((i : Fin (n+1)) × σ i) (fun _ => p))
        (fun j => ⟨p,coord_pow _ _ _ j⟩) (formalSigmaDeformed K σ F b q)=
      sigmaDeformed K p σ (fun i => formalEval K (σ i) p (F i))
        (fun i => formalEval K (σ i) p (b i)) q := by
  simp only [formalSigmaDeformed,map_add,map_sum,map_mul,nilEval_extension]
  unfold sigmaDeformed
  congr 1
  · exact congrArg (coefficientMap K (T K 3) _ (fun _ => p))
      (formalSigmaPotential_eval K p σ F)
  · apply Finset.sum_congr rfl
    intro i hi
    erw [show nilEval (T K 3) (coord (T K 3) ((i : Fin (n+1)) × σ i) (fun _ => p))
      (fun j => ⟨p,coord_pow _ _ _ j⟩) (MvPowerSeries.C (threeParameters (K:=K) q i))=
      algebraMap (T K 3) (Ring (T K 3) ((i : Fin (n+1)) × σ i) (fun _ => p))
        (threeParameters (K:=K) q i) from (nilEval (T K 3) _ _).commutes _]
    change algebraMap (T K 3) _ (threeParameters (K:=K) q i)*
      coefficientMap K (T K 3) _ (fun _ => p)
        (formalEval K _ p (MvPowerSeries.rename (Sigma.mk i) (b i)))=_
    rw [formalEval_rename]
    exact (Algebra.smul_def _ _).symm

end
end PD4Tensor.TruncatedForms

namespace PD4Tensor
noncomputable section
open MvPowerSeries.WithPiTopology
variable {R A σ : Type*} [CommRing R] [CommRing A] [Algebra R A] [Finite σ]

theorem nilEval_zero (q : MvPowerSeries σ R) :
    nilEval R (fun _ : σ => (0 : A)) (fun _ => IsNilpotent.zero) q =
      algebraMap R A (MvPowerSeries.constantCoeff q) := by
  let : UniformSpace R := ⊥
  let : UniformSpace A := ⊥
  let : ContinuousSMul R A := ⟨continuous_of_discreteTopology⟩
  have hn : MvPowerSeries.HasEval (fun _ : σ => (0 : A)) :=
    ⟨fun _ => IsNilpotent.zero.isTopologicallyNilpotent,
      by simp only [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩
  have hc : Continuous (nilEval R (fun _ : σ => (0 : A))
      (fun _ => IsNilpotent.zero) : MvPowerSeries σ R → A) := MvPowerSeries.continuous_aeval hn
  have hh := Continuous.ext_on (denseRange_toMvPowerSeries (σ:=σ) (R:=R)) hc
    ((continuous_of_discreteTopology : Continuous (algebraMap R A)).comp
      (continuous_constantCoeff R)) (by
        rintro _ ⟨f,rfl⟩
        rw [nilEval_coe]
        change MvPolynomial.aeval (fun _ : σ => (0 : A)) f =
          algebraMap R A (MvPowerSeries.coeff 0 (f : MvPowerSeries σ R))
        rw [MvPolynomial.coeff_coe]
        exact MvPolynomial.aeval_zero f)
  exact congr_fun hh q

end
end PD4Tensor
end

end OAI
