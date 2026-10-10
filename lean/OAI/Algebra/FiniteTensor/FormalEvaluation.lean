import Mathlib
import OAI.Algebra.FiniteTensor.CoordinateEquivalences

namespace OAI

/-! Nilpotent formal evaluation and bijective formal substitutions. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor
open MvPowerSeries.WithPiTopology
noncomputable section
variable (K : Type*) [CommRing K] {A σ : Type*} [CommRing A] [Algebra K A] [Finite σ]

 

def nilEval (v : σ → A) (hv : ∀ i, IsNilpotent (v i)) : MvPowerSeries σ K →ₐ[K] A := by
  letI : UniformSpace K := ⊥
  letI : UniformSpace A := ⊥
  letI : ContinuousSMul K A := ⟨continuous_of_discreteTopology⟩
  exact MvPowerSeries.aeval ⟨fun i => (hv i).isTopologicallyNilpotent,
    by simp only [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩

@[simp] theorem nilEval_X (v : σ → A) (hv : ∀ i, IsNilpotent (v i)) (i : σ) :
    nilEval K v hv (MvPowerSeries.X i)=v i := by
  let : UniformSpace K := ⊥
  let : UniformSpace A := ⊥
  let : ContinuousSMul K A := ⟨continuous_of_discreteTopology⟩
  simp only [nilEval,MvPowerSeries.coe_aeval]
  change MvPowerSeries.eval₂ (algebraMap K A) v (MvPowerSeries.X i)=v i
  exact MvPowerSeries.eval₂_X (algebraMap K A) v i

@[simp] theorem nilEval_coe (v : σ → A) (hv : ∀ i, IsNilpotent (v i)) (q : MvPolynomial σ K) :
    nilEval K v hv (q : MvPowerSeries σ K)=MvPolynomial.aeval v q := by
  let : UniformSpace K := ⊥
  let : UniformSpace A := ⊥
  let : ContinuousSMul K A := ⟨continuous_of_discreteTopology⟩
  exact MvPowerSeries.aeval_coe _ q

variable {K}
 
theorem nilEval_map {B : Type*} [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (v : σ → A) (hv : ∀ i, IsNilpotent (v i))
    (q : MvPowerSeries σ K) :
    f (nilEval K v hv q)=nilEval K (fun i => f (v i)) (fun i => (hv i).map f) q := by
  let : UniformSpace K := ⊥
  let : UniformSpace A := ⊥
  let : ContinuousSMul K A := ⟨continuous_of_discreteTopology⟩
  let : UniformSpace B := ⊥
  let : ContinuousSMul K B := ⟨continuous_of_discreteTopology⟩
  let hn : MvPowerSeries.HasEval v := ⟨fun i => (hv i).isTopologicallyNilpotent,
    by simp only [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩
  exact DFunLike.congr_fun (MvPowerSeries.comp_aeval hn (continuous_of_discreteTopology : Continuous f)) q

 

theorem nilEval_nilpotent (v : σ → A) (hv : ∀ i, IsNilpotent (v i))
    (q : MvPowerSeries σ K) (hq : IsNilpotent (MvPowerSeries.constantCoeff q)) :
    IsNilpotent (nilEval K v hv q) := by
  let : UniformSpace K := ⊥
  let : UniformSpace A := ⊥
  let : ContinuousSMul K A := ⟨continuous_of_discreteTopology⟩
  let hn : MvPowerSeries.HasEval v := ⟨fun i => (hv i).isTopologicallyNilpotent,
    by simp only [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩
  have h := (isTopologicallyNilpotent_of_constantCoeff_isNilpotent hq).map
    (MvPowerSeries.continuous_aeval hn)
  simp_rw [IsTopologicallyNilpotent,nhds_discrete,Filter.tendsto_pure] at h
  exact h.exists

 

theorem nilEval_subst {R τ : Type*} [CommRing R] [Algebra K R] [Algebra R A]
    [IsScalarTower K R A] [Finite τ]
    (a : σ → MvPowerSeries τ R) (ha : MvPowerSeries.HasSubst a)
    (v : τ → A) (hv : ∀ i, IsNilpotent (v i))
    (q : MvPowerSeries σ K) :
    nilEval R v hv (MvPowerSeries.subst a q)=
      nilEval K (fun i => nilEval R v hv (a i))
        (fun i => nilEval_nilpotent v hv (a i) (ha.const_coeff i)) q := by
  let : UniformSpace K := ⊥
  let : UniformSpace R := ⊥
  let : UniformSpace A := ⊥
  let : ContinuousSMul K A := ⟨continuous_of_discreteTopology⟩
  let : ContinuousSMul R A := ⟨continuous_of_discreteTopology⟩
  simp only [nilEval,MvPowerSeries.coe_aeval]
  exact MvPowerSeries.eval₂_subst ha
    ⟨fun i => (hv i).isTopologicallyNilpotent,
      by simp only [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩ q

 
omit [Finite σ] in
theorem continuous_formal_pderiv [TopologicalSpace K] [IsTopologicalRing K]
    [DecidableEq σ] (i : σ) : Continuous (MvPowerSeries.pderiv i : MvPowerSeries σ K → _) := by
  apply continuous_pi
  intro d
  change Continuous (fun f : MvPowerSeries σ K =>
    MvPowerSeries.coeff (d+Finsupp.single i 1) f * (d i+1 : K))
  exact (continuous_coeff K _).mul continuous_const

 

theorem nilEval_pderiv_coe [DecidableEq σ] (v : σ → A) (hv : ∀ i, IsNilpotent (v i))
    (i : σ) (D : Derivation K A A) (hD : ∀ j, D (v j)=if i=j then 1 else 0)
    (q : MvPolynomial σ K) :
    D (nilEval K v hv (q : MvPowerSeries σ K))=
      nilEval K v hv (MvPowerSeries.pderiv i (q : MvPowerSeries σ K)) := by
  rw [MvPowerSeries.pderiv_coe]
  simp only [nilEval_coe]
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add q r hq hr => simp only [map_add,hq,hr]
  | mul_X q j hq =>
    simp only [map_mul,Derivation.leibniz,MvPolynomial.aeval_X,
      MvPolynomial.pderiv_X,hD,hq,smul_eq_mul,map_add,apply_ite]
    split_ifs <;> simp_all [eq_comm]

 

theorem nilEval_pderiv [DecidableEq σ] (v : σ → A) (hv : ∀ i, IsNilpotent (v i))
    (i : σ) (D : Derivation K A A) (hD : ∀ j, D (v j)=if i=j then 1 else 0)
    (q : MvPowerSeries σ K) :
    D (nilEval K v hv q)=nilEval K v hv (MvPowerSeries.pderiv i q) := by
  let : UniformSpace K := ⊥
  let : UniformSpace A := ⊥
  let : ContinuousSMul K A := ⟨continuous_of_discreteTopology⟩
  let hn : MvPowerSeries.HasEval v := ⟨fun i => (hv i).isTopologicallyNilpotent,
    by simp only [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩
  have hc : Continuous (nilEval K v hv : MvPowerSeries σ K → A) :=
    MvPowerSeries.continuous_aeval hn
  have h := Continuous.ext_on (denseRange_toMvPowerSeries (σ:=σ) (R:=K))
    ((continuous_of_discreteTopology : Continuous D).comp hc)
    (hc.comp (continuous_formal_pderiv i)) (by
      rintro _ ⟨r,rfl⟩
      exact nilEval_pderiv_coe v hv i D hD r)
  exact congr_fun h q

end
end PD4Tensor

namespace PD4Tensor.FrobeniusTruncation
noncomputable section
open MvPowerSeries.WithPiTopology
variable (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ] (p : ℕ)
  [CharP K p] [Fact p.Prime]

def boundedCoeff (a : σ →₀ ℕ) (ha : ∀ i, a i<p) : Ring K σ p →ₗ[K] K :=
  ((ideal K σ p).restrictScalars K).liftQ (MvPolynomial.lcoeff K a) (by
    intro q hq
    exact coeff_zero_of_mem_ideal K σ p a ha q hq)

omit [Fintype σ] [DecidableEq σ] [CharP K p] [Fact p.Prime] in
@[simp] theorem boundedCoeff_mk (a : σ →₀ ℕ) (ha : ∀ i, a i<p) (q : MvPolynomial σ K) :
    boundedCoeff K σ p a ha (Ideal.Quotient.mk (ideal K σ p) q)=q.coeff a := rfl

 
def formalEval : MvPowerSeries σ K →ₐ[K] Ring K σ p :=
  nilEval K (coord K σ p) (fun i => ⟨p,variable_pow K σ p i⟩)

omit [DecidableEq σ] [CharP K p] [Fact p.Prime] in
@[simp] theorem formalEval_coe (q : MvPolynomial σ K) :
    formalEval K σ p (q : MvPowerSeries σ K)=Ideal.Quotient.mk (ideal K σ p) q := by
  have he : formalEval K σ p (q : MvPowerSeries σ K)=MvPolynomial.aeval (coord K σ p) q :=
    nilEval_coe K (coord K σ p) _ q
  rw [he]
  have h : MvPolynomial.aeval (coord K σ p)=Ideal.Quotient.mkₐ K (ideal K σ p) := by
    apply MvPolynomial.algHom_ext
    intro i
    exact MvPolynomial.aeval_X _ i
  exact DFunLike.congr_fun h q

 

omit [DecidableEq σ] [CharP K p] [Fact p.Prime] in
theorem boundedCoeff_formalEval (a : σ →₀ ℕ) (ha : ∀ i, a i<p)
    (q : MvPowerSeries σ K) :
    boundedCoeff K σ p a ha (formalEval K σ p q)=MvPowerSeries.coeff a q := by
  let : UniformSpace K := ⊥
  let : UniformSpace (Ring K σ p) := ⊥
  let : TopologicalSpace (Ring K σ p) := (⊥ : UniformSpace (Ring K σ p)).toTopologicalSpace
  let : ContinuousSMul K (Ring K σ p) := ⟨continuous_of_discreteTopology⟩
  have hc : Continuous (formalEval K σ p : MvPowerSeries σ K → Ring K σ p) :=
    MvPowerSeries.continuous_aeval _
  have h := Continuous.ext_on (denseRange_toMvPowerSeries (σ:=σ) (R:=K))
    ((continuous_of_discreteTopology : Continuous (boundedCoeff K σ p a ha)).comp hc)
    (continuous_coeff K a) (by
      rintro _ ⟨r,rfl⟩
      change boundedCoeff K σ p a ha (formalEval K σ p (r : MvPowerSeries σ K))=_
      rw [formalEval_coe,boundedCoeff_mk]
      rfl)
  exact congr_fun h q

omit [DecidableEq σ] in
theorem formalEval_pow (q : MvPowerSeries σ K) :
    formalEval K σ p q ^ p=algebraMap K (Ring K σ p) (MvPowerSeries.constantCoeff q ^ p) := by
  obtain ⟨r,hr⟩ := Ideal.Quotient.mk_surjective (formalEval K σ p q)
  rw [←hr,frobenius_mk]
  congr 2
  have h := boundedCoeff_formalEval K σ p 0 (fun i => (Fact.out : p.Prime).pos) q
  rw [←hr,boundedCoeff_mk] at h
  exact h

def formalSubst (c : σ → MvPowerSeries σ K)
    (hc : ∀ i, MvPowerSeries.constantCoeff (c i)=0) : Ring K σ p →ₐ[K] Ring K σ p :=
  FiniteCoordinates.evaluate (fun i => formalEval K σ p (c i)) (by
    intro i
    rw [formalEval_pow,hc]
    simp [zero_pow (Fact.out : p.Prime).ne_zero])

omit [DecidableEq σ] in
@[simp] theorem formalSubst_coord (c : σ → MvPowerSeries σ K)
    (hc : ∀ i, MvPowerSeries.constantCoeff (c i)=0) (i : σ) :
    formalSubst K σ p c hc (coord K σ p i)=formalEval K σ p (c i) := by
  change (MvPolynomial.aeval _) (MvPolynomial.X i)=_
  exact MvPolynomial.aeval_X _ i

 

theorem formalSubst_bijective (c : σ → MvPowerSeries σ K)
    (hc : ∀ i, MvPowerSeries.constantCoeff (c i)=0)
    (hM : Matrix.det (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (c i))≠0) :
    Function.Bijective (formalSubst K σ p c hc) := by
  choose r hr using fun i => Ideal.Quotient.mk_surjective (formalEval K σ p (c i))
  have hrc (i : σ) : MvPolynomial.constantCoeff (r i)=0 := by
    have h := boundedCoeff_formalEval K σ p 0 (fun j => (Fact.out : p.Prime).pos) (c i)
    rw [←hr i,boundedCoeff_mk] at h
    exact h.trans (hc i)
  have hrt : tangentMatrix K σ r=(fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (c i)) := by
    ext i j
    have hb : ∀ k : σ, (Finsupp.single j 1) k<p := by
      intro k
      simp only [Finsupp.single_apply]
      split_ifs <;> have := (Fact.out : p.Prime).two_le <;> omega
    have h := boundedCoeff_formalEval K σ p (Finsupp.single j 1) hb (c i)
    rw [←hr i,boundedCoeff_mk] at h
    exact h
  have he : formalSubst K σ p c hc=polynomialSubst K σ p r hrc := by
    apply FiniteCoordinates.hom_ext (e:=fun _ => p)
    intro i
    change formalSubst K σ p c hc (coord K σ p i)=polynomialSubst K σ p r hrc (coord K σ p i)
    rw [formalSubst_coord,polynomialSubst_coord,hr]
  rw [he]
  apply polynomialSubst_bijective K σ p r hrc
  rwa [hrt]

end
end PD4Tensor.FrobeniusTruncation
end

end OAI
