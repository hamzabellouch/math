import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceRemaining

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open UniqueFactorizationMonoid CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def assignedMass (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (coeff:ι→Ideal O→ℂ)(Z G:ℝ) : ℝ :=
  ‖∏i:↥J,coeff i.val (x i).val‖*Z^(-G)

def assignedTerm (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) : ℂ :=
  (∏i:↥J,coeff i.val (x i).val)*(moebius (assignedIdeal L J x):ℂ)*
    (Z^(-G):ℝ)*η (assignedIdeal L J x)^2*(idealRowHom u (assignedIdeal L J x))^2*
    star (remainingResidual S L J x coeff η (fun _=>1) W Z r z G u)

omit [Fintype ι] [DecidableEq ι] in
theorem assignedMass_nonneg (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (coeff:ι→Ideal O→ℂ)(Z G:ℝ)(hZ:0<Z) : 0≤assignedMass L J x coeff Z G :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hZ.le _)

theorem assignedTerm_norm_le (S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:Admissible (assignedIdeal L J x))(hη:‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)(u:O) :
    ‖assignedTerm S L J x coeff η W Z r z G u‖≤
      assignedMass L J x coeff Z G*‖remainingPolynomial S L J x coeff η W Z r z G u‖ := by
  have hμ:‖(moebius (assignedIdeal L J x):ℂ)‖=1 := by simp [hj.2.1.moebius_eq]
  have hrow:‖idealRowHom u (assignedIdeal L J x)‖^2≤1 := by
    have hh:=admissible_row_four_le_one _ hj u
    nlinarith [sq_nonneg (‖idealRowHom u (assignedIdeal L J x)‖^2-1)]
  have hmass:=assignedMass_nonneg L J x coeff Z G hZ
  have he:‖η (assignedIdeal L J x)‖^2≤1:=pow_le_one₀ (norm_nonneg _) hη
  rw [assignedTerm,remainingResidual_eq_polynomial S L hprime hdis]
  simp only [norm_mul,norm_pow,norm_star,norm_neg,norm_one,one_pow,one_mul,
    hμ,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hZ.le (-G))]
  change assignedMass L J x coeff Z G*‖η (assignedIdeal L J x)‖^2*
    ‖idealRowHom u (assignedIdeal L J x)‖^2*
    ‖remainingPolynomial S L J x coeff η W Z r z G u‖≤_
  calc
    _≤assignedMass L J x coeff Z G*1*1*
      ‖remainingPolynomial S L J x coeff η W Z r z G u‖ := by
      gcongr
    _=_:=by ring

theorem assignedTerm_energy_le (S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:Admissible (assignedIdeal L J x))(hη:‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)(rows:Finset O)(w:O→ℝ)(hw:∀u,0≤w u) :
    (∑u∈rows,w u*‖assignedTerm S L J x coeff η W Z r z G u‖^2)≤
      (assignedMass L J x coeff Z G)^2*
      ∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z G u‖^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  have hh:=mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (assignedTerm_norm_le S L hprime hdis J x coeff η hj hη W Z r z G hZ u) 2)
    (hw u)
  convert hh using 1 ; ring

theorem assigned_family_energy (S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:∀x:Assigned L J,Admissible (assignedIdeal L J x))
    (hη:∀x:Assigned L J,‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)(rows:Finset O)(w:O→ℝ)(hw:∀u,0≤w u) :
    (∑u∈rows,w u*‖∑x:Assigned L J,assignedTerm S L J x coeff η W Z r z G u‖^2)≤
      (∑x:Assigned L J,assignedMass L J x coeff Z G*
        Real.sqrt (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z G u‖^2))^2 := by
  refine (finite_weighted_triangle Finset.univ rows w hw
    (fun x u=>assignedTerm S L J x coeff η W Z r z G u)).trans ?_
  apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>Real.sqrt_nonneg _))
  apply Finset.sum_le_sum
  intro x hx
  have hh:=Real.sqrt_le_sqrt (assignedTerm_energy_le S L hprime hdis J x coeff η
    (hj x) (hη x) W Z r z G hZ rows w hw)
  rwa [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (assignedMass_nonneg L J x coeff Z G hZ)] at hh

theorem original_energy_of_remaining (S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:∀J:Finset ι,∀x:Assigned L J,Admissible (assignedIdeal L J x))
    (hη:∀J:Finset ι,∀x:Assigned L J,‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z:ℝ)(G:Finset ι→ℝ)(hZ:0<Z)
    (rows:Finset O)(w:O→ℝ)(hw:∀u,0≤w u)(E:ℝ)(hE:0≤E)
    (hres:∀J:Finset ι,∀x:Assigned L J,
      (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z (G J) u‖^2)≤E) :
    (∑u∈rows,w u*‖∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η (fun _=>1) W Z r z u‖^2)≤
      (∑J∈Finset.univ.powerset,∑x:Assigned L J,assignedMass L J x coeff Z (G J))^2*E := by
  have heq (u:O) :
      (∑q:Tuple L,(∏i,coeff i (q i).val)*
        originalTotalPolynomial S (∏i,(q i).val) η (fun _=>1) W Z r z u)=
      ∑J∈Finset.univ.powerset,∑x:Assigned L J,
        assignedTerm S L J x coeff η W Z r z (G J) u :=
    original_selected_overlap S L hprime hdis coeff η (fun _=>1) W Z r z G hZ u
  simp_rw [heq]
  have hroot (J:Finset ι) :
      Real.sqrt (∑u∈rows,w u*‖∑x:Assigned L J,
        assignedTerm S L J x coeff η W Z r z (G J) u‖^2)≤
      (∑x:Assigned L J,assignedMass L J x coeff Z (G J))*Real.sqrt E := by
    have hm:0≤∑x:Assigned L J,assignedMass L J x coeff Z (G J) :=
      Finset.sum_nonneg (fun x _=>assignedMass_nonneg L J x coeff Z (G J) hZ)
    have hb:=assigned_family_energy S L hprime hdis J coeff η (hj J) (hη J)
      W Z r z (G J) hZ rows w hw
    have hc : (∑x:Assigned L J,assignedMass L J x coeff Z (G J)*
        Real.sqrt (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z (G J) u‖^2))≤
        (∑x:Assigned L J,assignedMass L J x coeff Z (G J))*Real.sqrt E := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hres J x))
        (assignedMass_nonneg L J x coeff Z (G J) hZ)
    have hn : 0≤∑x:Assigned L J,assignedMass L J x coeff Z (G J)*
        Real.sqrt (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z (G J) u‖^2) :=
      Finset.sum_nonneg (fun x _=>mul_nonneg (assignedMass_nonneg L J x coeff Z (G J) hZ) (Real.sqrt_nonneg _))
    have hh:=Real.sqrt_le_sqrt (hb.trans (pow_le_pow_left₀ hn hc 2))
    rwa [Real.sqrt_sq (mul_nonneg hm (Real.sqrt_nonneg E))] at hh
  refine (finite_weighted_triangle Finset.univ.powerset rows w hw
    (fun J u=>∑x:Assigned L J,assignedTerm S L J x coeff η W Z r z (G J) u)).trans ?_
  calc
    _≤(∑J∈Finset.univ.powerset,
        (∑x:Assigned L J,assignedMass L J x coeff Z (G J))*Real.sqrt E)^2 := by
      apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>Real.sqrt_nonneg _))
      exact Finset.sum_le_sum (fun J _=>hroot J)
    _=_:=by rw [←Finset.sum_mul,mul_pow,Real.sq_sqrt hE]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
