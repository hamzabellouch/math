import OAI.Analysis.RotationWeights.BorelWeights

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uA

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

section

def rightTranslate (u : unitary ℂ) (m n : ℤ) : RegularHilbert ≃ₗᵢ[ℂ] RegularHilbert :=
  lpPhase (fun i : ℤ × ℤ ↦ u ^ (m*(i.2-n))) * lpPermute (Equiv.addLeft (m,n))

lemma rightTranslate_apply (u : unitary ℂ) (m n : ℤ) (f : RegularHilbert) (a b : ℤ) :
    rightTranslate u m n f (a,b) = (↑(u^(m*(b-n))) : ℂ)*f (a-m,b-n) := by
  change _*f (-m+a,-n+b)=_
  apply congrArg (fun i : ℤ × ℤ ↦ (↑(u^(m*(b-n))) : ℂ)*f i)
  ext <;> dsimp <;> omega

def rightOperator (u : unitary ℂ) (m n : ℤ) : RegularOperator :=
  (rightTranslate u m n).toLinearIsometry.toContinuousLinearMap

lemma rightOperator_vacuum (u : unitary ℂ) (m n : ℤ) :
    rightOperator u m n regularVacuum = lp.single 2 (m,n) (1:ℂ) := by
  ext ⟨a,b⟩
  change rightTranslate u m n regularVacuum (a,b)=_
  rw [rightTranslate_apply]
  simp only [regularVacuum,lp.single_apply]
  by_cases ha : a=m
  · subst a
    by_cases hb : b=n
    · subst b; simp
    · simp [hb,sub_eq_zero,Prod.mk.injEq]
  · have ham : a-m≠0 := sub_ne_zero.mpr ha
    simp [ham,Prod.mk.injEq,Ne.symm ha]

lemma rightOperator_U (u : unitary ℂ) (m n : ℤ) :
    Commute (regularU : RegularOperator) (rightOperator u m n) := by
  change _*_= _*_
  ext f ⟨a,b⟩
  change (regularU : RegularOperator) (rightTranslate u m n f) (a,b)=
    rightTranslate u m n ((regularU : RegularOperator) f) (a,b)
  simp only [regularU_apply,rightTranslate_apply]
  congr 2
  exact congrArg (fun i : ℤ × ℤ => f i) (Prod.ext (by dsimp; omega) rfl)

lemma rightOperator_V (u : unitary ℂ) (m n : ℤ) :
    Commute (regularV u : RegularOperator) (rightOperator u m n) := by
  change _*_= _*_
  ext f ⟨a,b⟩
  change (regularV u : RegularOperator) (rightTranslate u m n f) (a,b)=
    rightTranslate u m n ((regularV u : RegularOperator) f) (a,b)
  simp only [regularV_apply,rightTranslate_apply]
  rw [← mul_assoc,← mul_assoc,← Submonoid.coe_mul,← Submonoid.coe_mul,← zpow_add,← zpow_add]
  congr 2
  · exact congrArg (fun z : ℤ => u^z) (by ring)
  · exact congrArg (fun i : ℤ × ℤ => f i) (Prod.ext rfl (by dsimp; ring))

def regularAlgebra (u : unitary ℂ) : Set RegularOperator :=
  Set.centralizer (Set.centralizer ({(regularU : RegularOperator),(regularV u : RegularOperator)} : Set RegularOperator))

lemma in_regularAlgebra_commutes (u : unitary ℂ) {A : RegularOperator}
    (hA : A∈regularAlgebra u) (m n : ℤ) : Commute A (rightOperator u m n) := by
  have hr : rightOperator u m n ∈ Set.centralizer ({(regularU : RegularOperator),(regularV u : RegularOperator)} : Set RegularOperator) := by
    intro B hB
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hB
    rcases hB with rfl|rfl
    · exact (rightOperator_U u m n).eq
    · exact (rightOperator_V u m n).eq
  exact (hA _ hr).symm

lemma regular_column (u : unitary ℂ) {A : RegularOperator} (hA : A∈regularAlgebra u)
    (m n : ℤ) : A (lp.single 2 (m,n) (1:ℂ)) = rightOperator u m n (A regularVacuum) := by
  rw [← rightOperator_vacuum u m n]
  exact DFunLike.congr_fun (in_regularAlgebra_commutes u hA m n).eq regularVacuum

lemma regular_adjoint_coefficient (u : unitary ℂ) {A : RegularOperator} (hA : A∈regularAlgebra u)
    (m n : ℤ) : (star A) regularVacuum (m,n) =
      star ((↑(u^(-(m*n))) : ℂ) * (A regularVacuum) (-m,-n)) := by
  have he := ContinuousLinearMap.adjoint_inner_left A (lp.single 2 (m,n) (1:ℂ)) regularVacuum
  change inner ℂ ((star A) regularVacuum) (lp.single 2 (m,n) (1:ℂ))=
    inner ℂ regularVacuum (A (lp.single 2 (m,n) (1:ℂ))) at he
  rw [regular_column u hA,lp.inner_single_right,regularVacuum,lp.inner_single_left] at he
  simp only [RCLike.inner_apply'] at he
  change star ((star A) regularVacuum (m,n))*1=star (1:ℂ)*(rightTranslate u m n (A regularVacuum) (0,0)) at he
  simp only [mul_one,star_one,one_mul,rightTranslate_apply,zero_sub,mul_neg] at he
  have hh := congrArg star he
  simpa only [star_star] using hh

lemma regular_adjoint_norm_vacuum (u : unitary ℂ) {A : RegularOperator} (hA : A∈regularAlgebra u) :
    ‖(star A) regularVacuum‖=‖A regularVacuum‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num),lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  calc
    (∑' i : ℤ×ℤ, ‖(star A) regularVacuum i‖^(2:ℝ≥0∞).toReal) =
      ∑' i : ℤ×ℤ, ‖A regularVacuum (-i.1,-i.2)‖^(2:ℝ≥0∞).toReal := by
      congr 1
      funext ⟨m,n⟩
      rw [regular_adjoint_coefficient u hA,norm_star,norm_mul,CStarRing.norm_coe_unitary,one_mul]
    _ = _ := (Equiv.neg (ℤ×ℤ)).tsum_eq (fun i ↦ ‖A regularVacuum i‖^(2:ℝ≥0∞).toReal)

lemma regular_vacuum_separating (u : unitary ℂ) {A : RegularOperator} (hA : A∈regularAlgebra u)
    (hzero : A regularVacuum=0) : A=0 := by
  have hc : (Submodule.span ℂ (Set.range (fun i : ℤ×ℤ ↦ lp.single 2 i (1:ℂ)))).topologicalClosure = ⊤ := by
    have hh := regular_cyclic u
    simpa only [regular_monomial,Prod.eta] using hh
  have hk : Submodule.span ℂ (Set.range (fun i : ℤ×ℤ ↦ lp.single 2 i (1:ℂ))) ≤ A.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨m,n⟩,rfl⟩
    change A (lp.single 2 (m,n) (1:ℂ))=0
    rw [regular_column u hA,hzero,map_zero]
  have hk' := Submodule.topologicalClosure_minimal _ hk A.isClosed_ker
  rw [hc,top_le_iff] at hk'
  apply ContinuousLinearMap.ext
  intro x
  exact show x ∈ A.ker from hk'.symm ▸ Submodule.mem_top

end

open Set

def fiberConjugacy : RegularOperator ≃⋆ₐ[ℂ] CircleFiberOperator :=
  circleFiberBasis.repr.symm.conjStarAlgEquiv
lemma fiberConjugacy_apply (A : RegularOperator) (x : RegularHilbert) :
    fiberConjugacy A (circleFiberBasis.repr.symm x)=circleFiberBasis.repr.symm (A x) := by
  change circleFiberBasis.repr.symm (A (circleFiberBasis.repr (circleFiberBasis.repr.symm x)))=_
  rw [LinearIsometryEquiv.apply_symm_apply]
lemma fiberConjugacy_U : fiberConjugacy (regularU : RegularOperator)=fiberShiftL2 1 := circleFiberBasis_conj_U
lemma fiberConjugacy_V (θ : ℝ) : fiberConjugacy (regularV (rotationScalar θ) : RegularOperator)=continuousPi (θ:CircleX) (fourier 1) := circleFiberBasis_conj_V θ

def regularCommutant (θ : ℝ) : StarSubalgebra ℂ RegularOperator :=
  StarSubalgebra.centralizer ℂ ({(regularU:RegularOperator),(regularV (rotationScalar θ):RegularOperator)} : Set RegularOperator)
def fiberCommutant (θ : ℝ) : StarSubalgebra ℂ CircleFiberOperator :=
  (regularCommutant θ).map fiberConjugacy.toStarAlgHom

lemma commute_star_unitary {A : Type uA} [Monoid A] [StarMul A] (u : unitary A) (b : A)
    (h : Commute (u:A) b) : Commute (star (u:A)) b := by
  change star (u:A)*b=b*star (u:A)
  calc
    star (u:A)*b = star (u:A)*(b*(u:A))*star (u:A) := by simp [mul_assoc]
    _ = star (u:A)*((u:A)*b)*star (u:A) := by rw [h.eq]
    _ = b*star (u:A) := by simp [←mul_assoc]

lemma mem_regularCommutant (θ : ℝ) {B : RegularOperator}
    (hB : B∈Set.centralizer ({(regularU:RegularOperator),(regularV (rotationScalar θ):RegularOperator)} : Set RegularOperator)) :
    B∈regularCommutant θ := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  intro a ha
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
  rcases ha with rfl|rfl
  · exact ⟨hB _ (by simp), (commute_star_unitary regularU B (hB _ (by simp))).eq⟩
  · exact ⟨hB _ (by simp), (commute_star_unitary (regularV (rotationScalar θ)) B (hB _ (by simp))).eq⟩

lemma regularAlgebra_of_commutes (θ : ℝ) (A : CircleFiberOperator)
    (hA : ∀ B∈fiberCommutant θ,Commute A B) :
    fiberConjugacy.symm A∈regularAlgebra (rotationScalar θ) := by
  intro B hB
  have hh : Commute A (fiberConjugacy B) := hA _ ⟨B,mem_regularCommutant θ hB,rfl⟩
  apply fiberConjugacy.injective
  change fiberConjugacy (B*fiberConjugacy.symm A)=fiberConjugacy (fiberConjugacy.symm A*B)
  simpa only [map_mul,fiberConjugacy.apply_symm_apply] using hh.symm.eq

lemma fiber_commutes_of_regularAlgebra (θ : ℝ) (p : RegularOperator)
    (hp : p∈regularAlgebra (rotationScalar θ)) :
    ∀ B∈fiberCommutant θ,Commute (fiberConjugacy p) B := by
  rintro B ⟨b,hb,rfl⟩
  have hb' : b∈Set.centralizer ({(regularU:RegularOperator),(regularV (rotationScalar θ):RegularOperator)} : Set RegularOperator) :=
    fun a ha => ((StarSubalgebra.mem_centralizer_iff ℂ).mp hb a ha).1
  change fiberConjugacy p*fiberConjugacy b=fiberConjugacy b*fiberConjugacy p
  simpa only [map_mul] using congrArg fiberConjugacy (hp b hb').symm

lemma realPi_fiberCommutant (θ : ℝ) (g : RealBorel) :
    ∀ B∈fiberCommutant θ,Commute (realPi (θ:CircleX) g) B := by
  rintro B ⟨b,hb,rfl⟩
  apply realPi_commutes
  intro f
  change Commute (continuousPiHom (θ:CircleX) (complexCircleMap f)) (fiberConjugacy b)
  rw [circle_cfc_hom (continuousPiHom (θ:CircleX)) (continuous_continuousPiHom _) f]
  have hv := (StarSubalgebra.mem_centralizer_iff ℂ).mp hb (regularV (rotationScalar θ)) (by simp)
  have h1 : Commute (continuousPi (θ:CircleX) (fourier 1)) (fiberConjugacy b) := by
    rw [←fiberConjugacy_V]
    change fiberConjugacy _*fiberConjugacy b=fiberConjugacy b*fiberConjugacy _
    simpa only [map_mul] using congrArg fiberConjugacy hv.1
  have h2 : Commute (star (continuousPi (θ:CircleX) (fourier 1))) (fiberConjugacy b) := by
    have conjugacy_star (operator : RegularOperator) :
        fiberConjugacy (star operator) = star (fiberConjugacy operator) :=
      fiberConjugacy.map_star' operator
    rw [←fiberConjugacy_V,←conjugacy_star]
    change fiberConjugacy _*fiberConjugacy b=fiberConjugacy b*fiberConjugacy _
    simpa only [map_mul] using congrArg fiberConjugacy hv.2
  exact h1.cfc h2 (circleFunction f)

def fiberVacuum : CircleFiberL2 := circleFiberBasis.repr.symm regularVacuum
lemma fiber_vacuum_trace (θ : ℝ) (A : CircleFiberOperator)
    (hA : ∀ B∈fiberCommutant θ,Commute A B) : ‖star A fiberVacuum‖=‖A fiberVacuum‖ := by
  have h := regular_adjoint_norm_vacuum (rotationScalar θ) (regularAlgebra_of_commutes θ A hA)
  have h1 : A fiberVacuum = circleFiberBasis.repr.symm (fiberConjugacy.symm A regularVacuum) := by
    simpa only [fiberConjugacy.apply_symm_apply,fiberVacuum] using fiberConjugacy_apply (fiberConjugacy.symm A) regularVacuum
  have h2 : star A fiberVacuum = circleFiberBasis.repr.symm (star (fiberConjugacy.symm A) regularVacuum) := by
    have conjugacy_star (operator : RegularOperator) :
        fiberConjugacy (star operator) = star (fiberConjugacy operator) :=
      fiberConjugacy.map_star' operator
    simpa only [conjugacy_star,fiberConjugacy.apply_symm_apply,fiberVacuum] using fiberConjugacy_apply (star (fiberConjugacy.symm A)) regularVacuum
  rw [h1,h2,LinearIsometryEquiv.norm_map,LinearIsometryEquiv.norm_map]
  exact h
lemma fiber_vacuum_faithful (θ : ℝ) (A : CircleFiberOperator)
    (hA : ∀ B∈fiberCommutant θ,Commute A B) (hz : A fiberVacuum=0) : A=0 := by
  have h1 := fiberConjugacy_apply (fiberConjugacy.symm A) regularVacuum
  simp only [fiberConjugacy.apply_symm_apply] at h1
  have h2 : fiberConjugacy.symm A regularVacuum=0 := by
    apply circleFiberBasis.repr.symm.injective
    simpa only [map_zero] using h1.symm.trans hz
  have h3 := regular_vacuum_separating (rotationScalar θ) (regularAlgebra_of_commutes θ A hA) h2
  simpa only [fiberConjugacy.apply_symm_apply,map_zero] using congrArg fiberConjugacy h3


end ContinuousCircleWeight

end

end OAI
