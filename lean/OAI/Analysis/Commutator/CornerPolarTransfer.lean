import Mathlib
import OAI.Analysis.Commutator.CornerPolarAlgebra
import OAI.Analysis.Commutator.PolarSupport
import OAI.Analysis.Commutator.TracialL2Tools
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.CornerPolarTransfer

open TracialL2

section Estimates

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

include hτ in
lemma conjugation_difference (v b y : A) (hv : ‖v‖≤1) :
    norm τ (star v*y*v) ≤ norm τ (star b*y*b)+
      (1+‖b‖)*‖y‖*norm τ (v-b) := by
  have he : star v*y*v=star b*y*b+star (v-b)*y*v+star b*y*(v-b) := by
    simp only [star_sub,sub_mul,mul_sub]
    abel
  have h1 : norm τ (star (v-b)*y*v)≤‖y‖*norm τ (v-b) := by
    calc
      _≤norm τ (star (v-b)*y)*‖v‖ := norm_mul_right τ hτ _ _
      _≤norm τ (star (v-b)*y) := mul_le_of_le_one_right (norm_nonneg τ _) hv
      _≤norm τ (star (v-b))*‖y‖ := norm_mul_right τ hτ _ _
      _=_ := by rw [norm_star τ hτ,mul_comm]
  have h2 : norm τ (star b*y*(v-b))≤‖b‖*‖y‖*norm τ (v-b) := by
    calc
      _≤‖star b*y‖*norm τ (v-b) := norm_mul_left τ _ _
      _≤(‖star b‖*‖y‖)*norm τ (v-b) :=
        mul_le_mul_of_nonneg_right (_root_.norm_mul_le _ _) (norm_nonneg τ _)
      _=_ := by rw [_root_.norm_star]
  calc
    _=norm τ (star b*y*b+star (v-b)*y*v+star b*y*(v-b)) := congrArg (norm τ) he
    _≤norm τ (star b*y*b)+norm τ (star (v-b)*y*v)+norm τ (star b*y*(v-b)) :=
      (norm_add τ (star b*y*b+star (v-b)*y*v) (star b*y*(v-b))).trans
        (add_le_add (norm_add τ (star b*y*b) (star (v-b)*y*v)) le_rfl)
    _≤norm τ (star b*y*b)+‖y‖*norm τ (v-b)+‖b‖*‖y‖*norm τ (v-b) :=
      add_le_add (add_le_add le_rfl h1) h2
    _=_ := by simp only [add_mul,one_mul,add_assoc]

include hτ in
lemma range_compression (v y : A) (hv : ‖v‖≤1) :
    norm τ ((v*star v)*y*(v*star v))≤norm τ (star v*y*v) := by
  calc
    _=norm τ (v*(star v*y*v)*star v) := by simp only [mul_assoc]
    _≤norm τ (v*(star v*y*v))*‖star v‖ := norm_mul_right τ hτ _ _
    _≤norm τ (v*(star v*y*v)) :=
      mul_le_of_le_one_right (norm_nonneg τ _) (by simpa using hv)
    _≤‖v‖*norm τ (star v*y*v) := norm_mul_left τ _ _
    _≤norm τ (star v*y*v) := mul_le_of_le_one_left (norm_nonneg τ _) hv

lemma defect_bound {q r a v : A} (hq : IsStarProjection q)
    (hr : IsStarProjection r) (hrq : r≤q) (ha : 0≤a)
    (hra : r*a=a) (haq : a*q=a) (hv : star v*v=r) :
    norm τ (v-v*a) ≤ norm τ (q-a*a) :=
  norm_mono_square τ (CornerPolarAlgebra.polar_defect_le hq hr hrq ha hra haq hv)

lemma trace_kernel_bound {q r a : A} (hq : IsStarProjection q)
    (hr : IsStarProjection r) (ha : 0≤a) (hra : r*a=a) (haq : a*q=a) :
    (τ q).re-(τ r).re≤norm τ (q-a*a)^2 := by
  have h := (τ.monotone (CornerPolarAlgebra.kernel_defect_le hq hr ha hra haq)).1
  change (τ (q-r)).re≤(τ (star (q-a*a)*(q-a*a))).re at h
  simpa only [map_sub,Complex.sub_re,←norm_sq] using h

include hτ in
lemma compressed_scalar_polar {p q v b y : A} {c : ℝ}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpy : p*y=y) (hyp : y*p=y)
    (hb : b=c • (p*q)) (hv : ‖v‖≤1) :
    norm τ ((v*star v)*y*(v*star v)) ≤ c^2*norm τ (q*y*q)+
      (1+‖b‖)*‖y‖*norm τ (v-b) := by
  have he : star b*y*b=(c*c) • (q*y*q) := by
    rw [hb]
    simp only [star_smul,star_mul,star_trivial,hp.isSelfAdjoint.star_eq,
      hq.isSelfAdjoint.star_eq,smul_mul_assoc,mul_smul_comm,smul_smul]
    congr 1
    rw [mul_assoc q p y,hpy,←mul_assoc,mul_assoc q y p,hyp]
  have hn : norm τ (star b*y*b)=c^2*norm τ (q*y*q) := by
    rw [he,norm_real_smul,abs_of_nonneg (mul_self_nonneg c),pow_two]
  exact (range_compression τ hτ v y hv).trans ((conjugation_difference τ hτ v b y hv).trans_eq
    (by rw [hn]))

omit [PartialOrder A] [StarOrderedRing A] in
lemma scaled_projection_defect {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) {c t : ℝ} (hct : c*c*t=1) :
    q-star (c • (p*q))*(c • (p*q))=(-c*c) • (q*(p-t • (1:A))*q) := by
  have hpc : star (p*q)*(p*q)=q*p*q := by
    simp only [star_mul,hp.isSelfAdjoint.star_eq,hq.isSelfAdjoint.star_eq]
    rw [mul_assoc q p,←mul_assoc p p q,hp.isIdempotentElem.eq,←mul_assoc]
  have hcen : q*(p-t • (1:A))*q=q*p*q-t • q := by
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,
      hq.isIdempotentElem.eq]
  have hct' : (-c*c)*t=-1 := by nlinarith only [hct]
  rw [hcen,star_smul,star_trivial,smul_mul_assoc,mul_smul_comm,smul_smul,hpc,
    smul_sub,smul_smul,hct',neg_one_smul,sub_neg_eq_add,neg_mul,neg_smul,add_comm]
  exact sub_eq_add_neg _ _

lemma norm_scaled_projection_defect {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) {c t : ℝ} (hct : c*c*t=1) :
    norm τ (q-star (c • (p*q))*(c • (p*q)))=
      c^2*norm τ (q*(p-t • (1:A))*q) := by
  rw [scaled_projection_defect hp hq hct,norm_real_smul,
    neg_mul,abs_neg,abs_of_nonneg (mul_self_nonneg c),pow_two]

end Estimates

section Represented

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

lemma abs_coe (b : M) : CFC.abs (b : H →L[ℂ] H)=(CFC.abs b : M) := by
  apply CFC.sqrt_unique
  · exact congrArg (fun x : M => (x : H →L[ℂ] H)) (CFC.abs_mul_abs b)
  · exact CFC.abs_nonneg b

lemma projection_of_coe {p : M} (hp : IsStarProjection (p : H →L[ℂ] H)) :
    IsStarProjection p := by
  exact ⟨Subtype.ext hp.isIdempotentElem.eq,Subtype.ext hp.isSelfAdjoint.star_eq⟩

theorem exists_polar_data (b : M) :
    ∃ v : M, v*CFC.abs b=b ∧
      IsStarProjection (star v*v) ∧ IsStarProjection (v*star v) ∧
      (star v*v)*CFC.abs b=CFC.abs b ∧
      ‖v‖≤1 ∧ (∀ (N : VonNeumannAlgebra H), (b : H →L[ℂ] H)∈N → (v : H →L[ℂ] H)∈N) ∧
      (∀ e : M, IsStarProjection e → e*b=b → v*star v≤e) ∧
      (∀ e : M, IsStarProjection e → b*e=b → star v*v≤e) := by
  let v : M := ⟨Polar.partialIsometry (b : H →L[ℂ] H),
    Polar.partialIsometry_mem_vonNeumann M b.property⟩
  have hi : ((star v*v : M) : H →L[ℂ] H)=Polar.rightSupport (b : H →L[ℂ] H) :=
    Polar.partialIsometry_initial _
  have hp : IsStarProjection (star v*v) := projection_of_coe M
    (hi.symm ▸ Polar.isProjection_rightSupport _)
  refine ⟨v,?_,hp,projection_of_coe M (Polar.isProjection_leftSupport _),?_,
    CornerPolarAlgebra.norm_partial_isometry_le hp rfl,?_,?_,?_⟩
  · apply Subtype.ext
    change Polar.partialIsometry _*((CFC.abs b : M) : H →L[ℂ] H)=_
    rw [←abs_coe M,Polar.factorization]
  · apply Subtype.ext
    change ((star v*v : M) : H →L[ℂ] H)*((CFC.abs b : M) : H →L[ℂ] H)=_
    rw [hi,←abs_coe M,Polar.initial_mul_abs]
  · intro N hb
    exact Polar.partialIsometry_mem_vonNeumann N hb
  · intro e he heb
    change Polar.leftSupport (b : H →L[ℂ] H)≤(e : H →L[ℂ] H)
    exact Polar.leftSupport_le _ _ (he.map M.toStarSubalgebra.subtype)
      (congrArg (fun x : M => (x : H →L[ℂ] H)) heb)
  · intro e he hbe
    change ((star v*v : M) : H →L[ℂ] H)≤(e : H →L[ℂ] H)
    rw [hi]
    exact Polar.rightSupport_le _ _ (he.map M.toStarSubalgebra.subtype)
      (congrArg (fun x : M => (x : H →L[ℂ] H)) hbe)

end Represented

end Kadison.CornerPolarTransfer

end

end
end

end OAI
