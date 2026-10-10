import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice11
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
open scoped BigOperators
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RationalLattice
open MalcevCharacters RationalLevelFlow
variable {G H : Type*} [Group G] [Group H]
variable [TopologicalSpace G] [TopologicalSpace H]
variable [IsTopologicalGroup G] [IsTopologicalGroup H]
variable {m n : ℕ} (c : RealCoordinates G m) (d : RealCoordinates H n)

def IsRealPolynomialMap {σ : Type*} (f : (σ → ℝ) → G) : Prop :=
  ∀ i,RealPolynomialMap.IsPolynomial (fun x=>c.coord (f x) i)

omit [IsTopologicalGroup G] in
lemma realPolynomialMap_one [IsTopologicalGroup G] {σ : Type*} : IsRealPolynomialMap c (fun _ : σ → ℝ=>(1:G)) := by
  intro i
  simpa only [c.one_coord] using RealPolynomialMap.const (σ:=σ) 0

omit [IsTopologicalGroup G] in
lemma realPolynomialMap_mul [IsTopologicalGroup G] {σ : Type*} {f g : (σ → ℝ) → G}
    (hf : IsRealPolynomialMap c f) (hg : IsRealPolynomialMap c g) :
    IsRealPolynomialMap c (fun x=>f x*g x) := by
  intro i
  have hp : RealPolynomialMap.IsPolynomial (fun x=>MvPolynomial.eval₂ (algebraMap ℚ ℝ)
      (Sum.elim (fun j : Fin i.val=>c.coord (f x) ⟨j.val,lt_trans j.isLt i.isLt⟩)
        (fun j : Fin i.val=>c.coord (g x) ⟨j.val,lt_trans j.isLt i.isLt⟩)) (c.correction i)) := by
    apply RealPolynomialMap.rational_eval
    intro j
    cases j with
    | inl j => exact hf _
    | inr j => exact hg _
  simpa only [c.mul_coord] using RealPolynomialMap.add (RealPolynomialMap.add (hf i) (hg i)) hp

lemma realPolynomialMap_list_prod {σ : Type*} (V : List ((σ → ℝ) → G))
    (hV : ∀ f∈V,IsRealPolynomialMap c f) :
    IsRealPolynomialMap c (fun x=>(V.map (fun f=>f x)).prod) := by
  induction V with
  | nil => simpa using realPolynomialMap_one c
  | cons f V ih =>
    simpa using realPolynomialMap_mul c (hV f (by simp)) (ih (fun f hf=>hV f (by simp [hf])))

omit [IsTopologicalGroup G] in
lemma realPolynomialMap_realPower [IsTopologicalGroup G] {σ : Type*} (g : G) {f : (σ → ℝ) → ℝ}
    (hf : RealPolynomialMap.IsPolynomial f) :
    IsRealPolynomialMap c (fun x=>realPower c g (f x)) := by
  intro i
  simpa only [realPower_coord] using RealPolynomialMap.polynomial_eval (powerPolynomial c g i) hf

omit [IsTopologicalGroup H] in
lemma map_realPower [IsTopologicalGroup H] (F : H →* G) (hF : Continuous F) (g : H) (t : ℝ) :
    F (realPower d g t)=realPower c (F g) t := by
  let A : Multiplicative ℝ →* H :=
    { toFun := fun t=>realPower d g t.toAdd
      map_one' := realPower_zero d g
      map_mul' := fun t u=>realPower_add d g t.toAdd u.toAdd }
  have he:=continuous_flow_eq_realPower c (F.comp A)
      (hF.comp ((realPower_continuous d g).comp continuous_toAdd)) t
  change F (realPower d g t)=realPower c (F (realPower d g 1)) t at he
  simpa only [realPower_one] using he

omit [IsTopologicalGroup H] in
theorem realHom_polynomial [IsTopologicalGroup H] (hsk : SecondKind d) (F : H →* G) (hF : Continuous F) :
    IsRealPolynomialMap c (fun x : Fin n → ℝ=>F (d.coord.symm x)) := by
  let A (i : Fin n) : Multiplicative ℝ →* H :=
    { toFun := fun t=>axis d i t.toAdd
      map_one' := axis_zero d i
      map_mul' := fun t u=>hsk.axis_add i t.toAdd u.toAdd }
  have he (i : Fin n) (t : ℝ) : F (axis d i t)=realPower c (F (axis d i 1)) t :=
    continuous_flow_eq_realPower c (F.comp (A i))
      (hF.comp ((axis_continuous d i).comp continuous_toAdd)) t
  have hp (i : Fin n) : IsRealPolynomialMap c (fun x : Fin n → ℝ=>F (axis d i (x i))) := by
    have hfun : (fun x : Fin n → ℝ=>F (axis d i (x i)))=
        (fun x=>realPower c (F (axis d i 1)) (x i)) := funext (fun x=>he i (x i))
    rw [hfun]
    exact realPolynomialMap_realPower c _ (RealPolynomialMap.coordinate i)
  have hprod:=realPolynomialMap_list_prod c (List.ofFn (fun i : Fin n=>
    (fun x : Fin n → ℝ=>F (axis d i (x i))))) (by
      intro f hf
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hf
      exact hp i)
  have hw (x : Fin n → ℝ) : F (d.coord.symm x)=
      ((List.ofFn (fun i : Fin n=>(fun x : Fin n → ℝ=>F (axis d i (x i))))).map
        (fun f=>f x)).prod := by
    conv_lhs => rw [hsk.ordered (d.coord.symm x)]
    rw [map_list_prod,List.map_ofFn,List.map_ofFn]
    simp only [Homeomorph.apply_symm_apply,Function.comp_def]
  simpa only [← hw] using hprod

def logHom (F : H →* G) (x : Fin n → ℝ) : Fin m → ℝ :=
  canonicalLog c (F (canonicalExp d x))

lemma logHom_polynomial (hsk : SecondKind d) (F : H →* G) (hF : Continuous F) (i : Fin m) :
    RealPolynomialMap.IsPolynomial (fun x=>logHom c d F x i) := by
  have hexp (j : Fin n) : RealPolynomialMap.IsPolynomial
      (fun x=>d.coord (canonicalExp d x) j) :=
    RealPolynomialMap.of_rational (canonicalExp_polynomial d j)
  have hh (j : Fin m) : RealPolynomialMap.IsPolynomial
      (fun x=>c.coord (F (canonicalExp d x)) j) := by
    simpa only [Homeomorph.symm_apply_apply] using
      RealPolynomialMap.comp (realHom_polynomial c d hsk F hF j) hexp
  simpa only [logHom,Homeomorph.symm_apply_apply] using
    RealPolynomialMap.comp (RealPolynomialMap.of_rational (canonicalLog_polynomial c i)) hh

lemma logHom_smul (F : H →* G) (hF : Continuous F) (t : ℝ) (x : Fin n → ℝ) :
    logHom c d F (t • x)=t • logHom c d F x := by
  simp only [logHom,canonicalExp_smul,map_realPower c d F hF,canonicalLog_realPower]

lemma logHom_contDiff (hsk : SecondKind d) (F : H →* G) (hF : Continuous F) :
    ContDiff ℝ ⊤ (logHom c d F) :=
  contDiff_pi.mpr (fun i=>RealPolynomialMap.contDiff (logHom_polynomial c d hsk F hF i))

def logHomLinear (F : H →* G) : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) :=
  fderiv ℝ (logHom c d F) 0

lemma logHomLinear_apply (hsk : SecondKind d) (F : H →* G) (hF : Continuous F)
    (x : Fin n → ℝ) : logHomLinear c d F x=logHom c d F x :=
  RealPolynomialMap.homogeneous_eq_fderiv
    ((logHom_contDiff c d hsk F hF).differentiable (by simp)).differentiableAt
    (logHom_smul c d F hF) x

lemma map_canonicalExp (hsk : SecondKind d) (F : H →* G) (hF : Continuous F)
    (x : Fin n → ℝ) : F (canonicalExp d x)=canonicalExp c (logHomLinear c d F x) := by
  rw [logHomLinear_apply c d hsk F hF,logHom,canonicalExp_log]

lemma logHomLinear_log (hsk : SecondKind d) (F : H →* G) (hF : Continuous F) (g : H) :
    logHomLinear c d F (canonicalLog d g)=canonicalLog c (F g) := by
  rw [logHomLinear_apply c d hsk F hF,logHom,canonicalExp_log]

end RationalLattice
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughKernelFactorization
open RationalLattice MalcevCharacters IntegerHyperplane
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G (n+1)) (hsk : SecondKind c)
variable (χ : G →* Multiplicative ℝ) (k : Fin (n+1) → ℤ) (p : Fin (n+1))
variable (hp : k p ≠ 0)
variable (hχ : ∀ g : G,(χ g).toAdd=form k (c.coord g))

def sectionFlow : Multiplicative ℝ →* G where
  toFun t := axis c p (t.toAdd/(k p:ℝ))
  map_one' := by simp
  map_mul' t u := by change axis c p ((t.toAdd+u.toAdd)/(k p:ℝ))=_; rw [add_div,hsk.axis_add]

omit [IsTopologicalGroup G] in
lemma sectionFlow_continuous [IsTopologicalGroup G] : Continuous (sectionFlow c hsk k p) :=
  (axis_continuous c p).comp (continuous_toAdd.div_const _)

include hp hχ in
omit [IsTopologicalGroup G] in
lemma sectionFlow_character [IsTopologicalGroup G] (t : ℝ) :
    (χ (sectionFlow c hsk k p (Multiplicative.ofAdd t))).toAdd=t := by
  classical
  change (χ (axis c p (t/(k p:ℝ)))).toAdd=t
  rw [hχ,coord_axis]
  change (∑ i,(k i:ℝ)*(Pi.single p (t/(k p:ℝ)) : Fin (n+1) → ℝ) i)=t
  simp only [Pi.single_apply,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact mul_div_cancel₀ t (by exact_mod_cast hp)

omit [IsTopologicalGroup G] in
lemma sectionFlow_rational [IsTopologicalGroup G] (t : ℚ) :
    IsRational c (sectionFlow c hsk k p (Multiplicative.ofAdd (t:ℝ))) := by
  classical
  intro i
  refine ⟨if i=p then t/(k p:ℚ) else 0,?_⟩
  change _=c.coord (axis c p ((t:ℝ)/(k p:ℝ))) i
  rw [coord_axis]
  simp only [Pi.single_apply]
  split_ifs <;> push_cast <;> rfl

omit [IsTopologicalGroup G] in
lemma sectionFlow_polynomial [IsTopologicalGroup G] {σ : Type*} {f : (σ → ℝ) → ℝ}
    (hf : RealPolynomialMap.IsPolynomial f) :
    IsRealPolynomialMap c (fun x=>sectionFlow c hsk k p (Multiplicative.ofAdd (f x))) := by
  classical
  intro i
  change RealPolynomialMap.IsPolynomial (fun x=>c.coord (axis c p (f x/(k p:ℝ))) i)
  simp only [coord_axis,Pi.single_apply]
  split_ifs
  · simpa [div_eq_mul_inv] using RealPolynomialMap.mul hf (RealPolynomialMap.const (k p:ℝ)⁻¹)
  · exact RealPolynomialMap.const 0

lemma sectionFlow_exponential (t : ℝ) :
    canonicalExp c (t • canonicalLog c (sectionFlow c hsk k p (Multiplicative.ofAdd 1)))=
      sectionFlow c hsk k p (Multiplicative.ofAdd t) := by
  rw [canonicalExp_smul,canonicalExp_log]
  exact (RationalLevelFlow.continuous_flow_eq_realPower c (sectionFlow c hsk k p)
    (sectionFlow_continuous c hsk k p) t).symm

variable (Γ : Subgroup G)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)

include hp hΓ in
omit [IsTopologicalGroup G] in
lemma sectionFlow_period [IsTopologicalGroup G] : ∃ K : ℕ,0<K ∧
    sectionFlow c hsk k p (Multiplicative.ofAdd (K:ℝ))∈Γ := by
  have hpN : 0<(k p).natAbs := Int.natAbs_pos.mpr hp
  refine ⟨(k p).natAbs^2,pow_pos hpN _,?_⟩
  apply (hΓ _).mpr
  have he : (((k p).natAbs^2:ℕ):ℝ)=(k p:ℝ)^2 := by
    have hh:=congrArg (fun z : ℤ=>(z:ℝ)) (Int.natAbs_sq (k p))
    simpa only [Int.cast_pow,Int.cast_natCast,Nat.cast_pow] using hh
  have hpR : (k p:ℝ)≠0 := by exact_mod_cast hp
  have hdiv : (((k p).natAbs^2:ℕ):ℝ)/(k p:ℝ)=(k p:ℝ) := by
    rw [he,pow_two,mul_div_cancel_right₀ _ hpR]
  intro i
  change ∃ z : ℤ,c.coord (axis c p ((((k p).natAbs^2:ℕ):ℝ)/(k p:ℝ))) i=(z:ℝ)
  rw [hdiv,coord_axis]
  classical
  by_cases hi : i=p
  · subst i
    exact ⟨k p,by simp⟩
  · exact ⟨0,by simp [hi]⟩

omit [IsTopologicalGroup G] in
lemma same_coset_of_mod [IsTopologicalGroup G] (K : ℕ)
    (hK : sectionFlow c hsk k p (Multiplicative.ofAdd (K:ℝ))∈Γ)
    (z j : ℤ) (hmod : (K:ℤ)∣z-j) :
    (QuotientGroup.mk (sectionFlow c hsk k p (Multiplicative.ofAdd (z:ℝ))) : G⧸Γ)=
      QuotientGroup.mk (sectionFlow c hsk k p (Multiplicative.ofAdd (j:ℝ))) := by
  apply QuotientGroup.eq.mpr
  obtain ⟨q,hq⟩:=hmod
  have hz : -(z:ℝ)+(j:ℝ)=(K:ℝ)*(-q:ℤ) := by
    have hh : (z:ℝ)-(j:ℝ)=(K:ℝ)*(q:ℝ) := by exact_mod_cast hq
    push_cast
    linarith
  have he : (sectionFlow c hsk k p (Multiplicative.ofAdd (z:ℝ)))⁻¹*
      sectionFlow c hsk k p (Multiplicative.ofAdd (j:ℝ))=
      sectionFlow c hsk k p (Multiplicative.ofAdd (K:ℝ))^(-q) := by
    rw [← map_inv,← map_mul,← map_zpow]
    congr 1
    apply Multiplicative.toAdd.injective
    change -(z:ℝ)+(j:ℝ)=(-q) • (K:ℝ)
    simpa [zsmul_eq_mul,mul_comm] using hz
  rw [he]
  exact Γ.zpow_mem hK _

variable (hlast : ∀ j : Fin (n+1),p<j → k j=0)
variable {σ : Type*} (P : (σ → ℝ) → G) (a m : (σ → ℝ) → ℝ)
variable (hP : ∀ x,(χ (P x)).toAdd=a x+m x)

include hp hχ hP in
lemma residual_mem (x : σ → ℝ) :
    sectionFlow c hsk k p (Multiplicative.ofAdd (-a x))*P x*
      sectionFlow c hsk k p (Multiplicative.ofAdd (-m x)) ∈ χ.ker := by
  change χ _=1
  apply Multiplicative.toAdd.injective
  simp only [MonoidHom.map_mul]
  change (χ (sectionFlow c hsk k p (Multiplicative.ofAdd (-a x)))).toAdd+
    (χ (P x)).toAdd+(χ (sectionFlow c hsk k p (Multiplicative.ofAdd (-m x)))).toAdd=0
  rw [sectionFlow_character c hsk χ k p hp hχ,sectionFlow_character c hsk χ k p hp hχ,hP]
  ring

def residual (x : σ → ℝ) : χ.ker :=
  ⟨sectionFlow c hsk k p (Multiplicative.ofAdd (-a x))*P x*
      sectionFlow c hsk k p (Multiplicative.ofAdd (-m x)),
    residual_mem c hsk χ k p hp hχ P a m hP x⟩

lemma residual_factorization (x : σ → ℝ) :
    P x=sectionFlow c hsk k p (Multiplicative.ofAdd (a x))*
      (residual c hsk χ k p hp hχ P a m hP x).val*
      sectionFlow c hsk k p (Multiplicative.ofAdd (m x)) := by
  change P x=_*( _*P x*_)*_
  have ha : sectionFlow c hsk k p (Multiplicative.ofAdd (-a x))=
      (sectionFlow c hsk k p (Multiplicative.ofAdd (a x)))⁻¹ := map_inv _ _
  have hm : sectionFlow c hsk k p (Multiplicative.ofAdd (-m x))=
      (sectionFlow c hsk k p (Multiplicative.ofAdd (m x)))⁻¹ := map_inv _ _
  rw [ha,hm]
  group

lemma residual_polynomial (hpoly : IsRealPolynomialMap c P)
    (ha : RealPolynomialMap.IsPolynomial a) (hm : RealPolynomialMap.IsPolynomial m) :
    IsRealPolynomialMap (RationalCharacterKernel.kernelCoordinates c χ k p hp hχ hlast)
      (residual c hsk χ k p hp hχ P a m hP) := by
  have hh := realPolynomialMap_mul c
    (realPolynomialMap_mul c (sectionFlow_polynomial c hsk k p (RealPolynomialMap.neg ha)) hpoly)
    (sectionFlow_polynomial c hsk k p (RealPolynomialMap.neg hm))
  exact fun i=>hh (p.succAbove i)

end RoughKernelFactorization

end
end
end
end

end OAI
