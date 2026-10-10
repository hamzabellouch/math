import Mathlib

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.SeedAbsorption
open MeasureTheory ProbabilityTheory Function
open scoped InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma dual_comp_norm (A : F →L[ℝ] E) (L : StrongDual ℝ E) :
    ‖L.comp A‖=‖A.adjoint ((InnerProductSpace.toDual ℝ E).symm L)‖ := by
  have he : L.comp A=(InnerProductSpace.toDual ℝ F)
      (A.adjoint ((InnerProductSpace.toDual ℝ E).symm L)) := by
    ext x
    change L (A x)=inner ℝ (A.adjoint ((InnerProductSpace.toDual ℝ E).symm L)) x
    rw [A.adjoint_inner_left,InnerProductSpace.toDual_symm_apply]
  rw [he,LinearIsometryEquiv.norm_map]

theorem restore_gaussian (P : E →L[ℝ] E) (U : F →L[ℝ] E)
    (hcov : P.comp P.adjoint+U.comp U.adjoint=ContinuousLinearMap.id ℝ E) :
    ((stdGaussian E).prod (stdGaussian F)).map (fun z : E × F => P z.1-U z.2)=
      stdGaussian E := by
  let A : E × F →L[ℝ] E := P.comp (ContinuousLinearMap.fst ℝ E F)-
    U.comp (ContinuousLinearMap.snd ℝ E F)
  change ((stdGaussian E).prod (stdGaussian F)).map A=stdGaussian E
  apply Measure.ext_of_charFunDual
  ext L
  have h₁ : (L.comp A).comp (ContinuousLinearMap.inl ℝ E F)=L.comp P := by
    ext x; simp [A]
  have h₂ : (L.comp A).comp (ContinuousLinearMap.inr ℝ E F)=-(L.comp U) := by
    ext x; simp [A]
  have hn : ‖L.comp P‖^2+‖L.comp U‖^2=‖L‖^2 := by
    let x := (InnerProductSpace.toDual ℝ E).symm L
    have he := congrArg (fun B : E →L[ℝ] E => inner ℝ x (B x)) hcov
    simp only [add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply,inner_add_right] at he
    rw [← P.adjoint_inner_left,← U.adjoint_inner_left] at he
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq] at he
    simpa only [x,dual_comp_norm,LinearIsometryEquiv.norm_map] using he
  rw [charFunDual_map,charFunDual_prod,h₁,h₂]
  simp only [charFunDual_stdGaussian,norm_neg]
  rw [← Complex.exp_add]
  congr 1
  norm_cast
  linarith

theorem absorb_center_noise {Y : Type*} [MeasurableSpace Y]
    (P : E →L[ℝ] E) (U : F →L[ℝ] E)
    (hcov : P.comp P.adjoint+U.comp U.adjoint=ContinuousLinearMap.id ℝ E)
    (M : F → E → Y) (hM : Measurable (uncurry M)) (x : F)
    (n : ℝ) (shift : F →L[ℝ] E)
    (hU : U=n • shift)
    (hshift : ∀x Δ g,M (x+Δ) g=M x (g-shift Δ)) :
    ((stdGaussian E).prod (stdGaussian F)).map
      (fun z : E × F => M (x+n • z.2) (P z.1))=
      (stdGaussian E).map (M x) := by
  have hm : Measurable (M x) := hM.comp (measurable_const.prodMk measurable_id)
  have he : (fun z : E × F => M (x+n • z.2) (P z.1))=
      M x ∘ (fun z : E × F => P z.1-U z.2) := by
    funext z
    rw [hshift,hU]
    simp only [smul_apply,map_smul,comp_apply]
  rw [he,← Measure.map_map hm (by fun_prop),restore_gaussian P U hcov]
end LogConcaveSampling.SeedAbsorption

end

end

section

noncomputable section
namespace LogConcaveSampling.SeedAbsorption
open MeasureTheory ProbabilityTheory Function
open scoped InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

def dampingCoefficient (t : ℝ) : ℝ := (1+Real.sqrt (1-t))⁻¹

def seedDamping (U : F →L[ℝ] E) (t : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E-dampingCoefficient t • U.comp U.adjoint

lemma dampingCoefficient_identity {t : ℝ} (ht : t≤1) :
    2*dampingCoefficient t-(dampingCoefficient t)^2*t=1 := by
  have hsq := Real.sq_sqrt (show 0≤1-t by linarith)
  have hp : 0<1+Real.sqrt (1-t) := by positivity
  dsimp [dampingCoefficient]
  field_simp
  nlinarith

lemma seedDamping_adjoint (U : F →L[ℝ] E) (t : ℝ) :
    (seedDamping U t).adjoint=seedDamping U t := by
  simp only [seedDamping,map_sub,map_smulₛₗ,ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]
  rfl

lemma seedDamping_covariance (U : F →L[ℝ] E) {t : ℝ} (ht : t≤1)
    (hU : U.adjoint.comp U=t • ContinuousLinearMap.id ℝ F) :
    (seedDamping U t).comp (seedDamping U t).adjoint+U.comp U.adjoint=
      ContinuousLinearMap.id ℝ E := by
  rw [seedDamping_adjoint]
  ext x
  have he : U.adjoint (U (U.adjoint x))=t • U.adjoint x :=
    congrArg (fun L : F →L[ℝ] F => L (U.adjoint x)) hU
  have hα := dampingCoefficient_identity ht
  simp only [seedDamping,ContinuousLinearMap.comp_apply,sub_apply,smul_apply,
    ContinuousLinearMap.id_apply,add_apply,map_sub,map_smul,he]
  calc
    _ = x+(1-dampingCoefficient t*2+dampingCoefficient t^2*t) • U (U.adjoint x) := by module
    _ = x := by rw [show 1-dampingCoefficient t*2+dampingCoefficient t^2*t=0 by nlinarith [hα]]; simp

lemma seedDamping_positive (U : F →L[ℝ] E) {t : ℝ} (ht0 : 0≤t) (ht1 : t<1)
    (hUn : ∀x,‖U.adjoint x‖^2≤t*‖x‖^2) (x : E) :
    Real.sqrt (1-t)*‖x‖^2≤ inner ℝ x (seedDamping U t x) := by
  have hsq := Real.sq_sqrt (show 0≤1-t by linarith)
  have hp : 0<1+Real.sqrt (1-t) := by positivity
  have he : 1-dampingCoefficient t*t=Real.sqrt (1-t) := by
    dsimp [dampingCoefficient]
    field_simp
    nlinarith
  have hα : 0≤dampingCoefficient t := by dsimp [dampingCoefficient]; positivity
  simp only [seedDamping,sub_apply,smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
    inner_sub_right,inner_smul_right,← U.adjoint_inner_left,real_inner_self_eq_norm_sq]
  have hh := mul_le_mul (hUn x) (le_refl (dampingCoefficient t)) hα
    (mul_nonneg ht0 (sq_nonneg ‖x‖))
  rw [← he]
  nlinarith

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

theorem seedDamping_restore (U : F →L[ℝ] E) {t : ℝ} (ht : t≤1)
    (hU : U.adjoint.comp U=t • ContinuousLinearMap.id ℝ F) :
    ((stdGaussian E).prod (stdGaussian F)).map
      (fun z : E × F => seedDamping U t z.1-U z.2)=stdGaussian E :=
  restore_gaussian _ U (seedDamping_covariance U ht hU)
end LogConcaveSampling.SeedAbsorption

end

end

section

noncomputable section
namespace LogConcaveSampling.SeedAbsorption
open MeasureTheory ProbabilityTheory Function
open scoped InnerProductSpace

variable {E F A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace A]

theorem restore_gaussian_with_anchor (μ : Measure A) [SFinite μ]
    (P : E →L[ℝ] E) (U : F →L[ℝ] E)
    (hcov : P.comp P.adjoint+U.comp U.adjoint=ContinuousLinearMap.id ℝ E) :
    (μ.prod ((stdGaussian E).prod (stdGaussian F))).map
      (fun z : A × (E × F) => (z.1,P z.2.1-U z.2.2))=μ.prod (stdGaussian E) := by
  have h := Measure.map_prod_map μ ((stdGaussian E).prod (stdGaussian F))
    (f:=id) (g:=fun z : E × F => P z.1-U z.2) measurable_id (by fun_prop)
  rw [Measure.map_id,restore_gaussian P U hcov] at h
  exact h.symm

theorem absorb_center_noise_with_anchor {Y : Type*} [MeasurableSpace Y]
    (μ : Measure A) [SFinite μ] (P : E →L[ℝ] E) (U : F →L[ℝ] E)
    (hcov : P.comp P.adjoint+U.comp U.adjoint=ContinuousLinearMap.id ℝ E)
    (M : F → E → Y) (hM : Measurable (uncurry M))
    (x : A → F) (hx : Measurable x) (n : ℝ) (shift : F →L[ℝ] E)
    (hU : U=n • shift)
    (hshift : ∀x Δ g,M (x+Δ) g=M x (g-shift Δ)) :
    (μ.prod ((stdGaussian E).prod (stdGaussian F))).map
      (fun z : A × (E × F) => (z.1,M (x z.1+n • z.2.2) (P z.2.1)))=
      (μ.prod (stdGaussian E)).map (fun z : A × E => (z.1,M (x z.1) z.2)) := by
  have he : (fun z : A × (E × F) => (z.1,M (x z.1+n • z.2.2) (P z.2.1)))=
      (fun z : A × E => (z.1,M (x z.1) z.2)) ∘
        (fun z : A × (E × F) => (z.1,P z.2.1-U z.2.2)) := by
    funext z
    rw [hshift,hU]
    simp only [smul_apply,map_smul,comp_apply]
  rw [he,← Measure.map_map]
  · rw [restore_gaussian_with_anchor μ P U hcov]
  · exact measurable_fst.prodMk (hM.comp ((hx.comp measurable_fst).prodMk measurable_snd))
  · fun_prop
end LogConcaveSampling.SeedAbsorption

end

end

section

noncomputable section
namespace LogConcaveSampling.SeedAbsorption
open MeasureTheory ProbabilityTheory Function
open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] {A F : Type*} [MeasurableSpace A]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {E : ι → Type*} [∀i,NormedAddCommGroup (E i)] [∀i,InnerProductSpace ℝ (E i)]
  [∀i,FiniteDimensional ℝ (E i)] [∀i,MeasurableSpace (E i)] [∀i,BorelSpace (E i)]

theorem restore_gaussian_blocks (P : ∀i,E i →L[ℝ] E i) (U : ∀i,F →L[ℝ] E i)
    (hcov : ∀i,(P i).comp (P i).adjoint+(U i).comp (U i).adjoint=ContinuousLinearMap.id ℝ (E i)) :
    (Measure.pi (fun i => (stdGaussian (E i)).prod (stdGaussian F))).map
      (fun z i => P i (z i).1-U i (z i).2)=Measure.pi (fun i => stdGaussian (E i)) := by
  exact (measurePreserving_pi
    (fun i => (stdGaussian (E i)).prod (stdGaussian F)) (fun i => stdGaussian (E i))
    (fun i => ⟨by fun_prop,restore_gaussian (P i) (U i) (hcov i)⟩)).map_eq

theorem restore_gaussian_blocks_with_anchor (μ : Measure A) [SFinite μ]
    (P : ∀i,E i →L[ℝ] E i) (U : ∀i,F →L[ℝ] E i)
    (hcov : ∀i,(P i).comp (P i).adjoint+(U i).comp (U i).adjoint=ContinuousLinearMap.id ℝ (E i)) :
    (μ.prod (Measure.pi (fun i => (stdGaussian (E i)).prod (stdGaussian F)))).map
      (fun z : A × (∀i,E i × F) => (z.1,fun i => P i (z.2 i).1-U i (z.2 i).2))=
        μ.prod (Measure.pi (fun i => stdGaussian (E i))) := by
  have h := Measure.map_prod_map μ (Measure.pi (fun i => (stdGaussian (E i)).prod (stdGaussian F)))
    (f:=id) (g:=fun z i => P i (z i).1-U i (z i).2) measurable_id (by fun_prop)
  rw [Measure.map_id,restore_gaussian_blocks P U hcov] at h
  exact h.symm

theorem absorb_center_noise_blocks {Y : ι → Type*} [∀i,MeasurableSpace (Y i)]
    (μ : Measure A) [SFinite μ] (P : ∀i,E i →L[ℝ] E i) (U : ∀i,F →L[ℝ] E i)
    (hcov : ∀i,(P i).comp (P i).adjoint+(U i).comp (U i).adjoint=ContinuousLinearMap.id ℝ (E i))
    (M : ∀i,F → E i → Y i) (hM : ∀i,Measurable (uncurry (M i)))
    (x : ι → A → F) (hx : ∀i,Measurable (x i)) (n : ι → ℝ)
    (shift : ∀i,F →L[ℝ] E i) (hU : ∀i,U i=n i • shift i)
    (hshift : ∀i x Δ g,M i (x+Δ) g=M i x (g-shift i Δ)) :
    (μ.prod (Measure.pi (fun i => (stdGaussian (E i)).prod (stdGaussian F)))).map
      (fun z : A × (∀i,E i × F) =>
        (z.1,fun i => M i (x i z.1+n i • (z.2 i).2) (P i (z.2 i).1)))=
      (μ.prod (Measure.pi (fun i => stdGaussian (E i)))).map
        (fun z : A × (∀i,E i) => (z.1,fun i => M i (x i z.1) (z.2 i))) := by
  let R : (A × (∀i,E i × F)) → (A × (∀i,E i)) :=
    fun z => (z.1,fun i => P i (z.2 i).1-U i (z.2 i).2)
  let C : (A × (∀i,E i)) → (A × (∀i,Y i)) :=
    fun z => (z.1,fun i => M i (x i z.1) (z.2 i))
  have he : (fun z : A × (∀i,E i × F) =>
      (z.1,fun i => M i (x i z.1+n i • (z.2 i).2) (P i (z.2 i).1)))=C ∘ R := by
    funext z
    apply Prod.ext
    · rfl
    funext i
    change M i (x i z.1+n i • (z.2 i).2) (P i (z.2 i).1)=
      M i (x i z.1) (P i (z.2 i).1-U i (z.2 i).2)
    rw [hshift,hU]
    simp only [smul_apply,map_smul]
  have hc : Measurable C := measurable_fst.prodMk (Measurable.of_eval
    (fun i => (hM i).comp (((hx i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))))
  rw [he,←Measure.map_map hc (by dsimp [R]; fun_prop)]
  change ((μ.prod (Measure.pi (fun i => (stdGaussian (E i)).prod (stdGaussian F)))).map R).map C=_
  rw [show (μ.prod (Measure.pi (fun i => (stdGaussian (E i)).prod (stdGaussian F)))).map R=
    μ.prod (Measure.pi (fun i => stdGaussian (E i))) from restore_gaussian_blocks_with_anchor μ P U hcov]
end LogConcaveSampling.SeedAbsorption

end

end

end

end OAI
