import Mathlib

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.Degree

section
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {m : ℕ}
abbrev CoordinateSpace (m : ℕ) := Fin m → ℝ

def coordinateVector (i : Fin m) : CoordinateSpace m := Pi.single i 1

def formFlux (w : CoordinateSpace (m+1) → CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ)
    (i : Fin (m+1)) (x : CoordinateSpace (m+1)) : ℝ :=
  (-1:ℝ)^i.val • w x (i.removeNth coordinateVector)

lemma formFlux_differentiable
    {w : CoordinateSpace (m+1) → CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ}
    (hw : Differentiable ℝ w) (i : Fin (m+1)) : Differentiable ℝ (formFlux w i) := by
  exact ((ContinuousAlternatingMap.apply ℝ _ ℝ (i.removeNth coordinateVector)).differentiable.comp hw).const_smul ((-1:ℝ)^i.val)

lemma formFlux_divergence
    {w : CoordinateSpace (m+1) → CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ}
    (hw : Differentiable ℝ w) (x : CoordinateSpace (m+1)) :
    (∑ i, fderiv ℝ (formFlux w i) x (coordinateVector i))=extDeriv w x coordinateVector := by
  rw [extDeriv_apply (hw x)]
  apply Finset.sum_congr rfl
  intro i hi
  have he : DifferentiableAt ℝ (fun y => w y (i.removeNth coordinateVector)) x :=
    (ContinuousAlternatingMap.apply ℝ _ ℝ (i.removeNth coordinateVector)).differentiableAt.comp x (hw x)
  change fderiv ℝ (fun y => (-1:ℝ)^i.val • w y (i.removeNth coordinateVector)) x
    (coordinateVector i)=_
  rw [fderiv_fun_const_smul he]
  simp only [smul_apply,smul_eq_mul,zsmul_eq_mul,Int.cast_pow,Int.cast_neg,Int.cast_one]

lemma closedForm_box_boundary
    {w : CoordinateSpace (m+1) → CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ}
    (hw : Differentiable ℝ w) (hclosed : ∀ x,extDeriv w x=0)
    (a b : CoordinateSpace (m+1)) (hab : a≤b) :
    (∑ i : Fin (m+1),
      ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),formFlux w i (i.insertNth (b i) y))-
        ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),formFlux w i (i.insertNth (a i) y)))=0 := by
  have hz (x : CoordinateSpace (m+1)) : (∑ i,fderiv ℝ (formFlux w i) x (coordinateVector i))=0 := by
    rw [formFlux_divergence hw,hclosed]
    rfl
  have he := integral_divergence_of_hasFDerivAt_off_countable' a b hab (formFlux w)
    (fun i x => fderiv ℝ (formFlux w i) x) ∅ countable_empty
    (fun i => (formFlux_differentiable hw i).continuous.continuousOn)
    (fun x hx i => (formFlux_differentiable hw i x).hasFDerivAt)
    (by
      change IntegrableOn (fun x => ∑ i,fderiv ℝ (formFlux w i) x (coordinateVector i)) (Icc a b)
      simpa only [hz] using (integrableOn_zero : IntegrableOn (fun _ : CoordinateSpace (m+1) => (0:ℝ)) (Icc a b)))
  have hz' : (∫ x in Icc a b,∑ i,fderiv ℝ (formFlux w i) x (Pi.single i 1))=0 := by
    change (∫ x in Icc a b,∑ i,fderiv ℝ (formFlux w i) x (coordinateVector i))=0
    simp only [hz,integral_zero]
  exact he.symm.trans hz'

lemma closedForm_endpoint_flux
    {w : CoordinateSpace (m+1) → CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ}
    (hw : Differentiable ℝ w) (hclosed : ∀ x,extDeriv w x=0)
    (a b : CoordinateSpace (m+1)) (hab : a≤b)
    (hside : ∀ i : Fin (m+1),i≠0 → ∀ y∈Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      formFlux w i (i.insertNth (b i) y)=0 ∧ formFlux w i (i.insertNth (a i) y)=0) :
    (∫ y in Icc (a ∘ (0:Fin (m+1)).succAbove) (b ∘ (0:Fin (m+1)).succAbove),
        formFlux w 0 ((0:Fin (m+1)).insertNth (b 0) y))=
      ∫ y in Icc (a ∘ (0:Fin (m+1)).succAbove) (b ∘ (0:Fin (m+1)).succAbove),
        formFlux w 0 ((0:Fin (m+1)).insertNth (a 0) y) := by
  have he := closedForm_box_boundary hw hclosed a b hab
  rw [Finset.sum_eq_single (0:Fin (m+1))] at he
  · exact sub_eq_zero.mp he
  · intro i hi hi0
    have htop : (∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),formFlux w i (i.insertNth (b i) y))=0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      exact fun y hy => (hside i hi0 y hy).1
    have hbottom : (∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),formFlux w i (i.insertNth (a i) y))=0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      exact fun y hy => (hside i hi0 y hy).2
    rw [htop,hbottom,sub_self]
  · simp

lemma topForm_closed (w : CoordinateSpace m → CoordinateSpace m [⋀^Fin m]→L[ℝ] ℝ)
    (x : CoordinateSpace m) : extDeriv w x=0 := by
  apply ContinuousAlternatingMap.ext
  intro v
  apply (extDeriv w x).toAlternatingMap.map_linearDependent v
  intro hv
  have hdim := hv.fintype_card_le_finrank
  simp only [Fintype.card_fin,Module.finrank_pi] at hdim
  omega


def pullTopForm (F : CoordinateSpace (m+1) → CoordinateSpace m)
    (w : CoordinateSpace m → CoordinateSpace m [⋀^Fin m]→L[ℝ] ℝ)
    (x : CoordinateSpace (m+1)) : CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ :=
  (w (F x)).compContinuousLinearMap (fderiv ℝ F x)

lemma pullTopForm_differentiable
    {F : CoordinateSpace (m+1) → CoordinateSpace m} (hF : ContDiff ℝ ∞ F)
    {w : CoordinateSpace m → CoordinateSpace m [⋀^Fin m]→L[ℝ] ℝ}
    (hw : Differentiable ℝ w) : Differentiable ℝ (pullTopForm F w) := by
  intro x
  exact ((hw (F x)).comp x (hF.differentiable (by simp) x)).continuousAlternatingMapCompContinuousLinearMap
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)

lemma pullTopForm_closed
    {F : CoordinateSpace (m+1) → CoordinateSpace m} (hF : ContDiff ℝ ∞ F)
    {w : CoordinateSpace m → CoordinateSpace m [⋀^Fin m]→L[ℝ] ℝ}
    (hw : Differentiable ℝ w) (x : CoordinateSpace (m+1)) :
    extDeriv (pullTopForm F w) x=0 := by
  change extDeriv (fun x => (w (F x)).compContinuousLinearMap (fderiv ℝ F x)) x=0
  rw [extDeriv_pullback (hw (F x)) hF.contDiffAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top),topForm_closed]
  ext v
  rfl

lemma pullTopForm_zero {F : CoordinateSpace (m+1) → CoordinateSpace m}
    {w : CoordinateSpace m → CoordinateSpace m [⋀^Fin m]→L[ℝ] ℝ}
    {x : CoordinateSpace (m+1)} (hw : w (F x)=0) : pullTopForm F w x=0 := by
  rw [pullTopForm,hw]
  ext v
  rfl

lemma finite_homotopy_flux
    {F : CoordinateSpace (m+1) → CoordinateSpace m} (hF : ContDiff ℝ ∞ F)
    {w : CoordinateSpace m → CoordinateSpace m [⋀^Fin m]→L[ℝ] ℝ}
    (hw : Differentiable ℝ w) (a b : CoordinateSpace (m+1)) (hab : a≤b)
    (hside : ∀ i : Fin (m+1),i≠0 → ∀ y∈Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      w (F (i.insertNth (b i) y))=0 ∧ w (F (i.insertNth (a i) y))=0) :
    (∫ y in Icc (a ∘ (0:Fin (m+1)).succAbove) (b ∘ (0:Fin (m+1)).succAbove),
        formFlux (pullTopForm F w) 0 ((0:Fin (m+1)).insertNth (b 0) y))=
      ∫ y in Icc (a ∘ (0:Fin (m+1)).succAbove) (b ∘ (0:Fin (m+1)).succAbove),
        formFlux (pullTopForm F w) 0 ((0:Fin (m+1)).insertNth (a 0) y) := by
  apply closedForm_endpoint_flux (pullTopForm_differentiable hF hw) (pullTopForm_closed hF hw) a b hab
  intro i hi y hy
  obtain ⟨ht,hb⟩ := hside i hi y hy
  constructor
  · simp only [formFlux,pullTopForm_zero ht,ContinuousAlternatingMap.coe_zero,Pi.zero_apply,smul_zero]
  · simp only [formFlux,pullTopForm_zero hb,ContinuousAlternatingMap.coe_zero,Pi.zero_apply,smul_zero]

lemma finite_homotopy_support_endpoint
    {F : CoordinateSpace (m+1) → CoordinateSpace m} (hF : ContDiff ℝ ∞ F)
    {w : CoordinateSpace m → CoordinateSpace m [⋀^Fin m]→L[ℝ] ℝ}
    (hw : Differentiable ℝ w) (a b : CoordinateSpace (m+1)) (hab : a≤b)
    (hside : ∀ i : Fin (m+1),i≠0 → ∀ y∈Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      w (F (i.insertNth (b i) y))=0 ∧ w (F (i.insertNth (a i) y))=0)
    (hinit : (∫ y in Icc (a ∘ (0:Fin (m+1)).succAbove) (b ∘ (0:Fin (m+1)).succAbove),
        formFlux (pullTopForm F w) 0 ((0:Fin (m+1)).insertNth (a 0) y))≠0) :
    ∃ y∈Icc (a ∘ (0:Fin (m+1)).succAbove) (b ∘ (0:Fin (m+1)).succAbove),
      w (F ((0:Fin (m+1)).insertNth (b 0) y))≠0 := by
  by_contra hn
  push Not at hn
  have he := finite_homotopy_flux hF hw a b hab hside
  apply hinit
  rw [←he]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  simp only [formFlux,pullTopForm_zero (hn y hy),ContinuousAlternatingMap.coe_zero,Pi.zero_apply,smul_zero]


def coordinateVolume (m : ℕ) : CoordinateSpace m [⋀^Fin m]→L[ℝ] ℝ where
  toAlternatingMap := (Pi.basisFun ℝ (Fin m)).det
  cont := by
    change Continuous (fun v : Fin m → CoordinateSpace m => (Pi.basisFun ℝ (Fin m)).det v)
    simp only [Pi.basisFun_det_apply]
    exact continuous_id.matrix_det

lemma coordinateVolume_basis : coordinateVolume m coordinateVector=1 := by
  change (Pi.basisFun ℝ (Fin m)).det _=1
  have he : (coordinateVector : Fin m → CoordinateSpace m)=Pi.basisFun ℝ (Fin m) := by
    funext i
    exact (Pi.basisFun_apply ℝ (Fin m) i).symm
  rw [he]
  exact Module.Basis.det_self _

def weightedVolume (ρ : CoordinateSpace m → ℝ) (x : CoordinateSpace m) :
    CoordinateSpace m [⋀^Fin m]→L[ℝ] ℝ := ρ x • coordinateVolume m

lemma weightedVolume_differentiable {ρ : CoordinateSpace m → ℝ} (hρ : Differentiable ℝ ρ) :
    Differentiable ℝ (weightedVolume ρ) := hρ.smul_const _

lemma weightedVolume_zero {ρ : CoordinateSpace m → ℝ} {x : CoordinateSpace m} (hx : ρ x=0) :
    weightedVolume ρ x=0 := by rw [weightedVolume,hx,zero_smul]

lemma weightedVolume_basis (ρ : CoordinateSpace m → ℝ) (x : CoordinateSpace m) :
    weightedVolume ρ x coordinateVector=ρ x := by
  simp [weightedVolume,coordinateVolume_basis]

def spaceInclusion (m : ℕ) : CoordinateSpace m →L[ℝ] CoordinateSpace (m+1) :=
  ContinuousLinearMap.pi (Fin.cons 0 (fun i => ContinuousLinearMap.proj i))

lemma spaceInclusion_apply (y : CoordinateSpace m) : spaceInclusion m y=Fin.cons 0 y := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

lemma spaceInclusion_coordinateVector (i : Fin m) :
    spaceInclusion m (coordinateVector i)=coordinateVector i.succ := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [spaceInclusion_apply,coordinateVector]
  · simp [spaceInclusion_apply,coordinateVector,Pi.single_apply]

def timeFace (t : ℝ) (y : CoordinateSpace m) : CoordinateSpace (m+1) := Fin.cons t y

lemma timeFace_hasFDerivAt (t : ℝ) (y : CoordinateSpace m) :
    HasFDerivAt (timeFace t) (spaceInclusion m) y := by
  have he : timeFace (m := m) t=(fun y => Pi.single (0:Fin (m+1)) t+spaceInclusion m y) := by
    funext y
    ext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp [timeFace,spaceInclusion_apply]
  rw [he]
  exact (spaceInclusion m).hasFDerivAt.const_add _

lemma initial_spatial_derivative
    {F : CoordinateSpace (m+1) → CoordinateSpace m} (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (hinit : ∀ y,F (timeFace t y)=y) (y : CoordinateSpace m) :
    (fderiv ℝ F (timeFace t y)).comp (spaceInclusion m)=ContinuousLinearMap.id ℝ (CoordinateSpace m) := by
  have hd := (hF.differentiable (by simp) (timeFace t y)).hasFDerivAt.comp y (timeFace_hasFDerivAt t y)
  have he : (F ∘ timeFace t)=id := funext hinit
  rw [he] at hd
  exact hd.unique (hasFDerivAt_id y)

lemma initial_weighted_flux
    {F : CoordinateSpace (m+1) → CoordinateSpace m} (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (hinit : ∀ y,F (timeFace t y)=y) (ρ : CoordinateSpace m → ℝ) (y : CoordinateSpace m) :
    formFlux (pullTopForm F (weightedVolume ρ)) 0 ((0:Fin (m+1)).insertNth t y)=ρ y := by
  have hd := initial_spatial_derivative hF t hinit y
  have hb (i : Fin m) : fderiv ℝ F (timeFace t y) (coordinateVector i.succ)=coordinateVector i := by
    have he := congrArg (fun A : CoordinateSpace m →L[ℝ] CoordinateSpace m => A (coordinateVector i)) hd
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,spaceInclusion_coordinateVector] using he
  simp only [formFlux,Fin.val_zero,pow_zero,one_smul,Fin.insertNth_zero']
  change weightedVolume ρ (F (timeFace t y)) (fun i => fderiv ℝ F (timeFace t y) (coordinateVector i.succ))=ρ y
  simp only [hb,hinit]
  exact weightedVolume_basis ρ y


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
variable {d : ℕ}

lemma topForm_evaluation (w : CoordinateSpace d [⋀^Fin d]→L[ℝ] ℝ)
    (A : CoordinateSpace d →L[ℝ] CoordinateSpace d) :
    w (fun i => A (coordinateVector i))=A.det*w coordinateVector := by
  have hb : (coordinateVector : Fin d → CoordinateSpace d)=Pi.basisFun ℝ (Fin d) := by
    funext i
    exact (Pi.basisFun_apply ℝ (Fin d) i).symm
  change w.toAlternatingMap (A ∘ coordinateVector)=_
  have he := w.toAlternatingMap.eq_smul_basis_det (Pi.basisFun ℝ (Fin d))
  conv_lhs => rw [he]
  simp only [AlternatingMap.smul_apply,smul_eq_mul,hb]
  change w (Pi.basisFun ℝ (Fin d)) *
    (Pi.basisFun ℝ (Fin d)).det (A.toLinearMap ∘ Pi.basisFun ℝ (Fin d))=_
  rw [Module.Basis.det_comp,Module.Basis.det_self,mul_one]
  exact mul_comm _ _

variable {M : Type*} [TopologicalSpace M]

theorem topForm_chartMass_change [T2Space M]
    (c b : OpenPartialHomeomorph M (CoordinateSpace d)) {K : Set M}
    (hK : IsCompact K) (hKb : K⊆b.source) (hKc : K⊆c.source)
    (hg : ContDiffOn ℝ ∞ (c ∘ b.symm) (b.symm ≫ₕ c).source)
    (ωb ωc : CoordinateSpace d → CoordinateSpace d [⋀^Fin d]→L[ℝ] ℝ)
    (σb σc : ℝ)
    (hω : ∀ y∈b '' K,ωb y=(ωc (c (b.symm y))).compContinuousLinearMap
      (fderiv ℝ (c ∘ b.symm) y))
    (hσ : ∀ y∈b '' K,σb*(fderiv ℝ (c ∘ b.symm) y).det=
      σc*|(fderiv ℝ (c ∘ b.symm) y).det|) :
    (∫ y in b '' K,σb*ωb y coordinateVector)=
      ∫ y in c '' K,σc*ωc y coordinateVector := by
  let g := c ∘ b.symm
  have hyb {y : CoordinateSpace d} (hy : y∈b '' K) : y∈b.target := by
    rcases hy with ⟨x,hx,rfl⟩
    exact b.map_source (hKb hx)
  have hyK {y : CoordinateSpace d} (hy : y∈b '' K) : b.symm y∈K := by
    rcases hy with ⟨x,hx,rfl⟩
    simpa only [b.left_inv (hKb hx)] using hx
  have hys {y : CoordinateSpace d} (hy : y∈b '' K) : y∈(b.symm ≫ₕ c).source :=
    ⟨hyb hy,hKc (hyK hy)⟩
  have hgs {y : CoordinateSpace d} (hy : y∈b '' K) : ContDiffAt ℝ ∞ g y :=
    hg.contDiffAt ((b.symm ≫ₕ c).open_source.mem_nhds (hys hy))
  have hgi : InjOn g (b '' K) := by
    intro y hy z hz he
    exact b.symm.injOn (hyb hy) (hyb hz) (c.injOn (hKc (hyK hy)) (hKc (hyK hz)) he)
  have him : g '' (b '' K)=c '' K := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨b.symm z,hyK hz,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      refine ⟨b x,⟨x,hx,rfl⟩,?_⟩
      exact congrArg c (b.left_inv (hKb hx))
  have hm : MeasurableSet (b '' K) :=
    (hK.image_of_continuousOn (b.continuousOn.mono hKb)).measurableSet
  have hi := integral_image_eq_integral_abs_det_fderiv_smul volume hm
    (f' := fderiv ℝ g)
    (fun y hy => ((hgs hy).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt)
    hgi (fun y => σc*ωc y coordinateVector)
  rw [him] at hi
  rw [hi]
  apply setIntegral_congr_fun hm
  intro y hy
  dsimp only
  rw [hω y hy]
  change σb*ωc (g y) (fun i => fderiv ℝ g y (coordinateVector i))=
    |(fderiv ℝ g y).det| • (σc*ωc (g y) coordinateVector)
  rw [topForm_evaluation,←mul_assoc,hσ y hy]
  simp only [smul_eq_mul]
  ring


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
variable {M I : Type*} [TopologicalSpace M] {d k : ℕ}

structure SignedSmoothAtlas (M I : Type*) [TopologicalSpace M] (d : ℕ) where
  chart : I → OpenPartialHomeomorph M (CoordinateSpace d)
  cover : ∀ x : M,∃ i,x∈(chart i).source
  sign : I → ℝ
  sign_sq : ∀ i,sign i*sign i=1
  transition_smooth : ∀ i j,ContDiffOn ℝ ∞ (chart j ∘ (chart i).symm)
    ((chart i).symm ≫ₕ chart j).source
  orientation : ∀ i j,∀ q∈((chart i).symm ≫ₕ chart j).source,
    sign i*(fderiv ℝ (chart j ∘ (chart i).symm) q).det =
      sign j*|(fderiv ℝ (chart j ∘ (chart i).symm) q).det|

structure AtlasForm (a : SignedSmoothAtlas M I d) (k : ℕ) where
  form : I → CoordinateSpace d → CoordinateSpace d [⋀^Fin k]→L[ℝ] ℝ
  smooth : ∀ i,ContDiffOn ℝ ∞ (form i) (a.chart i).target
  compatible : ∀ i j,∀ q∈((a.chart i).symm ≫ₕ a.chart j).source,
    form i q=(form j (a.chart j ((a.chart i).symm q))).compContinuousLinearMap
      (fderiv ℝ (a.chart j ∘ (a.chart i).symm) q)

namespace AtlasForm
variable {a : SignedSmoothAtlas M I d} (α : AtlasForm a k)

def SupportedIn (K : Set M) : Prop :=
  ∀ i q,q∈(a.chart i).target → (a.chart i).symm q∉K → α.form i q=0

lemma contDiffOn_extDeriv (i : I) : ContDiffOn ℝ ∞ (extDeriv (α.form i)) (a.chart i).target := by
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (CoordinateSpace d) ℝ).contDiff.comp_contDiffOn
    ((contDiffOn_infty_iff_fderiv_of_isOpen (a.chart i).open_target).mp (α.smooth i)).2

def exterior : AtlasForm a (k+1) where
  form := fun i => extDeriv (α.form i)
  smooth := α.contDiffOn_extDeriv
  compatible i j q hq := by
    let g := a.chart j ∘ (a.chart i).symm
    have he : α.form i =ᶠ[𝓝 q] (fun y => (α.form j (g y)).compContinuousLinearMap (fderiv ℝ g y)) := by
      filter_upwards [((a.chart i).symm ≫ₕ a.chart j).open_source.mem_nhds hq] with y hy
      exact α.compatible i j y hy
    have hgt : g q∈(a.chart j).target := (a.chart j).map_source hq.2
    have hω := ((α.smooth j).contDiffAt ((a.chart j).open_target.mem_nhds hgt)).differentiableAt (by simp)
    rw [he.extDeriv_eq]
    exact extDeriv_pullback hω
      ((a.transition_smooth i j).contDiffAt (((a.chart i).symm ≫ₕ a.chart j).open_source.mem_nhds hq)) (by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.mpr le_top)

lemma exterior_supported {K : Set M} (hK : IsClosed K) (hα : α.SupportedIn K) :
    α.exterior.SupportedIn K := by
  intro i q hq hn
  have he : α.form i =ᶠ[𝓝 q] fun _ => 0 := by
    have hg : ∀ᶠ y in 𝓝 q,(a.chart i).symm y∉K :=
      ((a.chart i).continuousOn_symm.continuousAt ((a.chart i).open_target.mem_nhds hq))
        (hK.isOpen_compl.mem_nhds hn)
    filter_upwards [(a.chart i).open_target.mem_nhds hq,hg] with y hy hyn
    exact hα i y hy hyn
  change extDeriv (α.form i) q=0
  rw [he.extDeriv_eq]
  ext v
  rw [extDeriv_apply (differentiableAt_const _)]
  simp

def smul (f : M → ℝ)
    (hf : ∀ i,ContDiffOn ℝ ∞ (f ∘ (a.chart i).symm) (a.chart i).target) : AtlasForm a k where
  form := fun i q => f ((a.chart i).symm q) • α.form i q
  smooth i := (hf i).smul (α.smooth i)
  compatible i j q hq := by
    have he := (a.chart j).left_inv hq.2
    simp only [OpenPartialHomeomorph.symm_symm] at he
    change f ((a.chart i).symm q) • α.form i q = _
    rw [α.compatible i j q hq,he]
    ext v
    rfl

lemma smul_supported (f : M → ℝ) (hf) {K : Set M} (hα : α.SupportedIn K) :
    (α.smul f hf).SupportedIn (K∩tsupport f) := by
  intro i q hq hn
  change f ((a.chart i).symm q) • α.form i q=0
  by_cases hk : (a.chart i).symm q∈K
  · rw [image_eq_zero_of_notMem_tsupport (fun hh => hn ⟨hk,hh⟩),zero_smul]
  · rw [hα i q hq hk,smul_zero]

end AtlasForm

end
open scoped ContDiff Topology
open Set Filter Function MeasureTheory
variable {m : ℕ}

lemma extDeriv_eq_zero_off_tsupport
    {w : CoordinateSpace (m+1) → CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ}
    {x : CoordinateSpace (m+1)} (hx : x∉tsupport w) : extDeriv w x=0 := by
  have he : w =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  rw [he.extDeriv_eq]
  simp only [extDeriv, fderiv_zero]
  exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ _ ℝ)

lemma continuous_extDeriv_coefficient
    {w : CoordinateSpace (m+1) → CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ}
    (hw : ContDiff ℝ 1 w) : Continuous (fun x => extDeriv w x coordinateVector) := by
  have hd : Continuous (fderiv ℝ w) := hw.continuous_fderiv (by norm_num)
  exact (ContinuousAlternatingMap.apply ℝ _ ℝ coordinateVector).continuous.comp
    ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ _ ℝ).continuous.comp hd)

theorem compact_euclidean_stokes
    {w : CoordinateSpace (m+1) → CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ}
    (hw : ContDiff ℝ 1 w) (hc : HasCompactSupport w) :
    (∫ x,extDeriv w x coordinateVector)=0 := by
  classical
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  let A : ℝ := max R 0+1
  have hAR : R<A := by dsimp [A]; linarith [le_max_left R 0]
  have hA : 0<A := by dsimp [A]; linarith [le_max_right R 0]
  let a : CoordinateSpace (m+1) := fun _ => -A
  let b : CoordinateSpace (m+1) := fun _ => A
  have hab : a≤b := fun _ => by dsimp [a,b]; linarith
  have hbound (x : CoordinateSpace (m+1)) (hx : x∈tsupport w) (i : Fin (m+1)) :
      |x i|<A := by
    exact (show |x i|≤‖x‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i).trans_lt
      ((hR x hx).trans_lt hAR)
  have hz (x : CoordinateSpace (m+1)) (i : Fin (m+1)) (he : x i=A ∨ x i= -A) : w x=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hx
    have hb := hbound x hx i
    rcases he with he|he
    · rw [he,abs_of_pos hA] at hb; exact (lt_irrefl A) hb
    · rw [he,abs_neg,abs_of_pos hA] at hb; exact (lt_irrefl A) hb
  have hd : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hi : IntegrableOn (fun x => ∑ i,fderiv ℝ (formFlux w i) x (Pi.single i 1)) (Icc a b) := by
    have he : (fun x => ∑ i,fderiv ℝ (formFlux w i) x (Pi.single i 1))=
        fun x => extDeriv w x coordinateVector := funext (formFlux_divergence hd)
    rw [he]
    exact (continuous_extDeriv_coefficient hw).continuousOn.integrableOn_compact isCompact_Icc
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable' a b hab (formFlux w)
    (fun i x => fderiv ℝ (formFlux w i) x) ∅ countable_empty
    (fun i => (formFlux_differentiable hd i).continuous.continuousOn)
    (fun x hx i => (formFlux_differentiable hd i x).hasFDerivAt) hi
  have hface (i : Fin (m+1)) (c : ℝ) (he : c=A ∨ c= -A) :
      (∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),formFlux w i (i.insertNth c y))=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    have h0 := hz (i.insertNth c y) i (by simpa using he)
    rw [formFlux,h0]
    change (-1:ℝ)^i.val • (0:ℝ)=0
    exact smul_zero _
  have hbox : (∫ x in Icc a b,extDeriv w x coordinateVector)=0 := by
    calc
      _=(∫ x in Icc a b,∑ i,fderiv ℝ (formFlux w i) x (Pi.single i 1)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => (formFlux_divergence hd x).symm)
      _=_ := hdiv
      _=0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hface i (b i) (Or.inl rfl),hface i (a i) (Or.inr rfl),sub_self]
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc a b)]
  · exact hbox
  · intro x hx
    have hxs : x∉tsupport w := by
      intro hxs
      apply hx
      exact ⟨fun i => (abs_lt.mp (hbound x hxs i)).1.le,
        fun i => (abs_lt.mp (hbound x hxs i)).2.le⟩
    rw [extDeriv_eq_zero_off_tsupport hxs]
    rfl



end HigherDimensionalBallPacking.Rigidity.Degree
end

end OAI
