import Mathlib
import OAI.Geometry.Cannon.Conformal.Normalizer

namespace OAI

section
section
section
noncomputable section
noncomputable section
open Set Filter Topology
open scoped OnePoint

noncomputable section
open Set Filter Topology

namespace CannonMobius
open Set Filter Topology CannonH3
open scoped OnePoint

def finiteB (t : Triple) : ℂ := (coordinate (t.val 1)-coordinate (t.val 0))⁻¹
def finiteA (t : Triple) : ℂ := (coordinate (t.val 2)-coordinate (t.val 0))⁻¹-finiteB t
lemma finiteA_ne_zero (t : Triple) (ht : ∀ i, t.val i ≠ ∞) : finiteA t ≠ 0 := by
  let p : Fin 3 → ℂ := fun i => coordinate (t.val i)
  have hp (i : Fin 3) : (p i:Sphere)=t.val i := coe_coordinate (ht i)
  have hinj : Function.Injective p := by
    intro i j h
    apply t.property
    rw [← hp i,← hp j,h]
  let b := (p 1-p 0)⁻¹
  let a := (p 2-p 0)⁻¹-b
  have ha : a ≠ 0 := by
    intro h
    have he : (p 2-p 0)⁻¹=(p 1-p 0)⁻¹ := sub_eq_zero.mp h
    have he' := inv_injective he
    exact (by decide : (2:Fin 3) ≠ 1) (hinj (sub_left_injective he'))
  exact ha

def finiteNormalizer (t : Triple) (ht : ∀ i, t.val i ≠ ∞) : Sphere ≃ₜ Sphere :=
  affine 1 (coordinate (t.val 0)) one_ne_zero*inversion*affine (finiteA t) (finiteB t) (finiteA_ne_zero t ht)
lemma finiteNormalizer_spec (t : Triple) (ht : ∀ i, t.val i ≠ ∞) :
    tripleMap (finiteNormalizer t ht) standard=t := by
  let p : Fin 3 → ℂ := fun i => coordinate (t.val i)
  have hp (i : Fin 3) : (p i:Sphere)=t.val i := coe_coordinate (ht i)
  have hinj : Function.Injective p := by
    intro i j h
    apply t.property
    rw [← hp i,← hp j,h]
  have h10 : p 1-p 0 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (1:Fin 3) ≠ 0) (hinj h))
  have h20 : p 2-p 0 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (2:Fin 3) ≠ 0) (hinj h))
  let b := (p 1-p 0)⁻¹
  let a := (p 2-p 0)⁻¹-b
  have ha : a ≠ 0 := by
    intro h
    have he : (p 2-p 0)⁻¹=(p 1-p 0)⁻¹ := sub_eq_zero.mp h
    have he' := inv_injective he
    exact (by decide : (2:Fin 3) ≠ 1) (hinj (sub_left_injective he'))
  change tripleMap (affine 1 (p 0) one_ne_zero*inversion*affine a b ha) standard=t
  apply Subtype.ext
  funext i
  fin_cases i
  · change affine 1 (p 0) one_ne_zero (inv ∞)=t.val 0
    rw [inv_infty,affine_coe]
    simpa using hp 0
  · change affine 1 (p 0) one_ne_zero (inv (affine a b ha (0:ℂ)))=t.val 1
    rw [affine_coe]
    simp only [mul_zero,zero_add]
    rw [inv_coe (inv_ne_zero h10),affine_coe]
    simpa [b] using hp 1
  · change affine 1 (p 0) one_ne_zero (inv (affine a b ha (1:ℂ)))=t.val 2
    rw [affine_coe]
    have he : a*1+b=(p 2-p 0)⁻¹ := by dsimp [a]; ring
    rw [he,inv_coe (inv_ne_zero h20),affine_coe]
    simpa using hp 2

lemma finiteNormalizer_biholomorphic (t : Triple) (ht : ∀ i, t.val i ≠ ∞) :
    finiteNormalizer t ht ∈ biholomorphic :=
  biholomorphic.mul_mem (biholomorphic.mul_mem (affine_biholomorphic _ _ _) inversion_biholomorphic)
    (affine_biholomorphic _ _ _)

def finiteCenterRaw (t : Triple) : ℂ × ℝ :=
  (coordinate (t.val 0)+star (finiteB t)/((‖finiteB t‖^2+‖finiteA t‖^2:ℝ):ℂ),
    ‖finiteA t‖/(‖finiteB t‖^2+‖finiteA t‖^2))
lemma center_finite (t : Triple) (ht : ∀ i, t.val i ≠ ∞) :
    ((center t).1,(center t).2.val)=finiteCenterRaw t := by
  have h := center_orbit (finiteNormalizer t ht) (finiteNormalizer_biholomorphic t ht)
  rw [finiteNormalizer_spec] at h
  rw [h]
  change ( (CannonH3.interior (⟨affine 1 (coordinate (t.val 0)) one_ne_zero,affine_mem_boundaryGroup _ _ _⟩*
    ⟨inversion,inversion_mem_boundaryGroup⟩*⟨affine (finiteA t) (finiteB t) (finiteA_ne_zero t ht),
    affine_mem_boundaryGroup _ _ _⟩) basepoint).1,
    (CannonH3.interior (⟨affine 1 (coordinate (t.val 0)) one_ne_zero,affine_mem_boundaryGroup _ _ _⟩*
    ⟨inversion,inversion_mem_boundaryGroup⟩*⟨affine (finiteA t) (finiteB t) (finiteA_ne_zero t ht),
    affine_mem_boundaryGroup _ _ _⟩) basepoint).2.val)=_
  rw [interior_mul,interior_mul,interior_affine,interior_inversion,interior_affine]
  simp only [Homeomorph.mul_apply]
  change (1*(star (finiteA t*0+finiteB t)/((‖finiteA t*0+finiteB t‖^2+(‖finiteA t‖*1)^2:ℝ):ℂ))+coordinate (t.val 0),
    ‖(1:ℂ)‖*((‖finiteA t‖*1)/(‖finiteA t*0+finiteB t‖^2+(‖finiteA t‖*1)^2)))=_
  simp [finiteCenterRaw,add_comm]

lemma continuousAt_finiteCenterRaw (t : Triple) (ht : ∀ i, t.val i ≠ ∞) :
    ContinuousAt finiteCenterRaw t := by
  have hc (i : Fin 3) : ContinuousAt (fun s : Triple => coordinate (s.val i)) t :=
    (continuousAt_coordinate (ht i)).comp (f := fun s : Triple => s.val i)
      (show ContinuousAt (fun s : Triple => s.val i) t from
        ((continuous_apply i).comp continuous_subtype_val).continuousAt)
  have h10 : coordinate (t.val 1)-coordinate (t.val 0) ≠ 0 := by
    intro hh
    have he := congrArg (fun z : ℂ => (z:Sphere)) (sub_eq_zero.mp hh)
    rw [coe_coordinate (ht 1),coe_coordinate (ht 0)] at he
    exact (by decide : (1:Fin 3) ≠ 0) (t.property he)
  have h20 : coordinate (t.val 2)-coordinate (t.val 0) ≠ 0 := by
    intro hh
    have he := congrArg (fun z : ℂ => (z:Sphere)) (sub_eq_zero.mp hh)
    rw [coe_coordinate (ht 2),coe_coordinate (ht 0)] at he
    exact (by decide : (2:Fin 3) ≠ 0) (t.property he)
  have hb : ContinuousAt finiteB t := ((hc 1).sub (hc 0)).inv₀ h10
  have ha : ContinuousAt finiteA t := (((hc 2).sub (hc 0)).inv₀ h20).sub hb
  have hq : ContinuousAt (fun s : Triple => ‖finiteB s‖^2+‖finiteA s‖^2) t :=
    (hb.norm.pow 2).add (ha.norm.pow 2)
  have hpos : 0 < ‖finiteB t‖^2+‖finiteA t‖^2 := by
    have hh := norm_pos_iff.mpr (finiteA_ne_zero t ht)
    nlinarith [sq_nonneg ‖finiteB t‖]
  exact ((hc 0).add (hb.star.div (Complex.continuous_ofReal.continuousAt.comp hq)
    (by change (↑(‖finiteB t‖^2+‖finiteA t‖^2):ℂ) ≠ 0; exact_mod_cast hpos.ne'))).prodMk (ha.norm.div hq hpos.ne')

lemma continuousAt_center_finite (t : Triple) (ht : ∀ i, t.val i ≠ ∞) : ContinuousAt center t := by
  have he : ∀ᶠ s : Triple in 𝓝 t, ∀ i, s.val i ≠ ∞ := by
    apply Filter.eventually_all.2
    intro i
    exact (((continuous_apply i).comp continuous_subtype_val).continuousAt).eventually
      (isOpen_compl_singleton.mem_nhds (ht i))
  have hh : ContinuousAt (fun s : Triple => ((center s).1,(center s).2.val)) t := by
    apply (continuousAt_finiteCenterRaw t ht).congr_of_eventuallyEq
    filter_upwards [he] with s hs
    exact center_finite s hs
  exact hh.fst.prodMk (hh.snd.codRestrict (fun s => (center s).2.property))

lemma continuous_center : Continuous center := by
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨p,hp⟩ := exists_pole_avoiding t
  let N : Sphere ≃ₜ Sphere := inversion*affine 1 (-p) one_ne_zero
  have hN : N ∈ biholomorphic := biholomorphic.mul_mem inversion_biholomorphic (affine_biholomorphic _ _ _)
  have hNp : N (p:Sphere)=∞ := by
    change inv (affine 1 (-p) one_ne_zero p)=∞
    rw [affine_coe]
    simp only [one_mul,add_neg_cancel,inv_zero]
  have ht (i : Fin 3) : (tripleMap N t).val i ≠ ∞ := fun he => hp i (N.injective (he.trans hNp.symm))
  have hc := (continuousAt_center_finite (tripleMap N t) ht).comp (continuous_tripleMap N).continuousAt
  let F := CannonH3.interior ⟨N,biholomorphic_mem_boundaryGroup hN⟩
  have he : (fun s : Triple => F.symm (center (tripleMap N s)))=center := by
    funext s
    rw [center_biholomorphic N hN]
    exact F.symm_apply_apply _
  have hh := F.symm.continuous.continuousAt.comp hc
  rwa [show (F.symm ∘ center ∘ tripleMap N) = center from he] at hh
end CannonMobius

namespace CannonMobius
open Set Filter Topology
open scoped OnePoint

def ratio (u v : ℂ) : Sphere := if v=0 then ∞ else (u/v:ℂ)
lemma ratio_of_ne {u v : ℂ} (hv : v ≠ 0) : ratio u v=(u/v:ℂ) := ite_eq_right hv
@[simp] lemma ratio_zero (u : ℂ) : ratio u 0=∞ := ite_eq_left rfl
lemma ratio_scale (u v s : ℂ) (hs : s ≠ 0) : ratio (s*u) (s*v)=ratio u v := by
  by_cases hv : v=0
  · simp [hv]
  · rw [ratio_of_ne (mul_ne_zero hs hv),ratio_of_ne hv,mul_div_mul_left _ _ hs]
lemma inv_ratio (u v : ℂ) (huv : u ≠ 0 ∨ v ≠ 0) : inv (ratio u v)=ratio v u := by
  by_cases hv : v=0
  · subst v
    have hu : u ≠ 0 := huv.resolve_right (not_not.mpr rfl)
    rw [ratio_zero,inv_infty,ratio_of_ne hu,zero_div]
  · by_cases hu : u=0
    · subst u
      rw [ratio_of_ne hv,zero_div,inv_zero,ratio_zero]
    · rw [ratio_of_ne hv,ratio_of_ne hu,inv_coe (div_ne_zero hu hv),inv_div]

lemma continuousAt_ratio {X : Type*} [TopologicalSpace X] {u v : X → ℂ} {x : X}
    (hu : ContinuousAt u x) (hv : ContinuousAt v x) (h : u x ≠ 0 ∨ v x ≠ 0) :
    ContinuousAt (fun y => ratio (u y) (v y)) x := by
  by_cases hvx : v x=0
  · have hux : u x ≠ 0 := h.resolve_right (not_not.mpr hvx)
    have hcont : ContinuousAt (fun y => inv ((v y/u y:ℂ):Sphere)) x :=
      continuous_inv.continuousAt.comp (OnePoint.continuous_coe.continuousAt.comp (hv.div hu hux))
    apply hcont.congr_of_eventuallyEq
    filter_upwards [hu.eventually_ne hux] with y hy
    rw [← ratio_of_ne hy,inv_ratio _ _ (Or.inr hy)]
  · have hcont : ContinuousAt (fun y => ((u y/v y:ℂ):Sphere)) x :=
      OnePoint.continuous_coe.continuousAt.comp (hu.div hv hvx)
    apply hcont.congr_of_eventuallyEq
    filter_upwards [hv.eventually_ne hvx] with y hy
    exact ratio_of_ne hy

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev Nonsingular := {M : Mat // M.det ≠ 0}

def matrixFun (M : Mat) (p : Sphere) : Sphere :=
  p.elim (ratio (M 0 0) (M 1 0))
    (fun z => ratio (M 0 0*z+M 0 1) (M 1 0*z+M 1 1))
@[simp] lemma matrixFun_infty (M : Mat) : matrixFun M ∞=ratio (M 0 0) (M 1 0) := rfl
@[simp] lemma matrixFun_coe (M : Mat) (z : ℂ) :
    matrixFun M z=ratio (M 0 0*z+M 0 1) (M 1 0*z+M 1 1) := rfl

def swapColumns (M : Mat) : Mat := !![M 0 1,M 0 0;M 1 1,M 1 0]
lemma matrixFun_inv (M : Mat) (p : Sphere) : matrixFun M (inv p)=matrixFun (swapColumns M) p := by
  induction p using OnePoint.rec with
  | infty => simp [swapColumns]
  | coe z =>
    by_cases hz : z=0
    · simp [hz,swapColumns]
    · rw [inv_coe hz,matrixFun_coe,matrixFun_coe]
      change ratio (M 0 0*z⁻¹+M 0 1) (M 1 0*z⁻¹+M 1 1)=
        ratio (M 0 1*z+M 0 0) (M 1 1*z+M 1 0)
      rw [← ratio_scale _ _ z hz]
      congr 1 <;> field_simp <;> ring

lemma matrix_nonzero (M : Mat) (hM : M.det ≠ 0) (z : ℂ) :
    M 0 0*z+M 0 1 ≠ 0 ∨ M 1 0*z+M 1 1 ≠ 0 := by
  by_contra hh
  push Not at hh
  apply hM
  rw [Matrix.det_fin_two]
  linear_combination M 0 0*hh.2-M 1 0*hh.1
lemma first_column_nonzero (M : Mat) (hM : M.det ≠ 0) : M 0 0 ≠ 0 ∨ M 1 0 ≠ 0 := by
  by_contra hh
  push Not at hh
  simp [Matrix.det_fin_two,hh.1,hh.2] at hM
lemma swapColumns_det (M : Mat) : (swapColumns M).det= -M.det := by
  simp [Matrix.det_fin_two,swapColumns]

lemma matrixFun_continuous_finite {X : Type*} [TopologicalSpace X]
    {M : X → Mat} {q : X → Sphere} {x : X} (hM : ContinuousAt M x)
    (hq : ContinuousAt q x) (hn : (M x).det ≠ 0) (hf : q x ≠ ∞) :
    ContinuousAt (fun y => matrixFun (M y) (q y)) x := by
  let c : Sphere → ℂ := fun p => p.elim 0 id
  have hc : ContinuousAt c (q x) := by
    induction h : q x using OnePoint.rec with
    | infty => exact (hf h).elim
    | coe z => exact OnePoint.continuousAt_coe.mpr continuousAt_id
  have hcoord : ContinuousAt (fun y => c (q y)) x := hc.comp hq
  have hentries (i j : Fin 2) : ContinuousAt (fun y => M y i j) x :=
    (continuousAt_pi.mp (continuousAt_pi.mp hM i)) j
  have hr := continuousAt_ratio ((hentries 0 0).mul hcoord |>.add (hentries 0 1))
    ((hentries 1 0).mul hcoord |>.add (hentries 1 1)) (matrix_nonzero (M x) hn (c (q x)))
  apply hr.congr_of_eventuallyEq
  filter_upwards [hq.eventually_ne hf] with y hy
  induction h : q y using OnePoint.rec with
  | infty => exact (hy h).elim
  | coe z => simp only [Pi.add_apply,Pi.mul_apply,h]; rfl

lemma matrixFun_continuous {X : Type*} [TopologicalSpace X]
    {M : X → Mat} {q : X → Sphere} {x : X} (hM : ContinuousAt M x)
    (hq : ContinuousAt q x) (hn : (M x).det ≠ 0) :
    ContinuousAt (fun y => matrixFun (M y) (q y)) x := by
  by_cases hf : q x=∞
  · have hs : ContinuousAt (fun y => swapColumns (M y)) x := by
      apply continuousAt_pi.mpr
      intro i
      apply continuousAt_pi.mpr
      intro j
      fin_cases i <;> fin_cases j <;>
        exact (continuousAt_pi.mp (continuousAt_pi.mp hM _)) _
    have hn' : (swapColumns (M x)).det ≠ 0 := by rw [swapColumns_det]; exact neg_ne_zero.mpr hn
    have hf' : inv (q x) ≠ ∞ := by rw [hf,inv_infty]; exact OnePoint.coe_ne_infty _
    have hh := matrixFun_continuous_finite hs (continuous_inv.continuousAt.comp hq) hn' hf'
    have he : (fun y => matrixFun (swapColumns (M y)) (inv (q y)))=
        (fun y => matrixFun (M y) (q y)) := by
      funext y
      rw [← matrixFun_inv,inv_involutive (q y)]
    change ContinuousAt (fun y => matrixFun (swapColumns (M y)) (inv (q y))) x at hh
    rwa [he] at hh
  · exact matrixFun_continuous_finite hM hq hn hf

lemma continuous_matrixFun : Continuous (fun u : Nonsingular × Sphere => matrixFun u.1.val u.2) :=
  continuous_iff_continuousAt.mpr (fun u => matrixFun_continuous
    (continuous_subtype_val.comp continuous_fst).continuousAt continuous_snd.continuousAt u.1.property)
end CannonMobius

namespace CannonMobius
open Set Filter Topology
open scoped OnePoint

lemma matrixFun_eq_smul (g : GL (Fin 2) ℂ) (p : Sphere) : matrixFun g.val p=g • p := by
  induction p using OnePoint.rec with
  | infty => exact (OnePoint.smul_infty_eq_ite g).symm
  | coe z => exact OnePoint.smul_some_eq_ite.symm

def matrixHomeomorph (M : Mat) (hM : M.det ≠ 0) : Sphere ≃ₜ Sphere where
  toEquiv := MulAction.toPerm (Matrix.GeneralLinearGroup.mkOfDetNeZero M hM)
  continuous_toFun := by
    change Continuous (fun p : Sphere => Matrix.GeneralLinearGroup.mkOfDetNeZero M hM • p)
    have he : (fun p : Sphere => Matrix.GeneralLinearGroup.mkOfDetNeZero M hM • p)=matrixFun M :=
      funext (fun p => (matrixFun_eq_smul _ p).symm)
    rw [he]
    exact continuous_iff_continuousAt.mpr (fun p => matrixFun_continuous continuousAt_const continuousAt_id hM)
  continuous_invFun := by
    change Continuous (fun p : Sphere => (Matrix.GeneralLinearGroup.mkOfDetNeZero M hM)⁻¹ • p)
    rw [show (fun p : Sphere => (Matrix.GeneralLinearGroup.mkOfDetNeZero M hM)⁻¹ • p)=
      matrixFun (Matrix.GeneralLinearGroup.mkOfDetNeZero M hM)⁻¹.val from
      funext (fun p => (matrixFun_eq_smul _ p).symm)]
    exact continuous_iff_continuousAt.mpr (fun p => matrixFun_continuous continuousAt_const
      continuousAt_id (Matrix.GeneralLinearGroup.det_ne_zero _))
lemma matrixHomeomorph_apply (M : Mat) (hM : M.det ≠ 0) (p : Sphere) :
    matrixHomeomorph M hM p=matrixFun M p := (matrixFun_eq_smul _ p).symm

lemma matrixFun_triangular {M : Mat} (hM : M.det ≠ 0) (hc : M 1 0=0) :
    ∃ ha : M 0 0/M 1 1 ≠ 0,
      matrixHomeomorph M hM=affine (M 0 0/M 1 1) (M 0 1/M 1 1) ha := by
  have had : M 0 0 ≠ 0 ∧ M 1 1 ≠ 0 := by
    simpa [Matrix.det_fin_two,hc] using hM
  refine ⟨div_ne_zero had.1 had.2,?_⟩
  apply Homeomorph.ext
  intro p
  rw [matrixHomeomorph_apply]
  induction p using OnePoint.rec with
  | infty => simp [hc,affine]
  | coe z =>
    rw [matrixFun_coe,affine_coe]
    simp only [hc,zero_mul,zero_add]
    rw [ratio_of_ne had.2]
    congr 1
    ring

lemma matrixFun_general {M : Mat} (hM : M.det ≠ 0) (hc : M 1 0 ≠ 0) :
    ∃ ha : -(M 1 0)^2/M.det ≠ 0,
      matrixHomeomorph M hM=affine 1 (M 0 0/M 1 0) one_ne_zero*inversion*
        affine (-(M 1 0)^2/M.det) (-(M 1 0*M 1 1)/M.det) ha := by
  have ha : -(M 1 0)^2/M.det ≠ 0 := div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ hc)) hM
  refine ⟨ha,?_⟩
  apply Homeomorph.ext
  intro p
  rw [matrixHomeomorph_apply]
  induction p using OnePoint.rec with
  | infty =>
    change ratio (M 0 0) (M 1 0)=affine 1 (M 0 0/M 1 0) one_ne_zero (inv ∞)
    rw [ratio_of_ne hc,inv_infty,affine_coe]
    simp
  | coe z =>
    change ratio (M 0 0*z+M 0 1) (M 1 0*z+M 1 1)=
      affine 1 (M 0 0/M 1 0) one_ne_zero
        (inv (affine (-(M 1 0)^2/M.det) (-(M 1 0*M 1 1)/M.det) ha z))
    rw [affine_coe]
    have he : -(M 1 0)^2/M.det*z+ -(M 1 0*M 1 1)/M.det=
        (-(M 1 0)/M.det)*(M 1 0*z+M 1 1) := by ring
    rw [he]
    by_cases hd : M 1 0*z+M 1 1=0
    · rw [hd,mul_zero,ratio_zero,inv_zero]
      rfl
    · rw [ratio_of_ne hd,inv_coe (mul_ne_zero (div_ne_zero (neg_ne_zero.mpr hc) hM) hd),affine_coe]
      congr 1
      rw [Matrix.det_fin_two]
      have hd' : z*M 1 0+M 1 1 ≠ 0 := by simpa only [mul_comm z] using hd
      field_simp [hc,hd,hd']
      ring

lemma matrixHomeomorph_biholomorphic (M : Mat) (hM : M.det ≠ 0) :
    matrixHomeomorph M hM ∈ biholomorphic := by
  by_cases hc : M 1 0=0
  · obtain ⟨ha,he⟩ := matrixFun_triangular hM hc
    rw [he]
    exact affine_biholomorphic _ _ _
  · obtain ⟨ha,he⟩ := matrixFun_general hM hc
    rw [he]
    exact biholomorphic.mul_mem (biholomorphic.mul_mem
      (affine_biholomorphic _ _ _) inversion_biholomorphic) (affine_biholomorphic _ _ _)
end CannonMobius

namespace CannonMobius
open Set Filter Topology
open CannonH3
open scoped Matrix.Norms.Elementwise

def rowNorm (M : Mat) : ℝ := ‖M 1 0‖^2+‖M 1 1‖^2
def numerator (M : Mat) : ℂ := M 0 0*star (M 1 0)+M 0 1*star (M 1 1)
def matrixCenterRaw (M : Mat) : ℂ × ℝ := (numerator M/(rowNorm M:ℂ),‖M.det‖/rowNorm M)
def matrixEnergy (M : Mat) : ℝ := ‖M 0 0‖^2+‖M 0 1‖^2+‖M 1 0‖^2+‖M 1 1‖^2

lemma rowNorm_pos (M : Mat) (hM : M.det ≠ 0) : 0 < rowNorm M := by
  have hn : M 1 0 ≠ 0 ∨ M 1 1 ≠ 0 := by
    by_contra h
    push Not at h
    simp [Matrix.det_fin_two,h.1,h.2] at hM
  rcases hn with hn|hn <;> have hh := norm_pos_iff.mpr hn <;>
    unfold rowNorm <;> nlinarith [sq_nonneg ‖M 1 0‖,sq_nonneg ‖M 1 1‖]

def matrixCenter (M : Mat) (hM : M.det ≠ 0) : Half :=
  ⟨(matrixCenterRaw M).1,⟨(matrixCenterRaw M).2,div_pos (norm_pos_iff.mpr hM) (rowNorm_pos M hM)⟩⟩

lemma complex_gram (a b c d : ℂ) :
    (‖a‖^2+‖b‖^2)*(‖c‖^2+‖d‖^2)=‖a*star c+b*star d‖^2+‖a*d-b*c‖^2 := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im]
  ring

lemma matrixEnergy_center (M : Mat) (hM : ‖M.det‖=1) :
    matrixEnergy M=(‖(matrixCenterRaw M).1‖^2+(matrixCenterRaw M).2^2+1)/(matrixCenterRaw M).2 := by
  have hn : M.det ≠ 0 := fun hh => by simp [hh] at hM
  have hr := (rowNorm_pos M hn).ne'
  have he := complex_gram (M 0 0) (M 0 1) (M 1 0) (M 1 1)
  rw [← Matrix.det_fin_two,hM,one_pow] at he
  unfold matrixCenterRaw
  simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (rowNorm_pos M hn),hM]
  unfold numerator rowNorm matrixEnergy at *
  field_simp
  nlinarith

lemma continuous_rowNorm : Continuous rowNorm := by unfold rowNorm; fun_prop
lemma continuous_numerator : Continuous numerator := by unfold numerator; fun_prop
lemma continuousAt_matrixCenterRaw {M : Mat} (hM : M.det ≠ 0) : ContinuousAt matrixCenterRaw M := by
  unfold matrixCenterRaw
  apply ContinuousAt.prodMk
  · exact continuous_numerator.continuousAt.div
      (Complex.continuous_ofReal.comp continuous_rowNorm).continuousAt
      (by exact_mod_cast (rowNorm_pos M hM).ne')
  · exact (continuous_id.matrix_det.norm).continuousAt.div continuous_rowNorm.continuousAt
      (rowNorm_pos M hM).ne'

def halfInclusion : Half → ℂ × ℝ := fun x => (x.1,x.2.val)
lemma continuous_halfInclusion : Continuous halfInclusion :=
  continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

def centerEnergy (x : Half) : ℝ := (‖x.1‖^2+x.2.val^2+1)/x.2.val
lemma continuous_centerEnergy : Continuous centerEnergy := by
  apply Continuous.div _ (continuous_subtype_val.comp continuous_snd) (fun x => x.2.property.ne')
  fun_prop

theorem compact_matrix_parameters (K : Set Half) (hK : IsCompact K) :
    IsCompact ({M : Mat | ‖M.det‖=1} ∩ matrixCenterRaw ⁻¹' (halfInclusion '' K)) := by
  have hS : IsClosed {M : Mat | ‖M.det‖=1} := isClosed_eq continuous_id.matrix_det.norm continuous_const
  have hcont : ContinuousOn matrixCenterRaw {M : Mat | ‖M.det‖=1} := by
    intro M hM
    apply (continuousAt_matrixCenterRaw ?_).continuousWithinAt
    intro hh
    simp [hh] at hM
  apply Metric.isCompact_of_isClosed_isBounded
    (hcont.preimage_isClosed_of_isClosed hS (hK.image continuous_halfInclusion).isClosed)
  obtain ⟨B,hB⟩ := hK.bddAbove_image continuous_centerEnergy.continuousOn
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max B 1,?_⟩
  rintro M ⟨hM,x,hx,he⟩
  have hE : matrixEnergy M ≤ B := by
    rw [matrixEnergy_center M hM,← he]
    exact hB (mem_image_of_mem centerEnergy hx)
  have hsq (i j : Fin 2) : ‖M i j‖^2 ≤ B := by
    unfold matrixEnergy at hE
    fin_cases i <;> fin_cases j
    · change ‖M 0 0‖^2 ≤ B
      nlinarith [sq_nonneg ‖M 0 1‖,sq_nonneg ‖M 1 0‖,sq_nonneg ‖M 1 1‖]
    · change ‖M 0 1‖^2 ≤ B
      nlinarith [sq_nonneg ‖M 0 0‖,sq_nonneg ‖M 1 0‖,sq_nonneg ‖M 1 1‖]
    · change ‖M 1 0‖^2 ≤ B
      nlinarith [sq_nonneg ‖M 0 0‖,sq_nonneg ‖M 0 1‖,sq_nonneg ‖M 1 1‖]
    · change ‖M 1 1‖^2 ≤ B
      nlinarith [sq_nonneg ‖M 0 0‖,sq_nonneg ‖M 0 1‖,sq_nonneg ‖M 1 0‖]
  apply (pi_norm_le_iff_of_nonneg (le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_right B 1))).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_right B 1))).mpr
  intro j
  have hb := hsq i j
  have hb' := le_max_left B 1
  have h1 := le_max_right B 1
  nlinarith [norm_nonneg (M i j)]
end CannonMobius

namespace CannonMobius
open Set Filter Topology CannonH3
open scoped OnePoint Matrix.Norms.Elementwise

def affineMatrix (a b : ℂ) : Mat := !![a,b;0,1]
def generalMatrix (p a b : ℂ) : Mat := !![p*a,p*b+1;a,b]
lemma affineMatrix_det (a b : ℂ) : (affineMatrix a b).det=a := by simp [affineMatrix,Matrix.det_fin_two]
lemma generalMatrix_det (p a b : ℂ) : (generalMatrix p a b).det= -a := by
  simp [generalMatrix,Matrix.det_fin_two]
  ring
lemma affineMatrix_fun (a b : ℂ) (ha : a ≠ 0) : matrixFun (affineMatrix a b)=affine a b ha := by
  funext z
  induction z using OnePoint.rec with
  | infty => simp [matrixFun_infty,affineMatrix,affine]
  | coe z => simp [matrixFun_coe,affineMatrix,ratio,affine_coe]
lemma generalMatrix_fun (p a b : ℂ) (ha : a ≠ 0) :
    matrixFun (generalMatrix p a b)=affine 1 p one_ne_zero*inversion*affine a b ha := by
  funext z
  induction z using OnePoint.rec with
  | infty =>
    change ratio (p*a) a=affine 1 p one_ne_zero (inv ∞)
    rw [ratio_of_ne ha,inv_infty,affine_coe]
    simp [ha]
  | coe z =>
    change ratio ((p*a)*z+(p*b+1)) (a*z+b)=affine 1 p one_ne_zero (inv (affine a b ha (z:ℂ)))
    rw [affine_coe]
    by_cases hh : a*z+b=0
    · rw [hh,ratio_zero,inv_zero]
      rfl
    · rw [ratio_of_ne hh,inv_coe hh,affine_coe]
      congr 1
      field_simp
      ring
lemma affineMatrix_center (a b : ℂ) : matrixCenterRaw (affineMatrix a b)=(b,‖a‖) := by
  simp [matrixCenterRaw,numerator,rowNorm,affineMatrix,Matrix.det_fin_two]
lemma generalMatrix_center (p a b : ℂ) (ha : a ≠ 0) :
    matrixCenterRaw (generalMatrix p a b)=
      (p+star b/((‖b‖^2+‖a‖^2:ℝ):ℂ),‖a‖/(‖b‖^2+‖a‖^2)) := by
  have hq : 0 < ‖a‖^2+‖b‖^2 := by have hh := norm_pos_iff.mpr ha; nlinarith [sq_nonneg ‖b‖]
  have han : a*star a=(‖a‖^2:ℝ) := by
    rw [Complex.star_def,Complex.mul_conj,Complex.sq_norm]
  have hbn : b*star b=(‖b‖^2:ℝ) := by
    rw [Complex.star_def,Complex.mul_conj,Complex.sq_norm]
  have hu : numerator (generalMatrix p a b)=p*((‖a‖^2+‖b‖^2:ℝ):ℂ)+star b := by
    change (p*a)*star a+(p*b+1)*star b=_
    rw [Complex.ofReal_add,← han,← hbn]
    ring
  apply Prod.ext
  · change numerator (generalMatrix p a b)/(rowNorm (generalMatrix p a b):ℂ)=_
    rw [hu]
    change (p*((‖a‖^2+‖b‖^2:ℝ):ℂ)+star b)/((‖a‖^2+‖b‖^2:ℝ):ℂ)=_
    rw [add_comm (‖b‖^2) (‖a‖^2)]
    have hn : ((‖a‖^2+‖b‖^2:ℝ):ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
  · change ‖(generalMatrix p a b).det‖/rowNorm (generalMatrix p a b)=_
    rw [generalMatrix_det,norm_neg]
    simp [rowNorm,generalMatrix,add_comm]

lemma center_normal_form (p a b : ℂ) (ha : a ≠ 0) :
    let f := affine 1 p one_ne_zero*inversion*affine a b ha
    let hf := biholomorphic.mul_mem (biholomorphic.mul_mem (affine_biholomorphic 1 p one_ne_zero)
      inversion_biholomorphic) (affine_biholomorphic a b ha)
    let x := CannonH3.interior ⟨f,biholomorphic_mem_boundaryGroup hf⟩ basepoint
    (x.1,x.2.val)=(p+star b/((‖b‖^2+‖a‖^2:ℝ):ℂ),‖a‖/(‖b‖^2+‖a‖^2)) := by
  change ( (CannonH3.interior (⟨affine 1 p one_ne_zero,affine_mem_boundaryGroup _ _ _⟩*
    ⟨inversion,inversion_mem_boundaryGroup⟩*⟨affine a b ha,affine_mem_boundaryGroup _ _ _⟩) basepoint).1,
    (CannonH3.interior (⟨affine 1 p one_ne_zero,affine_mem_boundaryGroup _ _ _⟩*
    ⟨inversion,inversion_mem_boundaryGroup⟩*⟨affine a b ha,affine_mem_boundaryGroup _ _ _⟩) basepoint).2.val)=_
  rw [interior_mul,interior_mul,interior_affine,interior_inversion,interior_affine]
  simp only [Homeomorph.mul_apply]
  change (1*(star (a*0+b)/((‖a*0+b‖^2+(‖a‖*1)^2:ℝ):ℂ))+p,
    ‖(1:ℂ)‖*((‖a‖*1)/(‖a*0+b‖^2+(‖a‖*1)^2)))=_
  simp [add_comm]

lemma exists_center_matrix (f : Sphere ≃ₜ Sphere) (hf : f ∈ biholomorphic) :
    ∃ M : Mat, M.det ≠ 0 ∧ matrixFun M=f ∧
      matrixCenterRaw M=((CannonH3.interior ⟨f,biholomorphic_mem_boundaryGroup hf⟩ basepoint).1,
        (CannonH3.interior ⟨f,biholomorphic_mem_boundaryGroup hf⟩ basepoint).2.val) := by
  rcases biholomorphic_normal_form f hf with ⟨a,b,ha,rfl⟩|⟨p,a,b,ha,rfl⟩
  · refine ⟨affineMatrix a b,by simpa [affineMatrix_det] using ha,affineMatrix_fun a b ha,?_⟩
    rw [affineMatrix_center,interior_affine]
    simp [CannonH3.affine,complexAffine,heightScale,basepoint]
  · exact ⟨generalMatrix p a b,by simpa [generalMatrix_det] using ha,generalMatrix_fun p a b ha,
      (generalMatrix_center p a b ha).trans (center_normal_form p a b ha).symm⟩
end CannonMobius

namespace CannonMobius
open Set Filter Topology CannonH3
open scoped OnePoint Matrix.Norms.Elementwise

def rescale (r : ℝ) (M : Mat) : Mat := (r:ℂ) • M
lemma rescale_det (r : ℝ) (M : Mat) : (rescale r M).det=(r:ℂ)^2*M.det := by
  simp only [rescale,Matrix.det_fin_two,Matrix.smul_apply,smul_eq_mul]
  ring
lemma rescale_rowNorm (r : ℝ) (M : Mat) : rowNorm (rescale r M)=r^2*rowNorm M := by
  simp only [rowNorm,rescale,Matrix.smul_apply,smul_eq_mul,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  ring
lemma rescale_numerator (r : ℝ) (M : Mat) : numerator (rescale r M)=(r:ℂ)^2*numerator M := by
  simp only [numerator,rescale,Matrix.smul_apply,smul_eq_mul,star_mul,Complex.star_def,Complex.conj_ofReal]
  ring
lemma rescale_matrixFun (r : ℝ) (hr : r ≠ 0) (M : Mat) : matrixFun (rescale r M)=matrixFun M := by
  have hr' : (r:ℂ) ≠ 0 := by exact_mod_cast hr
  funext p
  induction p using OnePoint.rec with
  | infty => exact ratio_scale _ _ _ hr'
  | coe z =>
    change ratio ((r:ℂ)*M 0 0*z+(r:ℂ)*M 0 1) ((r:ℂ)*M 1 0*z+(r:ℂ)*M 1 1)=_
    rw [show (r:ℂ)*M 0 0*z+(r:ℂ)*M 0 1=(r:ℂ)*(M 0 0*z+M 0 1) by ring,
      show (r:ℂ)*M 1 0*z+(r:ℂ)*M 1 1=(r:ℂ)*(M 1 0*z+M 1 1) by ring]
    exact ratio_scale _ _ _ hr'
lemma rescale_center (r : ℝ) (hr : r ≠ 0) (M : Mat) :
    matrixCenterRaw (rescale r M)=matrixCenterRaw M := by
  have hr' : (r:ℂ) ≠ 0 := by exact_mod_cast hr
  apply Prod.ext
  · change numerator (rescale r M)/(rowNorm (rescale r M):ℂ)=_
    rw [rescale_numerator,rescale_rowNorm,Complex.ofReal_mul,Complex.ofReal_pow]
    exact mul_div_mul_left _ _ (pow_ne_zero 2 hr')
  · change ‖(rescale r M).det‖/rowNorm (rescale r M)=_
    rw [rescale_det,rescale_rowNorm,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    exact mul_div_mul_left _ _ (pow_ne_zero 2 hr)
lemma exists_normalized_matrix (M : Mat) (hM : M.det ≠ 0) :
    ∃ N : Mat, ‖N.det‖=1 ∧ matrixFun N=matrixFun M ∧ matrixCenterRaw N=matrixCenterRaw M := by
  have hnp : 0 < ‖M.det‖ := norm_pos_iff.mpr hM
  let r := (Real.sqrt ‖M.det‖)⁻¹
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hnp)
  refine ⟨rescale r M,?_,rescale_matrixFun r hr.ne' M,rescale_center r hr.ne' M⟩
  rw [rescale_det,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  dsimp [r]
  rw [inv_pow,Real.sq_sqrt hnp.le,inv_mul_cancel₀ hnp.ne']

lemma exists_normalized_triple_matrix (t : Triple) :
    ∃ M : Mat, ‖M.det‖=1 ∧ (∀ i, matrixFun M (std i)=t.val i) ∧
      matrixCenterRaw M=((center t).1,(center t).2.val) := by
  obtain ⟨M,hM,hMf,hMc⟩ := exists_center_matrix (normalizer t).val (normalizer t).property
  obtain ⟨N,hN,hNf,hNc⟩ := exists_normalized_matrix M hM
  refine ⟨N,hN,?_,hNc.trans hMc⟩
  intro i
  rw [hNf,hMf]
  exact congrFun (congrArg Subtype.val (normalizer_spec t)) i

lemma compact_center_preimage {K : Set Half} (hK : IsCompact K) : IsCompact (center ⁻¹' K) := by
  let P : Set Mat := {M | ‖M.det‖=1 ∧ ∃ x ∈ K, (x.1,x.2.val)=matrixCenterRaw M}
  have hP : IsCompact P := compact_matrix_parameters K hK
  let _ : CompactSpace P := isCompact_iff_compactSpace.mp hP
  have hd (M : P) : M.val.det ≠ 0 := by
    intro he
    have hh := M.property.1
    rw [he,norm_zero] at hh
    norm_num at hh
  let F : P → Triple := fun M => tripleMap (matrixHomeomorph M.val (hd M)) standard
  have hF : Continuous F := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    have he : (fun M : P => (F M).val i)=(fun M : P => matrixFun M.val (std i)) := by
      funext M
      exact matrixHomeomorph_apply M.val (hd M) _
    change Continuous (fun M : P => (F M).val i)
    rw [he]
    exact continuous_iff_continuousAt.mpr (fun M => matrixFun_continuous continuous_subtype_val.continuousAt
      continuous_const.continuousAt (hd M))
  apply (isCompact_range hF).of_isClosed_subset (hK.isClosed.preimage continuous_center)
  intro t ht
  obtain ⟨M,hM,hMt,hMc⟩ := exists_normalized_triple_matrix t
  have hh : M ∈ P := ⟨hM,center t,ht,hMc.symm⟩
  refine ⟨⟨M,hh⟩,?_⟩
  apply Subtype.ext
  funext i
  exact (matrixHomeomorph_apply M (hd ⟨M,hh⟩) (std i)).trans (hMt i)

lemma proper_center : IsProperMap center :=
  isProperMap_iff_isCompact_preimage.mpr ⟨continuous_center,fun _ => compact_center_preimage⟩
end CannonMobius

end
end
end
end
end
end

end OAI
