import Mathlib
import OAI.Analysis.Conductivity.Flux.PhysicalTensorPatch
import OAI.Analysis.Conductivity.Geometry.RegularPatchTranslation
import OAI.Analysis.Conductivity.Flux.LinearFluxWeakTransport

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma matrix_congruence_energy (N A : Mat3) (v : Coord3) :
    v ⬝ᵥ ((N*A*Nᵀ)*ᵥv)=(Nᵀ*ᵥv) ⬝ᵥ (A*ᵥ(Nᵀ*ᵥv)) := by
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
  calc
    _ = (A*ᵥ(Nᵀ*ᵥv)) ⬝ᵥ (Nᵀ*ᵥv) := by
      simpa only [Matrix.transpose_transpose] using
        Matrix.dotProduct_transpose_mulVec Nᵀ v (A*ᵥ(Nᵀ*ᵥv))
    _ = _ := dotProduct_comm _ _

lemma linearTensorPullback_elliptic (P : Coord3 ≃L[ℝ] Coord3)
    {A : Coord3 → Mat3} {c C : ℝ} (hc : 0<c) (hcC : c≤C)
    (hA : ∀ x w,c*(w ⬝ᵥ w)≤w ⬝ᵥ(A x*ᵥw) ∧ w ⬝ᵥ(A x*ᵥw)≤C*(w ⬝ᵥ w)) :
    ∃ l L : ℝ,0<l ∧ l<L ∧ ∀ x (v : Coord3),
      l*(v ⬝ᵥ v)≤v ⬝ᵥ(linearTensorPullback P A x*ᵥv) ∧
        v ⬝ᵥ(linearTensorPullback P A x*ᵥv)≤L*(v ⬝ᵥ v) := by
  let N := operatorMatrix (P.symm : Coord3 →L[ℝ] Coord3)
  have hn (v : Coord3) (hv : v≠0) : Nᵀ*ᵥv≠0 := by
    intro hz
    have he : (operatorMatrix (P : Coord3 →L[ℝ] Coord3))ᵀ*(Nᵀ)=1 := by
      rw [←Matrix.transpose_mul,operatorMatrix_equiv_symm_mul,Matrix.transpose_one]
    have hh := congrArg (fun w => (operatorMatrix (P : Coord3 →L[ℝ] Coord3))ᵀ*ᵥw) hz
    rw [Matrix.mulVec_mulVec,he,Matrix.one_mulVec,Matrix.mulVec_zero] at hh
    exact hv hh
  have he (v : Coord3) : v ⬝ᵥ ((N*Nᵀ)*ᵥv)=(Nᵀ*ᵥv) ⬝ᵥ (Nᵀ*ᵥv) := by
    simpa only [Matrix.mul_one,Matrix.one_mulVec] using matrix_congruence_energy N 1 v
  obtain ⟨l,L,hl,hlL,hbound⟩ := compact_matrix_energy_bounds isCompact_singleton
    (fun _ : Unit => N*Nᵀ) continuousOn_const (fun _ _ v hv => by
      rw [he]
      exact lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_self_nonneg _))
        (Ne.symm (mt dotProduct_self_eq_zero.mp (hn v hv))))
  obtain ⟨d,D,hd,hdD,hid⟩ := identity_matrix_energy_bounds
  have hD : 0<D := hd.trans hdD
  have hL : 0<L := hl.trans hlL
  refine ⟨c*l/D,C*L/d,div_pos (mul_pos hc hl) hD,?_,?_⟩
  · have heq : (c*l/D)*D=c*l := div_mul_cancel₀ _ hD.ne'
    have heq' : (C*L/d)*d=C*L := div_mul_cancel₀ _ hd.ne'
    have hcl : c*l<C*L := (mul_lt_mul_of_pos_left hlL hc).trans_le
      (mul_le_mul_of_nonneg_right hcC hL.le)
    have hup : 0<C*L/d := div_pos (mul_pos (hc.trans_le hcC) hL) hd
    nlinarith [mul_lt_mul_of_pos_left hdD hup]
  · intro x v
    have h := hbound () (mem_singleton ()) v
    rw [he] at h
    have hi := hid v
    simp only [Matrix.one_mulVec] at hi
    have hg := hA (P x) (Nᵀ*ᵥv)
    change _ ≤ v ⬝ᵥ ((N*A (P x)*Nᵀ)*ᵥv) ∧ v ⬝ᵥ ((N*A (P x)*Nᵀ)*ᵥv) ≤ _
    simp only [matrix_congruence_energy]
    constructor
    · have h1 := mul_le_mul_of_nonneg_left hi.2 (div_nonneg (mul_nonneg hc.le hl.le) hD.le)
      have h2 := mul_le_mul_of_nonneg_left h.1 hc.le
      have heq : (c*l/D)*D=c*l := div_mul_cancel₀ _ hD.ne'
      nlinarith
    · have h1 := mul_le_mul_of_nonneg_left hi.1 (div_nonneg
          (mul_nonneg (hc.le.trans hcC) hL.le) hd.le)
      have h2 := mul_le_mul_of_nonneg_left h.2 (hc.le.trans hcC)
      have heq : (C*L/d)*d=C*L := div_mul_cancel₀ _ hd.ne'
      nlinarith

lemma RegularPatch.tensor_smul {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {O : Set Coord3} (h : RegularPatch u A O) (r : ℝ) :
    RegularPatch u (fun x => ⟨r • (A x).val,by
      change (r • (A x).val)ᵀ=r • (A x).val
      rw [Matrix.transpose_smul]
      exact congrArg (r • ·) (show (A x).valᵀ=(A x).val from (A x).property)⟩) O := by
  refine ⟨h.1,h.2.1,?_,h.2.2.2⟩
  change ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun x => r • (A x).val) O
  exact (contDiffOn_const : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun _ : Coord3 => r) O).smul h.2.2.1

lemma mem_regularRegion_tensor_smul {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {U : Set Coord3} {x : Coord3} (h : x∈regularRegion u A U) (r : ℝ) :
    x∈regularRegion u (fun y => ⟨r • (A y).val,by
      change (r • (A y).val)ᵀ=r • (A y).val
      rw [Matrix.transpose_smul]
      exact congrArg (r • ·) (show (A y).valᵀ=(A y).val from (A y).property)⟩) U := by
  obtain ⟨O,hOU,hO,hx⟩ := mem_regularRegion_iff.mp h
  exact mem_regularRegion_iff.mpr ⟨O,hOU,hO.tensor_smul r,hx⟩

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma flux_translate_weak {F : Coord3 → Coord3} {U : Set Coord3} (c : Coord3)
    (hF : ∀ ψ : SmoothScalar Coord3,HasCompactSupport ψ.val → tsupport ψ.val⊆U →
      (∫ x,fderiv ℝ ψ.val x (F x))=0)
    (ψ : SmoothScalar Coord3) (hc : HasCompactSupport ψ.val)
    (hs : tsupport ψ.val⊆(fun x => x-c) ⁻¹' U) :
    (∫ x,fderiv ℝ ψ.val x (F (x-c)))=0 := by
  let φ : SmoothScalar Coord3 := ⟨fun y => ψ.val (y+c),
    (smoothScalar_contDiff ψ).comp (contDiff_id.add contDiff_const)⟩
  have hφc : HasCompactSupport φ.val := hc.comp_homeomorph (Homeomorph.addRight c)
  have hφs : tsupport φ.val⊆U := by
    intro y hy
    have hh : y+c∈tsupport ψ.val := tsupport_comp_subset_preimage ψ.val
      (continuous_id.add continuous_const) hy
    simpa only [mem_preimage,add_sub_cancel_right] using hs hh
  calc
    _ = ∫ y,fderiv ℝ ψ.val (y+c) (F y) := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self (fun x => fderiv ℝ ψ.val x (F (x-c))) c).symm
    _ = ∫ y,fderiv ℝ φ.val y (F y) := by simp only [φ,fderiv_comp_add_right]
    _ = 0 := hF φ hφc hφs

lemma translatedTensor_C1_representative {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Mat3}
    {G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ} (c : Coord3) (d : Fin 2 → ℝ)
    (hG : ∀ᵐ x : Coord3,A x*gradientColumns (fderiv ℝ u x)=G x) :
    ∀ᵐ x : Coord3,A (x-c)*gradientColumns
      (fderiv ℝ (fun y => u (y-c)+d) x)=G (x-c) := by
  filter_upwards [(measurePreserving_sub_right volume c).quasiMeasurePreserving.ae hG] with x hx
  simpa only [fderiv_add_const,fderiv_comp_sub] using hx

lemma scalar_flux_weak {F : Coord3 → Coord3} {U : Set Coord3} (r : ℝ)
    (hF : ∀ ψ : SmoothScalar Coord3,HasCompactSupport ψ.val → tsupport ψ.val⊆U →
      (∫ x,fderiv ℝ ψ.val x (F x))=0)
    (ψ : SmoothScalar Coord3) (hc : HasCompactSupport ψ.val) (hs : tsupport ψ.val⊆U) :
    (∫ x,fderiv ℝ ψ.val x (r • F x))=0 := by
  simp only [map_smul,smul_eq_mul,integral_const_mul,hF ψ hc hs,mul_zero]

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

local instance : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

structure WeakFiniteTensorPair (U : Set Coord3) where
  v : Coord3 → Fin 2 → ℝ
  E : Coord3 → Mat3
  symm : ∀ x,(E x).IsSymm
  smooth : ContDiff ℝ 2 v
  measurable : Measurable E
  elliptic : ∃ c C : ℝ,0<c ∧ c≤C ∧ ∀ x w,
    c*(w ⬝ᵥ w)≤w ⬝ᵥ(E x*ᵥw) ∧ w ⬝ᵥ(E x*ᵥw)≤C*(w ⬝ᵥ w)
  regular : ∀ᵐ x : Coord3,x∈U → x∈regularRegion v (fun y => ⟨E y,symm y⟩) U
  G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ
  flux_C1 : ContDiff ℝ 1 G
  constitution : ∀ᵐ x : Coord3,E x*gradientColumns (fderiv ℝ v x)=G x
  weak : ∀ (j : Fin 2) (ψ : SmoothScalar Coord3),HasCompactSupport ψ.val →
    tsupport ψ.val⊆U → (∫ x,fderiv ℝ ψ.val x ((G x).col j))=0

namespace WeakFiniteTensorPair

lemma linear_smooth {U : Set Coord3} (d : WeakFiniteTensorPair U)
    (P : Coord3 ≃L[ℝ] Coord3) (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) :
    ContDiff ℝ 2 (fun x => Q (d.v (P x))) := Q.contDiff.comp (d.smooth.comp P.contDiff)

lemma linear_elliptic {U : Set Coord3} (d : WeakFiniteTensorPair U)
    (P : Coord3 ≃L[ℝ] Coord3) :
    ∃ l L : ℝ,0<l ∧ l≤L ∧ ∀ x w,
      l*(w ⬝ᵥ w)≤w ⬝ᵥ(linearTensorPullback P d.E x*ᵥw) ∧
        w ⬝ᵥ(linearTensorPullback P d.E x*ᵥw)≤L*(w ⬝ᵥ w) := by
  obtain ⟨c,C,hc,hcC,hb⟩ := d.elliptic
  obtain ⟨l,L,hl,hlL,hbound⟩ := linearTensorPullback_elliptic P hc hcC hb
  exact ⟨l,L,hl,hlL.le,hbound⟩

lemma linear_regular {U : Set Coord3} (d : WeakFiniteTensorPair U)
    (P : Coord3 ≃L[ℝ] Coord3) (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) :
    ∀ᵐ x : Coord3,x∈P ⁻¹' U → x∈regularRegion (fun y => Q (d.v (P y)))
      (fun y => ⟨linearTensorPullback P d.E y,linearTensorPullback_symmetric P d.symm y⟩)
      (P ⁻¹' U) := by
  filter_upwards [(continuousLinearEquiv_quasiMeasurePreserving P).ae d.regular] with x hx
  intro hxU
  exact mem_regularRegion_linearCoordinates (u := d.v)
    (A := fun y => ⟨d.E y,d.symm y⟩) (U := U) P Q (x := x) (hx hxU)

def linear {U : Set Coord3} (d : WeakFiniteTensorPair U)
    (P : Coord3 ≃L[ℝ] Coord3) (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) :
    WeakFiniteTensorPair (P ⁻¹' U) where
  v x := Q (d.v (P x))
  E := linearTensorPullback P d.E
  symm := linearTensorPullback_symmetric P d.symm
  smooth := d.linear_smooth P Q
  measurable := linearTensorPullback_measurable P d.measurable
  elliptic := d.linear_elliptic P
  regular := d.linear_regular P Q
  G := linearColumnsPullback P Q d.G
  flux_C1 := linearColumnsPullback_C1 P Q d.flux_C1
  constitution := linearTensorPullback_C1_representative P Q
    (d.smooth.differentiable (by norm_num)) d.constitution
  weak j ψ hc hs := (linearColumnsPullback_weak P Q d.flux_C1.continuous d.weak j ψ hc hs).2

def translate {U : Set Coord3} (d : WeakFiniteTensorPair U) (c : Coord3) (b : Fin 2 → ℝ) :
    WeakFiniteTensorPair ((fun x => x-c) ⁻¹' U) where
  v x := d.v (x-c)+b
  E x := d.E (x-c)
  symm x := d.symm (x-c)
  smooth := (d.smooth.comp (contDiff_id.sub contDiff_const)).add contDiff_const
  measurable := d.measurable.comp (measurable_id.sub measurable_const)
  elliptic := by
    obtain ⟨l,L,hl,hlL,hb⟩ := d.elliptic
    exact ⟨l,L,hl,hlL,fun x => hb (x-c)⟩
  regular := by
    filter_upwards [(measurePreserving_sub_right volume c).quasiMeasurePreserving.ae d.regular] with x hx
    exact fun hxU => mem_regularRegion_translate (hx hxU) b
  G x := d.G (x-c)
  flux_C1 := d.flux_C1.comp (contDiff_id.sub contDiff_const)
  constitution := translatedTensor_C1_representative c b d.constitution
  weak j := flux_translate_weak c (d.weak j)

def scaleTensor {U : Set Coord3} (d : WeakFiniteTensorPair U) (r : ℝ) (hr : 0<r) :
    WeakFiniteTensorPair U where
  v := d.v
  E x := r • d.E x
  symm x := by
    change (r • d.E x)ᵀ=r • d.E x
    rw [Matrix.transpose_smul,(d.symm x).eq]
  smooth := d.smooth
  measurable := (measurable_const : Measurable (fun _ : Coord3 => r)).smul d.measurable
  elliptic := by
    obtain ⟨l,L,hl,hlL,hb⟩ := d.elliptic
    refine ⟨r*l,r*L,mul_pos hr hl,mul_le_mul_of_nonneg_left hlL hr.le,?_⟩
    intro x w
    simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
    constructor
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb x w).1 hr.le
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb x w).2 hr.le
  regular := by
    filter_upwards [d.regular] with x hx
    exact fun hxU => mem_regularRegion_tensor_smul (hx hxU) r
  G x := r • d.G x
  flux_C1 := (contDiff_const : ContDiff ℝ 1 (fun _ : Coord3 => r)).smul d.flux_C1
  constitution := by
    filter_upwards [d.constitution] with x hx
    rw [Matrix.smul_mul,hx]
  weak j ψ hc hs := by
    change (∫ x,fderiv ℝ ψ.val x (r • (d.G x).col j))=0
    exact scalar_flux_weak r (d.weak j) ψ hc hs

lemma integrable {U : Set Coord3} (d : WeakFiniteTensorPair U) (j : Fin 2)
    (ψ : SmoothScalar Coord3) (hc : HasCompactSupport ψ.val) :
    Integrable (fun x => fderiv ℝ ψ.val x ((d.G x).col j)) :=
  continuous_flux_compact_test_integrable
    (continuous_pi fun i => (continuous_apply j).comp ((continuous_apply i).comp d.flux_C1.continuous)) ψ hc

end WeakFiniteTensorPair
end ScalarConductivity

end

end OAI
