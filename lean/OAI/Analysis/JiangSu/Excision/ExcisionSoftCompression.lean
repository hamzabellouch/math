import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Excision.PureGNSStrongDensity

namespace OAI

noncomputable section


namespace PureStateExcision
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def softScalar (t : ℝ) : ℝ := (1+max 0 t)⁻¹
lemma softScalar_continuous : Continuous softScalar := by
  apply Continuous.inv₀ (by fun_prop)
  intro t
  have : 0 < 1+max 0 t := by have := le_max_left 0 t; linarith
  exact this.ne'
lemma softScalar_nonneg (t : ℝ) : 0 ≤ softScalar t := by unfold softScalar; positivity
lemma softScalar_le_one (t : ℝ) : softScalar t ≤ 1 := by
  unfold softScalar
  exact inv_le_one_of_one_le₀ (by have := le_max_left 0 t; linarith)
lemma softScalar_error {t : ℝ} (ht : 0 ≤ t) : 1-softScalar t ≤ t := by
  unfold softScalar
  rw [max_eq_right ht]
  have hd : 0 < 1+t := by linarith
  apply (mul_le_mul_iff_left₀ hd).mp
  field_simp
  nlinarith [sq_nonneg t]
lemma softScalar_compressed {t : ℝ} (ht : 0 ≤ t) : softScalar t*t*softScalar t ≤ 1 := by
  unfold softScalar
  rw [max_eq_right ht]
  have hd : 0 < 1+t := by linarith
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hd)).mp
  field_simp
  nlinarith [sq_nonneg t]

def softCompression (u : A) : A := cfc softScalar u
lemma softCompression_nonneg (u : A) : 0 ≤ softCompression u :=
  cfc_nonneg fun t _ => softScalar_nonneg t
lemma softCompression_le_one (u : A) : softCompression u ≤ 1 :=
  cfc_le_one _ _ fun t _ => softScalar_le_one t
lemma softCompression_norm_le (u : A) : ‖softCompression u‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (softCompression_nonneg u)).mpr (softCompression_le_one u)
lemma softCompression_error (u : A) (hu : 0 ≤ u) : 1-softCompression u ≤ u := by
  have ha := hu.isSelfAdjoint
  have he : 1-softCompression u=cfc (fun t : ℝ => 1-softScalar t) u := by
    rw [cfc_sub (fun _ : ℝ => 1) softScalar u continuousOn_const softScalar_continuous.continuousOn, cfc_const (1 : ℝ) u, map_one]
    rfl
  calc
    1-softCompression u=cfc (fun t : ℝ => 1-softScalar t) u := he
    _ ≤ cfc (fun t : ℝ => t) u :=
      (cfc_le_iff (fun t : ℝ => 1-softScalar t) (fun t : ℝ => t) u
        (continuous_const.sub softScalar_continuous).continuousOn continuousOn_id ha).mpr
        fun t ht => softScalar_error (spectrum_nonneg_of_nonneg hu ht)
    _=u := cfc_id' ℝ u
lemma softCompression_compressed (u : A) (hu : 0 ≤ u) :
    softCompression u*u*softCompression u ≤ 1 := by
  have ha := hu.isSelfAdjoint
  have he : softCompression u*u*softCompression u=
      cfc (fun t => softScalar t*t*softScalar t) u := by
    rw [cfc_mul (fun t : ℝ => softScalar t*t) softScalar u (softScalar_continuous.mul continuous_id).continuousOn
      softScalar_continuous.continuousOn,cfc_mul softScalar (fun t : ℝ => t) u softScalar_continuous.continuousOn
      continuousOn_id,cfc_id' ℝ u]
    rfl
  rw [he]
  exact cfc_le_one _ _ fun t ht => softScalar_compressed (spectrum_nonneg_of_nonneg hu ht)

lemma norm_mul_softCompression_le (u b : A) (hu : 0 ≤ u) {r : ℝ} (hr : 0 ≤ r)
    (hb : star b*b ≤ r^2 • u) : ‖b*softCompression u‖ ≤ r := by
  let g := softCompression u
  have hg := (softCompression_nonneg u).isSelfAdjoint
  have h : star (b*g)*(b*g) ≤ r^2 • (1 : A) := by
    calc
      star (b*g)*(b*g)=g*(star b*b)*g := by rw [star_mul,hg.star_eq]; noncomm_ring
      _ ≤ g*(r^2 • u)*g := hg.conjugate_le_conjugate hb
      _=r^2 • (g*u*g) := by simp only [mul_smul_comm,smul_mul_assoc]
      _ ≤ r^2 • (1 : A) := smul_le_smul_of_nonneg_left (softCompression_compressed u hu) (sq_nonneg r)
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg h (star_mul_self_nonneg (b*g))
  rw [CStarRing.norm_star_mul_self,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)] at hn
  have h1 : ‖(1 : A)‖ ≤ 1 := by nontriviality A; simp
  have hnr : ‖b*g‖^2 ≤ r^2 := by nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg r)]
  nlinarith [norm_nonneg (b*g)]

omit [PartialOrder A] [StarOrderedRing A] in
lemma realPart_compression (g b : A) (hg : IsSelfAdjoint g) :
    (realPart (g*b*g) : A)=g*(realPart b : A)*g := by
  rw [realPart_apply_coe,realPart_apply_coe]
  simp only [star_mul,hg.star_eq,mul_smul_comm,smul_mul_assoc]
  congr 1
  noncomm_ring

omit [PartialOrder A] [StarOrderedRing A] in
lemma realPart_compression_norm_le (g b : A) (hg : IsSelfAdjoint g) (hgn : ‖g‖ ≤ 1) :
    ‖g*(realPart b : A)*g‖ ≤ ‖b*g‖ := by
  rw [←realPart_compression g b hg]
  calc
    ‖(realPart (g*b*g) : A)‖ ≤ ‖g*b*g‖ := by simpa only [AddSubgroup.norm_coe] using realPart.norm_le (g*b*g)
    _=‖g*(b*g)‖ := by rw [mul_assoc]
    _ ≤ ‖g‖*‖b*g‖ := norm_mul_le _ _
    _ ≤ ‖b*g‖ := by nlinarith [norm_nonneg (b*g)]

end PureStateExcision


namespace PureStateExcision
open scoped ComplexOrder ComplexStarModule InnerProductSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {I : Type*} [Fintype I]

lemma state_left_norm_sq (f : A →ₚ[ℂ] ℂ) (b : A) :
    (f (star b*b)).re=‖f.gnsStarAlgHom b (Pureness.stateGNSVector f)‖^2 := by
  rw [←Pureness.stateGNS_vector_value f (star b*b),map_mul,map_star]
  change (inner ℂ (Pureness.stateGNSVector f)
    (star (f.gnsStarAlgHom b) (f.gnsStarAlgHom b (Pureness.stateGNSVector f)))).re=_
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

omit [StarOrderedRing A] in
lemma state_real_smul (f : A →ₚ[ℂ] ℂ) (t : ℝ) (a : A) :
    (f (t • a)).re=t*(f a).re := by
  rw [←Complex.coe_smul,map_smul]
  simp

lemma state_selfadjoint_real (f : A →ₚ[ℂ] ℂ) (a : A) (ha : IsSelfAdjoint a) :
    ((f a).re : ℂ)=f a := by
  have him := Complex.conj_eq_iff_im.mp (ha.map f).star_eq
  apply Complex.ext
  · rfl
  · simpa using him.symm

 theorem pure_state_finite_selfadjoint_excision (f : A →ₚ[ℂ] ℂ) (hf1 : f 1=1)
    (hpure : ofPositiveState f hf1∈(realStateCarrier (A := A)).extremePoints ℝ)
    (a : I → selfAdjoint A) {ε ρ : ℝ} (hε : 0<ε) (hρ : 0<ρ) :
    ∃ g : A, 0 ≤ g ∧ ‖g‖ ≤ 1 ∧ 1-ρ<(f g).re ∧
      ∀ i, ‖g*(a i : A)*g-f (a i) • (g*g)‖<ε := by
  classical
  let c (i : I) : A := (a i : A)-(f (a i)).re • 1
  have hc (i : I) : IsSelfAdjoint (c i) :=
    (a i).property.sub ((IsSelfAdjoint.all _).smul (IsSelfAdjoint.one A))
  have hfc (i : I) : f (c i)=0 := by
    simp only [c,map_sub,←Complex.coe_smul,map_smul,hf1,smul_eq_mul,mul_one]
    rw [state_selfadjoint_real f (a i) (a i).property,sub_self]
  let r := ε/2
  have hr : 0<r := by dsimp [r]; positivity
  have hr2 : 0<r^2 := sq_pos_of_pos hr
  let n : ℝ := Fintype.card I
  have hn : 0 ≤ n := by dsimp [n]; positivity
  let δ := Real.sqrt (ρ*r^2/(n+1))
  have hδ : 0<δ := Real.sqrt_pos.mpr (by positivity)
  have hδsq : δ^2=ρ*r^2/(n+1) := Real.sq_sqrt (by positivity)
  choose b hb hbn using fun i => pure_state_small_left_error f hf1 hpure (c i) (hc i) (hfc i) hδ
  let u : A := (r^2)⁻¹ • ∑ i,star (b i)*b i
  have hu : 0 ≤ u := smul_nonneg (inv_nonneg.mpr hr2.le)
    (Finset.sum_nonneg fun i _ => star_mul_self_nonneg (b i))
  have hmass : r^2 • u=∑ i,star (b i)*b i := by
    dsimp only [u]
    rw [smul_smul,mul_inv_cancel₀ hr2.ne',one_smul]
  have hbi (i : I) : star (b i)*b i ≤ r^2 • u := by
    rw [hmass]
    exact Finset.single_le_sum (fun j _ => star_mul_self_nonneg (b j)) (Finset.mem_univ i)
  have hfu : (f u).re<ρ := by
    have hs : ∑ i,(f (star (b i)*b i)).re ≤ n*δ^2 := by
      calc
        _ ≤ ∑ i,δ^2 := Finset.sum_le_sum fun i _ => by
          rw [state_left_norm_sq]
          nlinarith [hbn i,norm_nonneg (f.gnsStarAlgHom (b i) (Pureness.stateGNSVector f))]
        _=n*δ^2 := by simp [n]
    have hnum : (r^2)⁻¹*(n*δ^2)<ρ := by
      rw [hδsq]
      have hn1 : 0<n+1 := by linarith
      field_simp
      nlinarith
    calc
      (f u).re=(r^2)⁻¹*(∑ i,(f (star (b i)*b i)).re) := by
        rw [state_real_smul]
        simp only [map_sum,Complex.re_sum]
      _ ≤ (r^2)⁻¹*(n*δ^2) := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hr2.le)
      _<ρ := hnum
  let g := softCompression u
  have hg := softCompression_nonneg u
  have hgn := softCompression_norm_le u
  refine ⟨g,hg,hgn,?_,fun i => ?_⟩
  · have hle : f (1-g) ≤ f u := f.monotone (softCompression_error u hu)
    have hleR := (Complex.le_def.mp hle).1
    simp only [map_sub,Complex.sub_re,hf1,Complex.one_re] at hleR
    linarith
  · have hi : ‖g*c i*g‖ ≤ r := by
      rw [←hb i]
      exact (realPart_compression_norm_le g (b i) hg.isSelfAdjoint hgn).trans
        (norm_mul_softCompression_le u (b i) hu hr.le (hbi i))
    have he : g*(a i : A)*g-f (a i) • (g*g)=g*c i*g := by
      rw [←state_selfadjoint_real f (a i) (a i).property,Complex.coe_smul]
      simp [c,mul_sub,sub_mul]
    rw [he]
    exact hi.trans_lt (by dsimp [r]; linarith)

end PureStateExcision

end

end OAI
