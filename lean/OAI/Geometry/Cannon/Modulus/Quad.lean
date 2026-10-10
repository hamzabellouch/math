import Mathlib

namespace OAI

section
noncomputable section
namespace CannonGeneralizedDisk
open Set Metric
open scoped ComplexConjugate OnePoint

structure Quad where
  A : ℝ
  b : ℂ
  C : ℝ

def Quad.value (q : Quad) (z : ℂ) : ℝ :=
  q.A*Complex.normSq z-2*(conj q.b*z).re+q.C

def Quad.discr (q : Quad) : ℝ := Complex.normSq q.b-q.A*q.C

def Quad.region (q : Quad) : Set (OnePoint ℂ) :=
  {p | p.elim (q.A<0) (fun z=>q.value z<0)}

@[simp] lemma Quad.mem_region_coe (q : Quad) (z : ℂ) :
    (z : OnePoint ℂ)∈q.region ↔ q.value z<0 := Iff.rfl
@[simp] lemma Quad.mem_region_infty (q : Quad) :
    ∞∈q.region ↔ q.A<0 := Iff.rfl

lemma Quad.value_inner (q : Quad) (z : ℂ) :
    q.value z=q.A*‖z‖^2-2*inner ℝ q.b z+q.C := by
  simp only [value,Complex.normSq_eq_norm_sq,Complex.inner,mul_comm (conj q.b) z]

def Quad.affine (q : Quad) (a b : ℂ) : Quad :=
  ⟨q.A,(q.A:ℂ)*b+a*q.b,
    q.A*Complex.normSq b+2*(conj (a*q.b)*b).re+q.C*Complex.normSq a⟩

def Quad.inv (q : Quad) : Quad := ⟨q.C,conj q.b,q.A⟩

lemma Quad.affine_value (q : Quad) (a b z : ℂ) :
    (q.affine a b).value (a*z+b)=Complex.normSq a*q.value z := by
  simp only [value,affine,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.ofReal_re,Complex.ofReal_im]
  ring

lemma Quad.affine_discr (q : Quad) (a b : ℂ) :
    (q.affine a b).discr=Complex.normSq a*q.discr := by
  simp only [discr,affine,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.ofReal_re,Complex.ofReal_im]
  ring

lemma Quad.inv_discr (q : Quad) : q.inv.discr=q.discr := by
  simp only [discr,inv,Complex.normSq_conj]
  ring

lemma Quad.inv_value (q : Quad) {z : ℂ} (hz : z≠0) :
    q.inv.value z⁻¹=q.value z/Complex.normSq z := by
  have hnorm : Complex.normSq z≠0:=(Complex.normSq_pos.mpr hz).ne'
  change q.C*Complex.normSq z⁻¹-2*(conj (conj q.b)*z⁻¹).re+q.A = _
  rw [Complex.normSq_inv]
  simp only [value,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    Complex.inv_re,Complex.inv_im]
  field_simp
  ring

lemma Quad.affine_mem_iff (q : Quad) (a b : ℂ) (ha : a≠0) (z : ℂ) :
    (q.affine a b).value (a*z+b)<0 ↔ q.value z<0 := by
  rw [affine_value]
  simpa only [mul_zero] using
    (mul_lt_mul_iff_right₀ (Complex.normSq_pos.mpr ha) :
      Complex.normSq a*q.value z<Complex.normSq a*0 ↔ q.value z<0)

lemma Quad.inv_mem_iff (q : Quad) {z : ℂ} (hz : z≠0) :
    q.inv.value z⁻¹<0 ↔ q.value z<0 := by
  rw [inv_value q hz,div_lt_iff₀ (Complex.normSq_pos.mpr hz),zero_mul]

def disk (a : ℂ) (r : ℝ) : Quad := ⟨1,a,Complex.normSq a-r^2⟩

lemma disk_value (a z : ℂ) (r : ℝ) :
    (disk a r).value z=dist z a^2-r^2 := by
  rw [Quad.value_inner,dist_eq_norm,norm_sub_sq_real]
  simp only [disk,one_mul,Complex.normSq_eq_norm_sq]
  rw [real_inner_comm a z]
  ring

lemma disk_discr (a : ℂ) (r : ℝ) : (disk a r).discr=r^2 := by
  simp [disk,Quad.discr]

lemma disk_region (a : ℂ) {r : ℝ} (hr : 0<r) :
    (disk a r).region=((↑) '' ball a r : Set (OnePoint ℂ)) := by
  ext p
  induction p using OnePoint.rec with
  | infty => simp [disk,Quad.region]
  | coe z =>
    rw [Quad.mem_region_coe,disk_value]
    constructor
    · intro h
      exact ⟨z,by rw [mem_ball]; nlinarith [dist_nonneg (x:=z) (y:=a)],rfl⟩
    · rintro ⟨w,hw,hwz⟩
      have he : w=z:=OnePoint.coe_injective hwz
      subst w
      rw [mem_ball] at hw
      nlinarith [dist_nonneg (x:=z) (y:=a)]

end CannonGeneralizedDisk

end
end

end OAI
