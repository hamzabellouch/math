import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI

noncomputable section
namespace FourEdgeSurgery
variable {G : Type*} [Group G]

@[simp] lemma Flow.map_zero (p : Flow G) : p 0=1 := p.zero

@[simp] lemma Flow.map_neg (p : Flow G) (r : ℝ) : p (-r)=(p r)⁻¹ := by
  have h : p r*p (-r)=1 := by rw [←p.map_add,add_neg_cancel,p.map_zero]
  exact eq_inv_of_mul_eq_one_right h
lemma Flow.commute (p : Flow G) (r s : ℝ) : Commute (p r) (p s) := by
  change p r*p s=p s*p r
  rw [←p.map_add,←p.map_add,add_comm]

variable (p q : Flow G)

def correction (p : Flow G) (v : G) (a τ : ℝ) : G :=
  p τ*v*p (-a*τ)*v⁻¹

def surgery (v₀ v₁ v : G) (a b c d : ℝ) : G :=
  correction p v₁ b d*correction q v₀ a c*v*p 1*q 1*p b*q a

@[simp] lemma correction_zero (v : G) (a : ℝ) : correction p v a 0=1 := by
  simp [correction]
@[simp] lemma correction_scalar_zero (v : G) (τ : ℝ) : correction p v 0 τ=p τ := by
  simp [correction,mul_assoc]
@[simp] lemma correction_one (τ : ℝ) : correction p 1 1 τ=1 := by
  simp [correction]

variable (hp : p 1*p 1=1) (hq : q 1*q 1=1)
variable (hc : ∀ r s,Commute (p r) (q s))

include hq in
lemma surgery_left_zero (v₁ v : G) (c d : ℝ) :
    surgery p q 1 v₁ v 1 0 c d=p d*v*p 1 := by
  simp only [surgery,correction_scalar_zero,correction_one,mul_one,p.map_zero]
  rw [mul_assoc (p d*v*p 1) (q 1) (q 1),hq,mul_one]

include hp hc in
lemma surgery_left_one (v₀ v : G) (c d : ℝ) :
    surgery p q v₀ 1 v 0 1 c d=q c*v*q 1 := by
  simp only [surgery,correction_scalar_zero,correction_one,one_mul,q.map_zero,mul_one]
  rw [mul_assoc (q c*v), (hc 1 1).eq]
  simp only [mul_assoc,hp,mul_one]

include hc in
lemma surgery_right_zero (v₀ v₁ : G) (a b : ℝ) :
    surgery p q v₀ v₁ v₀ a b 1 0=(q 1*v₀*q 1)*p 1*p b := by
  simp only [surgery]
  rw [correction_zero]
  simp only [one_mul,correction,mul_one,q.map_neg]
  have hK : Commute (q a) (p 1*q 1*p b) :=
    (((hc 1 a).symm).mul_right (q.commute a 1)).mul_right (hc b a).symm
  have hcan : (q a)⁻¹*(p 1*q 1*p b)*q a=p 1*q 1*p b := hK.inv_mul_cancel
  calc
    _ = (q 1*v₀)*((q a)⁻¹*(p 1*q 1*p b)*q a) := by group
    _ = (q 1*v₀)*(p 1*q 1*p b) := by rw [hcan]
    _ = (q 1*v₀*q 1)*p 1*p b := by rw [(hc 1 1).eq]; group

include hc in
lemma surgery_right_one (v₀ v₁ : G) (a b : ℝ) :
    surgery p q v₀ v₁ v₁ a b 0 1=(p 1*v₁*p 1)*q 1*q a := by
  simp only [surgery]
  rw [correction_zero]
  simp only [mul_one,correction,p.map_neg]
  have hK : Commute (p b) (p 1*q 1) :=
    (p.commute b 1).mul_right (hc b 1)
  have hcan : (p b)⁻¹*(p 1*q 1)*p b=p 1*q 1 := hK.inv_mul_cancel
  calc
    _ = (p 1*v₁)*((p b)⁻¹*(p 1*q 1)*p b)*q a := by group
    _ = (p 1*v₁)*(p 1*q 1)*q a := by rw [hcan]
    _ = (p 1*v₁*p 1)*q 1*q a := by group

include hc in

lemma surgery_trivial (a b c d : ℝ) :
    surgery p q 1 1 1 a b c d=
      p (1+b+d*(1-b))*q (1+a+c*(1-a)) := by
  simp only [surgery,correction,inv_one,mul_one]
  rw [←p.map_add,←q.map_add]
  have h₁ := (hc 1 (c + -a*c)).symm.eq
  have h₂ := (hc b (c + -a*c+1)).symm.eq
  rw [mul_assoc (p (d + -b*d)),h₁,←mul_assoc,←p.map_add]
  rw [mul_assoc (p (d + -b*d+1)),←q.map_add]
  rw [mul_assoc (p (d + -b*d+1)),h₂,←mul_assoc,←p.map_add,mul_assoc,←q.map_add]
  congr 2 <;> ring

end FourEdgeSurgery

end

namespace FourEdgeSurgery
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
lemma correction_continuous (p : Flow G) (hp : Continuous p) :
    Continuous (fun z : G×ℝ×ℝ => correction p z.1 z.2.1 z.2.2) := by
  unfold correction
  exact (((hp.comp continuous_snd.snd).mul continuous_fst).mul
    (hp.comp (continuous_snd.fst.neg.mul continuous_snd.snd))).mul continuous_fst.inv
lemma surgery_continuous {X : Type*} [TopologicalSpace X]
    (p q : Flow G) (hp : Continuous p) (hq : Continuous q)
    (v₀ v₁ v : X → G) (a b c d : X → ℝ)
    (h₀ : Continuous v₀) (h₁ : Continuous v₁) (hv : Continuous v)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d) :
    Continuous (fun x => surgery p q (v₀ x) (v₁ x) (v x) (a x) (b x) (c x) (d x)) := by
  unfold surgery
  have hC := (correction_continuous q hq).comp (h₀.prodMk (ha.prodMk hc))
  have hD := (correction_continuous p hp).comp (h₁.prodMk (hb.prodMk hd))
  exact ((((((hD.mul hC).mul hv).mul continuous_const).mul continuous_const).mul
    (hp.comp hb)).mul (hq.comp ha))
end FourEdgeSurgery

end OAI
