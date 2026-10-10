import Mathlib

namespace OAI

section
section
section
noncomputable section
namespace CannonPackingGeometry
open Set Metric

lemma half_cos_pos {a : ℝ} (ha : a∈Ioo (0:ℝ) Real.pi) : 0<Real.cos (a/2) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,ha.1],by linarith [ha.2]⟩

theorem intrinsic_inradius_identity {a b c x y z q : ℝ}
    (ha : a∈Ioo (0:ℝ) Real.pi) (hb : b∈Ioo (0:ℝ) Real.pi)
    (hc : c∈Ioo (0:ℝ) Real.pi) (hsum : a+b+c=Real.pi)
    (hx : 0<x) (hy : 0<y) (hz : 0<z) (_hq : 0<q)
    (hax : Real.tan (a/2)=q/x) (hby : Real.tan (b/2)=q/y)
    (hcz : Real.tan (c/2)=q/z) : q^2*(x+y+z)=x*y*z := by
  have hca := half_cos_pos ha
  have hcb := half_cos_pos hb
  have hcc := half_cos_pos hc
  have hsa : Real.sin (a/2)=q/x*Real.cos (a/2) := by
    rw [Real.tan_eq_sin_div_cos] at hax
    exact (div_eq_iff hca.ne').mp hax
  have hsb : Real.sin (b/2)=q/y*Real.cos (b/2) := by
    rw [Real.tan_eq_sin_div_cos] at hby
    exact (div_eq_iff hcb.ne').mp hby
  have hsc : Real.sin (c/2)=q/z*Real.cos (c/2) := by
    rw [Real.tan_eq_sin_div_cos] at hcz
    exact (div_eq_iff hcc.ne').mp hcz
  have hangle : a/2+b/2+c/2=Real.pi/2 := by linarith
  have hzero : Real.cos (a/2+b/2+c/2)=0 := by rw [hangle,Real.cos_pi_div_two]
  rw [Real.cos_add,Real.cos_add,Real.sin_add,hsa,hsb,hsc] at hzero
  have hprod : Real.cos (a/2)*Real.cos (b/2)*Real.cos (c/2)≠0 := by positivity
  have hid : (1-q/y*(q/z)-q/x*(q/z)-q/x*(q/y))*
      (Real.cos (a/2)*Real.cos (b/2)*Real.cos (c/2))=0 := by nlinarith only [hzero]
  have he := (mul_eq_zero.mp hid).resolve_right hprod
  field_simp [hx.ne',hy.ne',hz.ne'] at he
  nlinarith only [he]

theorem intrinsic_cosine_law {a x y z q : ℝ}
    (ha : a∈Ioo (0:ℝ) Real.pi) (hx : 0<x) (_hy : 0<y) (_hz : 0<z)
    (hax : Real.tan (a/2)=q/x) (hid : q^2*(x+y+z)=x*y*z) :
    2*(x+y)*(x+z)*Real.cos a=(x+y)^2+(x+z)^2-(y+z)^2 := by
  have hca := half_cos_pos ha
  have hsa : Real.sin (a/2)=q/x*Real.cos (a/2) := by
    rw [Real.tan_eq_sin_div_cos] at hax
    exact (div_eq_iff hca.ne').mp hax
  have ht := Real.sin_sq_add_cos_sq (a/2)
  rw [hsa] at ht
  have ht' : (q^2+x^2)*Real.cos (a/2)^2=x^2 := by
    field_simp [hx.ne'] at ht
    nlinarith only [ht]
  have hc : Real.cos a=2*Real.cos (a/2)^2-1 := by
    convert Real.cos_two_mul (a/2) using 1
    congr 1
    ring
  rw [hc]
  have hdiv : (x+y)*(x+z)=(x+y+z)*(q^2+x^2)/x := by
    apply (eq_div_iff hx.ne').mpr
    nlinarith only [hid]
  rw [show 2*(x+y)*(x+z)=2*((x+y)*(x+z)) by ring,hdiv]
  field_simp [hx.ne']
  linear_combination 4*(x+y+z)*ht'-2*hid

def trianglePoint (x z a : ℝ) : ℂ := ⟨(x+z)*Real.cos a,(x+z)*Real.sin a⟩

theorem intrinsic_triangle {a b c x y z q : ℝ}
    (ha : a∈Ioo (0:ℝ) Real.pi) (hb : b∈Ioo (0:ℝ) Real.pi)
    (hc : c∈Ioo (0:ℝ) Real.pi) (hsum : a+b+c=Real.pi)
    (hx : 0<x) (hy : 0<y) (hz : 0<z) (hq : 0<q)
    (hax : Real.tan (a/2)=q/x) (hby : Real.tan (b/2)=q/y)
    (hcz : Real.tan (c/2)=q/z) :
    dist (0:ℂ) (x+y : ℂ)=x+y ∧
    dist (0:ℂ) (trianglePoint x z a)=x+z ∧
    dist (x+y : ℂ) (trianglePoint x z a)=y+z ∧
    0<(trianglePoint x z a).im := by
  have hid := intrinsic_inradius_identity ha hb hc hsum hx hy hz hq hax hby hcz
  have hcos := intrinsic_cosine_law ha hx hy hz hax hid
  have hsincos := Real.sin_sq_add_cos_sq a
  have hnorm : ‖trianglePoint x z a‖^2=(x+z)^2 := by
    rw [Complex.sq_norm]
    simp only [trianglePoint,Complex.normSq_apply]
    nlinarith only [hsincos]
  have hnorm' : ‖(x+y : ℂ)-trianglePoint x z a‖^2=(y+z)^2 := by
    rw [Complex.sq_norm]
    simp only [trianglePoint,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im]
    nlinarith only [hsincos,hcos]
  refine ⟨?_,?_,?_,?_⟩
  · rw [dist_zero_left,←Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (add_pos hx hy)]
  · rw [dist_zero_left]
    nlinarith [norm_nonneg (trianglePoint x z a)]
  · rw [dist_eq_norm]
    nlinarith [norm_nonneg ((x+y : ℂ)-trianglePoint x z a)]
  · exact mul_pos (add_pos hx hz) (Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2)
end CannonPackingGeometry

end
end
section
noncomputable section
namespace CannonPackingGeometry
open Set

def cornerAngle {V A : Type*} (vertex : A × Fin 3 → V) (θ : A × Fin 3 → ℝ)
    (f : A) (v : V) : ℝ := by
  classical
  exact ∑ k : Fin 3, if vertex (f,k)=v then θ (f,k) else 0

lemma cornerAngle_at {V A : Type*} (vertex : A × Fin 3 → V) (θ : A × Fin 3 → ℝ)
    (hinj : ∀ f,Function.Injective (fun k=>vertex (f,k))) (f : A) (k : Fin 3) :
    cornerAngle vertex θ f (vertex (f,k))=θ (f,k) := by
  classical
  unfold cornerAngle
  rw [Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    simp only [ite_eq_right (fun h=>hjk (hinj f h))]
  · simp

lemma cornerAngle_zero {V A : Type*} (vertex : A × Fin 3 → V) (θ : A × Fin 3 → ℝ)
    (f : A) (v : V) (h : ¬∃ k,vertex (f,k)=v) : cornerAngle vertex θ f v=0 := by
  classical
  apply Finset.sum_eq_zero
  intro k hk
  exact ite_eq_right (fun hk=>h ⟨k,hk⟩)

lemma sum_cornerAngle {V A : Type*} [Fintype A] [DecidableEq V] (vertex : A × Fin 3 → V)
    (θ : A × Fin 3 → ℝ) (v : V) :
    (∑ f,cornerAngle vertex θ f v)=∑ i : A × Fin 3,if vertex i=v then θ i else 0 := by
  classical
  simp only [cornerAngle,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : vertex (f,k)=v <;> simp [h]

theorem intrinsic_cosine_law_fin3 (θ r : Fin 3 → ℝ) (q : ℝ)
    (hθ : ∀ k,θ k∈Ioo (0:ℝ) Real.pi) (hs : ∑ k,θ k=Real.pi)
    (hr : ∀ k,0<r k) (hq : 0<q)
    (ht : ∀ k,Real.tan (θ k/2)=q/r k) {i j k : Fin 3}
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    2*(r i+r j)*(r i+r k)*Real.cos (θ i)=
      (r i+r j)^2+(r i+r k)^2-(r j+r k)^2 := by
  have hs' : θ 0+θ 1+θ 2=Real.pi := by simpa only [Fin.sum_univ_three] using hs
  have hid := intrinsic_inradius_identity (hθ 0) (hθ 1) (hθ 2) hs'
    (hr 0) (hr 1) (hr 2) hq (ht 0) (ht 1) (ht 2)
  apply intrinsic_cosine_law (hθ i) (hr i) (hr j) (hr k) (ht i)
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  all_goals nlinarith only [hid]
end CannonPackingGeometry

end
end
end
end

end OAI
