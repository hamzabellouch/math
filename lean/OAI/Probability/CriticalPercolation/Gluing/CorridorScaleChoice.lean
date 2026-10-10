import Mathlib

namespace OAI

section
section
noncomputable section
open scoped Classical

namespace CriticalPercolation.Corridor.ScaleChoice

def J : ℝ := 30000
def L : ℕ := 1000000
def contour : ℝ := 1/16
def epsilon : ℝ := contour^4
def delta : ℝ := epsilon/4
def kappa : ℝ := epsilon*delta/(8*(L+1))
def e : ℝ := 1/(200*(L+3))
def eta : ℝ := kappa^2/(32*(Real.log (4/kappa)+1))

lemma J_lower : 26200<J := by norm_num [J]
lemma L_lower : 10*(J+210)<L := by norm_num [J,L]
lemma e_pos : 0<e := by norm_num [e,L]
lemma e_lt : e<1/10 := by norm_num [e,L]
lemma e_small : (L+3)*e<1/100 := by norm_num [e,L]
lemma kappa_pos : 0<kappa := by norm_num [kappa,epsilon,delta,contour,L]
lemma kappa_le : kappa≤1 := by norm_num [kappa,epsilon,delta,contour,L]
lemma log_nonneg : 0≤Real.log (4/kappa) :=
  Real.log_nonneg (by norm_num [kappa,epsilon,delta,contour,L])
lemma eta_pos : 0<eta := by
  unfold eta
  exact div_pos (sq_pos_of_pos kappa_pos) (mul_pos (by norm_num) (by linarith [log_nonneg]))
lemma eta_le : eta≤kappa := by
  unfold eta
  rw [div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ)<32) (by linarith [log_nonneg]))]
  have hk := kappa_pos
  have hkl := kappa_le
  have hlog := mul_nonneg hk.le log_nonneg
  nlinarith
lemma eta_lt : eta<1/10 :=
  eta_le.trans_lt (by norm_num [kappa,epsilon,delta,contour,L])
lemma eta_small : eta≤kappa*(kappa/4)/(4*(Real.log (4/kappa)+1)) := by
  have hp : 0<Real.log (4/kappa)+1 := by linarith [log_nonneg]
  unfold eta
  field_simp
  nlinarith [sq_nonneg kappa]
lemma delta_pos : 0<delta := by norm_num [delta,epsilon,contour]
lemma root_error : 2*(eta+L*kappa)<delta := by
  have he := eta_le
  have hn : 2*(kappa+L*kappa)<delta := by norm_num [delta,kappa,epsilon,contour,L]
  linarith
lemma contour_nonneg : 0≤contour := by norm_num [contour]
lemma contour_small : 8*contour<1 := by norm_num [contour]
lemma test_error : delta+2*((L+1)*kappa)/delta≤contour^4 := by
  norm_num [delta,kappa,epsilon,contour,L]

lemma trial_scales (pc : ℝ) (D M VM m : ℕ) :
    ∃ k R : ℕ,
      M*⌈Real.log (4/kappa)/(pc/2)^(m+1+VM)⌉₊<k ∧ m<R ∧
      4/(kappa*(1-pc)^(D*k))<(R : ℝ)-m := by
  let k := M*⌈Real.log (4/kappa)/(pc/2)^(m+1+VM)⌉₊+1
  obtain ⟨r,hr⟩ := exists_nat_gt (4/(kappa*(1-pc)^(D*k)))
  refine ⟨k,m+r+1,by dsimp [k]; omega,by omega,?_⟩
  push_cast
  linarith

lemma mesh (R m : ℕ) : ∃ rho : ℝ, 0<rho ∧ (R+m+1)*rho<e/10 := by
  have hd : (0 : ℝ)<(R:ℝ)+m+1 := by positivity
  refine ⟨e/(20*((R:ℝ)+m+1)),div_pos e_pos (mul_pos (by norm_num) hd),?_⟩
  have he : ((R:ℝ)+m+1)*(e/(20*((R:ℝ)+m+1)))=e/20 := by field_simp
  rw [he]
  linarith [e_pos]

end CriticalPercolation.Corridor.ScaleChoice
end
end
end

end OAI
