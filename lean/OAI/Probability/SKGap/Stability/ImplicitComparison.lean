import Mathlib
import OAI.Probability.SKGap.Localization.ResidualRecipe
import OAI.Probability.SKGap.Localization.PhiResponse

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Matrix SKGap.Stein
variable {n : ℕ}

lemma implicit_scalar_cancellation (m t v : Fin n→ℝ) (b b₀ q : ℝ)
    (hb : (∑i,(m i)^2)=(n:ℝ)*(1-b)) (hq : (∑i,(t i)^2)=(n:ℝ)*q) :
    (∑i,(m i-t i)*(v i+t i))+(n:ℝ)*(b-b₀)=
      (n:ℝ)*(1-b₀-q)+(∑i,(v i-m i)*(m i-t i)) := by
  have HH : (∑i,(m i-t i)*(v i+t i))-(∑i,(v i-m i)*(m i-t i))=
      (∑i,(m i)^2)-(∑i,(t i)^2) := by
    rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl;intro i _;ring
  rw [hb,hq] at HH
  linarith

theorem implicit_comparison (J : Interaction n) (hJ : J.IsSymm)
    (z r h v w y w₀ d₀ : Fin n→ℝ) (j b b₀ q χ c : ℝ)
    (hroot : ∀i,r i-h i-J.mulVec (fun k=>Real.tanh (r k)) i+j*(1-q)*Real.tanh (r i)=0)
    (hb : (∑i,(Real.tanh (z i))^2)=(n:ℝ)*(1-b))
    (hq : (∑i,(Real.tanh (r i))^2)=(n:ℝ)*q)
    (hw : ∀i,w i=w₀ i+phi (z i) (r i) (j*(1-b₀-q))*(y i-j*c*Real.tanh (r i)))
    (hy : ∀i,y i=J.mulVec w i-j*χ*w i-j*c*v i)
    (hc : (n:ℝ)*c=∑i,(d₀ i+phiZ (z i) (r i) (j*(1-b₀-q))*(y i-j*c*Real.tanh (r i)))) :
    (∑i,(z i-h i-J.mulVec (fun k=>Real.tanh (z k)) i+j*b₀*Real.tanh (z i))*w i)-j*(b-b₀)*(n:ℝ)*c=
      (∑i,((z i-r i-j*(1-b₀-q)*Real.tanh (z i))*w₀ i-j*(1-b₀-q)*d₀ i))+
      j*(1-q-χ)*(∑i,(Real.tanh (z i)-Real.tanh (r i))*w i)-
      j*c*(∑i,(v i-Real.tanh (z i))*(Real.tanh (z i)-Real.tanh (r i))) := by
  let m:=fun i=>Real.tanh (z i)
  let t:=fun i=>Real.tanh (r i)
  let p:=m-t
  let a:=j*(1-b₀-q)
  have hfield (i : Fin n) : z i-h i-J.mulVec m i+j*b₀*m i=
      z i-r i-a*m i-J.mulVec p i+j*(1-q)*p i := by
    have hr:=hroot i
    dsimp only [p,m,t,a,Pi.sub_apply]
    rw [Matrix.mulVec_sub]
    simp only [Pi.sub_apply]
    linarith
  have hcoord (i : Fin n) :
      (z i-r i-a*m i)*w i=(z i-r i-a*m i)*w₀ i-a*d₀ i+
        p i*(y i-j*c*t i)+a*(d₀ i+phiZ (z i) (r i) a*(y i-j*c*t i)) := by
    have hh:=phi_stein (z i) (r i) a
    rw [hw i]
    dsimp only [p,m,t,a,Pi.sub_apply] at *
    linear_combination (y i-j*c*Real.tanh (r i))*hh
  have hsym : (∑i,J.mulVec p i*w i)=(∑i,p i*J.mulVec w i) := by
    have hh:=dotProduct_transpose_mulVec J w p
    rw [hJ] at hh
    simpa only [dotProduct,mul_comm] using hh
  have hscalar:=implicit_scalar_cancellation m t v b b₀ q hb hq
  have hc' : (n:ℝ)*c=∑i,(d₀ i+phiZ (z i) (r i) a*(y i-j*c*t i)) := hc
  have hcoords : (∑i,(z i-r i-a*m i)*w i)=
      (∑i,((z i-r i-a*m i)*w₀ i-a*d₀ i))+
      (∑i,p i*(y i-j*c*t i))+a*((n:ℝ)*c) := by
    simp_rw [hcoord]
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,hc']
  have hpy : (∑i,p i*(y i-j*c*t i))=(∑i,p i*J.mulVec w i)-
      j*χ*(∑i,p i*w i)-j*c*(∑i,p i*(v i+t i)) := by
    simp only [hy,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl;intro i _;ring
  have hsum : (∑i,(z i-h i-J.mulVec m i+j*b₀*m i)*w i)=
      (∑i,((z i-r i-a*m i)*w₀ i-a*d₀ i))+a*((n:ℝ)*c)+
      j*(1-q-χ)*(∑i,p i*w i)-j*c*(∑i,p i*(v i+t i)) := by
    calc
      _ = (∑i,(z i-r i-a*m i)*w i)-(∑i,J.mulVec p i*w i)+j*(1-q)*(∑i,p i*w i) := by
        simp only [hfield,sub_mul,add_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]
        congr 1;apply Finset.sum_congr rfl;intros;ring
      _ = _ := by rw [hcoords,hpy,hsym];ring
  change (∑i,(z i-h i-J.mulVec m i+j*b₀*m i)*w i)-j*(b-b₀)*(n:ℝ)*c=_
  rw [hsum]
  dsimp only [a,p,m,t,Pi.sub_apply] at *
  linear_combination -j*c*hscalar

lemma implicit_phi_source (z r : Fin n→ℝ) (a : ℝ) (e : Fin n→ℝ) :
    (∑i,((z i-r i-a*Real.tanh (z i))*(phi (z i) (r i) a*e i)-a*(phiZ (z i) (r i) a*e i)))=
      ∑i,(Real.tanh (z i)-Real.tanh (r i))*e i := by
  apply Finset.sum_congr rfl;intro i _
  linear_combination e i*phi_stein (z i) (r i) a

lemma implicit_phiR_source (z r : Fin n→ℝ) (a : ℝ) :
    (∑i,((z i-r i-a*Real.tanh (z i))*(phiR (z i) (r i) a/Real.sqrt (n:ℝ))-
      a*(phiRZ (z i) (r i) a/Real.sqrt (n:ℝ))))=
      (∑i,(phi (z i) (r i) a-scalarVariance (r i)))/Real.sqrt (n:ℝ) := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl;intro i _
  linear_combination (phiR_stein (z i) (r i) a)/Real.sqrt (n:ℝ)

end SKGapCutoff.Recipe

end
end

end OAI
