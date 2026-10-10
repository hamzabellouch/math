import Mathlib
import OAI.Probability.SKGap.Entropy.WeightedMean

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

def squareMass (P : Observables n) (f : Observables n) (x : Spin n) : ℝ :=
  P x*(f x)^2/(∑y,P y*(f y)^2)

def squareMean (P : Observables n) (f : Observables n) (i : Fin n) : ℝ :=
  ∑x,squareMass P f x*spin x i

lemma squareMass_probability (P f : Observables n) (hP : ∀x,0≤P x)
    (hN : 0<∑x,P x*(f x)^2) :
    (∀x,0 ≤ squareMass P f x) ∧ ∑x,squareMass P f x=1 := by
  refine ⟨fun x=>div_nonneg (mul_nonneg (hP x) (sq_nonneg _)) hN.le,?_⟩
  simp only [squareMass,←Finset.sum_div,div_self (ne_of_gt hN)]

lemma squareMean_centered (P f : Observables n) (t : Fin n→ℝ)
    (hN : 0<∑x,P x*(f x)^2) :
    squareMean P f-t=fun i=>(∑x,P x*(f x)^2*(spin x i-t i))/(∑x,P x*(f x)^2) := by
  ext i
  simp only [squareMean,squareMass,Pi.sub_apply,div_mul_eq_mul_div,←Finset.sum_div,
    mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,sub_div]
  rw [mul_div_cancel_left₀ _ (ne_of_gt hN)]

lemma normalized_square_bound (hn : 0<n) (P f : Observables n) (t : Fin n→ℝ)
    (hN : 0<∑x,P x*(f x)^2) (L A : ℝ)
    (H : vectorNorm (fun i=>∑x,P x*(f x)^2*(spin x i-t i))≤
      L*Real.sqrt (n:ℝ)*(∑x,P x*(f x)^2)+A*starSquared P f) :
    vectorNorm (squareMean P f-t)/Real.sqrt (n:ℝ)≤
      L+A/Real.sqrt (n:ℝ)*(1+varianceEnergy P f/(∑x,P x*(f x)^2)) := by
  have hs : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  rw [squareMean_centered P f t hN]
  have he : vectorNorm (fun i=>(∑x,P x*(f x)^2*(spin x i-t i))/(∑x,P x*(f x)^2))=
      vectorNorm (fun i=>∑x,P x*(f x)^2*(spin x i-t i))/(∑x,P x*(f x)^2) := by
    simp only [div_eq_mul_inv,mul_comm _ (∑x,P x*(f x)^2)⁻¹]
    change SKGap.vectorNorm _ = _
    rw [SKGap.vectorNorm_smul,abs_of_pos (inv_pos.mpr hN)]
    rfl
  rw [he]
  calc
    _ ≤ (L*Real.sqrt (n:ℝ)*(∑x,P x*(f x)^2)+A*starSquared P f)/(∑x,P x*(f x)^2)/Real.sqrt (n:ℝ) :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right H hN.le) hs.le
    _ = _ := by unfold starSquared;field_simp [ne_of_gt hN,ne_of_gt hs]

universe u
variable {Ω : Type u} {N : Ω→ℕ} {j R B W C ρ : ℝ}
variable {J : ∀a,Interaction (N a)} {h : ∀a,Fin (N a)→ℝ}

theorem gibbs_normalized_square_mean (m : ℕ) {c r₀ ε : ℝ}
    (hj : 0≤j) (hR : 0≤R) (hc : 0<c) (hr₀ : 0<r₀) (hρ : 0<ρ) (hε : 0<ε)
    (hbuffer : (R+4*j)*ρ<r₀) (hm : 2<(m:ℝ)*ρ^2/4) (he : 2*(2*m:ℕ)*ε≤1)
    (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<N a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) (J a))
    (hH : ∀a y,vectorNorm (SKGap.tapField j (J a) (h a) y)≤r₀*Real.sqrt (N a:ℝ)→∀v,
      c*SKGap.vectorSqNorm v≤SKGap.quadraticForm (SKGap.fieldHessian j (J a) y (SKGap.spinVariance y)) v) :
    ∃r : ∀a,Fin (N a)→ℝ,
      (∀a,SKGap.tapField j (J a) (h a) (r a)=0 ∧
        ∀y,SKGap.tapField j (J a) (h a) y=0→y=r a) ∧
      ∃A:ℝ,0≤A ∧ ∀a (f:Observables (N a)),
      0<(∑x,fieldGibbs (J a) (h a) x*(f x)^2)→
      vectorNorm (squareMean (fieldGibbs (J a) (h a)) f-SKGap.magnetization (r a))/Real.sqrt (N a:ℝ)≤
        ((1+(R+3*j)/c)*(R+4*j))*ρ+A/Real.sqrt (N a:ℝ)*
          (1+varianceEnergy (fieldGibbs (J a) (h a)) f/(∑x,fieldGibbs (J a) (h a) x*(f x)^2)) := by
  obtain ⟨r,hr,A,hA,hb⟩:=gibbs_square_mean (h:=h) m hj hR hc hr₀ hρ hε hbuffer hm he hB hW hC hn hJ hdiag hevent hH
  exact ⟨r,hr,A,hA,fun a f hN=>normalized_square_bound (hn a) _ f _ hN _ A (hb a f)⟩

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static

structure StableRecipeInstance (j R B W C c r₀ : ℝ) (m : ℕ) where
  n : ℕ
  positive : 0<n
  J : Interaction n
  field : Fin n→ℝ
  symmetric : J.IsSymm
  diagonal : ∀i,J i i=0
  event : RecipeMatrixEvent j R (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) J
  stability : ∀y,vectorNorm (SKGap.tapField j J field y)≤r₀*Real.sqrt (n:ℝ)→∀v,
    c*SKGap.vectorSqNorm v≤SKGap.quadraticForm (SKGap.fieldHessian j J y (SKGap.spinVariance y)) v

theorem uniform_stable_square_mean {j R B W C c r₀ ρ ε : ℝ} (m : ℕ)
    (hj : 0≤j) (hR : 0≤R) (hc : 0<c) (hr₀ : 0<r₀) (hρ : 0<ρ) (hε : 0<ε)
    (hbuffer : (R+4*j)*ρ<r₀) (hm : 2<(m:ℝ)*ρ^2/4) (he : 2*(2*m:ℕ)*ε≤1)
    (hB : 0≤B) (hW : 0≤W) (hC : 0≤C) :
    ∃A:ℝ,0≤A ∧ ∀{n:ℕ},0<n→∀(J:Interaction n) (h:Fin n→ℝ),
      J.IsSymm→(∀i,J i i=0)→
      RecipeMatrixEvent j R (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) J→
      (∀y,vectorNorm (SKGap.tapField j J h y)≤r₀*Real.sqrt (n:ℝ)→∀v,
        c*SKGap.vectorSqNorm v≤SKGap.quadraticForm (SKGap.fieldHessian j J y (SKGap.spinVariance y)) v)→
      ∃r:Fin n→ℝ,SKGap.tapField j J h r=0 ∧ (∀y,SKGap.tapField j J h y=0→y=r) ∧
        ∀f:Observables n,0<(∑x,fieldGibbs J h x*(f x)^2)→
        vectorNorm (squareMean (fieldGibbs J h) f-SKGap.magnetization r)/Real.sqrt (n:ℝ)≤
          ((1+(R+3*j)/c)*(R+4*j))*ρ+A/Real.sqrt (n:ℝ)*
            (1+varianceEnergy (fieldGibbs J h) f/(∑x,fieldGibbs J h x*(f x)^2)) := by
  let Ω:=StableRecipeInstance j R B W C c r₀ m
  obtain ⟨r,hr,A,hA,hb⟩:=gibbs_normalized_square_mean (Ω:=Ω) (N:=fun a=>a.n)
    (J:=fun a=>a.J) (h:=fun a=>a.field) m hj hR hc hr₀ hρ hε hbuffer hm he hB hW hC
    (fun a=>a.positive) (fun a=>a.symmetric) (fun a=>a.diagonal) (fun a=>a.event) (fun a=>a.stability)
  refine ⟨A,hA,?_⟩
  intro n hn J h hJ hd hev hst
  let a:Ω:=⟨n,hn,J,h,hJ,hd,hev,hst⟩
  exact ⟨r a,(hr a).1,(hr a).2,hb a⟩

lemma choose_selection_depth {ρ : ℝ} (hρ : 0<ρ) :
    ∃m:ℕ,∃ε:ℝ,0<ε ∧ 2<(m:ℝ)*ρ^2/4 ∧ 2*(2*m:ℕ)*ε≤1 := by
  obtain ⟨m,hm⟩:=exists_nat_gt (8/ρ^2)
  have hρ2 : 0<ρ^2:=sq_pos_of_pos hρ
  have hm' : 2<(m:ℝ)*ρ^2/4 := by
    have H:8<(m:ℝ)*ρ^2:=(div_lt_iff₀ hρ2).mp hm
    linarith
  refine ⟨m,1/(2*(2*m:ℕ)+1),by positivity,hm',?_⟩
  have hp : 0≤(2*(2*m:ℕ):ℝ):=by positivity
  rw [mul_one_div]
  exact (div_le_one (by positivity)).mpr (by linarith)

end SKGapCutoff.Recipe

end
end

end OAI
