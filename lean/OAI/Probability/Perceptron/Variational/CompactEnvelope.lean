import Mathlib
import OAI.Probability.Perceptron.Pressure.FiniteTerminal

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction ContDiff
namespace SphericalPerceptronFreeEnergy

def Jet3.addConstant (g : Jet3) (c : ℝ) : Jet3 where
  f:=g.f+BoundedContinuousFunction.const ℝ c
  d1:=g.d1
  d2:=g.d2
  d3:=g.d3
  has1 x:=by
    change HasDerivAt (fun y => g.f y + c) (g.d1 x) x
    exact (g.has1 x).add_const c
  has2:=g.has2
  has3:=g.has3

def Jet3.negative (g : Jet3) : Jet3 where
  f:=-g.f
  d1:=-g.d1
  d2:=-g.d2
  d3:=-g.d3
  has1 x:=by simpa using (g.has1 x).neg
  has2 x:=by simpa using (g.has2 x).neg
  has3 x:=by simpa using (g.has3 x).neg

lemma exists_smooth_lower_envelope (f : ℝ→ᵇℝ) {R ε : ℝ} (hR : 0<R) (hε : 0<ε) :
    ∃ g : Jet3,
      HasCompactSupport (g.d1 : ℝ→ℝ) ∧ HasCompactSupport (g.d2 : ℝ→ℝ) ∧
      HasCompactSupport (g.d3 : ℝ→ℝ) ∧ ‖g.f‖≤‖f‖+2*ε ∧
      (∀ x : ℝ,g.f x≤f x) ∧ (∀ x : ℝ,|x|≤R→|g.f x-f x|≤2*ε) := by
  let K:=‖f‖
  let ψ : ContDiffBump (0:ℝ):=⟨R,R+1,hR,by linarith⟩
  let F : ℝ→ℝ:=fun x=>ψ x*(f x+K)
  have hF : Continuous F:=ψ.continuous.mul (f.continuous.add continuous_const)
  have hFs : HasCompactSupport F:=ψ.hasCompactSupport.mul_right
  obtain ⟨g,hg,hgf,hgs⟩:=hF.exists_contDiff_approx (⊤:ℕ∞)
    (ε:=fun _=>ε) continuous_const (fun _=>hε)
  have hg' : ContDiff ℝ ∞ g:=hg
  have hs : HasCompactSupport g:=hFs.mono hgs
  let J:=(Jet3.ofCompactSmooth g hg' hs).addConstant (-K-ε)
  have hJ (x : ℝ) : J.f x=g x-K-ε := by simp [J,Jet3.addConstant]; ring
  have hzero (x : ℝ) : 0≤F x := by
    have hf:= (abs_le.mp (f.norm_coe_le_norm x)).1
    dsimp [F,K]
    exact mul_nonneg ψ.nonneg (by linarith)
  have hle (x : ℝ) : F x≤f x+K :=
    mul_le_of_le_one_left (by have hf:=(abs_le.mp (f.norm_coe_le_norm x)).1; dsimp [K]; linarith) ψ.le_one
  have herr (x : ℝ) : |g x-F x|<ε := by simpa only [Real.dist_eq] using hgf x
  have hlower (x : ℝ) : J.f x≤f x := by
    rw [hJ]
    have hh:=(abs_lt.mp (herr x)).2
    linarith [hle x]
  refine ⟨J,?_,?_,?_,?_,hlower,?_⟩
  · change HasCompactSupport (deriv g)
    exact hs.deriv
  · change HasCompactSupport (deriv (deriv g))
    exact hs.deriv.deriv
  · change HasCompactSupport (deriv (deriv (deriv g)))
    exact hs.deriv.deriv.deriv
  · apply (BoundedContinuousFunction.norm_le (by positivity : 0≤‖f‖+2*ε)).mpr
    intro x
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · rw [hJ]
      have hh:=(abs_lt.mp (herr x)).1
      dsimp [K] at *
      linarith [hzero x]
    · have hh:=(abs_le.mp (f.norm_coe_le_norm x)).2
      linarith [hlower x]
  · intro x hx
    have hψ : ψ x=1:=ψ.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hx)
    have he : F x=f x+K:=by simp [F,hψ]
    rw [hJ]
    have hh:=herr x
    rw [he] at hh
    exact abs_le.mpr ⟨by linarith [(abs_lt.mp hh).1],by linarith [(abs_lt.mp hh).2]⟩

lemma exists_smooth_lower_sequence (f : ℝ→ᵇℝ) :
    ∃ g : ℕ→Jet3,
      (∀ n,HasCompactSupport ((g n).d1 : ℝ→ℝ) ∧ HasCompactSupport ((g n).d2 : ℝ→ℝ) ∧
        HasCompactSupport ((g n).d3 : ℝ→ℝ)) ∧
      (∀ n,‖(g n).f‖≤‖f‖+1) ∧ (∀ n x,(g n).f x≤f x) ∧
      ∀ R : ℝ,0<R→∀ ε : ℝ,0<ε→∃ N : ℕ,∀ n≥N,∀ x : ℝ,|x|≤R→|(g n).f x-f x|≤ε := by
  have hx (n : ℕ):=exists_smooth_lower_envelope f
    (by positivity : 0<(n:ℝ)+1) (by positivity : 0<(1:ℝ)/(2*((n:ℝ)+1)))
  choose g h1 h2 h3 hn hlo he using hx
  refine ⟨g,(fun n=>⟨h1 n,h2 n,h3 n⟩),?_,hlo,?_⟩
  · intro n
    have hh : 2*((1:ℝ)/(2*((n:ℝ)+1)))=1/((n:ℝ)+1) := by field_simp
    have hle : (1:ℝ)/((n:ℝ)+1)≤1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])
    have hi:=hn n
    rw [hh] at hi
    exact hi.trans (by linarith)
  · intro R hR ε hε
    obtain ⟨N1,hN1⟩:=exists_nat_ge R
    obtain ⟨N2,hN2⟩:=exists_nat_one_div_lt hε
    refine ⟨max N1 N2,fun n hn x hx=>?_⟩
    have hN1' : N1≤n:=(le_max_left _ _).trans hn
    have hN2' : N2≤n:=(le_max_right _ _).trans hn
    have hx' : |x|≤(n:ℝ)+1 := by
      have hc : (N1:ℝ)≤n:=by exact_mod_cast hN1'
      linarith
    have hh:=he n x hx'
    have heq : 2*((1:ℝ)/(2*((n:ℝ)+1)))=1/((n:ℝ)+1) := by field_simp
    rw [heq] at hh
    exact hh.trans ((one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hN2' 1)).trans hN2.le)

lemma exists_smooth_upper_sequence (f : ℝ→ᵇℝ) :
    ∃ g : ℕ→Jet3,
      (∀ n,HasCompactSupport ((g n).d1 : ℝ→ℝ) ∧ HasCompactSupport ((g n).d2 : ℝ→ℝ) ∧
        HasCompactSupport ((g n).d3 : ℝ→ℝ)) ∧
      (∀ n,‖(g n).f‖≤‖f‖+1) ∧ (∀ n x,f x≤(g n).f x) ∧
      ∀ R : ℝ,0<R→∀ ε : ℝ,0<ε→∃ N : ℕ,∀ n≥N,∀ x : ℝ,|x|≤R→|(g n).f x-f x|≤ε := by
  obtain ⟨g,hs,hn,hlo,he⟩:=exists_smooth_lower_sequence (-f)
  refine ⟨fun n=>(g n).negative,fun n=>⟨(hs n).1.neg,(hs n).2.1.neg,(hs n).2.2.neg⟩,?_,?_,?_⟩
  · intro n
    simpa only [Jet3.negative,norm_neg] using hn n
  · intro n x
    have h:=hlo n x
    change f x≤-(g n).f x
    change (g n).f x≤-f x at h
    linarith
  · intro R hR ε hε
    obtain ⟨N,hN⟩:=he R hR ε hε
    refine ⟨N,fun n hn x hx=>?_⟩
    have h:=hN n hn x hx
    change |-(g n).f x-f x|≤ε
    change |(g n).f x- -f x|≤ε at h
    rw [show -(g n).f x-f x = -((g n).f x+f x) by ring,abs_neg]
    simpa only [sub_neg_eq_add] using h

end SphericalPerceptronFreeEnergy

end

end OAI
