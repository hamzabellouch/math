import OAI.NumberTheory.DirichletL.Descent.ActualChildStateDepth
import OAI.NumberTheory.DirichletL.Descent.ActualChildStateTriples

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment

def actualDepth (Mmax cutoff : ℝ) : ℕ := ⌈2*Mmax/(3*cutoff)⌉₊+1

lemma actualDepth_pos (Mmax cutoff : ℝ) : 0<actualDepth Mmax cutoff := by
  exact Nat.succ_pos _

lemma actualDepth_strict (Mmax cutoff : ℝ) :
    2*Mmax/(3*cutoff)<(actualDepth Mmax cutoff:ℝ) := by
  have h := Nat.le_ceil (2*Mmax/(3*cutoff))
  unfold actualDepth
  push_cast
  linarith

theorem actual_depth_parameters (depth : ℕ) (cutoff c eps : ℝ)
    (hd : 0<cutoff) (hc : 0<c) (heps : 0<eps) :
    ∃eta tau pi : ℝ,0<eta ∧ 0<tau ∧ 0<pi ∧ eta≤cutoff/16 ∧
      (depth:ℝ)*7*eta≤c/2 ∧ (depth:ℝ)*15*eta≤1 ∧
      (depth:ℝ)*(100*eta+4*tau+4*pi)≤eps/4 := by
  let D : ℝ := (depth:ℝ)+1
  have hD : 0<D := by dsimp [D];positivity
  have hn : 0≤(depth:ℝ) := Nat.cast_nonneg _
  have hnD : (depth:ℝ)≤D := by dsimp [D];linarith
  let eta := min (cutoff/16) (min (c/(28*D)) (min (1/(30*D)) (eps/(1600*D))))
  let tau := eps/(128*D)
  have heta : 0<eta := by dsimp [eta];positivity
  have htau : 0<tau := by dsimp [tau];positivity
  have he1 : eta≤cutoff/16 := min_le_left _ _
  have he2 : eta≤c/(28*D) := (min_le_right _ _).trans (min_le_left _ _)
  have he3 : eta≤1/(30*D) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have he4 : eta≤eps/(1600*D) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hb2 : eta*(28*D)≤c := (le_div_iff₀ (by positivity)).mp he2
  have hb3 : eta*(30*D)≤1 := (le_div_iff₀ (by positivity)).mp he3
  have hb4 : eta*(1600*D)≤eps := (le_div_iff₀ (by positivity)).mp he4
  have ht : tau*(128*D)=eps := by dsimp [tau];field_simp
  have hne : (depth:ℝ)*eta≤D*eta := mul_le_mul_of_nonneg_right hnD heta.le
  have hnt : (depth:ℝ)*tau≤D*tau := mul_le_mul_of_nonneg_right hnD htau.le
  refine ⟨eta,tau,tau,heta,htau,htau,he1,?_,?_,?_⟩ <;> nlinarith

theorem actual_depth_margin_size (depth n : ℕ) (hn : n≤depth)
    (c eta F0 : ℝ) (heta : 0≤eta)
    (hmargin : (depth:ℝ)*7*eta≤c/2) (hsize : (depth:ℝ)*15*eta≤1) :
    c/2≤c-7*(n:ℝ)*eta ∧ F0+15*(n:ℝ)*eta≤F0+1 := by
  have hnn : (n:ℝ)≤depth := by exact_mod_cast hn
  have hh := mul_le_mul_of_nonneg_right hnn heta
  constructor <;> nlinarith

theorem actual_depth_uniform_caps (depth n : ℕ) (hn : n≤depth)
    (F M N V Q z c F0 M0 eta : ℝ) (heta : 0≤eta) (hc : 0<c)
    (hmargin : (depth:ℝ)*7*eta≤c/2) (hsize : (depth:ℝ)*15*eta≤1)
    (hF : F≤F0+15*(n:ℝ)*eta) (hM0 : M≤M0)
    (hN : 0≤N) (hV : 0≤V) (hM : 0≤M) (hQ : 0≤Q) (hz : 0≤z)
    (hsum : F=N+V) (hinv : CanonicalMargins F M Q z (c-7*(n:ℝ)*eta)) :
    N≤F0+1 ∧ V≤F0+1 ∧ M≤min M0 (F0+1) ∧ Q≤F0+1 ∧ z≤F0+1 := by
  have hh := actual_depth_margin_size depth n hn c eta F0 heta hmargin hsize
  have hFcap : F≤F0+1 := hF.trans hh.2
  have hcaps := actual_child_size_caps F M Q z (c-7*(n:ℝ)*eta) (F0+1)
    hinv hM hQ hz (by linarith [hh.1]) hFcap
  refine ⟨?_,?_,le_min hM0 hcaps.1,hcaps.2.1,hcaps.2.2⟩ <;> linarith

theorem actual_depth_retained_loss (depth n : ℕ) (hn : n≤depth)
    (eta tau pi epsChild eps : ℝ) (he : 0≤eta) (ht : 0≤tau) (hp : 0≤pi)
    (hc : 0≤epsChild) (hbudget : (depth:ℝ)*(100*eta+4*tau+4*pi)≤eps/4)
    (hchild : (depth:ℝ)*epsChild≤eps/4) :
    (n:ℝ)*(48*eta+tau+pi+epsChild)≤eps/2 := by
  have hn' : (n:ℝ)≤depth := by exact_mod_cast hn
  have h1 := mul_le_mul_of_nonneg_right hn' (show 0≤48*eta+tau+pi+epsChild by positivity)
  have h2 : (depth:ℝ)*(48*eta+tau+pi)≤(depth:ℝ)*(100*eta+4*tau+4*pi) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    linarith
  nlinarith

theorem actual_depth_row_negative (M Mmax cutoff : ℝ) (n : ℕ) (hd : 0<cutoff)
    (hn : actualDepth Mmax cutoff≤n)
    (hpath : M+3*(n:ℝ)*cutoff/2≤Mmax) : M<0 := by
  have hn' : (actualDepth Mmax cutoff:ℝ)≤n := by exact_mod_cast hn
  have hs := (actualDepth_strict Mmax cutoff).trans_le hn'
  have hs' := (div_lt_iff₀ (by positivity : 0<3*cutoff)).mp hs
  nlinarith

end SevenEighths.InverseMoment
end

end OAI
