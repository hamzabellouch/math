import OAI.Geometry.IsometricImmersion.Caps.HeightCapLowData
import OAI.Geometry.IsometricImmersion.Energy.DirectedParameterChoice

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Model

def HeightNumericData (G Z d c e0 kappa : ℝ) : Prop :=
  0 ≤ G ∧ 0 ≤ Z ∧ 0 < d ∧ 0 < c ∧ 0 < e0 ∧ 0 < kappa

def HeightDirectedBudgets (G Z d c e0 kappa : ℝ) (ell : ℕ) (v : ℝ × ℝ × ℝ) : Prop :=
  let epsilon := v.1
  let lambda := v.2.1
  let c1 := v.2.2
  let rhoMax := 1/Real.exp (-2*heightQuotientJetBound G Z d c)
  let cG := heightG1Lower G Z d c e0
  let MG := heightG1JetBound G Z d c
  let MB := heightBJetBound G Z d c ell
  let Mr := heightRemainderBound G Z d c e0 ell
  let MA := heightAJetBound G Z d c
  0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < lambda ∧ 0 < c1 ∧
  epsilon*2*((1 : ℝ)/100) ≤ ((ell : ℝ)+1/2)/rhoMax ∧
  2*(2*MB+epsilon+epsilon*2*MB) ≤ lambda ∧
  (2*MB+1+2*MB)/2+Mr ≤ lambda/8 ∧
  4*(2*((ell : ℝ)*MA+MA*Mr+MA*(2*MB)+1))^2*epsilon^2*MA ≤ 1/8 ∧
  (4*(2*((ell : ℝ)*MA+MA*Mr+MA*(2*MB)+1))^2*epsilon^2)/lambda ≤
    modelCoercivityMargin cG kappa rhoMax epsilon ell/8 ∧
  directedPrincipalBound ell epsilon 2 MA MA+modelCoercivityMargin cG kappa rhoMax epsilon ell/2 ≤
    lambda*(cG*modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell)/4 ∧
  c1*2 ≤ modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell ∧
  MG*c1*(lambda*2+8) ≤ modelCoercivityMargin cG kappa rhoMax epsilon ell/6

theorem exists_heightDirectedBudgets {G Z d c e0 kappa : ℝ}
    (h : HeightNumericData G Z d c e0 kappa) (ell : ℕ) :
    ∃ v : ℝ × ℝ × ℝ, HeightDirectedBudgets G Z d c e0 kappa ell v := by
  obtain ⟨hG,hZ,hd,hc,he0,hk⟩ := h
  have hcG := heightG1Lower_pos (c := c) hG hZ hd he0
  have hrho : 0 < 1/Real.exp (-2*heightQuotientJetBound G Z d c) := by positivity
  have hMG := heightG1JetBound_nonneg hG hZ hd hc
  have hMB := heightBJetBound_nonneg hG hZ hd hc ell
  have hMr := heightRemainderBound_nonneg hG hZ hd hc he0 ell
  have hMA := heightAJetBound_nonneg hG hZ hd hc
  obtain ⟨epsilon,lambda,c1,hbudget⟩ :=
    exists_directed_parameters ell hk hcG hrho hMG (show 0 ≤ 2*heightBJetBound G Z d c ell by positivity)
      hMB hMr hMA hMA hMA hMG (by norm_num : (0 : ℝ) ≤ 2)
  exact ⟨(epsilon,lambda,c1),hbudget⟩

def heightDirectedNumbers (G Z d c e0 kappa : ℝ) (ell : ℕ) : ℝ × ℝ × ℝ := by
  classical
  exact if h : HeightNumericData G Z d c e0 kappa then Classical.choose (exists_heightDirectedBudgets h ell)
    else (1,1,1)

def heightDirectedEpsilon (G Z d c e0 kappa : ℝ) (ell : ℕ) : ℝ :=
  (heightDirectedNumbers G Z d c e0 kappa ell).1
def heightDirectedLambda (G Z d c e0 kappa : ℝ) (ell : ℕ) : ℝ :=
  (heightDirectedNumbers G Z d c e0 kappa ell).2.1
def heightDirectedSlope (G Z d c e0 kappa : ℝ) (ell : ℕ) : ℝ :=
  (heightDirectedNumbers G Z d c e0 kappa ell).2.2
def heightDirectedCoercivity (G Z d c e0 kappa : ℝ) (ell : ℕ) : ℝ :=
  min (heightDirectedLambda G Z d c e0 kappa ell/8)
    (modelCoercivityMargin (heightG1Lower G Z d c e0) kappa
      (1/Real.exp (-2*heightQuotientJetBound G Z d c))
      (heightDirectedEpsilon G Z d c e0 kappa ell) ell/4)

theorem heightDirectedNumbers_spec {G Z d c e0 kappa : ℝ}
    (h : HeightNumericData G Z d c e0 kappa) (ell : ℕ) :
    HeightDirectedBudgets G Z d c e0 kappa ell (heightDirectedNumbers G Z d c e0 kappa ell) := by
  rw [heightDirectedNumbers,dite_eq_left h]
  exact Classical.choose_spec (exists_heightDirectedBudgets h ell)

theorem heightDirectedParameters_pos {G Z d c e0 kappa : ℝ}
    (h : HeightNumericData G Z d c e0 kappa) (ell : ℕ) :
    0 < heightDirectedEpsilon G Z d c e0 kappa ell ∧
    heightDirectedEpsilon G Z d c e0 kappa ell ≤ 1 ∧
    0 < heightDirectedLambda G Z d c e0 kappa ell ∧
    0 < heightDirectedSlope G Z d c e0 kappa ell ∧
    0 < heightDirectedCoercivity G Z d c e0 kappa ell := by
  have hs := heightDirectedNumbers_spec h ell
  obtain ⟨hG,hZ,hd,_,he0,hk⟩ := h
  have heps : 0 < heightDirectedEpsilon G Z d c e0 kappa ell := hs.1
  have heps1 : heightDirectedEpsilon G Z d c e0 kappa ell ≤ 1 := hs.2.1
  have hlambda : 0 < heightDirectedLambda G Z d c e0 kappa ell := hs.2.2.1
  have hc1 : 0 < heightDirectedSlope G Z d c e0 kappa ell := hs.2.2.2.1
  have hmargin := modelCoercivityMargin_pos ell (heightG1Lower_pos (c := c) hG hZ hd he0)
    hk (show 0 < 1/Real.exp (-2*heightQuotientJetBound G Z d c) by positivity) heps
  refine ⟨heps,heps1,hlambda,hc1,?_⟩
  unfold heightDirectedCoercivity
  positivity

end SmoothLocal.Flow

end

end OAI
