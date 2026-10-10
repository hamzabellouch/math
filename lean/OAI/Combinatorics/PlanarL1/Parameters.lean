import Mathlib

namespace OAI


section

namespace PlanarL1.Parameters
noncomputable section
/-- Universal ordered parameter choices. The two free widths are chosen
strictly smaller than every displayed upper bound, not adapted to a graph. -/
def R : ℝ := 1/10^8
def D : ℝ := 1/10^3
def g : ℝ := 1/10^14
def j : ℝ := 1/10^20
def epsilon : ℝ := 1/10^24
def EA : ℝ := epsilon/1000
def EB : ℝ := R/1000
def zetaA : ℝ := epsilon/100
def zetaB : ℝ := 1/10
def a₁ : ℝ := 1/10^100
def a₂ : ℝ := 1/10^160
def kappaA : ℝ := a₁/10^6
def kappaB : ℝ := a₂/10^6
def lambda : ℝ := R/(10^12*100)

lemma positive : 0<R ∧ 0<D ∧ 0<g ∧ 0<j ∧ 0<epsilon ∧ 0<EA ∧ 0<EB ∧
    0<zetaA ∧ 0<zetaB ∧ 0<a₁ ∧ 0<a₂ ∧ 0<kappaA ∧ 0<kappaB ∧ 0<lambda := by
  norm_num [R,D,g,j,epsilon,EA,EB,zetaA,zetaB,a₁,a₂,kappaA,kappaB,lambda]

lemma interpolationA : 0<EA ∧ 0<a₁ ∧ 0<zetaA ∧ zetaA<1 ∧
    a₁ ≤ zetaA*(EA/8)/1000000 := by
  norm_num [EA,epsilon,a₁,zetaA]
lemma interpolationB : 0<EB ∧ 0<a₂ ∧ 0<zetaB ∧ zetaB<1 ∧
    a₂ ≤ zetaB*(EB/8)/1000000 := by
  norm_num [EB,R,a₂,zetaB]
lemma thinA : a₁≤(1/1000:ℝ)/1000 := by norm_num [a₁]
lemma widthA : a₁≤EA/10^6 ∧ a₁≤g/10^6 := by norm_num [a₁,EA,epsilon,g]
lemma widthB : a₂ ≤ min a₁ (kappaA*j)/10^6 := by
  norm_num [a₁,a₂,kappaA,j]
lemma verticalA : 0≤kappaA ∧ kappaA*max 1 (3/(9*a₁/100))≤1 ∧
    kappaA*(3/(9*a₁/100))<1 := by
  norm_num [kappaA,a₁]
lemma verticalB : 0≤kappaB ∧ kappaB*max 5 (3/(9*a₂/100))≤1 ∧
    kappaB*(3/(9*a₂/100))<1 ∧ kappaB*5≤1 := by
  norm_num [kappaB,a₂]

/-- Numeric input to the literal interpolation hierarchy. -/
structure Interpolation where
  error : ℝ
  width : ℝ
  zeta : ℝ
  error_pos : 0 < error
  width_pos : 0 < width
  zeta_pos : 0 < zeta
  zeta_lt : zeta < 1
  width_bound : width ≤ zeta*(error/8)/1000000

def broad : Interpolation := ⟨EA,a₁,zetaA,interpolationA.1,
  interpolationA.2.1,interpolationA.2.2.1,interpolationA.2.2.2.1,
  interpolationA.2.2.2.2⟩
def narrow : Interpolation := ⟨EB,a₂,zetaB,interpolationB.1,
  interpolationB.2.1,interpolationB.2.2.1,interpolationB.2.2.2.1,
  interpolationB.2.2.2.2⟩

end
end PlanarL1.Parameters

end

end OAI
