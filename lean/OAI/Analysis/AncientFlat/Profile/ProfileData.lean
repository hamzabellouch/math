import OAI.Analysis.AncientFlat.Profile.OriginalPotential

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace FlatMain

def rightD (f : ℝ → ℝ) (y : ℝ) : ℝ := derivWithin f (Ici 0) y
def rightT (f : ℝ → ℝ) (y : ℝ) : ℝ := y*rightD (rightD f) y+12*rightD f y
def eulerShift (a : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ := y*rightD f y+a*f y
def profileQ (G : ℝ → ℝ) := eulerShift (-1) (eulerShift 9 (eulerShift 10 (fun y => G y-1)))

structure ProfileData where
  G : ℝ → ℝ
  c : ℝ
  c_pos : 0<c
  smooth : ContDiffOn ℝ ∞ G (Ici 0)
  equation : ∀ y : ℝ, 0≤y → profileQ G y=y^2/2*(1/G y-1/c)
  bounds : ∃ κ K : ℝ, 0<κ ∧ ∀ y : ℝ, 0≤y → κ≤G y ∧ G y≤K
  value_zero : G 0=1
  slope_negative : rightD G 0<0
  analytic_zero : ∃ g : ℝ → ℝ, AnalyticAt ℝ g 0 ∧ G=ᶠ[𝓝[Ici 0] 0] g
  coefficients : ℕ → ℝ
  expansion : ∀ J ℓ : ℕ,
    Asymptotics.IsBigO atTop
      (iteratedDeriv ℓ (fun y : ℝ => G y-c-∑ j∈Finset.Icc 1 J, coefficients j*y^(-(2*(j:ℝ)))))
      (fun y : ℝ => y^(-(2*((J:ℝ)+1))-(ℓ:ℝ)))
  H : ℝ → ℝ
  compactified_smooth : ContDiffOn ℝ ∞ H (Ici 0)
  compactified_zero : H 0=c
  compactified_match : ∀ u : ℝ, 0<u → H u=G (u^(-(1:ℝ)/2))
  h : ℝ → ℝ
  quotient : ∀ y : ℝ, 0<y → h y=(G y-1)/y
  quotient_zero : h 0=rightD G 0
  quotient_smooth : ContDiffOn ℝ ∞ h (Ici 0)
  shrinker : ∀ t : ℝ, t<0 → ∀ y : ℝ, 0≤y →
    deriv (fun r => FlatRadial.scalarF h r y) t+
      (1+y*FlatRadial.scalarF h t y)^2*rightT (rightT (FlatRadial.scalarF h t)) y=0
end FlatMain

end

end OAI
