import OAI.NumberTheory.DirichletL.Descent.FirstNominal
import OAI.NumberTheory.DirichletL.Descent.Basic

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section

theorem firstRootScale_rpow (Z : ℝ) (hZ : 0 < Z) (s : Fin 9 → ℝ) :
    firstRootScale (fun i => Z^(s i)) = Z^(s 3+s 4/2+s 5+s 7/2+s 8/2) := by
  have hs (x : ℝ) : Real.sqrt (Z^x) = Z^(x/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hZ.le]
    congr 1
    ring
  unfold firstRootScale
  rw [hs,hs,hs,← Real.rpow_add hZ,← Real.rpow_add hZ,← Real.rpow_add hZ,← Real.rpow_add hZ]

def firstKappa (M r ell V δ A B R : ℝ) : ℝ := M-2*r-2*ell-V-δ+A+B-R/2
def firstPhysicalHeight (M r ell V δ B j : ℝ) : ℝ := 2*r-2*B-M+4*ell+2*V+δ-j
def secondLambda (M r ell V δ A B j t g θ : ℝ) : ℝ :=
  firstPhysicalHeight M r ell V δ B j - θ - (r-A-B-t-g)
def secondCount (ell R j t g θ : ℝ) : ℝ := ell+R/2-j+t+g-θ
def secondFormalColumn (r A B t g v : ℝ) : ℝ := r-A-B-t-g-v
def secondFormalLabel (B θ v j : ℝ) : ℝ := B+θ+v+j

theorem first_physical_scalar (Z : ℝ) (hZ : 0 < Z)
    (M r ell V δ A₁ A₂ B R t h : ℝ) :
    Z^(-r-2*ell-V) * Z^M /
      firstRootScale (fun i => Z^(![A₁,A₂,B,δ,R,t,h,r-A₁-B-t,r-A₂-B-t] i)) =
    Z^((firstKappa M r ell V δ A₁ B R+firstKappa M r ell V δ A₂ B R)/2) := by
  rw [firstRootScale_rpow Z hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ]
  congr 1
  norm_num [firstKappa]
  ring

theorem second_physical_scalar (Z : ℝ) (hZ : 0 < Z)
    (M r ell V δ A B j t g θ v η τ : ℝ) :
    Z^(firstPhysicalHeight M r ell V δ B j+12*η+τ) /
      (Z^θ*Z^v*Z^(secondFormalColumn r A B t g v)) * Real.exp (6*(η*Real.log Z)) =
    Z^(secondLambda M r ell V δ A B j t g θ+18*η+τ) := by
  have he : Real.exp (6*(η*Real.log Z)) = Z^(6*η) := by
    rw [Real.rpow_def_of_pos hZ]
    congr 1
    ring
  rw [he,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ,←Real.rpow_add hZ]
  congr 1
  unfold secondLambda secondFormalColumn
  ring

theorem physical_prefactor_identity (M r ell V δ A B R j t g θ v : ℝ) :
    firstKappa M r ell V δ A B R + secondLambda M r ell V δ A B j t g θ +
      secondCount ell R j t g θ +
      2*(secondFormalColumn r A B t g v+secondFormalLabel B θ v j) = r+3*ell+V := by
  unfold firstKappa secondLambda firstPhysicalHeight secondCount secondFormalColumn secondFormalLabel
  ring

theorem physical_step_energy_exponent (M r ell V δ A B R j t g θ v η τ π ε clip : ℝ)
    (hclip : clip ≤ 6*η) :
    firstKappa M r ell V δ A B R + secondLambda M r ell V δ A B j t g θ +
      secondCount ell R j t g θ +
      2*(secondFormalColumn r A B t g v+secondFormalLabel B θ v j+clip) +
      (9/2+18+11/2)*η+τ+π+ε ≤ r+3*ell+V+40*η+τ+π+ε :=
  step_energy_exponent (physical_prefactor_identity M r ell V δ A B R j t g θ v) hclip

end
end SevenEighths.InverseMoment

end OAI
