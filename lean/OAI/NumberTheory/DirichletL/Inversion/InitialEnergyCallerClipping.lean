import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerPhysical

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss
namespace SevenEighths.InverseInitialEnergyCallerClipping
open InverseMoment InverseInitialClippedColumns InverseInitialProfile
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

omit [DecidableEq σ] in
theorem normalized_energy_clipping
    (pool:Finset ι)(Ψ:Eis→*ℂ)(m:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(labels:Finset (Ideal Eis))(rows:Finset Eis)
    (d:Ideal Eis→ℝ)(w:ℝ→ℂ){Z:ℝ}(hZ:0<Z)(N h F:ℝ) :
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows d
      (childLogTest w h) (Z^N) Z F =
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows d
      (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) Z F := by
  unfold normalizedColumnEnergy
  simp_rw [norm_mul, canonical_row_clipping_norm p hp hcop hg pool Ψ m _ _
    slots lists a w hZ N h]

theorem initial_scalar_identity (m D B _v θ η δ π ε:ℝ) :
    prefactorCenter m D B θ+3*η+(D-B+θ+δ)+(B-θ+2*η)+π+
      ((D-B+θ+δ)+ε)=m+5*η+2*δ+π+ε := by
  unfold prefactorCenter
  ring

theorem initial_scalar_le (m D B v θ η δ π ε:ℝ)(hδ:δ≤3*η) :
    prefactorCenter m D B θ+3*η+(D-B+θ+δ)+(B-θ+2*η)+π+
      ((D-B+θ+δ)+ε)≤m+11*η+π+ε := by
  rw [initial_scalar_identity m D B v θ η δ π ε]
  linarith

end SevenEighths.InverseInitialEnergyCallerClipping

end

end OAI
