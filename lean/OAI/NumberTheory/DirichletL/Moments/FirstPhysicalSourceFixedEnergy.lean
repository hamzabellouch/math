import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedSource
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceDyadicWindowEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy
open CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
variable {η:Character}{C D:Ideal O}{hC:Supported C}
  {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}

theorem FixedPair.left_common_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(s:OriginalData ι)
    (t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):
    (∑'z:O,((‖leftChild s η (fixedBadMask*idealGenerator s.R) t C D hC E ξ₁ L z‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K))=commonEnergy s C hC F.left t L U K:=by
  change gaussEnergy Finset.univ (element C C hC.1 s.columns)
    (element_supported C C hC.1 s.columns) _ U K=_
  rw [funext (F.left_column s t L)]
  exact column_unwindowed_energy s C C hC.1 hC rfl F.left t L U K

theorem FixedPair.right_common_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)(t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):
    (∑'z:O,((‖rightChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L z‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K))=commonEnergy s D hD F.right t L U K:=by
  change gaussEnergy Finset.univ (element C D hD.1 s.columns)
    (element_supported C D hD.1 s.columns) _ U K=_
  rw [funext (F.right_column hD s t L)]
  exact column_unwindowed_energy s C D hC.1 hD hCD F.right t L U K

theorem FixedPair.right_reflected_common_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)(t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):
    (∑'z:O,((‖rightChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L (-z)‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K))=commonEnergy s D hD F.right t L U K:=by
  rw [←F.right_common_energy hD hCD s t L U K]
  simpa only [Equiv.neg_apply,map_neg,norm_neg] using (Equiv.neg O).tsum_eq
    (fun z:O=>((‖rightChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L z‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K))

theorem FixedPair.left_window_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(s:OriginalData ι)
    (t θ X:ℝ)(hX:0<X)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)
    (hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)(J:ℕ)(B:ℝ)(hB:0≤B)
    (hsource:∀v:ℝ,(commonEnergy s C hC F.left v L U K).re≤B*(1+‖v‖)^(2*J)):
    (∑'z:O,((‖leftWindowChild s η (fixedBadMask*idealGenerator s.R) t C D hC E ξ₁ L θ X logAnnulus z‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K)).re≤(windowBudget J t B*(1+‖θ‖)^J)^2:=by
  exact column_dyadic_window_energy s C C hC.1 hC rfl F.left t θ X hX L _
    (F.left_column s t L) U K hK hU J B hB hsource

theorem FixedPair.right_window_energy (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(s:OriginalData ι)(t θ X:ℝ)(hX:0<X)(L:Ideal O)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(B:ℝ)(hB:0≤B)
    (hsource:∀v:ℝ,(commonEnergy s D hD F.right v L U K).re≤B*(1+‖v‖)^(2*J)):
    (∑'z:O,((‖rightWindowChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L θ X logAnnulus z‖^2:ℝ):ℂ)*
      U (‖eisEmbedding z‖^2/K)).re≤(windowBudget J t B*(1+‖θ‖)^J)^2:=by
  exact column_star_dyadic_window_energy s C D hC.1 hD hCD F.right t θ X hX L _
    (F.right_column hD s t L) U K hK hU J B hB hsource

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
