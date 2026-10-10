import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceUnitAmplitude
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseQuotient
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

theorem unitHistoryPhase_indexed_permutation (k j : ℕ) (width : Role → ℕ) {A : ℕ}
    (σ : Equiv.Perm ((schedule k j).Constituent width))
    (x : (schedule k j).Constituent width → PrimeUpTo A)
    (ζ : PrimeUnitData (schedule k j) width A)
    (χd : PrimeCharacterData (schedule k j) width A)
    (ad : PrimeTranslationData (schedule k j) width A)
    (hχ : ∀ i p,χd (σ i) p = χd i p)
    (ha : ∀ i p,ad (σ i) p = ad i p)
    (s : ℤ) (t : HistoryReconstruction.Tree j) :
    letI : ∀ i,Fact (x i).val.Prime := fun i => ⟨primeUpTo_prime (x i)⟩
    unitHistoryPhase k j width ζ χd ad (fun i => x (σ.symm i)) s t =
      (∏ i,ZMod.stdAddChar (-(ad i (x i)*crtFrequency (fun i => (x i).val) s i))) *
        primeGraphPhase (permutedGraph (constituentGraph k j width) σ)
          (fun i => (x i).val) (fun i => χd i (x i))
          (fun i => ζ (σ i) (x i)*actualHistoryUnary k width (χd i (x i)) j s t (σ i)) := by
  let : ∀ i,Fact (x i).val.Prime := fun i => ⟨primeUpTo_prime (x i)⟩
  have hχ' : (fun i => χd i (x (σ.symm i))) =
      (fun i => χd (σ.symm i) (x (σ.symm i))) := by
    funext i
    simpa only [Equiv.apply_symm_apply] using hχ (σ.symm i) (x (σ.symm i))
  have ha' : (fun i => ad i (x (σ.symm i))) =
      (fun i => ad (σ.symm i) (x (σ.symm i))) := by
    funext i
    simpa only [Equiv.apply_symm_apply] using ha (σ.symm i) (x (σ.symm i))
  have hζ : (∏ i,ζ i (x (σ.symm i))) = ∏ i,ζ (σ i) (x i) := by
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.prod_comp σ (fun i => ζ i (x (σ.symm i)))).symm
  unfold unitHistoryPhase sampledHistoryPhase sampleUnitMultiplier
  rw [hχ',ha']
  dsimp only
  rw [actualHistoryPhase_permutation k j width σ (fun i => (x i).val)
    (fun i => χd i (x i)) (fun i => ad i (x i)) s t,hζ]
  simp only [primeGraphPhase,Finset.prod_mul_distrib]
  ring

theorem unitHistoryPhase_indexed_pair (k j : ℕ) (width : Role → ℕ) {A : ℕ}
    (σ ρ : Equiv.Perm ((schedule k j).Constituent width))
    (x : (schedule k j).Constituent width → PrimeUpTo A)
    (hx : Pairwise (fun i h => (x i).val.Coprime (x h).val))
    (ζ : PrimeUnitData (schedule k j) width A)
    (χd : PrimeCharacterData (schedule k j) width A)
    (ad : PrimeTranslationData (schedule k j) width A)
    (hχσ : ∀ i p,χd (σ i) p = χd i p) (haσ : ∀ i p,ad (σ i) p = ad i p)
    (hχρ : ∀ i p,χd (ρ i) p = χd i p) (haρ : ∀ i p,ad (ρ i) p = ad i p)
    (s : ℤ) (t u : HistoryReconstruction.Tree j) :
    letI : ∀ i,Fact (x i).val.Prime := fun i => ⟨primeUpTo_prime (x i)⟩
    unitHistoryPhase k j width ζ χd ad (fun i => x (σ.symm i)) s t *
      conj (unitHistoryPhase k j width ζ χd ad (fun i => x (ρ.symm i)) s u) =
      primeGraphPhase
        (fun i h => permutedGraph (constituentGraph k j width) σ i h -
          permutedGraph (constituentGraph k j width) ρ i h)
        (fun i => (x i).val) (fun i => χd i (x i))
        (fun i => (ζ (σ i) (x i)*actualHistoryUnary k width (χd i (x i)) j s t (σ i))*
          conj (ζ (ρ i) (x i)*actualHistoryUnary k width (χd i (x i)) j s u (ρ i))) := by
  let : ∀ i,Fact (x i).val.Prime := fun i => ⟨primeUpTo_prime (x i)⟩
  let : ∀ i,NeZero (x i).val := fun i => ⟨(primeUpTo_prime (x i)).ne_zero⟩
  have htrans :
      (∏ i,ZMod.stdAddChar (-(ad i (x i)*crtFrequency (fun i => (x i).val) s i))) *
        conj (∏ i,ZMod.stdAddChar (-(ad i (x i)*crtFrequency (fun i => (x i).val) s i))) = 1 := by
    have hn : ‖∏ i,ZMod.stdAddChar (-(ad i (x i)*crtFrequency (fun i => (x i).val) s i))‖ = 1 := by
      rw [norm_prod]
      have hh (i : (schedule k j).Constituent width) :=
        (ZMod.stdAddChar : AddChar (ZMod (x i).val) ℂ).norm_apply
          (-(ad i (x i)*crtFrequency (fun i => (x i).val) s i))
      simp only [hh,Finset.prod_const_one]
    rw [Complex.mul_conj',hn]
    norm_num
  rw [unitHistoryPhase_indexed_permutation k j width σ x ζ χd ad hχσ haσ s t,
    unitHistoryPhase_indexed_permutation k j width ρ x ζ χd ad hχρ haρ s u,map_mul]
  rw [show ∀ a b c d : ℂ,(a*b)*(c*d)=(a*c)*(b*d) by intros;ring,htrans,one_mul]
  apply primeGraphPhase_mul_conj _ _ _ _ _ hx
  · intro i
    simp [permutedGraph,constituentGraph,liftGraph]
  · intro i
    simp [permutedGraph,constituentGraph,liftGraph]

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
