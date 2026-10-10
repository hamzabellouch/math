import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FreeSplit
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DivisorPathTemplate
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PackedGapPrefactor

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.NumericalSubtrees OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SharedSlotPatterns Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L K t J : ℕ}

abbrev DivisorPathFilling (S : PrimeSystem) (h ℓ K J t : ℕ) :=
  (m : Fin (ℓ*J+1)) × (GoodDivisorPathTemplate h ℓ K J t m.val × (Fin m.val → S.Index))
namespace DivisorPathFilling
def weight (z : DivisorPathFilling S h ℓ K J t) (P Z : ℝ) : ℝ :=
  (z.2.1.val.system h z.2.1.property).fiberWeight P Z (fun a => (z.2.2 a:ℕ))
lemma weight_nonneg (z : DivisorPathFilling S h ℓ K J t) (P Z : ℝ) : 0≤z.weight P Z :=
  TriangularExpressions.fiberWeight_nonneg ..
def decode (z : DivisorPathFilling S h ℓ K J t) :
    (Fin ℓ → Bool) × (Fin ℓ × Fin J → Option S.Index) :=
  (z.2.1.val.1,fun s => (z.2.1.val.2.1 s).map z.2.2)
lemma sum_weight (P Z : ℝ) :
    (∑ z : DivisorPathFilling S h ℓ K J t,z.weight P Z)=divisorPathTemplateMass S P Z h ℓ K J t := by
  unfold divisorPathTemplateMass
  rw [Fintype.sum_sigma]
  exact sum_congr rfl (fun m hm => Fintype.sum_prod_type _)
end DivisorPathFilling
namespace NumericalLine
namespace ShortCorruptSelection
variable {w : NumericalLine D h ℓ} (s : w.ShortCorruptSelection K t)
def encode : DivisorPathFilling S h ℓ K ⌈C₀*Real.log B⌉₊ t :=
  ⟨⟨(support w.linePrimeCode).card,by
      have he := card_support_le w.linePrimeCode
      simp only [Fintype.card_prod,Fintype.card_fin] at he
      omega⟩,⟨s.template,s.formed⟩,values w.linePrimeCode⟩
lemma decode_encode : s.encode.decode=w.basicCode := by
  change (signBit w.line,fun a => (pattern w.linePrimeCode a).map (values w.linePrimeCode))=(signBit w.line,w.linePrimeCode)
  exact Prod.ext rfl (funext (decode_pattern w.linePrimeCode))
lemma weight_encode (P : ℝ) (hB : 0≤B) (hS : ∀ p : S.Index,(p:ℝ) ≤ Real.exp B) :
    s.encode.weight P (Specification.densitySize B C₀ h K)=w.lineReciprocalWeight := by
  change (if (s.template.system h s.formed).Admissible P _ (fun i => (values w.linePrimeCode i:ℕ)) then
    ∏ i,((values w.linePrimeCode i:ℕ):ℝ)⁻¹ else 0)=w.lineReciprocalWeight
  rw [ite_eq_left (s.template_admissible P hB hS)]
  exact (weight_identity w.linePrimeCode (fun p => (p:ℝ)⁻¹)).symm
end ShortCorruptSelection

def ManyShortCorrupted (w : NumericalLine D h ℓ) (K t : ℕ) : Prop :=
  (2*(K*⌈C₀*Real.log B⌉₊)+1)*t ≤ (shortCorrupted w K).card

def nearCorruptMass (D : S.DivisorFamily B τ C₀) (h ℓ K t : ℕ) : ℝ :=
  ∑ w : {w : NumericalLine D h ℓ // w.ManyShortCorrupted K t},w.val.lineReciprocalWeight

lemma nearCorruptMass_le_templateMass (P : ℝ) (hB : 0≤B)
    (hS : ∀ p : S.Index,(p:ℝ) ≤ Real.exp B) :
    nearCorruptMass D h ℓ K t ≤
      divisorPathTemplateMass S P (Specification.densitySize B C₀ h K) h ℓ K ⌈C₀*Real.log B⌉₊ t := by
  let cert := fun w : {w : NumericalLine D h ℓ // w.ManyShortCorrupted K t} =>
    Classical.choice (w.val.shortCorruptSelection_exists K t w.property)
  let f := fun w : {w : NumericalLine D h ℓ // w.ManyShortCorrupted K t} => (cert w).encode
  have hinj : Function.Injective f := by
    intro w v he
    apply Subtype.ext
    apply basicCode_injective
    have hdec := congrArg DivisorPathFilling.decode he
    simpa only [f,ShortCorruptSelection.decode_encode] using hdec
  rw [←DivisorPathFilling.sum_weight]
  calc
    _ = ∑ z ∈ univ.image f,z.weight P (Specification.densitySize B C₀ h K) := by
      rw [sum_image (fun w _ v _ he => hinj he)]
      exact sum_congr rfl (fun w hw => ((cert w).weight_encode P hB hS).symm)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun z hz hn => z.weight_nonneg _ _)

def nearCorruptSum {T : ℝ} (D : S.DivisorFamily B τ C₀) (h ℓ L K t : ℕ)
    (cut : S.Cutoffs T) : ℝ :=
  ∑ w : NumericalLine D h ℓ,avg (fun r : S.Residues =>
    if w.ManyShortCorrupted K t then |S.chronologicalKernel w.line cut r*allowedIndicator w.line D L r| else 0)

lemma nearCorruptSum_le_mass {T : ℝ} (cut : S.Cutoffs T) :
    nearCorruptSum D h ℓ L K t cut ≤
      (A^(ℓ*⌈C₀*Real.log B⌉₊)*((ℓ:ℝ)+2)^(ℓ*⌈C₀*Real.log B⌉₊))*nearCorruptMass D h ℓ K t := by
  unfold nearCorruptSum nearCorruptMass
  rw [mul_sum,GlobalRecord.subtype_sum_as_ite (fun w : NumericalLine D h ℓ => w.ManyShortCorrupted K t)
    (fun w => (A^(ℓ*⌈C₀*Real.log B⌉₊)*((ℓ:ℝ)+2)^(ℓ*⌈C₀*Real.log B⌉₊))*w.lineReciprocalWeight)]
  apply sum_le_sum
  intro w hw
  by_cases hm : w.ManyShortCorrupted K t
  · simp only [hm,ite_true]
    exact w.line_absolute_integral cut
  · simp only [hm,ite_false]
    simp [avg]

theorem nearCorruptSum_bound {T : ℝ} (cut : S.Cutoffs T) (P : ℝ)
    (hP : 0<P) (hB : 0≤B)
    (hS : ∀ p : S.Index,P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp B) :
    nearCorruptSum D h ℓ L K t cut ≤ packedGapPrefactor S ℓ K ⌈C₀*Real.log B⌉₊ t *
      (max (Specification.densitySize B C₀ h K/(P*Real.log 2)) ((2+B)/P))^t := by
  apply (nearCorruptSum_le_mass cut).trans
  have hb := (nearCorruptMass_le_templateMass (D:=D) (h:=h) (ℓ:=ℓ) (K:=K) (t:=t) P hB (fun p => (hS p).2)).trans
    (divisorPathTemplateMass_le S P B _ h ℓ K ⌈C₀*Real.log B⌉₊ t hP hB Specification.densitySize_nonneg hS)
  have hc := mul_le_mul_of_nonneg_left hb (by positivity [A_pos] : 0≤A^(ℓ*⌈C₀*Real.log B⌉₊)*((ℓ:ℝ)+2)^(ℓ*⌈C₀*Real.log B⌉₊))
  simpa only [packedGapPrefactor,mul_assoc] using hc

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
