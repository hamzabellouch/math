import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GoodGapTemplate
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrimeIndex

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SharedSlotPatterns Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L t J : ℕ}

abbrev GapFilling (S : PrimeSystem) (h ℓ L J t : ℕ) :=
  (m : Fin (ℓ*J+1)) × (GoodGapTemplate h ℓ L J t m.val × (Fin m.val → S.Index))

namespace GapFilling

def weight (z : GapFilling S h ℓ L J t) (P : ℝ) : ℝ :=
  (z.2.1.val.system h z.2.1.property).fiberWeight P 0 (fun a => (z.2.2 a:ℕ))
lemma weight_nonneg (z : GapFilling S h ℓ L J t) (P : ℝ) : 0 ≤ z.weight P :=
  TriangularExpressions.fiberWeight_nonneg ..
def decode (z : GapFilling S h ℓ L J t) :
    (Fin ℓ → Bool) × (Fin ℓ × Fin J → Option S.Index) :=
  (z.2.1.val.1,fun s => (z.2.1.val.2.1 s).map z.2.2)
lemma sum_weight (P : ℝ) :
    (∑ z : GapFilling S h ℓ L J t,z.weight P)=gapTemplateMass S P h ℓ L J t := by
  unfold gapTemplateMass
  rw [Fintype.sum_sigma]
  exact sum_congr rfl (fun m hm => Fintype.sum_prod_type _)
end GapFilling

namespace NumericalLine
variable {w : NumericalLine D h ℓ} {P : ℝ}
namespace GapCertificate
variable (c : w.GapCertificate (L:=L) (t:=t) P)

def encode : GapFilling S h ℓ L ⌈C₀*Real.log B⌉₊ t :=
  ⟨⟨(support w.linePrimeCode).card,by
      have he := card_support_le w.linePrimeCode
      simp only [Fintype.card_prod,Fintype.card_fin] at he
      omega⟩,⟨c.code,c.formed⟩,values w.linePrimeCode⟩
lemma decode_encode : c.encode.decode=w.basicCode := by
  change (c.code.1,fun s => (c.code.2.1 s).map (values w.linePrimeCode))=(signBit w.line,w.linePrimeCode)
  rw [c.sign_eq,c.pattern_eq]
  exact Prod.ext rfl (funext (decode_pattern w.linePrimeCode))
lemma weight_encode : c.encode.weight P=w.lineReciprocalWeight := by
  change (if (c.code.system h c.formed).Admissible P 0 (fun i => (values w.linePrimeCode i:ℕ)) then
    ∏ i, ((values w.linePrimeCode i:ℕ):ℝ)⁻¹ else 0)=w.lineReciprocalWeight
  rw [ite_eq_left c.admissible]
  exact (weight_identity w.linePrimeCode (fun p => (p:ℝ)⁻¹)).symm
end GapCertificate

def packedGapMass (D : S.DivisorFamily B τ C₀) (h ℓ L t : ℕ) : ℝ :=
  ∑ w : {w : NumericalLine D h ℓ // w.PackedGaps L t},w.val.lineReciprocalWeight

theorem packedGapMass_le_templateMass (P : ℝ) (hP : ∀ p : S.Index,P ≤ (p:ℝ))
    (hh : ∀ p : S.Index, ¬(p:ℕ) ∣ h) :
    packedGapMass D h ℓ L t ≤ gapTemplateMass S P h ℓ L ⌈C₀*Real.log B⌉₊ t := by
  let cert := fun w : {w : NumericalLine D h ℓ // w.PackedGaps L t} =>
    Classical.choice (w.val.packed_gap_certificate P hP hh w.property)
  let f := fun w : {w : NumericalLine D h ℓ // w.PackedGaps L t} => (cert w).encode
  have hinj : Function.Injective f := by
    intro w v he
    apply Subtype.ext
    apply basicCode_injective
    have hdec := congrArg GapFilling.decode he
    simpa only [f,GapCertificate.decode_encode] using hdec
  rw [←GapFilling.sum_weight]
  calc
    _ = ∑ z ∈ univ.image f,z.weight P := by
      rw [sum_image (fun w _ v _ he => hinj he)]
      exact sum_congr rfl (fun w hw => (cert w).weight_encode.symm)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun z hz hn => z.weight_nonneg P)

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
