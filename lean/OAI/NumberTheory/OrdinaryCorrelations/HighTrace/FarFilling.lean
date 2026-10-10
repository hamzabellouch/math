import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RootCode

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
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L K t J R : ℕ}

abbrev FarFilling (S : PrimeSystem) (h ℓ K J t R : ℕ) :=
  (m : Fin (ℓ*J+1)) × (GoodFarTemplate h ℓ K J t m.val R × (Fin m.val → S.Index))
namespace FarFilling
def weight (z : FarFilling S h ℓ K J t R) (P Z : ℝ) : ℝ :=
  (z.2.1.val.system h z.2.1.property).fiberWeight P Z (fun a => (z.2.2 a:ℕ))
lemma weight_nonneg (z : FarFilling S h ℓ K J t R) (P Z : ℝ) : 0≤z.weight P Z :=
  TriangularExpressions.fiberWeight_nonneg ..
def decode (z : FarFilling S h ℓ K J t R) :
    (Fin ℓ → Bool) × (Fin ℓ × Fin J → Option S.Index) :=
  (z.2.1.val.2.1,fun s => (z.2.1.val.2.2.1 s).map z.2.2)
lemma sum_weight (P Z : ℝ) :
    (∑ z : FarFilling S h ℓ K J t R,z.weight P Z)=farTemplateMass S P Z h ℓ K J t R := by
  unfold farTemplateMass
  rw [Fintype.sum_sigma]
  exact sum_congr rfl (fun m hm => Fintype.sum_prod_type _)
end FarFilling

namespace NumericalLine
variable (w : NumericalLine D h ℓ) (hh : 0<h)
structure FarCertificate (K t R : ℕ) where
  blocks : FarBlockPair w hh K
  paths : blocks.PathData
  order : blocks.OrderedSelection t
  root_small : paths.rootOffset.natAbs ≤ R

def ManyFarCorrupted (K t : ℕ) : Prop := ((2*ℓ)/K+1)^2*t ≤ (farCorrupted w K).card

lemma farCertificate_exists (hK : 0<K) (ht : 0<t) (hm : w.ManyFarCorrupted K t)
    (hτ : 0≤τ) (hℓ : (ℓ:ℝ) ≤ 2*B) :
    Nonempty (w.FarCertificate hh K t (farRootBudget B C₀ τ h)) := by
  have hQ : 0<((2*ℓ)/K+1)^2 := by positivity
  have ha : (farCorrupted w K).Nonempty := card_pos.mp ((Nat.mul_pos hQ ht).trans_le hm)
  obtain ⟨F,hF⟩ := far_block_pair_exists w hh hK ha
  have hsel : t ≤ F.selected.card := Nat.le_of_mul_le_mul_left (hm.trans hF) hQ
  have hfne : F.selected.Nonempty := card_pos.mp (ht.trans_le hsel)
  obtain ⟨d⟩ := F.pathData_exists hfne
  obtain ⟨s⟩ := F.orderedSelection_exists hsel
  exact ⟨⟨F,d,s,d.root_bound hτ hℓ⟩⟩

namespace FarCertificate
variable {w hh} (s : w.FarCertificate hh K t R)
def encode : FarFilling S h ℓ K ⌈C₀*Real.log B⌉₊ t R :=
  ⟨⟨(support w.linePrimeCode).card,by
      have he := card_support_le w.linePrimeCode
      simp only [Fintype.card_prod,Fintype.card_fin] at he
      omega⟩,⟨s.paths.template s.order s.root_small,s.paths.formed s.order s.root_small⟩,values w.linePrimeCode⟩
lemma decode_encode : s.encode.decode=w.basicCode := by
  change (signBit w.line,fun a => (pattern w.linePrimeCode a).map (values w.linePrimeCode))=(signBit w.line,w.linePrimeCode)
  exact Prod.ext rfl (funext (decode_pattern w.linePrimeCode))
lemma weight_encode (P : ℝ) (hτ : 0≤τ) (hℓ : (ℓ:ℝ) ≤ 2*B) :
    s.encode.weight P (farTestSize B C₀ τ h)=w.lineReciprocalWeight := by
  change (if ((s.paths.template s.order s.root_small).system h (s.paths.formed s.order s.root_small)).Admissible P _
    (fun i => (values w.linePrimeCode i:ℕ)) then ∏ i,((values w.linePrimeCode i:ℕ):ℝ)⁻¹ else 0)=w.lineReciprocalWeight
  rw [ite_eq_left (s.paths.template_admissible s.order s.root_small P hτ hℓ)]
  exact (weight_identity w.linePrimeCode (fun p => (p:ℝ)⁻¹)).symm
end FarCertificate

def manyFarMass (D : S.DivisorFamily B τ C₀) (h ℓ K t : ℕ) : ℝ :=
  ∑ w : {w : NumericalLine D h ℓ // w.ManyFarCorrupted K t},w.val.lineReciprocalWeight

lemma manyFarMass_le_templateMass (hh : 0<h) (P : ℝ) (hK : 0<K) (ht : 0<t) (hτ : 0≤τ) (hℓ : (ℓ:ℝ) ≤ 2*B) :
    manyFarMass D h ℓ K t ≤ farTemplateMass S P (farTestSize B C₀ τ h) h ℓ K ⌈C₀*Real.log B⌉₊ t (farRootBudget B C₀ τ h) := by
  let cert := fun w : {w : NumericalLine D h ℓ // w.ManyFarCorrupted K t} =>
    Classical.choice (w.val.farCertificate_exists hh hK ht w.property hτ hℓ)
  let f := fun w : {w : NumericalLine D h ℓ // w.ManyFarCorrupted K t} => (cert w).encode
  have hinj : Function.Injective f := by
    intro w v he
    apply Subtype.ext
    apply basicCode_injective
    have hdec := congrArg FarFilling.decode he
    simpa only [f,FarCertificate.decode_encode] using hdec
  rw [←FarFilling.sum_weight]
  calc
    _ = ∑ z ∈ univ.image f,z.weight P (farTestSize B C₀ τ h) := by
      rw [sum_image (fun w _ v _ he => hinj he)]
      exact sum_congr rfl (fun w hw => ((cert w).weight_encode P hτ hℓ).symm)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun z hz hn => z.weight_nonneg _ _)

def manyFarSum {T : ℝ} (D : S.DivisorFamily B τ C₀) (h ℓ L K t : ℕ) (cut : S.Cutoffs T) : ℝ :=
  ∑ w : NumericalLine D h ℓ,avg (fun r : S.Residues =>
    if w.ManyFarCorrupted K t then |S.chronologicalKernel w.line cut r*allowedIndicator w.line D L r| else 0)

lemma manyFarSum_le_mass {T : ℝ} (cut : S.Cutoffs T) :
    manyFarSum D h ℓ L K t cut ≤
      (A^(ℓ*⌈C₀*Real.log B⌉₊)*((ℓ:ℝ)+2)^(ℓ*⌈C₀*Real.log B⌉₊))*manyFarMass D h ℓ K t := by
  unfold manyFarSum manyFarMass
  rw [mul_sum,GlobalRecord.subtype_sum_as_ite (fun w : NumericalLine D h ℓ => w.ManyFarCorrupted K t)
    (fun w => (A^(ℓ*⌈C₀*Real.log B⌉₊)*((ℓ:ℝ)+2)^(ℓ*⌈C₀*Real.log B⌉₊))*w.lineReciprocalWeight)]
  apply sum_le_sum
  intro w hw
  by_cases hm : w.ManyFarCorrupted K t
  · simp only [hm,ite_true]
    exact w.line_absolute_integral cut
  · simp only [hm,ite_false]
    simp [avg]

theorem manyFarSum_bound {T : ℝ} (hh : 0<h) (cut : S.Cutoffs T) (P : ℝ)
    (hP : 0<P) (hB : 0≤B) (hK : 0<K) (ht : 0<t) (hτ : 0≤τ) (hℓ : (ℓ:ℝ) ≤ 2*B)
    (hS : ∀ p : S.Index,P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp B) :
    manyFarSum D h ℓ L K t cut ≤ ((2*farRootBudget B C₀ τ h+1:ℕ):ℝ)*
      packedGapPrefactor S ℓ (K+K) ⌈C₀*Real.log B⌉₊ t *
      (max (farTestSize B C₀ τ h/(P*Real.log 2)) ((2+B)/P))^t := by
  apply (manyFarSum_le_mass cut).trans
  have hb := (manyFarMass_le_templateMass (D:=D) (h:=h) (ℓ:=ℓ) (K:=K) (t:=t) hh P hK ht hτ hℓ).trans
    (farTemplateMass_le S P B _ h ℓ K ⌈C₀*Real.log B⌉₊ t (farRootBudget B C₀ τ h) hP hB farTestSize_nonneg hS)
  have hc := mul_le_mul_of_nonneg_left hb (by positivity [A_pos] : 0≤A^(ℓ*⌈C₀*Real.log B⌉₊)*((ℓ:ℝ)+2)^(ℓ*⌈C₀*Real.log B⌉₊))
  convert hc using 1
  unfold packedGapPrefactor
  ring

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
