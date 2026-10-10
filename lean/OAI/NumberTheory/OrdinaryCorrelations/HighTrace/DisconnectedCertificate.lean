import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AllCoreLit
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FarFilling
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DisconnectedWitness
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SelectedUsed

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
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L t u R : ℕ}
namespace NumericalLine
variable (w : NumericalLine D h ℓ) (hh : 0<h)
structure DisconnectedCertificate (L t R : ℕ) where
  residues : S.FixedResidues w.line
  cuts : Finset (Fin ℓ)
  gap_cut : ∀ (P : TreePath w L) (p : S.FixedIndex w.line),P.IsGap residues p → ∃ i,P.edge i ∈ cuts
  blocks : DisconnectedBlockPair w hh residues cuts L
  gates : blocks.GateSelection
  paths : gates.PathData
  order : gates.OrderedSelection t
  prime_not_div : ∀ p : blocks.selected,¬(p.val.val:ℕ) ∣ h
  root_small : paths.rootOffset.natAbs ≤ R

lemma disconnectedCertificate_exists (a : S.FixedResidues w.line)
    (hL : 0<L) (ht : 0<t) (hc : AllCoreLit w.line a)
    (hu : repeatedCenterUnlitCount w.line a<u) (hpack : ¬Nonempty (GapFamily w a L u))
    (hph : ∀ p : S.Index,¬(p:ℕ) ∣ h)
    (hm : ((2*ℓ)/L+6*u+1)^2*((2*⌈C₀*Real.log B⌉₊+1)*t)^8 ≤ disconnectedCount w.line hh a)
    (hτ : 0≤τ) (hℓ : (ℓ:ℝ) ≤ 2*B) :
    Nonempty (w.DisconnectedCertificate hh L t (farRootBudget B C₀ τ h)) := by
  let Q := ((2*ℓ)/L+6*u+1)^2
  let J := ⌈C₀*Real.log B⌉₊
  let n := (2*J+1)*t
  have hQ : 0<Q := by positivity
  have hn : 0<n := Nat.mul_pos (by omega) ht
  have hd : 0<disconnectedCount w.line hh a := (Nat.mul_pos hQ (pow_pos hn _)).trans_le hm
  obtain ⟨H,hH,hcard,huncut,hcut⟩ := w.forest_cuts hh a hc hu hpack
  obtain ⟨F,hF⟩ := disconnected_block_pair_exists w hh a H hL hd
  have hF' : disconnectedCount w.line hh a ≤ Q*F.selected.card :=
    hF.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 2))
  have hsel : n^8 ≤ F.selected.card := Nat.le_of_mul_le_mul_left (hm.trans hF') hQ
  have hne : F.selected.Nonempty := card_pos.mp ((pow_pos hn _).trans_le hsel)
  obtain ⟨g,hg⟩ := F.gateSelection_exists hcut (fun p => hph p.val.val) hne n hsel
  have ht' : t ≤ g.selected.card := Nat.le_of_mul_le_mul_left hg (by positivity : 0<2*J+1)
  obtain ⟨d⟩ := g.pathData_exists huncut hcut (fun p => hph p.val.val)
  obtain ⟨s⟩ := g.orderedSelection_exists ht'
  exact ⟨⟨a,H,hcut,F,g,d,s,(fun p => hph p.val.val),d.root_bound hτ hℓ⟩⟩

namespace DisconnectedCertificate
variable {w hh} (s : w.DisconnectedCertificate hh L t R)
def encode : FarFilling S h ℓ L ⌈C₀*Real.log B⌉₊ t R :=
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
  rw [ite_eq_left (s.paths.template_admissible s.order s.root_small s.gap_cut s.prime_not_div P hτ hℓ)]
  exact (weight_identity w.linePrimeCode (fun p => (p:ℝ)⁻¹)).symm
end DisconnectedCertificate

def disconnectedCertificateMass (D : S.DivisorFamily B τ C₀) (hh : 0<h) (ℓ L t R : ℕ) : ℝ :=
  ∑ w : {w : NumericalLine D h ℓ // Nonempty (w.DisconnectedCertificate hh L t R)},w.val.lineReciprocalWeight

lemma disconnectedCertificateMass_le_templateMass (P : ℝ) (hτ : 0≤τ) (hℓ : (ℓ:ℝ) ≤ 2*B) :
    disconnectedCertificateMass D hh ℓ L t R ≤ farTemplateMass S P (farTestSize B C₀ τ h) h ℓ L ⌈C₀*Real.log B⌉₊ t R := by
  let cert := fun w : {w : NumericalLine D h ℓ // Nonempty (w.DisconnectedCertificate hh L t R)} =>
    Classical.choice w.property
  let f := fun w : {w : NumericalLine D h ℓ // Nonempty (w.DisconnectedCertificate hh L t R)} => (cert w).encode
  have hinj : Function.Injective f := by
    intro w v he
    apply Subtype.ext
    apply basicCode_injective
    have hdec := congrArg FarFilling.decode he
    simpa only [f,DisconnectedCertificate.decode_encode] using hdec
  rw [←FarFilling.sum_weight]
  calc
    _ = ∑ z ∈ univ.image f,z.weight P (farTestSize B C₀ τ h) := by
      rw [sum_image (fun _ _ _ _ he => hinj he)]
      exact sum_congr rfl (fun w _ => ((cert w).weight_encode P hτ hℓ).symm)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun z _ _ => z.weight_nonneg _ _)

def disconnectedCertificateSum {T : ℝ} (D : S.DivisorFamily B τ C₀) (hh : 0<h)
    (ℓ L t R : ℕ) (cut : S.Cutoffs T) : ℝ :=
  ∑ w : NumericalLine D h ℓ,avg (fun r : S.Residues =>
    if Nonempty (w.DisconnectedCertificate hh L t R) then
      |S.chronologicalKernel w.line cut r*allowedIndicator w.line D L r| else 0)
lemma disconnectedCertificateSum_le_mass {T : ℝ} (cut : S.Cutoffs T) :
    disconnectedCertificateSum D hh ℓ L t R cut ≤
      (A^(ℓ*⌈C₀*Real.log B⌉₊)*((ℓ:ℝ)+2)^(ℓ*⌈C₀*Real.log B⌉₊))*disconnectedCertificateMass D hh ℓ L t R := by
  unfold disconnectedCertificateSum disconnectedCertificateMass
  rw [mul_sum,GlobalRecord.subtype_sum_as_ite
    (fun w : NumericalLine D h ℓ => Nonempty (w.DisconnectedCertificate hh L t R))
    (fun w => (A^(ℓ*⌈C₀*Real.log B⌉₊)*((ℓ:ℝ)+2)^(ℓ*⌈C₀*Real.log B⌉₊))*w.lineReciprocalWeight)]
  apply sum_le_sum
  intro w _
  by_cases hm : Nonempty (w.DisconnectedCertificate hh L t R)
  · simp only [hm,ite_true]
    exact w.line_absolute_integral cut
  · simp only [hm,ite_false]
    simp [avg]

theorem disconnectedCertificateSum_bound {T : ℝ} (cut : S.Cutoffs T) (P : ℝ)
    (hP : 0<P) (hB : 0≤B) (hτ : 0≤τ) (hℓ : (ℓ:ℝ) ≤ 2*B)
    (hS : ∀ p : S.Index,P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp B) :
    disconnectedCertificateSum D hh ℓ L t R cut ≤ ((2*R+1:ℕ):ℝ)*
      packedGapPrefactor S ℓ (L+L) ⌈C₀*Real.log B⌉₊ t *
      (max (farTestSize B C₀ τ h/(P*Real.log 2)) ((2+B)/P))^t := by
  apply (disconnectedCertificateSum_le_mass hh cut).trans
  have hb := (disconnectedCertificateMass_le_templateMass (D:=D) (ℓ:=ℓ) (L:=L) (t:=t) (R:=R) hh P hτ hℓ).trans
    (farTemplateMass_le S P B _ h ℓ L ⌈C₀*Real.log B⌉₊ t R hP hB farTestSize_nonneg hS)
  have hc := mul_le_mul_of_nonneg_left hb (by positivity [A_pos] : 0≤A^(ℓ*⌈C₀*Real.log B⌉₊)*((ℓ:ℝ)+2)^(ℓ*⌈C₀*Real.log B⌉₊))
  convert hc using 1
  unfold packedGapPrefactor
  ring

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
