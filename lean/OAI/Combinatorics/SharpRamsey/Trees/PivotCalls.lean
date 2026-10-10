import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.ReadyTests

namespace OAI

section
namespace SharpLogRamsey.ReadyTests
open Finset Real Incidence Validation Selection PivotGeometry GeometricCover ProjectiveDuality
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

def firstCall (A U W : Finset (Projectivization K V))
    (B UT : Finset (Projectivization K (Module.Dual K V)))
    (b : ℝ) (hB : B.Nonempty)
    (htrimB : (9/10:ℝ)*B.card ≤ (B∩UT).card)
    (hsource : ((A∩U)∩W).Nonempty)
    (hfrac : (A.card:ℝ) ≤ 2*((A∩U)∩W).card)
    (hratio : (W.card:ℝ) ≤ exp (b+log 1000000)*((A∩U)∩W).card)
    (hsparse : (incidenceCount A B:ℝ) ≤ (A.card:ℝ)*B.card/(40000*Nat.card K)) : Call A where
  source := (A∩U)∩W
  proposal := W
  targetOriginal := B
  target := B∩UT
  domain := UT
  overhead := b+log 1000000
  source_nonempty := hsource
  source_original := inter_subset_left.trans inter_subset_left
  source_proposal := inter_subset_right
  target_nonempty := by
    have hBpos : (0:ℝ)<B.card := by exact_mod_cast card_pos.mpr hB
    exact card_pos.mp (by exact_mod_cast (by linarith : (0:ℝ)<(B∩UT).card))
  target_original := inter_subset_left
  target_domain := inter_subset_right
  target_fraction := by linarith
  source_fraction := hfrac
  proposal_ratio := hratio
  sparse := hsparse

omit [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))] in
theorem firstCall_exists {n : ℕ}
    (A U : Finset (Projectivization K V))
    (B UT : Finset (Projectivization K (Module.Dual K V)))
    (b τ : ℝ) (hA : A.Nonempty) (hB : B.Nonempty) (hτ : 0 ≤ τ)
    (htrimA : (9/10:ℝ)*A.card ≤ (A∩U).card)
    (htrimB : (9/10:ℝ)*B.card ≤ (B∩UT).card)
    (hprod : (Nat.card K:ℝ)^(n+3)*exp (-b) ≤ (A.card:ℝ)*B.card)
    (hsp : (incidenceCount A B:ℝ) ≤ τ*(A.card:ℝ)*B.card/Nat.card K)
    (hsparse : (incidenceCount A B:ℝ) ≤ (A.card:ℝ)*B.card/(40000*Nat.card K))
    (P H : ℝ)
    (hlib : Validated (Nat.card K) P H (n+3) U UT (A∩U).card (B∩UT).card (4*τ)) :
    ∃ c : Call A, c.source = (A∩U)∩c.proposal ∧ c.proposal ⊆ U ∧
      c.targetOriginal = B ∧ c.target = B∩UT ∧ c.domain = UT ∧
      c.overhead = b+log 1000000 ∧
      (c.proposal.card:ℝ) ≤ 100000*(Nat.card K:ℝ)^(n+3)/(B∩UT).card := by
  obtain ⟨F,hF,hcapture,_hsize⟩ := hlib
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.zero_lt_one.trans (Finite.one_lt_card (α:=K))
  obtain ⟨W,hW,hWU,hsource,hfrac,hratio⟩ := first_source A U B UT
    (Nat.card K) τ b (n+3) hA hB hq hτ htrimA htrimB hprod hsp F hF
    (by intro S T hSU hSn hTU hTt hst; exact hcapture S T hSU hSn hTU hTt hst)
  exact ⟨firstCall A U W B UT b hB htrimB hsource hfrac hratio hsparse,
    rfl,hWU,rfl,rfl,rfl,rfl,(hF W hW).2⟩

def Call.production {S : Finset (Projectivization K V)} (c : Call S) (n : ℕ) : ℝ :=
  let q : ℝ := Nat.card K
  let h := scheduleLength q c.domain.card c.target.card
  let m := scheduleCutoff q c.overhead h
  PublicTables.integral (rowLaw c.proposal (c.source_nonempty.mono c.source_proposal) h)
    (implementAccept c.source
      (GoodCap SharpLogRamsey.Incidence.Incident q c.domain c.target (2000*q^(n+3)/S.card)))
    (fun _ => 1) m

lemma Call.failure_bound {S : Finset (Projectivization K V)} (c : Call S)
    {n : ℕ} (hdim : Module.finrank K V = n+3) :
    1-c.production n ≤ exp (-(Nat.card K:ℝ)) := by
  have h := (scheduled_from_original hdim S c.source c.proposal
    (c.source_nonempty.mono c.source_original) c.source_nonempty
    c.source_original c.source_proposal c.targetOriginal c.target c.domain
    c.target_nonempty c.target_original c.target_domain c.target_fraction
    2 c.overhead (by norm_num) c.source_fraction c.proposal_ratio
    (by convert c.sparse using 1; ring)).2.1
  norm_num only [show (1000:ℝ)*2=2000 by norm_num] at h
  exact h

variable [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

def secondCall {n : ℕ} (hdim : Module.finrank K V=n+3)
    (A U W : Finset (Projectivization K V))
    (B UT : Finset (Projectivization K (Module.Dual K V)))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (htrimA : (9/10:ℝ)*A.card≤(A∩U).card)
    (htrimB : (9/10:ℝ)*B.card≤(B∩UT).card)
    (b : ℝ) (hprod : (Nat.card K:ℝ)^(n+3)*exp (-b)≤(A.card:ℝ)*B.card)
    (hsparse : (incidenceCount A B:ℝ)≤(A.card:ℝ)*B.card/(40000*Nat.card K))
    {h m : ℕ} (table : PublicTables.Table (Fin h→Projectivization K V) m) (i : Fin m)
    (hi : PublicTables.firstIndex (implementAccept ((A∩U)∩W)
      (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K) UT (B∩UT)
        (2000*(Nat.card K:ℝ)^(n+3)/A.card))) m table=some i) : Call B := by
  let e := bidual (K:=K) (V:=V)
  let capB := cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT (PublicTables.rowAt m table i)
  let sourceB := (B∩UT)∩capB
  have hd := second_scheduled hdim A U W B UT hA hB htrimA htrimB b hprod hsparse table i hi
  dsimp only at hd
  have hAa : (A.image e).card=A.card := card_image_of_injective _ e.injective
  have hTa : ((A∩U).image e).card=(A∩U).card := card_image_of_injective _ e.injective
  refine {
    source := sourceB
    proposal := capB
    targetOriginal := A.image e
    target := (A∩U).image e
    domain := U.image e
    overhead := b+log 1000000
    source_nonempty := hd.1
    source_original := inter_subset_left.trans inter_subset_left
    source_proposal := inter_subset_right
    target_nonempty := ?_
    target_original := image_subset_image inter_subset_left
    target_domain := image_subset_image inter_subset_right
    target_fraction := ?_
    source_fraction := hd.2.1
    proposal_ratio := hd.2.2.1
    sparse := ?_ }
  · have hAp : (0:ℝ)<A.card := by exact_mod_cast card_pos.mpr hA
    exact (card_pos.mp (by exact_mod_cast (by linarith : (0:ℝ)<(A∩U).card))).image e
  · rw [hAa,hTa]
    linarith
  · rw [incidenceCount_bidual,hAa]
    convert hsparse using 1
    ring

end
end SharpLogRamsey.ReadyTests

end

end OAI
