import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.TableCompositions

namespace OAI

section
namespace SharpLogRamsey.PivotGeometry
open Finset Real Incidence Validation ProjectiveDuality PublicTables
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

def reverseLength (A U : Finset (Projectivization K V)) : ℕ :=
  scheduleLength (Nat.card K) (U.image (bidual (K:=K) (V:=V))).card
    ((A∩U).image (bidual (K:=K) (V:=V))).card

def reverseIntegral {h : ℕ} (n : ℕ)
    (A U : Finset (Projectivization K V))
    (B UT : Finset (Projectivization K (Module.Dual K V)))
    (b : ℝ) (z : Fin h→Projectivization K V)
    (f : (Fin (reverseLength A U)→Projectivization K (Module.Dual K V))→ℝ) : ℝ :=
  let q : ℝ := Nat.card K
  let e := bidual (K:=K) (V:=V)
  let capB := cap SharpLogRamsey.Incidence.Incident q UT z
  if hc : capB.Nonempty then
    integral (rowLaw capB hc (reverseLength A U))
      (implementAccept ((B∩UT)∩capB)
        (GoodCap SharpLogRamsey.Incidence.Incident q (U.image e) ((A∩U).image e) (2000*q^(n+3)/B.card)))
      f (scheduleCutoff q (b+log 1000000) (reverseLength A U))
  else 0

theorem reverse_good {n h : ℕ} (hdim : Module.finrank K V=n+3)
    (A U W : Finset (Projectivization K V))
    (B UT : Finset (Projectivization K (Module.Dual K V)))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (htrimA : (9/10:ℝ)*A.card≤(A∩U).card)
    (htrimB : (9/10:ℝ)*B.card≤(B∩UT).card)
    (b : ℝ) (hprod : (Nat.card K:ℝ)^(n+3)*exp (-b)≤(A.card:ℝ)*B.card)
    (hsparse : (incidenceCount A B:ℝ)≤(A.card:ℝ)*B.card/(40000*Nat.card K))
    (z : Fin h→Projectivization K V)
    (hz : implementAccept ((A∩U)∩W)
      (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K) UT (B∩UT) (2000*(Nat.card K:ℝ)^(n+3)/A.card)) z) :
    1-reverseIntegral n A U B UT b z (fun _ => 1)≤ exp (-(Nat.card K:ℝ)) ∧
    ∀ y,reverseIntegral n A U B UT b z
      (fun u => if ¬pass SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) u y then 1 else 0)≤
        12*(Nat.card K:ℝ)*(∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass B x) := by
  let M := 2000*(Nat.card K:ℝ)^(n+3)/A.card
  let accept : (Fin h→Projectivization K V)→Prop :=
    implementAccept ((A∩U)∩W) (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT (B∩UT) M)
  have hi : firstIndex accept 1 (z,PUnit.unit)=some 0 := by
    simp only [firstIndex]
    rw [ite_eq_left hz]
  have hh := second_scheduled (h:=h) (m:=1) hdim A U W B UT hA hB htrimA htrimB b hprod hsparse
    (z,PUnit.unit) 0 hi
  dsimp only [rowAt] at hh
  simp only [Fin.cases_zero] at hh
  have hc : (cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT z).Nonempty :=
    hh.1.mono (inter_subset_right)
  have hf := (hh.2.2.2 hc).2
  simp only [reverseIntegral,dite_eq_left hc,reverseLength]
  with_unfolding_all exact hf

theorem fresh_pair {n : ℕ} (hdim : Module.finrank K V=n+3)
    (A U W : Finset (Projectivization K V))
    (B UT : Finset (Projectivization K (Module.Dual K V)))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hX : ((A∩U)∩W).Nonempty)
    (htrimA : (9/10:ℝ)*A.card≤(A∩U).card)
    (htrimB : (9/10:ℝ)*B.card≤(B∩UT).card)
    (b : ℝ) (hprod : (Nat.card K:ℝ)^(n+3)*exp (-b)≤(A.card:ℝ)*B.card)
    (hsparse : (incidenceCount A B:ℝ)≤(A.card:ℝ)*B.card/(40000*Nat.card K))
    (hsource : (A.card:ℝ)≤2*((A∩U)∩W).card)
    (hratio : (W.card:ℝ)≤ exp (b+log 1000000)*((A∩U)∩W).card) :
    let q : ℝ := Nat.card K
    let h := scheduleLength q UT.card (B∩UT).card
    let m := scheduleCutoff q (b+log 1000000) h
    let accept := implementAccept ((A∩U)∩W)
      (GoodCap SharpLogRamsey.Incidence.Incident q UT (B∩UT) (2000*q^(n+3)/A.card))
    let p := rowLaw W (hX.mono inter_subset_right) h
    1-integral p accept (fun z => reverseIntegral n A U B UT b z (fun _ => 1)) m≤2*exp (-q) ∧
    (∀ y,integral p accept (fun z => if ¬pass SharpLogRamsey.Incidence.Incident q z y then 1 else 0) m≤
      12*q*(∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass A x)) ∧
    ∀ y,integral p accept (fun z => reverseIntegral n A U B UT b z
      (fun u => if ¬pass SharpLogRamsey.Incidence.Incident q u y then 1 else 0)) m≤
      12*q*(∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass B x) := by
  dsimp only
  have hBpos : (0:ℝ)<B.card := by exact_mod_cast card_pos.mpr hB
  have hBT : (B∩UT).Nonempty := card_pos.mp (by exact_mod_cast (by linarith : (0:ℝ)<(B∩UT).card))
  have hf := scheduled_from_original hdim A ((A∩U)∩W) W hA hX
    (inter_subset_left.trans inter_subset_left) inter_subset_right
    B (B∩UT) UT hBT inter_subset_left inter_subset_right (by linarith)
    2 (b+log 1000000) (by norm_num) hsource hratio
    (by convert hsparse using 1; ring)
  dsimp only at hf
  norm_num only [show (1000:ℝ)*2=2000 by norm_num,
    show (6:ℝ)*2=12 by norm_num] at hf
  have hg := reverse_good (h:=scheduleLength (Nat.card K:ℝ) UT.card (B∩UT).card)
    hdim A U W B UT hA hB htrimA htrimB b hprod hsparse
  refine ⟨?_,hf.2.2,?_⟩
  · have hh := two_stage_failure _ _ _ _ (exp (-(Nat.card K:ℝ))) (exp (-(Nat.card K:ℝ)))
      (exp_pos _).le hf.2.1 (fun z hz => (hg z hz).1)
    linarith
  · intro y
    apply integral_bounded
    · apply mul_nonneg (by positivity)
      exact sum_nonneg (fun x _ => uniform_nonneg B x)
    · intro z hz
      exact (hg z hz).2 y

end
end SharpLogRamsey.PivotGeometry

end

end OAI
