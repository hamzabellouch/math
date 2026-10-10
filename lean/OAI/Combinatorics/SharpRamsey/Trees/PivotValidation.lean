import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.PivotDomains

namespace OAI

section
namespace SharpLogRamsey.PivotGeometry
open Finset Real Incidence Validation GeometricCover ProjectiveDuality
open scoped Classical BigOperators
noncomputable section

lemma second_ratio {w Q A B X b : ℝ} (hA : 0<A) (hX : 0≤ X)
    (hprod : Q*exp (-b)≤ A*B) (hsource : B≤2*X) (hW : w≤2000*Q/A) :
    w≤ exp (b+log 1000000)*X := by
  have hp : Q≤ A*B*exp b := by
    simpa only [mul_assoc, ←exp_add, neg_add_cancel, exp_zero, mul_one] using
      mul_le_mul_of_nonneg_right hprod (exp_pos b).le
  calc
    w ≤ 2000*Q/A := hW
    _ ≤ 2000*(A*B*exp b)/A := by gcongr
    _ = 2000*B*exp b := by field_simp
    _ ≤ 4000*X*exp b := by nlinarith [mul_le_mul_of_nonneg_right hsource (show 0≤2000*exp b by positivity)]
    _ ≤ 1000000*X*exp b := by gcongr; norm_num
    _ = _ := by rw [exp_add,exp_log (by norm_num : (0:ℝ)<1000000)]; ring

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

theorem second_scheduled {n : ℕ} (hdim : Module.finrank K V=n+3)
    (A U W : Finset (Projectivization K V))
    (B UT : Finset (Projectivization K (Module.Dual K V)))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (htrimA : (9/10:ℝ)*A.card≤(A∩U).card)
    (htrimB : (9/10:ℝ)*B.card≤(B∩UT).card)
    (b : ℝ) (hprod : (Nat.card K:ℝ)^(n+3)*exp (-b)≤(A.card:ℝ)*B.card)
    (hsparse : (incidenceCount A B:ℝ)≤(A.card:ℝ)*B.card/(40000*Nat.card K))
    {h m : ℕ} (table : PublicTables.Table (Fin h→Projectivization K V) m) (i : Fin m)
    (hi : PublicTables.firstIndex (implementAccept ((A∩U)∩W)
      (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K) UT (B∩UT) (2000*(Nat.card K:ℝ)^(n+3)/A.card))) m table=some i) :
    let q : ℝ := Nat.card K
    let e := bidual (K:=K) (V:=V)
    let capB := cap SharpLogRamsey.Incidence.Incident q UT (PublicTables.rowAt m table i)
    let sourceB := (B∩UT)∩capB
    let targetA := (A∩U).image e
    let domainA := U.image e
    let h' := scheduleLength q domainA.card targetA.card
    let m' := scheduleCutoff q (b+log 1000000) h'
    let M' := 2000*q^(n+3)/B.card
    sourceB.Nonempty ∧ (B.card:ℝ)≤2*sourceB.card ∧
    (capB.card:ℝ)≤ exp (b+log 1000000)*sourceB.card ∧
    ∀ hcapB : capB.Nonempty,
      (9/10:ℝ)≤ prob (uniformMass sourceB) h' (GoodCap SharpLogRamsey.Incidence.Incident q domainA targetA M') ∧
      1-PublicTables.integral (rowLaw capB hcapB h')
        (implementAccept sourceB (GoodCap SharpLogRamsey.Incidence.Incident q domainA targetA M')) (fun _ => 1) m'≤ exp (-q) ∧
      ∀ y,PublicTables.integral (rowLaw capB hcapB h')
        (implementAccept sourceB (GoodCap SharpLogRamsey.Incidence.Incident q domainA targetA M'))
        (fun z => if ¬pass SharpLogRamsey.Incidence.Incident q z y then 1 else 0) m'≤
          12*q*(∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass B x) := by
  dsimp only
  let e := bidual (K:=K) (V:=V)
  let capB := cap SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT (PublicTables.rowAt m table i)
  let sourceB := (B∩UT)∩capB
  have hd := decoded_cap ((A∩U)∩W) SharpLogRamsey.Incidence.Incident (Nat.card K:ℝ) UT (B∩UT)
    inter_subset_right (2000*(Nat.card K:ℝ)^(n+3)/A.card) h m table i hi
  have hs := second_source B (B∩UT) capB hB htrimB hd.2.2
  have hApos : (0:ℝ)<A.card := by exact_mod_cast card_pos.mpr hA
  have hA' : (A∩U).Nonempty := card_pos.mp (by exact_mod_cast (by linarith : (0:ℝ)<(A∩U).card))
  have hratio := second_ratio hApos (Nat.cast_nonneg sourceB.card) hprod hs.2 hd.2.1
  refine ⟨hs.1,hs.2,hratio,?_⟩
  intro hcapB
  have hdu : Module.finrank K (Module.Dual K V)=n+3 := Subspace.dual_finrank_eq.trans hdim
  have hAa : (A.image e).card=A.card := card_image_of_injective _ e.injective
  have hTa : ((A∩U).image e).card=(A∩U).card := card_image_of_injective _ e.injective
  have hsp : (incidenceCount B (A.image e):ℝ)≤(B.card:ℝ)*(A.image e).card/(20000*2*Nat.card K) := by
    rw [incidenceCount_bidual,hAa]
    convert hsparse using 1; ring
  have hh := scheduled_from_original hdu B sourceB capB hB hs.1
    (inter_subset_left.trans inter_subset_left) inter_subset_right
    (A.image e) ((A∩U).image e) (U.image e) (hA'.image e)
    (image_subset_image inter_subset_left) (image_subset_image inter_subset_right)
    (by rw [hAa,hTa]; linarith) 2 (b+log 1000000) (by norm_num) hs.2 hratio hsp
  dsimp only at hh
  norm_num only [show (1000:ℝ)*2=2000 by norm_num,
    show (6:ℝ)*2=12 by norm_num] at hh
  exact hh

end
end SharpLogRamsey.PivotGeometry

end

end OAI
