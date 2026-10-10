import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationModuli
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeSourceSeparationSelected

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkResidueCRT
open ResidueHaar HistoryCRTIntegration Construction HistoryRepresentativeSourceSeparation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def arrayEquiv {D R : ℕ} (hc : D.Coprime R) :
    (ι→(ZMod (D*R))ˣ) ≃ ((ι→(ZMod D)ˣ)×(ι→(ZMod R)ˣ)) :=
  (Equiv.piCongrRight (fun _ : ι=>(crtUnits hc).toEquiv)).trans
    (DiagonalSmallResidueNorm.pairPiEquiv (fun _ : ι=>(ZMod D)ˣ)
      (fun _ : ι=>(ZMod R)ˣ)).symm

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem arrayEquiv_left_coe {D R : ℕ} (hc : D.Coprime R)
    (x : ι→(ZMod (D*R))ˣ) (i : ι) :
    ((arrayEquiv hc x).1 i:ZMod D)=
      ZMod.castHom (Nat.dvd_mul_right D R) (ZMod D) (x i:ZMod (D*R)) := by
  change (ZMod.cast (x i : ZMod (D*R)) : ZMod D × ZMod R).1 = _
  exact Prod.fst_zmod_cast _

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem arrayEquiv_right_coe {D R : ℕ} (hc : D.Coprime R)
    (x : ι→(ZMod (D*R))ˣ) (i : ι) :
    ((arrayEquiv hc x).2 i:ZMod R)=
      ZMod.castHom (Nat.dvd_mul_left R D) (ZMod R) (x i:ZMod (D*R)) := by
  change (ZMod.cast (x i : ZMod (D*R)) : ZMod D × ZMod R).2 = _
  exact Prod.snd_zmod_cast _

theorem array_joint_average {D R : ℕ} [NeZero D] [NeZero R] (hc : D.Coprime R)
    (F : ((ι→(ZMod D)ˣ)×(ι→(ZMod R)ˣ))→ℂ) :
    average (fun x : ι→(ZMod (D*R))ˣ=>F (arrayEquiv hc x))=average F :=
  average_equiv (arrayEquiv hc) F

theorem array_product_average {D R : ℕ} [NeZero D] [NeZero R] (hc : D.Coprime R)
    (F : (ι→(ZMod D)ˣ)→ℂ) (G : (ι→(ZMod R)ˣ)→ℂ) :
    average (fun x : ι→(ZMod (D*R))ˣ=>F ((arrayEquiv hc x).1)*G ((arrayEquiv hc x).2))=
      average F*average G :=
  (array_joint_average hc (fun z=>F z.1*G z.2)).trans (average_product F G)

theorem actual_array_product_average {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (hp : ∀q∈outside,q.Prime) (n : ℕ)
    (F : (ι→(ZMod outside.prod)ˣ)→ℂ)
    (G : (ι→(ZMod (frequencyModulus h k n))ˣ)→ℂ) :
    letI : NeZero outside.prod := ⟨(outsideModulus_pos hp).ne'⟩
    letI : NeZero (frequencyModulus h k n) := ⟨(frequencyModulus_pos h k hs ks n).ne'⟩
    average (fun x : ι→(ZMod (outside.prod*frequencyModulus h k n))ˣ=>
      F ((arrayEquiv (had.2.2.2 n).2.2.2.1 x).1)*
      G ((arrayEquiv (had.2.2.2 n).2.2.2.1 x).2))=average F*average G := by
  let : NeZero outside.prod := ⟨(outsideModulus_pos hp).ne'⟩
  let : NeZero (frequencyModulus h k n) := ⟨(frequencyModulus_pos h k hs ks n).ne'⟩
  have hc : outside.prod.Coprime (frequencyModulus h k n) := (had.2.2.2 n).2.2.2.1
  exact array_product_average hc F G

end Ostmann.Arithmetic.HistoryBulkResidueCRT

end

end OAI
