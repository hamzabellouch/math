import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesBasic
import OAI.NumberTheory.Ostmann.Construction.HistoryGiantGuard

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction HistorySignedDecode

def divisorProduct : {l : ℕ} → History l → ℤ
  | _,.leaf _ => 1
  | _,.node a _ u _ _ left right =>
      (a.frequency*((u.map SmallSlot.value).prod:ℤ))*divisorProduct left*divisorProduct right

theorem DivisorData.mono {R S : ℤ} {l : ℕ} {h : History l}
    (hd : DivisorData R h) (hRS : R ∣ S) : DivisorData S h := by
  induction h with
  | leaf a => trivial
  | node a p u hp hm left right il ir =>
    exact ⟨hd.1,hd.2.1.trans hRS,il hd.2.2.1,ir hd.2.2.2⟩

theorem divisorProduct_ne_zero {l : ℕ} (h : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) : divisorProduct h ≠ 0 := by
  induction h with
  | leaf a => exact one_ne_zero
  | node a p u hp hm left right il ir =>
    have hu : ((u.map SmallSlot.value).prod:ℤ)≠0 := by
      exact_mod_cast (History.supported_compensation_product_pos hs).ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (History.supported_root_frequency_ne_zero hs) hu)
      (il (History.supported_left hs))) (ir (History.supported_right hs))

theorem divisorData_actual {l : ℕ} (h : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) : DivisorData (divisorProduct h) h := by
  induction h with
  | leaf a => trivial
  | node a p u hp hm left right il ir =>
    have hu : ((u.map SmallSlot.value).prod:ℤ)≠0 := by
      exact_mod_cast (History.supported_compensation_product_pos hs).ne'
    refine ⟨mul_ne_zero (History.supported_root_frequency_ne_zero hs) hu,?_,?_,?_⟩
    · change _ ∣ (_*divisorProduct left)*divisorProduct right
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    · apply (il (History.supported_left hs)).mono
      exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    · apply (ir (History.supported_right hs)).mono
      exact dvd_mul_left _ _

def pairedDivisorProduct {l : ℕ} (h k : History l) : ℤ := divisorProduct h*divisorProduct k

theorem pairedDivisorProduct_ne_zero {l : ℕ} (h k : History l)
    {V : ℕ → ℕ} {outside : List ℕ} (hs : h.Supported V outside) (ks : k.Supported V outside) :
    pairedDivisorProduct h k ≠ 0 :=
  mul_ne_zero (divisorProduct_ne_zero h hs) (divisorProduct_ne_zero k ks)

theorem paired_divisorData {l : ℕ} (h k : History l)
    {V : ℕ → ℕ} {outside : List ℕ} (hs : h.Supported V outside) (ks : k.Supported V outside) :
    DivisorData (pairedDivisorProduct h k) h ∧ DivisorData (pairedDivisorProduct h k) k :=
  ⟨(divisorData_actual h hs).mono (dvd_mul_right _ _),
    (divisorData_actual k ks).mono (dvd_mul_left _ _)⟩

theorem paired_rebuild_congruent {l : ℕ} (h k : History l)
    {V : ℕ → ℕ} {outside : List ℕ} (hs : h.Supported V outside) (ks : k.Supported V outside)
    (N Xp Xm Yp Ym : ℤ)
    (hp : Xp ≡ Yp [ZMOD (pairedDivisorProduct h k)^l*N])
    (hm : Xm ≡ Ym [ZMOD (pairedDivisorProduct h k)^l*N]) :
    Congruent N (rebuild h Xp Xm) (rebuild h Yp Ym) ∧
      Congruent N (rebuild k Xp Xm) (rebuild k Yp Ym) :=
  ⟨rebuild_congruent h _ N Xp Xm Yp Ym (paired_divisorData h k hs ks).1 hp hm,
    rebuild_congruent k _ N Xp Xm Yp Ym (paired_divisorData h k hs ks).2 hp hm⟩

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
