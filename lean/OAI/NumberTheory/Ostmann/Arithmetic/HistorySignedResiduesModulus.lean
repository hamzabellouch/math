import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesTests

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction HistorySignedDecode HistorySignedSupportReduction

def testProduct : {l : ℕ} → History l → ℤ
  | _,.leaf a => a.frequency*((a.small.map SmallSlot.value).prod:ℤ)
  | _,h@(.node a _ u _ _ left right) =>
      h.frequencies.prod*((a.small.map SmallSlot.value).prod:ℤ)*
        ((a.frequency*((u.map SmallSlot.value).prod:ℤ))*
          ((u.map SmallSlot.value).prod:ℤ)^2*testProduct left*testProduct right)

theorem frequencies_rebuild {l : ℕ} (h : History l) (Xp Xm : ℤ) :
    frequencies (rebuild h Xp Xm)=h.frequencies := by
  induction h generalizing Xp Xm with
  | leaf a => rfl
  | node a p u hp hm left right il ir =>
    simp only [rebuild,frequencies,History.frequencies,il,ir]

theorem Covers.mono {N M : ℤ} {l : ℕ} {h : SignedHistory l}
    (hn : Covers N h) (hd : N ∣ M) : Covers M h := by
  induction h with
  | leaf a => exact ⟨fun v hv=>(hn.1 v hv).trans hd,
      fun q hq=>(hn.2.1 q hq).trans hd,trivial⟩
  | node a p u hp hm left right il ir =>
    exact ⟨fun v hv=>(hn.1 v hv).trans hd,
      fun q hq=>(hn.2.1 q hq).trans hd,hn.2.2.1.trans hd,
      fun q hq=>(hn.2.2.2.1 q hq).trans hd,
      il hn.2.2.2.2.1,ir hn.2.2.2.2.2⟩

theorem small_dvd_product {xs : List SmallSlot} {q : SmallSlot} (hq : q∈xs) :
    (q.value:ℤ) ∣ ((xs.map SmallSlot.value).prod:ℤ) := by
  exact_mod_cast List.dvd_prod (List.mem_map.mpr ⟨q,hq,rfl⟩)

theorem testProduct_covers_rebuild {l : ℕ} (h : History l) (Xp Xm : ℤ) :
    Covers (testProduct h) (rebuild h Xp Xm) := by
  induction h generalizing Xp Xm with
  | leaf a =>
    refine ⟨?_,?_,trivial⟩
    · intro v hv
      have he : v=a.frequency := by simpa only [rebuild,frequencies,List.mem_singleton] using hv
      subst v
      exact dvd_mul_right _ _
    · intro q hq
      exact dvd_mul_of_dvd_right (small_dvd_product hq) _
  | node a p u hp hm left right il ir =>
    let F := (History.node a p u hp hm left right).frequencies.prod
    let S := ((a.small.map SmallSlot.value).prod:ℤ)
    let U := ((u.map SmallSlot.value).prod:ℤ)
    let d := a.frequency*U
    have hleft : testProduct left ∣ testProduct (.node a p u hp hm left right) := by
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
    have hright : testProduct right ∣ testProduct (.node a p u hp hm left right) := by
      exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
    refine ⟨?_,?_,?_,?_,(il _ _).mono hleft,(ir _ _).mono hright⟩
    · intro v hv
      change v∈frequencies (rebuild (History.node a p u hp hm left right) Xp Xm) at hv
      rw [frequencies_rebuild] at hv
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (List.dvd_prod hv) _) _
    · intro q hq
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (small_dvd_product hq) _) _
    · exact dvd_mul_of_dvd_right
        (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _) _
    · intro q hq
      have hqU : (q.value:ℤ) ∣ U := small_dvd_product hq
      have hq2 : (q.value:ℤ)*(q.value:ℤ) ∣ U^2 := by
        simpa only [pow_two] using mul_dvd_mul hqU hqU
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hq2 _) _) _) _

def fullTestProduct {l : ℕ} (h : History l) (outside : List ℕ) : ℤ :=
  testProduct h*(outside.prod:ℤ)

theorem fullTestProduct_covers_rebuild {l : ℕ} (h : History l) (outside : List ℕ) (Xp Xm : ℤ) :
    Covers (fullTestProduct h outside) (rebuild h Xp Xm) :=
  (testProduct_covers_rebuild h Xp Xm).mono (dvd_mul_right _ _)

theorem outside_dvd_fullTestProduct {l : ℕ} (h : History l) (outside : List ℕ)
    (q : ℕ) (hq : q∈outside) : (q:ℤ) ∣ fullTestProduct h outside := by
  apply dvd_mul_of_dvd_right
  exact_mod_cast List.dvd_prod hq

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
