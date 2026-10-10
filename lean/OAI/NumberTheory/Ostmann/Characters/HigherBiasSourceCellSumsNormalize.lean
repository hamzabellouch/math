import OAI.NumberTheory.Ostmann.Characters.CyclicGeneration
import OAI.NumberTheory.Ostmann.Characters.IntervalLifting

namespace OAI

noncomputable section
namespace Ostmann.Characters
open scoped BigOperators

structure NormalizedCellSet (I : Finset ℕ) where
  base : ℕ
  gcd : ℕ
  endpoint : ℕ
  cells : Finset ℕ
  gcd_pos : 0 < gcd
  endpoint_pos : 0 < endpoint
  zero_mem : 0 ∈ cells
  endpoint_mem : endpoint ∈ cells
  cells_le : ∀ x ∈ cells, x ≤ endpoint
  gcd_one : cells.gcd id=1
  recover : cells.image (fun x => base+gcd*x)=I
  base_mem : base ∈ I
  max_mem : base+gcd*endpoint ∈ I

theorem cell_gcd_intCast (I : Finset ℕ) :
    (I.image (fun x:ℕ => (x:ℤ))).gcd id=((I.gcd id : ℕ) : ℤ) := by
  classical
  rw [Finset.gcd_image]
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
    rw [Finset.gcd_insert,Finset.gcd_insert,ih]
    simp only [Function.comp_apply,id_eq]
    rw [← Int.coe_gcd,Int.gcd_natCast_natCast]
    rfl

theorem exists_normalizedCellSet (I : Finset ℕ) (hI : 1 < I.card) :
    Nonempty (NormalizedCellSet I) := by
  classical
  have hne : I.Nonempty := Finset.card_pos.mp (by omega)
  let a := I.min' hne
  let d := I.max' hne
  have ha : a ∈ I := I.min'_mem hne
  have hd : d ∈ I := I.max'_mem hne
  have hmin (x : ℕ) (hx : x∈I) : a ≤ x := I.min'_le x hx
  have hmax (x : ℕ) (hx : x∈I) : x ≤ d := I.le_max' x hx
  have had : a < d := by
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hI
    have hax := hmin x hx
    have hay := hmin y hy
    have hxd := hmax x hx
    have hyd := hmax y hy
    omega
  let D := I.image (fun x=>x-a)
  have hD0 : 0∈D := Finset.mem_image.mpr ⟨a,ha,by omega⟩
  have hDs : d-a∈D := Finset.mem_image.mpr ⟨d,hd,rfl⟩
  have hDbound (x : ℕ) (hx : x∈D) : x ≤ d-a := by
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact Nat.sub_le_sub_right (hmax y hy) a
  let g := D.gcd id
  have hg : 0 < g := by
    by_contra hh
    have hz : g=0 := by omega
    have hz' := Finset.gcd_eq_zero_iff.mp hz (d-a) hDs
    simp only [id_eq] at hz'
    omega
  have hdiv (x : ℕ) (hx : x∈D) : g∣x := Finset.gcd_dvd hx
  have hgs : g ≤ d-a := Nat.le_of_dvd (by omega) (hdiv _ hDs)
  let s := (d-a)/g
  have hs : 0 < s := Nat.div_pos hgs hg
  let B := D.image (fun x=>x/g)
  have hB0 : 0∈B := Finset.mem_image.mpr ⟨0,hD0,by simp⟩
  have hBs : s∈B := Finset.mem_image.mpr ⟨d-a,hDs,rfl⟩
  have hBgcd : B.gcd id=1 := by
    rw [Finset.gcd_image]
    exact Finset.gcd_div_id_eq_one hDs (by omega)
  have hrecover : B.image (fun x=>a+g*x)=I := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
      have hzg : g*(z/g)=z := by
        rw [mul_comm,Nat.div_mul_cancel (hdiv _ hz)]
      rw [hzg]
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
      have hua := hmin u hu
      simpa only [Nat.add_sub_of_le hua] using hu
    · intro hx
      have hxa := hmin x hx
      have hxD : x-a∈D := Finset.mem_image.mpr ⟨x,hx,rfl⟩
      refine Finset.mem_image.mpr ⟨(x-a)/g,Finset.mem_image.mpr ⟨x-a,hxD,rfl⟩,?_⟩
      rw [mul_comm g,Nat.div_mul_cancel (hdiv _ hxD),Nat.add_sub_of_le hxa]
  refine ⟨{ base := a
            gcd := g
            endpoint := s
            cells := B
            gcd_pos := hg
            endpoint_pos := hs
            zero_mem := hB0
            endpoint_mem := hBs
            gcd_one := hBgcd
            recover := hrecover
            base_mem := ha
            max_mem := ?_
            cells_le := ?_ }⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact Nat.div_le_div_right (hDbound y hy)
  · rw [←hrecover]
    exact Finset.mem_image.mpr ⟨s,hBs,rfl⟩

end Ostmann.Characters

end

end OAI
