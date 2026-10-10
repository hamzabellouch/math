import Mathlib
import OAI.GroupTheory.SimpleAmenable.Arithmetic.LatticeCounting
import OAI.GroupTheory.SimpleAmenable.Arithmetic.PropagationArithmetic

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section WindowCells

noncomputable def cutFraction (z : CutRing) : CutRing := z-(⌊ordinary z⌋:ℤ)

@[simp] theorem ordinary_cutFraction (z : CutRing) :
    ordinary (cutFraction z) = Int.fract (ordinary z) := by
  simp only [cutFraction,map_sub,map_intCast,Int.fract]

@[simp] theorem endpointLabel_cutFraction (z : CutRing) :
    endpointLabel (cutFraction z) = endpointLabel z := by
  simp [cutFraction,endpointLabel_sub]

@[simp] theorem endpointLabel_labelTau (q : ℤ) :
    endpointLabel ((q:CutRing)*cutTau) = q := by
  simp [endpointLabel,cutTau,QuadraticAlgebra.im_mul]

@[simp] theorem cutFraction_zero : cutFraction 0 = 0 := by
  simp [cutFraction]

noncomputable def windowEndpointSet (n : ℕ) : Finset CutRing := by
  classical
  exact Finset.univ.image fun i : Fin n => cutFraction ((i.val:CutRing)*cutTau)

theorem windowEndpointSet_card (n : ℕ) : (windowEndpointSet n).card = n := by
  classical
  rw [windowEndpointSet,Finset.card_image_of_injective]
  · simp
  · intro i j hij
    have hh := congrArg endpointLabel hij
    simp only [endpointLabel_cutFraction] at hh
    have he (k : ℕ) : endpointLabel ((k:CutRing)*cutTau) = (k:ℤ) := by
      exact_mod_cast endpointLabel_labelTau (k:ℤ)
    simp only [he] at hh
    exact Fin.ext (by omega)

@[instance_reducible] noncomputable def cutOrdinaryOrder : LinearOrder CutRing :=
  LinearOrder.lift' ordinary ordinary_injective

attribute [local instance] cutOrdinaryOrder

noncomputable def windowInterior (n : ℕ) : Fin n ↪o CutRing :=
  (windowEndpointSet n).orderEmbOfFin (windowEndpointSet_card n)

theorem windowInterior_mem (n : ℕ) (i : Fin n) :
    windowInterior n i ∈ windowEndpointSet n := Finset.orderEmbOfFin_mem _ _ _

theorem windowInterior_bounds (n : ℕ) (i : Fin n) :
    0 ≤ ordinary (windowInterior n i) ∧ ordinary (windowInterior n i) < 1 := by
  have hh := windowInterior_mem n i
  simp only [windowEndpointSet,Finset.mem_image,Finset.mem_univ,true_and] at hh
  obtain ⟨j,hj⟩ := hh
  rw [← hj,ordinary_cutFraction]
  exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩

theorem windowInterior_label (n : ℕ) (i : Fin n) :
    0 ≤ endpointLabel (windowInterior n i) ∧ endpointLabel (windowInterior n i) < n := by
  have hh := windowInterior_mem n i
  simp only [windowEndpointSet,Finset.mem_image,Finset.mem_univ,true_and] at hh
  obtain ⟨j,hj⟩ := hh
  rw [← hj,endpointLabel_cutFraction]
  have he : endpointLabel ((j.val:CutRing)*cutTau) = (j.val:ℤ) := by
    exact_mod_cast endpointLabel_labelTau (j.val:ℤ)
  rw [he]
  exact ⟨by omega,by omega⟩

theorem windowInterior_zero (n : ℕ) (hn : 0 < n) :
    windowInterior n ⟨0,hn⟩ = 0 := by
  have hmem : (0:CutRing) ∈ windowEndpointSet n := by
    apply Finset.mem_image.mpr
    exact ⟨⟨0,hn⟩,Finset.mem_univ _,by simp⟩
  have hrange := Finset.range_orderEmbOfFin (windowEndpointSet n) (windowEndpointSet_card n)
  have hx : (0:CutRing) ∈ Set.range (windowInterior n) := by
    change (0:CutRing) ∈ Set.range ((windowEndpointSet n).orderEmbOfFin (windowEndpointSet_card n))
    rw [hrange]; exact hmem
  obtain ⟨i,hi⟩ := hx
  apply ordinary_injective
  have hle := (windowInterior n).monotone (show (⟨0,hn⟩:Fin n) ≤ i by exact Nat.zero_le _)
  change ordinary (windowInterior n ⟨0,hn⟩) ≤ ordinary (windowInterior n i) at hle
  rw [hi,map_zero] at hle
  rw [map_zero]
  exact le_antisymm hle (windowInterior_bounds n ⟨0,hn⟩).1

noncomputable def windowCut (n : ℕ) (q : ℤ) (i : Fin (n+1)) : CutRing :=
  (q:CutRing)*cutTau+if hi : i.val < n then windowInterior n ⟨i.val,hi⟩ else 1

theorem windowCut_zero (n : ℕ) (q : ℤ) (hn : 0 < n) :
    windowCut n q 0 = (q:CutRing)*cutTau := by
  simp only [windowCut,Fin.val_zero,dite_eq_left hn,windowInterior_zero n hn,add_zero]

theorem windowCut_last (n : ℕ) (q : ℤ) :
    windowCut n q (Fin.last n) = (q:CutRing)*cutTau+1 := by
  simp [windowCut]

theorem windowCut_label (n : ℕ) (q : ℤ) (hn : 0 < n) (i : Fin (n+1)) :
    q ≤ endpointLabel (windowCut n q i) ∧ endpointLabel (windowCut n q i) < q+n := by
  unfold windowCut
  split_ifs with hi
  · rw [endpointLabel_add,endpointLabel_labelTau]
    have hh := windowInterior_label n ⟨i.val,hi⟩
    omega
  · simp only [endpointLabel_add,endpointLabel_labelTau]
    change q ≤ q+0 ∧ q+0 < q+n
    omega

theorem windowCut_strictMono (n : ℕ) (q : ℤ) :
    StrictMono fun i => ordinary (windowCut n q i) := by
  intro i j hij
  have hi : i.val < n := by have hh := j.isLt; change i.val < j.val at hij; omega
  simp only [windowCut,dite_eq_left hi,map_add]
  split_ifs with hj
  · apply add_lt_add_right
    exact (windowInterior n).strictMono (show (⟨i.val,hi⟩:Fin n) < ⟨j.val,hj⟩ from hij)
  · simpa only [map_one] using add_lt_add_right (windowInterior_bounds n ⟨i.val,hi⟩).2
      (ordinary ((q:CutRing)*cutTau))

@[simp] theorem cutFraction_eq_self (z : CutRing)
    (hz : 0 ≤ ordinary z ∧ ordinary z < 1) : cutFraction z = z := by
  apply ordinary_injective
  rw [ordinary_cutFraction,Int.fract_eq_self.mpr hz]

theorem cutFraction_label (z : CutRing) :
    cutFraction z = cutFraction ((endpointLabel z:CutRing)*cutTau) := by
  have he : z = ((endpointLabel z:CutRing)*cutTau)+(z.re:CutRing) := by
    apply QuadraticAlgebra.ext <;> simp [endpointLabel,cutTau]
  apply ordinary_injective
  simp only [ordinary_cutFraction]
  conv_lhs => rw [he,map_add,map_intCast,Int.fract_add_intCast]

theorem windowEndpointSet_of_bounds (n : ℕ) (z : CutRing)
    (hl : 0 ≤ endpointLabel z ∧ endpointLabel z < n)
    (ho : 0 ≤ ordinary z ∧ ordinary z < 1) : z ∈ windowEndpointSet n := by
  classical
  have hi : (endpointLabel z).toNat < n := by omega
  have he : ((endpointLabel z).toNat:ℤ) = endpointLabel z := Int.toNat_of_nonneg hl.1
  apply Finset.mem_image.mpr
  refine ⟨⟨(endpointLabel z).toNat,hi⟩,Finset.mem_univ _,?_⟩
  change cutFraction (((endpointLabel z).toNat:CutRing)*cutTau) = z
  have hc : ((endpointLabel z).toNat:CutRing) = (endpointLabel z:CutRing) := by
    exact_mod_cast he
  rw [hc,← cutFraction_label,cutFraction_eq_self z ho]

theorem windowCut_bounds (n : ℕ) (q : ℤ) (i : Fin (n+1)) :
    ordinary ((q:CutRing)*cutTau) ≤ ordinary (windowCut n q i) ∧
      ordinary (windowCut n q i) ≤ ordinary ((q:CutRing)*cutTau)+1 := by
  unfold windowCut
  split_ifs with hi
  · simp only [map_add]
    have hh := windowInterior_bounds n ⟨i.val,hi⟩
    constructor <;> linarith
  · simp only [map_add,map_one]
    constructor <;> linarith

theorem windowCut_no_between (n : ℕ) (q : ℤ) (i : Fin n) (z : CutRing)
    (hz : q ≤ endpointLabel z ∧ endpointLabel z < q+n) :
    ¬(ordinary (windowCut n q i.castSucc) < ordinary z ∧
      ordinary z < ordinary (windowCut n q i.succ)) := by
  rintro ⟨hlo,hup⟩
  let z' : CutRing := z-(q:CutRing)*cutTau
  have hzl : 0 ≤ endpointLabel z' ∧ endpointLabel z' < n := by
    simp only [z',endpointLabel_sub,endpointLabel_labelTau]
    omega
  have hzo : 0 ≤ ordinary z' ∧ ordinary z' < 1 := by
    simp only [z',map_sub]
    have hh := (windowCut_bounds n q i.castSucc).1
    have hh' := (windowCut_bounds n q i.succ).2
    constructor <;> linarith
  have hmem := windowEndpointSet_of_bounds n z' hzl hzo
  have hx : z' ∈ Set.range (windowInterior n) := by
    change z' ∈ Set.range ((windowEndpointSet n).orderEmbOfFin (windowEndpointSet_card n))
    rw [Finset.range_orderEmbOfFin]; exact hmem
  obtain ⟨j,hj⟩ := hx
  have hlow : ordinary (windowInterior n i) < ordinary (windowInterior n j) := by
    simp only [windowCut,Fin.val_castSucc,dite_eq_left i.isLt,map_add] at hlo
    rw [hj]
    dsimp only [z']
    rw [map_sub]
    linarith
  have hij : i < j := (windowInterior n).lt_iff_lt.mp hlow
  have hin : i.val+1 < n := by have h := j.isLt; change i.val < j.val at hij; omega
  have hupper : ordinary (windowInterior n j) < ordinary (windowInterior n ⟨i.val+1,hin⟩) := by
    simp only [windowCut,Fin.val_succ,dite_eq_left hin,map_add] at hup
    rw [hj]
    dsimp only [z']
    rw [map_sub]
    linarith
  have hji : j < (⟨i.val+1,hin⟩:Fin n) := (windowInterior n).lt_iff_lt.mp hupper
  change j.val < i.val+1 at hji
  change i.val < j.val at hij
  omega

theorem windowCut_mesh (n : ℕ) (q : ℤ) (i : Fin n) :
    ordinary (windowCut n q i.succ)-ordinary (windowCut n q i.castSucc) ≤ 200/(n:ℝ) := by
  by_contra hbad
  have hn : 1 ≤ n := by have hh := i.isLt; omega
  have hg : 200/(n:ℝ) < ordinary (windowCut n q i.succ)-ordinary (windowCut n q i.castSucc) := lt_of_not_ge hbad
  obtain ⟨z,hzl,hzu,hz⟩ := coordinate_window_net n hn q
    ((ordinary (windowCut n q i.castSucc)+ordinary (windowCut n q i.succ))/2)
  have hab := abs_le.mp hz
  have hden : 200/(n:ℝ)=2*(100/(n:ℝ)) := by ring
  rw [hden] at hg
  exact windowCut_no_between n q i z ⟨hzl,hzu⟩ ⟨by linarith,by linarith⟩

end WindowCells

end SimpleAmenable
end
end

end OAI
