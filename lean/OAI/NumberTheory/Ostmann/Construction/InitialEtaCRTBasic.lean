import OAI.NumberTheory.Ostmann.Construction.ActualAmplitude
import OAI.NumberTheory.Ostmann.Construction.FavorableGiant
import OAI.NumberTheory.Ostmann.Construction.FiniteCRTPoisson
import OAI.NumberTheory.Ostmann.Construction.HalfTransform

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Construction.InitialEta

def crtTail (a : State) (outside : List ℕ) : List ℕ := a.small.map SmallSlot.value ++ outside

abbrev StatePosition (a : State) (outside : List ℕ) := Fin ((crtTail a outside).length+1+1)

def stateModuli (a : State) (outside : List ℕ) : StatePosition a outside → ℕ :=
  Fin.cons a.giantPlus (Fin.cons a.giantMinus (fun i => (crtTail a outside).get i))

def stateLocalTest (d : Decomposition) (P : Finset ℕ) (a : State) (outside : List ℕ) :
    (i : StatePosition a outside) → ZMod (stateModuli a outside i) → ℂ :=
  Fin.cases (favorableGiantResidueTest d P a.giantPlus)
    (Fin.cases (favorableGiantResidueTest d P a.giantMinus)
      (fun i => residueTest d ((crtTail a outside).get i)))

theorem stateModuli_ofFn (a : State) (outside : List ℕ) :
    List.ofFn (stateModuli a outside) = a.values ++ outside := by
  rw [stateModuli, List.ofFn_cons, List.ofFn_cons, List.ofFn_get]
  rfl

theorem stateModuli_prod (a : State) (outside : List ℕ) :
    (∏ i, stateModuli a outside i) = outsideProduct outside*a.product := by
  have h := congrArg List.prod (stateModuli_ofFn a outside)
  simpa only [List.prod_ofFn,List.prod_append,State.product,outsideProduct,mul_comm] using h

theorem stateModuli_prime (a : State) (outside : List ℕ)
    (hp : ∀ q ∈ a.values ++ outside, q.Prime) :
    ∀ i, (stateModuli a outside i).Prime := by
  intro i
  apply hp
  rw [← stateModuli_ofFn]
  exact List.mem_ofFn.mpr ⟨i,rfl⟩

theorem stateModuli_pairwise (a : State) (outside : List ℕ)
    (hc : a.Coprime outside) :
    Pairwise (fun i j => (stateModuli a outside i).Coprime (stateModuli a outside j)) := by
  have hh : (List.ofFn (stateModuli a outside)).Pairwise Nat.Coprime := by
    rw [stateModuli_ofFn]
    exact hc
  have hi := List.pairwise_ofFn.mp hh
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt|hlt
  · exact hi hlt
  · exact (hi hlt).symm

theorem state_coprime_of_distinct (a : State) (outside : List ℕ)
    (hp : ∀ q ∈ a.values ++ outside, q.Prime) (hnd : (a.values ++ outside).Nodup) :
    a.Coprime outside := by
  apply hnd.pairwise_of_forall_ne
  intro p hp' q hq' hne
  exact (Nat.coprime_primes (hp p hp') (hp q hq')).mpr hne

theorem otherProduct_eq_div {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) (i : ι) :
    otherProduct p i = (∏ j,p j)/p i := by
  rw [← mul_otherProduct p i, Nat.mul_div_right _ (hp i)]

def statePhysicalProduct (d : Decomposition) (P : Finset ℕ)
    (a : State) (outside : List ℕ) (n : ℤ) : ℂ :=
  favorableGiantResidueTest d P a.giantPlus (n:ZMod a.giantPlus) *
    favorableGiantResidueTest d P a.giantMinus (n:ZMod a.giantMinus) *
    (a.small.map fun q => residueTest d q.value (n:ZMod q.value)).prod *
    (outside.map fun q => residueTest d q (n:ZMod q)).prod

theorem stateLocalTest_product (d : Decomposition) (P : Finset ℕ)
    (a : State) (outside : List ℕ) (n : ℤ) :
    (∏ i,stateLocalTest d P a outside i (n:ZMod (stateModuli a outside i))) =
      statePhysicalProduct d P a outside n := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  change favorableGiantResidueTest d P a.giantPlus (n:ZMod a.giantPlus) *
    (favorableGiantResidueTest d P a.giantMinus (n:ZMod a.giantMinus) *
      ∏ i : Fin (crtTail a outside).length,
        residueTest d ((crtTail a outside).get i) (n:ZMod ((crtTail a outside).get i))) = _
  have htail : (∏i : Fin (crtTail a outside).length,
      residueTest d ((crtTail a outside).get i) (n:ZMod ((crtTail a outside).get i))) =
      ((crtTail a outside).map fun q => residueTest d q (n:ZMod q)).prod := by
    rw [← List.prod_ofFn]
    exact congrArg List.prod (List.ofFn_getElem_eq_map (crtTail a outside)
      (fun q => residueTest d q (n:ZMod q)))
  rw [htail]
  simp only [crtTail,List.map_append,List.map_map,List.prod_append,statePhysicalProduct,Function.comp_def]
  ring

end Ostmann.Construction.InitialEta

end

end OAI
