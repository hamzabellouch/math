import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeChartCover

namespace OAI

/-! Exact finite parametrization of the right cosets for the cubed-prime
trace by the two integral affine charts. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeChart {p : Eisenstein} (hp : primaryPrime p) :
    Residues (p^3) ⊕ cubicThetaPrimeCubeUpperParameter p → cubicThetaPrimeCubeTransversal p :=
  Sum.elim (cubicThetaPrimeCubeLowerChart p) (cubicThetaPrimeCubeUpperChart hp)

lemma cubicThetaPrimeCubeChart_injective {p : Eisenstein} (hp : primaryPrime p) :
    Function.Injective (cubicThetaPrimeCubeChart hp) := by
  intro r s h
  cases r with
  | inl r =>
    cases s with
    | inl s => exact congrArg Sum.inl (cubicThetaPrimeCubeLowerChart_injective hp h)
    | inr s => exact False.elim (cubicThetaPrimeCubeLower_ne_upper hp r s h)
  | inr r =>
    cases s with
    | inl s => exact False.elim (cubicThetaPrimeCubeLower_ne_upper hp s r h.symm)
    | inr s => exact congrArg Sum.inr (cubicThetaPrimeCubeUpperChart_injective hp h)

lemma cubicThetaPrimeCubeCoset_self (p : Eisenstein) (t : cubicThetaPrimeCubeTransversal p) :
    cubicThetaPrimeCubeCoset p t.val=t :=
  (cubicThetaPrimeCubeTransversal_complement p).equiv_snd_eq_self_of_mem_of_one_mem
    (cubicThetaPrimeIwahori (p^3)).one_mem t.property

lemma cubicThetaPrimeCubeChart_surjective {p : Eisenstein} (hp : primaryPrime p) :
    Function.Surjective (cubicThetaPrimeCubeChart hp) := by
  intro t
  by_cases hd : p∣t.val.val 1 1
  · obtain ⟨r,hr⟩ := cubicThetaPrimeCubeUpperChart_covers hp t.val hd
    exact ⟨Sum.inr r,hr.trans (cubicThetaPrimeCubeCoset_self p t)⟩
  · obtain ⟨r,hr⟩ := cubicThetaPrimeCubeLowerChart_covers hp t.val hd
    exact ⟨Sum.inl r,hr.trans (cubicThetaPrimeCubeCoset_self p t)⟩

def cubicThetaPrimeCubeChartEquiv {p : Eisenstein} (hp : primaryPrime p) :
    (Residues (p^3) ⊕ cubicThetaPrimeCubeUpperParameter p) ≃ cubicThetaPrimeCubeTransversal p :=
  Equiv.ofBijective (cubicThetaPrimeCubeChart hp)
    ⟨cubicThetaPrimeCubeChart_injective hp,cubicThetaPrimeCubeChart_surjective hp⟩

lemma cubicThetaPrimeCubeTraceTerm_coset (p : Eisenstein) (F : cubicThetaPrimeCubeSections p)
    (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeTraceTerm p F (cubicThetaPrimeCubeCoset p g).val x=
      cubicThetaPrimeCubeTraceTerm p F g x := by
  let C := cubicThetaPrimeCubeTransversal_complement p
  have he := C.equiv_fst_mul_equiv_snd g
  calc
    _ = cubicThetaPrimeCubeTraceTerm p F
        ((C.equiv g).fst.val*(C.equiv g).snd.val) x :=
      (cubicThetaPrimeCubeTraceTerm_left p F (C.equiv g).fst (C.equiv g).snd.val x).symm
    _ = _ := by rw [he]

end CubicFirstMoment

end

end OAI
