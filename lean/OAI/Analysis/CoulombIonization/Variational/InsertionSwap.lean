import Mathlib
import OAI.Analysis.CoulombIonization.Variational.Spatial
import OAI.Analysis.CoulombIonization.Variational.SumPairsHalf
import OAI.Analysis.CoulombIonization.Variational.TensorLp
import OAI.Analysis.CoulombIonization.FormDomain.SumForm

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators

lemma corePerm_last {N : ℕ} (π : Equiv.Perm (Fin N)) :
    corePerm 1 π (Fin.last N) = Fin.last N := by
  have hh : (Fin.last N : Fin (N+1)) = finSumFinEquiv (Sum.inr (0 : Fin 1)) := by
    ext; simp
  rw [hh]
  simp [corePerm, Equiv.permCongr]

lemma corePerm_castSucc {N : ℕ} (π : Equiv.Perm (Fin N)) (i : Fin N) :
    corePerm 1 π i.castSucc = (π i).castSucc := by
  change corePerm 1 π (finSumFinEquiv (Sum.inl i)) = finSumFinEquiv (Sum.inl (π i))
  simp [corePerm,Equiv.permCongr]

lemma perm_fixed_last_is_core {N : ℕ} (κ : Equiv.Perm (Fin (N+1)))
    (hκ : κ (Fin.last N) = Fin.last N) : ∃ ρ : Equiv.Perm (Fin N), κ = corePerm 1 ρ := by
  let e := finSuccAboveEquiv (Fin.last N)
  have hh (i : Fin (N+1)) : κ i ≠ Fin.last N ↔ i ≠ Fin.last N := by
    rw [← hκ, κ.injective.ne_iff, hκ]
  let ρ := e.symm.permCongr (κ.subtypePerm hh)
  refine ⟨ρ, ?_⟩
  apply Equiv.ext
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · exact hκ.trans (corePerm_last ρ).symm
  · rw [corePerm_castSucc]
    have he (j : Fin N) : (e j).val = j.castSucc := by
      simp [e, finSuccAboveEquiv, Fin.succAbove_last]
    have hp : κ ((e i).val) = (e (ρ i)).val := by
      simp [ρ, Equiv.permCongr, Equiv.Perm.subtypePerm]
    simpa only [he] using hp

def insertionSwap {N : ℕ} (i : Fin (N+1)) : Equiv.Perm (Fin (N+1)) :=
  Equiv.swap i (Fin.last N)

@[simp] lemma insertionSwap_last {N : ℕ} (i : Fin (N+1)) :
    insertionSwap i (Fin.last N) = i := Equiv.swap_apply_right _ _
@[simp] lemma insertionSwap_self {N : ℕ} (i : Fin (N+1)) :
    insertionSwap i i = Fin.last N := Equiv.swap_apply_left _ _
@[simp] lemma insertionSwap_symm {N : ℕ} (i : Fin (N+1)) :
    (insertionSwap i).symm = insertionSwap i := rfl

lemma insertion_coset {N : ℕ} (π : Equiv.Perm (Fin (N+1))) (i : Fin (N+1)) :
    ∃ ρ : Equiv.Perm (Fin N), π * insertionSwap i = insertionSwap (π i) * corePerm 1 ρ := by
  let κ := (insertionSwap (π i))⁻¹ * (π * insertionSwap i)
  have hk : κ (Fin.last N) = Fin.last N := by
    simp only [κ, Equiv.Perm.coe_mul, Function.comp_apply, insertionSwap_last,
      Equiv.Perm.inv_def, insertionSwap_symm, insertionSwap_self]
  obtain ⟨ρ,hρ⟩ := perm_fixed_last_is_core κ hk
  refine ⟨ρ, ?_⟩
  rw [← hρ]
  simp only [κ, mul_inv_cancel_left]

lemma real_sign_sq {N : ℕ} (π : Equiv.Perm (Fin N)) :
    (((Equiv.Perm.sign π : ℤ) : ℝ))^2 = 1 := by
  have hh : (Equiv.Perm.sign π : ℤ) * (Equiv.Perm.sign π : ℤ) = 1 :=
    congrArg (fun u : ℤˣ => (u : ℤ)) (Int.units_mul_self (Equiv.Perm.sign π))
  have hh' : (((Equiv.Perm.sign π : ℤ) : ℝ))*(((Equiv.Perm.sign π : ℤ) : ℝ)) = 1 := by
    exact_mod_cast hh
  simpa only [pow_two] using hh'


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators


lemma tensor_coreAntisymmetric {N M : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (φ : FormVector M) : CoreAntisymmetric (tensorForm ψ φ) := by
  intro π s
  have hp : ∀ᵐ z : Configuration N × Configuration M,
      ψ.value (leftList s ∘ π) (z.1 ∘ π) =
        (((Equiv.Perm.sign π : ℤ) : ℂ) * ψ.value (leftList s) z.1) :=
    Measure.quasiMeasurePreserving_fst.ae (hψ.2.2.2 π (leftList s))
  have hh := (configurationJoin_symm_preserving N M).quasiMeasurePreserving.ae hp
  filter_upwards [hh] with x hx
  simp only [configurationJoin_symm_apply] at hx
  have hp (z : Fin (N+M) → Space) :
      leftList (z ∘ corePerm M π) = leftList z ∘ π ∧
      rightList (z ∘ corePerm M π) = rightList z := by
    have he := joinLists_corePerm (leftList z) (rightList z) π
    rw [join_list_parts] at he
    constructor
    · rw [he,leftList_join]
    · rw [he,rightList_join]
  have hs : leftList (s ∘ corePerm M π) = leftList s ∘ π ∧
      rightList (s ∘ corePerm M π) = rightList s := by
    have he := joinLists_corePerm (leftList s) (rightList s) π
    rw [join_list_parts] at he
    constructor
    · rw [he,leftList_join]
    · rw [he,rightList_join]
  change ψ.value _ _ * φ.value _ _ = _ * (ψ.value _ _ * φ.value _ _)
  rw [hs.1,hs.2,(hp x).1,(hp x).2,hx,mul_assoc]

lemma CoreAntisymmetric.fixed_last {N : ℕ} {T : FormVector (N+1)}
    (hT : CoreAntisymmetric (N := N) (M := 1) T)
    (κ : Equiv.Perm (Fin (N+1))) (hκ : κ (Fin.last N) = Fin.last N) (s : Spins (N+1)) :
    ∀ᵐ x, T.value (s ∘ κ) (x ∘ κ) = (((Equiv.Perm.sign κ : ℤ) : ℂ) * T.value s x) := by
  obtain ⟨ρ,rfl⟩ := perm_fixed_last_is_core κ hκ
  simpa only [corePerm_sign] using hT ρ s

def insertionTerm {N : ℕ} (T : FormVector (N+1)) (i : Fin (N+1)) : FormVector (N+1) :=
  scaleForm (((Equiv.Perm.sign (insertionSwap i) : ℤ) : ℝ))
    (reindexForm (insertionSwap i) T)

def wedgeForm {N : ℕ} (T : FormVector (N+1)) : FormVector (N+1) :=
  sumForm (insertionTerm T)

@[simp] lemma insertionTerm_value {N : ℕ} (T : FormVector (N+1)) (i : Fin (N+1))
    (s : Spins (N+1)) (x : Configuration (N+1)) :
    (insertionTerm T i).value s x = (((Equiv.Perm.sign (insertionSwap i) : ℤ) : ℂ)) *
      T.value (s ∘ insertionSwap i) (x ∘ insertionSwap i) := by
  simp only [insertionTerm,scaleForm,reindexForm,insertionSwap_symm,Complex.ofReal_intCast]

lemma SobolevVector.insertionTerm {N : ℕ} {T : FormVector (N+1)} (hT : SobolevVector T)
    (i : Fin (N+1)) : SobolevVector (insertionTerm T i) :=
  (hT.reindex (insertionSwap i)).scale _

lemma wedgeForm_fermion {N : ℕ} {T : FormVector (N+1)} (hT : SobolevVector T)
    (hTa : CoreAntisymmetric (N := N) (M := 1) T) : SobolevFermion (wedgeForm T) := by
  have hw := SobolevVector.sum (fun i => hT.insertionTerm i)
  refine ⟨hw.1,hw.2.1,hw.2.2,?_⟩
  intro π s
  have hh (i : Fin (N+1)) : ∀ᵐ x,
      (insertionTerm T i).value (s ∘ π) (x ∘ π) =
      (((Equiv.Perm.sign π : ℤ) : ℂ)) * (insertionTerm T (π i)).value s x := by
    obtain ⟨ρ,hρ⟩ := insertion_coset π i
    have hp := (permuteConfiguration_preserving (insertionSwap (π i))).quasiMeasurePreserving.ae
      (hTa ρ (s ∘ insertionSwap (π i)))
    filter_upwards [hp] with x hx
    simp only [permuteConfiguration_apply] at hx
    have hv : ((s ∘ π) ∘ insertionSwap i) = (s ∘ insertionSwap (π i)) ∘ corePerm 1 ρ := by
      change s ∘ (π * insertionSwap i) = s ∘ (insertionSwap (π i) * corePerm 1 ρ)
      rw [hρ]
    have hvx : ((x ∘ π) ∘ insertionSwap i) = (x ∘ insertionSwap (π i)) ∘ corePerm 1 ρ := by
      change x ∘ (π * insertionSwap i) = x ∘ (insertionSwap (π i) * corePerm 1 ρ)
      rw [hρ]
    have hsg : (((Equiv.Perm.sign π : ℤ) : ℂ)) *
        (((Equiv.Perm.sign (insertionSwap i) : ℤ) : ℂ)) =
        (((Equiv.Perm.sign (insertionSwap (π i)) : ℤ) : ℂ)) *
        (((Equiv.Perm.sign ρ : ℤ) : ℂ)) := by
      have ht := congrArg (fun σ => (((Equiv.Perm.sign σ : ℤ) : ℂ))) hρ
      simpa only [Equiv.Perm.sign_mul,corePerm_sign,Units.val_mul,Int.cast_mul] using ht
    have hsg' : (((Equiv.Perm.sign (insertionSwap i) : ℤ) : ℂ)) *
        (((Equiv.Perm.sign ρ : ℤ) : ℂ)) =
        (((Equiv.Perm.sign π : ℤ) : ℂ)) *
        (((Equiv.Perm.sign (insertionSwap (π i)) : ℤ) : ℂ)) := by
      have hs := complex_sign_sq (insertionSwap (π i))
      have hq := complex_sign_sq (insertionSwap i)
      linear_combination -(((Equiv.Perm.sign (insertionSwap (π i)) : ℤ) : ℂ)) *
        (((Equiv.Perm.sign (insertionSwap i) : ℤ) : ℂ)) * hsg +
        (((Equiv.Perm.sign π : ℤ) : ℂ)) *
        (((Equiv.Perm.sign (insertionSwap (π i)) : ℤ) : ℂ)) * hq -
        (((Equiv.Perm.sign ρ : ℤ) : ℂ)) *
        (((Equiv.Perm.sign (insertionSwap i) : ℤ) : ℂ)) * hs
    simp only [insertionTerm_value,hv,hvx,hx,← mul_assoc,hsg']
  filter_upwards [ae_all_iff.mpr hh] with x hx
  change (∑ i, (insertionTerm T i).value (s ∘ π) (x ∘ π)) = _ * ∑ i, (insertionTerm T i).value s x
  simp_rw [hx,← Finset.mul_sum]
  rw [Equiv.sum_comp π (fun i => (insertionTerm T i).value s x)]

lemma formMass_insertionTerm {N : ℕ} (T : FormVector (N+1)) (i : Fin (N+1)) :
    formMass (insertionTerm T i) = formMass T := by
  rw [insertionTerm,formMass_scale,formMass_reindex,real_sign_sq,one_mul]

lemma formEnergy_insertionTerm {N : ℕ} (T : FormVector (N+1)) (i : Fin (N+1)) (Z : ℝ) :
    formEnergy Z (insertionTerm T i) = formEnergy Z T := by
  rw [insertionTerm,formEnergy_scale,formEnergy_reindex,real_sign_sq,one_mul]


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
