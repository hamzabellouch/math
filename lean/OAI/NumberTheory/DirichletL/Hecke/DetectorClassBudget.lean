import OAI.NumberTheory.DirichletL.Hecke.DetectorBatch
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationBudget

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.HeckeDetectorClassBudget
open HeckeDetectorFiberPartition HeckeDetectorWitnessRows

def alphabetBound (mesh : ℝ) : ℕ := 2+(⌈(1/2 : ℝ)/mesh⌉+1 : ℤ).toNat

theorem labels_card_le (cap mesh : ℝ) (hcap : cap≤1/2) (hm : 0<mesh) :
    (HeckePrimeAmplitudeBins.labels cap mesh).card≤alphabetBound mesh := by
  have hceil : ⌈cap/mesh⌉≤⌈(1/2 : ℝ)/mesh⌉ :=
    Int.ceil_mono (div_le_div_of_nonneg_right hcap hm.le)
  have hsub : Finset.Icc (0 : ℤ) ⌈cap/mesh⌉ ⊆ Finset.Icc (0 : ℤ) ⌈(1/2 : ℝ)/mesh⌉ := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans hceil⟩
  have h1 := Finset.card_insert_le (0 : ℝ)
    (insert cap ((Finset.Icc (0 : ℤ) ⌈cap/mesh⌉).image (fun n : ℤ => mesh*(n : ℝ))))
  have h2 := Finset.card_insert_le cap
    ((Finset.Icc (0 : ℤ) ⌈cap/mesh⌉).image (fun n : ℤ => mesh*(n : ℝ)))
  have h3 := Finset.card_image_le (s:=Finset.Icc (0 : ℤ) ⌈cap/mesh⌉)
    (f:=fun n : ℤ => mesh*(n : ℝ))
  have h4 := Finset.card_le_card hsub
  simp only [Int.card_Icc,sub_zero] at h4 h3
  unfold HeckePrimeAmplitudeBins.labels alphabetBound
  omega

theorem bin_card_le {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ)
    (hcap : cap≤1/2) (hm : 0<mesh) :
    Fintype.card (BinLabel slots cap mesh)≤(alphabetBound mesh)^slots.card := by
  simpa only [BinLabel,Fintype.card_fun,Fintype.card_coe] using
    Nat.pow_le_pow_left (labels_card_le cap mesh hcap hm) slots.card

theorem dyadic_cost_eventually (η : ℝ) (hη : 0<η) :
    ∃ K : ℝ,0≤K ∧ ∀ᶠ U : ℝ in atTop,(dyadicLength U : ℝ)^2≤K*U^η := by
  let K := 625/(Real.log 2)^2
  have hK : 0≤K := by positivity
  have hlog := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hη).bound (by norm_num : (0 : ℝ)<1)
  refine ⟨K,hK,?_⟩
  filter_upwards [hlog,eventually_ge_atTop (2 : ℝ)] with U hlog hU
  have hUp : 0<U := by linarith
  have hs : (Real.log U)^2≤U^η := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log U)),
      abs_of_nonneg (Real.rpow_nonneg hUp.le _),one_mul] using hlog
  have hd := HeckeDetectorBudget.source_pair_count_bound U hU
  calc
    (dyadicLength U : ℝ)^2 ≤ 625*(Real.logb 2 U)^2 := hd
    _ = K*(Real.log U)^2 := by unfold K Real.logb; ring
    _ ≤ K*U^η := mul_le_mul_of_nonneg_left hs hK

end SevenEighths.HeckeDetectorClassBudget

end

end OAI
