import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorCount
import OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeScale

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorWitnessRows HeckeDetectorClassBudget

lemma eventually_all_rpow_ge {P : ℝ→Prop} (hP : ∀ᶠU in atTop,P U)
    (dmin : ℝ) (hdmin : 0<dmin) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → P (Z^d) := by
  obtain ⟨A,hA⟩ := Filter.eventually_atTop.1 hP
  have hh := (tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop A)
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with Z hZ hZ1
  intro d hd
  exact hA _ (hZ.trans (Real.rpow_le_rpow_of_exponent_le hZ1 hd))

lemma source_count_frequency_eventually (n : ℕ) (dmax τ h : ℝ)
    (hdmax : 0<dmax) (hτ : 0<τ) (hh : τ<h) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,d≤dmax → ∀i : ℕ,i≤n →
      2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ≤Z^h := by
  have hC := HeckeDyadic.constant_absorbed_eventually
    (2*Real.pi+3*(n:ℝ)) (h-τ) (by linarith)
  filter_upwards [hC,eventually_ge_atTop (1:ℝ)] with Z hC hZ
  intro d hd i hi
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hexp : d*(τ/(2*dmax))≤τ := by
    have h1 := mul_le_mul_of_nonneg_right hd (show 0≤τ/(2*dmax) by positivity)
    have h2 : dmax*(τ/(2*dmax))=τ/2 := by field_simp
    rw [h2] at h1
    linarith
  have hp : (Z^d)^(τ/(2*dmax))≤Z^τ := by
    rw [←Real.rpow_mul hZp.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ hexp
  have hi' : (i:ℝ)≤n := by exact_mod_cast hi
  calc
    _ ≤ (2*Real.pi+3*(n:ℝ))*Z^τ := by push_cast; nlinarith [Real.pi_pos,Real.rpow_pos_of_pos hZp τ]
    _ ≤ Z^(h-τ)*Z^τ := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^h := by rw [←Real.rpow_add hZp];congr 1;ring

lemma source_fiberConstant_bound (C K Z heightCost momentCost : ℝ)
    (hC : 0≤C) (hZ : 1≤Z) (hh : 0≤heightCost) :
    fiberConstant (C*Z^momentCost) (Z^heightCost) K ≤
      (384*max 1 K)*C*Z^(heightCost+momentCost) := by
  have hp := Real.one_le_rpow hZ hh
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  unfold fiberConstant
  calc
    _ ≤ (192*(2*Z^heightCost)*(C*Z^momentCost))*max 1 K := by gcongr;linarith
    _ = _ := by rw [Real.rpow_add hZp];ring

lemma source_dyadic_cost_eventually (dmin dmax loss : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hl : 0<loss) :
    ∃K : ℝ,0≤K ∧ ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax →
      (dyadicLength (Z^d):ℝ)^2≤K*Z^loss := by
  obtain ⟨K,hK,hbound⟩ := dyadic_cost_eventually (loss/dmax) (by positivity)
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_all_rpow_ge hbound dmin hdmin,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd'
  apply (hb d hd).trans
  apply mul_le_mul_of_nonneg_left _ hK
  rw [←Real.rpow_mul (zero_lt_one.trans_le hZ).le]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hh := mul_le_mul_of_nonneg_right hd' (show 0≤loss/dmax by positivity)
  simpa only [mul_div_cancel₀ _ hdmax.ne'] using hh

lemma source_count_prefactor_eventually {Label : Type*} [Fintype Label]
    (N : ℕ) (dmin dmax logCost heightCost momentCost binWidth K₀ : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hl : 0<logCost)
    (hh : 0≤heightCost) (_hb : 0<binWidth) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax →
      ∀(C a ε tstar T allowance : ℝ) (i : ℕ),0≤C → a≤1 →
      ∀{M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Slot : Type*}
        (B : Batch M H Label Slot (Z^d) a ε tstar T allowance i),
      B.slots.card≤N → B.binWidth=binWidth →
      (Fintype.card Label:ℝ)*(dyadicLength (Z^d):ℝ)^2*
        fiberConstant (C*Z^momentCost) (Z^heightCost) K₀*(Fintype.card B.Bin:ℝ) ≤
      K*C*Z^(logCost+heightCost+momentCost) := by
  obtain ⟨L,hL,hbound⟩ := source_dyadic_cost_eventually dmin dmax logCost hdmin hdmax hl
  let A : ℝ := (alphabetBound binWidth : ℕ)^N
  let K : ℝ := (Fintype.card Label:ℝ)*L*(384*max 1 K₀)*A
  have hA : 0≤A := by dsimp [A];positivity
  have hK : 0≤K := by dsimp [K];positivity
  refine ⟨K+1,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with Z hbound hZ
  intro d hd hd' C a ε tstar T allowance i hC ha M H Slot B hslots hbin
  have hbin' : (Fintype.card B.Bin:ℝ)≤A := by
    have h1 := bin_card_le B.slots ((2*a-1)/2) B.binWidth (by linarith) B.binWidth_pos
    rw [hbin] at h1
    have h2 : (alphabetBound binWidth)^B.slots.card≤(alphabetBound binWidth)^N :=
      Nat.pow_le_pow_right (by unfold alphabetBound;omega) hslots
    change (Fintype.card (HeckeDetectorFiberPartition.BinLabel B.slots ((2*a-1)/2) B.binWidth):ℝ)≤A
    rw [hbin]
    dsimp only [A]
    exact_mod_cast h1.trans h2
  have hf := source_fiberConstant_bound C K₀ Z heightCost momentCost hC hZ hh
  have hf0 : 0≤fiberConstant (C*Z^momentCost) (Z^heightCost) K₀ := by unfold fiberConstant; positivity
  calc
    _ ≤ (Fintype.card Label:ℝ)*(L*Z^logCost)*
        ((384*max 1 K₀)*C*Z^(heightCost+momentCost))*A := by
      gcongr
      exact hbound d hd hd'
    _ = K*C*Z^(logCost+heightCost+momentCost) := by
      simp only [Real.rpow_add (zero_lt_one.trans_le hZ)]
      dsimp [K]
      ring
    _ ≤ _ := by gcongr;linarith

end SevenEighths.ProbeHighRowFamily

end

end OAI
