import OAI.Dynamics.ThreeTorus.PacketStates
import OAI.Dynamics.ThreeTorus.PhysicalJets
import OAI.Dynamics.ThreeTorus.PredictionModels

namespace OAI

/-! Refresh and residue estimates, physical aggregates, tracked producers, pair/color aggregates, and colored states. -/

section

/-! Deterministic refresh--transmit estimate (03-signals, equation
`signal-refresh-error`).  Residues are the residues of the ACTUAL refreshed
indices, and the coefficient comparison is only required on their support.
No independence of the phase variable is used. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma sum_fibers_univ {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (r : ι → κ) (p : ι → ℝ) :
    ∑ h, ∑ i, (if r i = h then p i else 0) = ∑ i, p i := by
  classical
  rw [Finset.sum_comm]
  simp

lemma sum_selected_fibers {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (r : ι → κ) (p : ι → ℝ) (H : Finset κ) :
    ∑ h ∈ H, ∑ i, (if r i = h then p i else 0) =
      ∑ i, if r i ∈ H then p i else 0 := by
  classical
  rw [Finset.sum_comm]
  congr 1
  ext i
  simp

lemma residue_total_error {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : ι → κ) (p : ι → ℝ) (q : ℝ) :
    |(∑ i, p i)-q| ≤
      ∑ h, |(∑ i, if r i = h then p i else 0)-q/Fintype.card κ| := by
  classical
  have hc : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (∑ i, p i)-q =
      ∑ h, ((∑ i, if r i = h then p i else 0)-q/Fintype.card κ) := by
    rw [Finset.sum_sub_distrib,sum_fibers_univ]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp
  rw [he]
  exact Finset.abs_sum_le_sum_abs _ _

lemma residue_selected_error {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (r : ι → κ) (p : ι → ℝ) (q : ℝ) (H : Finset κ) :
    |(∑ i, if r i ∈ H then p i else 0)-(H.card:ℝ)/Fintype.card κ*q| ≤
      ∑ h, |(∑ i, if r i = h then p i else 0)-q/Fintype.card κ| := by
  classical
  have he : (∑ i, if r i ∈ H then p i else 0)-(H.card:ℝ)/Fintype.card κ*q =
      ∑ h ∈ H, ((∑ i, if r i = h then p i else 0)-q/Fintype.card κ) := by
    rw [Finset.sum_sub_distrib,sum_selected_fibers]
    simp only [Finset.sum_const,nsmul_eq_mul]
    ring
  rw [he]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_univ_sum_of_nonneg (fun h => abs_nonneg _))

lemma selected_coefficient_error {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (r : ι → κ) (H : Finset κ) (p : ι → ℝ) (c : ι → ℂ) (a : ℂ) {ρ : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hρ : 0 ≤ ρ)
    (hmatch : ∀ i, p i ≠ 0 → ‖c i-a‖ ≤ ρ) :
    ‖(∑ i, if r i ∈ H then (p i:ℂ)*c i else 0)-
      ((∑ i, if r i ∈ H then p i else 0):ℝ)*a‖ ≤ ρ*(∑ i, p i) := by
  classical
  have he : (∑ i, if r i ∈ H then (p i:ℂ)*c i else 0)-
      ((∑ i, if r i ∈ H then p i else 0):ℝ)*a =
      ∑ i, if r i ∈ H then (p i:ℂ)*(c i-a) else 0 := by
    simp only [Complex.ofReal_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : r i ∈ H
    · simp only [ite_eq_left h]
      ring
    · simp only [ite_eq_right h,Complex.ofReal_zero,zero_mul,sub_zero]
  rw [he,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  by_cases h : r i ∈ H
  · simp only [ite_eq_left h,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp i)]
    by_cases hz : p i = 0
    · simp only [hz,zero_mul,mul_zero,le_refl]
    · simpa only [mul_comm ρ] using mul_le_mul_of_nonneg_left (hmatch i hz) (hp i)
  · simp only [ite_eq_right h,norm_zero]
    exact mul_nonneg hρ (hp i)

/-- Pointwise colored version, before integrating. The exact fraction is the
fraction of selected refreshed residue classes. -/
lemma refresh_transmit_pointwise {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : ι → κ) (H : Finset κ) (p : ι → ℝ) (c : ι → ℂ) (a e : ℂ)
    (q : ℝ) {γ ρ A : ℝ} (hγ : 0 ≤ γ) (hρ : 0 ≤ ρ)
    (hp : ∀ i, 0 ≤ p i) (he : ‖e‖ ≤ 1) (ha : ‖a‖ ≤ A)
    (hmatch : ∀ i, p i ≠ 0 → ‖c i-a‖ ≤ ρ) :
    |(∑ i, p i)+2*γ*(e*(∑ i, if r i ∈ H then (p i:ℂ)*c i else 0)).re-
      q*(1+2*(γ*(H.card:ℝ)/Fintype.card κ)*(e*a).re)| ≤
      (1+2*γ*A)*(∑ h, |(∑ i, if r i = h then p i else 0)-q/Fintype.card κ|)+
      2*γ*ρ*(∑ i, p i) := by
  classical
  let t := ∑ i, p i
  let s := ∑ i, if r i ∈ H then p i else 0
  let v := ∑ i, if r i ∈ H then (p i:ℂ)*c i else 0
  let u : ℝ := (H.card:ℝ)/Fintype.card κ
  let E := ∑ h, |(∑ i, if r i = h then p i else 0)-q/Fintype.card κ|
  have hEt : |t-q| ≤ E := residue_total_error r p q
  have hEs : |s-u*q| ≤ E := residue_selected_error r p q H
  have hv : ‖v-(s:ℂ)*a‖ ≤ ρ*t := selected_coefficient_error r H p c a hp hρ hmatch
  have her : |(e*(v-(s:ℂ)*a)).re| ≤ ρ*t := calc
    _ ≤ ‖e*(v-(s:ℂ)*a)‖ := Complex.abs_re_le_norm _
    _ = ‖e‖*‖v-(s:ℂ)*a‖ := norm_mul _ _
    _ ≤ 1*‖v-(s:ℂ)*a‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
    _ ≤ ρ*t := by simpa only [one_mul] using hv
  have hea : |(e*a).re| ≤ A := (Complex.abs_re_le_norm _).trans (by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans (by simpa using ha))
  have hcoef : |(e*(v-(s:ℂ)*a)).re+(s-u*q)*(e*a).re| ≤ ρ*t+E*A := by
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    exact add_le_add her (mul_le_mul hEs hea (abs_nonneg _) (Finset.sum_nonneg (fun h _ => abs_nonneg _)))
  have heq : t+2*γ*(e*v).re-q*(1+2*(γ*(H.card:ℝ)/Fintype.card κ)*(e*a).re) =
      (t-q)+2*γ*((e*(v-(s:ℂ)*a)).re+(s-u*q)*(e*a).re) := by
    simp only [mul_sub,Complex.sub_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    dsimp [u]
    ring
  change |t+2*γ*(e*v).re-q*(1+2*(γ*(H.card:ℝ)/Fintype.card κ)*(e*a).re)| ≤ _
  rw [heq]
  calc
    _ ≤ |t-q|+|2*γ*((e*(v-(s:ℂ)*a)).re+(s-u*q)*(e*a).re)| := abs_add_le _ _
    _ = |t-q|+2*γ*|(e*(v-(s:ℂ)*a)).re+(s-u*q)*(e*a).re| := by
      rw [abs_mul,abs_of_nonneg (mul_nonneg (by norm_num) hγ)]
    _ ≤ E+2*γ*(ρ*t+E*A) := add_le_add hEt
      (mul_le_mul_of_nonneg_left hcoef (mul_nonneg (by norm_num) hγ))
    _ = _ := by dsimp [E,t]; ring

/-- Summed residue discrepancy, for one color. -/
def refreshResidueError {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (r : ι → κ) (p : ι → UnitAddCircle → ℝ) (q : UnitAddCircle → ℝ) (z : UnitAddCircle) : ℝ :=
  ∑ h, |(∑ i, if r i = h then p i z else 0)-q z/Fintype.card κ|

def refreshSignalAggregate {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (r : ι → κ) (H : Finset κ) (p : ι → UnitAddCircle → ℝ) (c : ι → ℂ)
    (γ : ℝ) (e : UnitAddCircle → ℂ) (z : UnitAddCircle) : ℝ :=
  (∑ i, p i z)+2*γ*(e z*(∑ i, if r i ∈ H then (p i z:ℂ)*c i else 0)).re

lemma continuous_refreshResidueError {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (r : ι → κ) {p : ι → UnitAddCircle → ℝ} {q : UnitAddCircle → ℝ}
    (hp : ∀ i, Continuous (p i)) (hq : Continuous q) : Continuous (refreshResidueError r p q) := by
  unfold refreshResidueError
  apply continuous_finsetSum
  intro h _
  apply Continuous.abs
  apply Continuous.sub _ (hq.div_const _)
  apply continuous_finsetSum
  intro i _
  split_ifs <;> first | exact hp i | exact continuous_const

lemma continuous_refreshSignalAggregate {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (r : ι → κ) (H : Finset κ) {p : ι → UnitAddCircle → ℝ} (c : ι → ℂ)
    (γ : ℝ) {e : UnitAddCircle → ℂ} (hp : ∀ i, Continuous (p i)) (he : Continuous e) :
    Continuous (refreshSignalAggregate r H p c γ e) := by
  unfold refreshSignalAggregate
  apply Continuous.add (continuous_finsetSum _ (fun i _ => hp i))
  apply Continuous.const_mul
  apply Complex.continuous_re.comp
  apply he.mul
  apply continuous_finsetSum
  intro i _
  split_ifs <;> first | exact (Complex.continuous_ofReal.comp (hp i)).mul_const _ | exact continuous_const

/-- Exact manuscript constant, for the actual selected residue family. Here
`g` is any final transmission density; its L1 mismatch with the explicit
signal aggregate is retained as `T`, not silently dropped. -/
theorem refresh_transmit_L1 {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [Nonempty κ]
    (r : ι → κ) (H : Finset κ) {p : ι → UnitAddCircle → ℝ} (c : ι → ℂ)
    {a e : UnitAddCircle → ℂ} {q g : UnitAddCircle → ℝ} {γ ρ A : ℝ}
    (hp : ∀ i, Continuous (p i)) (ha : Continuous a) (he : Continuous e)
    (hq : Continuous q) (hg : Continuous g)
    (hγ : 0 ≤ γ) (hρ : 0 ≤ ρ) (hp0 : ∀ i z, 0 ≤ p i z)
    (he1 : ∀ z, ‖e z‖ ≤ 1) (haA : ∀ z, ‖a z‖ ≤ A)
    (hmatch : ∀ i z, p i z ≠ 0 → ‖c i-a z‖ ≤ ρ) :
    (∫ z, |g z-q z*(1+2*(γ*(H.card:ℝ)/Fintype.card κ)*(e z*a z).re)| ∂phaseHaar) ≤
      (∫ z, |g z-refreshSignalAggregate r H p c γ e z| ∂phaseHaar)+
      (1+2*γ*A)*(∫ z, refreshResidueError r p q z ∂phaseHaar)+
      2*γ*ρ*((∫ z, |q z| ∂phaseHaar)+(∫ z, refreshResidueError r p q z ∂phaseHaar)) := by
  let E := refreshResidueError r p q
  let t := fun z => ∑ i, p i z
  let model := refreshSignalAggregate r H p c γ e
  let target := fun z => q z*(1+2*(γ*(H.card:ℝ)/Fintype.card κ)*(e z*a z).re)
  have hEc : Continuous E := continuous_refreshResidueError r hp hq
  have htc : Continuous t := continuous_finsetSum _ (fun i _ => hp i)
  have hmc : Continuous model := continuous_refreshSignalAggregate r H c γ hp he
  have htar : Continuous target := by
    exact hq.mul (continuous_const.add (continuous_const.mul
      (Complex.continuous_re.comp (he.mul ha))))
  have hE := continuous_circle_integrable hEc
  have ht := continuous_circle_integrable htc
  have hm := continuous_circle_integrable hmc
  have htarget := continuous_circle_integrable htar
  have htq : (∫ z, t z ∂phaseHaar) ≤ (∫ z, |q z| ∂phaseHaar)+(∫ z, E z ∂phaseHaar) := by
    have hb z : t z ≤ |q z|+E z := by
      have hh := residue_total_error r (fun i => p i z) (q z)
      change |t z-q z| ≤ E z at hh
      linarith [le_abs_self (t z-q z),le_abs_self (q z)]
    have hh := integral_mono ht ((continuous_circle_integrable hq).abs.add hE) hb
    dsimp only [Pi.add_apply] at hh
    rwa [integral_add (continuous_circle_integrable hq).abs hE] at hh
  have hpoint z : |model z-target z| ≤ (1+2*γ*A)*E z+2*γ*ρ*t z :=
    refresh_transmit_pointwise r H (fun i => p i z) c (a z) (e z) (q z) hγ hρ
      (fun i => hp0 i z) (he1 z) (haA z) (fun i => hmatch i z)
  have hb := integral_mono (hm.sub htarget).abs
    ((hE.const_mul (1+2*γ*A)).add (ht.const_mul (2*γ*ρ))) hpoint
  dsimp only [Pi.add_apply,Pi.sub_apply] at hb
  rw [integral_add (hE.const_mul (1+2*γ*A)) (ht.const_mul (2*γ*ρ)),
    integral_const_mul,integral_const_mul] at hb
  have htq' := mul_le_mul_of_nonneg_left htq
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hγ) hρ)
  have htri := integral_abs_sub_triangle (continuous_circle_integrable hg) hm htarget
  change (∫ z, |g z-target z| ∂phaseHaar) ≤
    (∫ z, |g z-model z| ∂phaseHaar)+(1+2*γ*A)*(∫ z, E z ∂phaseHaar)+
    2*γ*ρ*((∫ z, |q z| ∂phaseHaar)+(∫ z, E z ∂phaseHaar))
  linarith

end ThreeTorus
end
end

section

/-! Exact arithmetic conversion of refreshed integer residues to the unit
fraction used in the signal. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

 def signalResidue (P : ℕ) [NeZero P] (j : ℤ) : Fin P :=
  ⟨(j:ZMod P).val,ZMod.val_lt _⟩

lemma signalResidue_eq_iff (P : ℕ) [NeZero P] (j : ℤ) (h : Fin P) :
    signalResidue P j = h ↔ j % (P:ℤ) = (h.val:ℤ) % (P:ℤ) := by
  have hmod : (h.val:ℤ) % (P:ℤ) = h.val := Int.emod_eq_of_lt
    (by exact_mod_cast (Nat.zero_le h.val)) (by exact_mod_cast h.isLt)
  rw [hmod,Fin.ext_iff]
  constructor
  · intro hh
    have he := congrArg (fun n : ℕ => (n:ℤ)) hh
    change ((j:ZMod P).val:ℤ) = h.val at he
    rwa [ZMod.val_intCast] at he
  · intro hh
    have he : ((j:ZMod P).val:ℤ) = h.val := by rwa [ZMod.val_intCast]
    exact_mod_cast he

def signalUnitResidues (P : ℕ) [NeZero P] : Finset (Fin P) := by
  classical
  exact Finset.univ.filter (fun h => IsUnit (h.val:ZMod P))

lemma mem_signalUnitResidues (P : ℕ) [NeZero P] (h : Fin P) :
    h ∈ signalUnitResidues P ↔ IsUnit (h.val:ZMod P) := by
  classical
  simp [signalUnitResidues]

lemma signalResidue_mem_units (P : ℕ) [NeZero P] (j : ℤ) :
    signalResidue P j ∈ signalUnitResidues P ↔ IsUnit (j:ZMod P) := by
  rw [mem_signalUnitResidues]
  change IsUnit (((j:ZMod P).val:ℕ):ZMod P) ↔ _
  simp

lemma signalUnitResidues_card_pos (P : ℕ) [NeZero P] :
    0 < (signalUnitResidues P).card := by
  apply Finset.card_pos.mpr
  refine ⟨signalResidue P 1,?_⟩
  rw [signalResidue_mem_units]
  simpa only [Int.cast_one] using (isUnit_one : IsUnit (1:ZMod P))

/-- The selected finite residue classes are exactly the source unit group. -/
lemma signalUnitResidues_card (P : ℕ) [NeZero P] :
    (signalUnitResidues P).card = Fintype.card (ZMod P)ˣ := by
  classical
  let f : (ZMod P)ˣ → ↥(signalUnitResidues P) := fun u =>
    ⟨⟨(u:ZMod P).val,ZMod.val_lt _⟩,by
      rw [mem_signalUnitResidues]
      simpa only [ZMod.natCast_zmod_val] using u.isUnit⟩
  have hf : Bijective f := by
    constructor
    · intro u v he
      apply Units.ext
      apply ZMod.val_injective P
      exact congrArg (fun x : ↥(signalUnitResidues P) => x.val.val) he
    · intro h
      have hu := (mem_signalUnitResidues P h.val).mp h.property
      refine ⟨hu.unit,Subtype.ext (Fin.ext ?_)⟩
      change (hu.unit:ZMod P).val = h.val.val
      rw [hu.unit_spec,ZMod.val_natCast_of_lt h.val.isLt]
  simpa only [Fintype.card_coe] using (Fintype.card_congr (Equiv.ofBijective f hf)).symm

/-- The source's exact positive strength after residue refresh. -/
def refreshedStrength (P : ℕ) [NeZero P] (γ : ℝ) : ℝ :=
  γ*((signalUnitResidues P).card:ℝ)/P

lemma refreshedStrength_eq_unit_fraction (P : ℕ) [NeZero P] (γ : ℝ) :
    refreshedStrength P γ = γ*(Fintype.card (ZMod P)ˣ:ℝ)/P := by
  rw [refreshedStrength,signalUnitResidues_card]

lemma refreshedStrength_pos (P : ℕ) [NeZero P] {γ : ℝ} (hγ : 0 < γ) :
    0 < refreshedStrength P γ := by
  unfold refreshedStrength
  exact div_pos (mul_pos hγ (by exact_mod_cast signalUnitResidues_card_pos P))
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P))

lemma refreshedStrength_le (P : ℕ) [NeZero P] {γ : ℝ} (hγ : 0 ≤ γ) :
    refreshedStrength P γ ≤ γ := by
  have hP : 0 < (P:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P)
  rw [refreshedStrength,div_le_iff₀ hP]
  have hh : (signalUnitResidues P).card ≤ P := by
    simpa only [Fintype.card_fin] using (Finset.card_le_univ (s := signalUnitResidues P))
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hh) hγ

lemma signal_sum_aggregate {ι : Type*} [Fintype ι] (P : ℕ) [NeZero P]
    (γ B : ℝ) (d : ℝ → ℂ) (m : ι → ℤ) (p : ι → UnitAddCircle → ℝ)
    (N : ℤ) (z : UnitAddCircle) :
    (∑ i, p i z*signalCircleModel P γ B d (m i) (N • z)) =
      refreshSignalAggregate (fun i => signalResidue P (m i)) (signalUnitResidues P)
        p (fun i => d ((m i:ℝ)/B)) γ (fun z => fourier (-1) (N • z)) z := by
  classical
  unfold refreshSignalAggregate signalCircleModel
  simp only [mul_add,mul_one,Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum,Complex.re_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hu : IsUnit (m i:ZMod P)
  · have hh := (signalResidue_mem_units P (m i)).mpr hu
    simp only [ite_eq_left hu,ite_eq_left hh,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im]
    ring
  · have hh : signalResidue P (m i) ∉ signalUnitResidues P :=
      fun h => hu ((signalResidue_mem_units P (m i)).mp h)
    simp [hu,hh]

end ThreeTorus
end
end

section

/-! Physical vectors and spectral densities grouped by their actual source
packet. No spectral data is chosen independently of the literal amplitudes. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

 def outputVector {ι : Type*} {S : ι → Finset ℤ}
    (G : PassagePackets (PassageOutputIndex S)) (i : ι) (x : TripleTorus) : ℂ :=
  ∑ j : ↥(S i), packet (G.m ⟨i,j⟩) (G.A ⟨i,j⟩) x

 def outputDensity {ι : Type*} {S : ι → Finset ℤ}
    (G : PassagePackets (PassageOutputIndex S)) (i : ι) (z : UnitAddCircle) : ℝ :=
  ∑ j : ↥(S i), G.density ⟨i,j⟩ z

lemma continuous_outputDensity {ι : Type*} {S : ι → Finset ℤ}
    (G : PassagePackets (PassageOutputIndex S)) (i : ι) : Continuous (outputDensity G i) :=
  continuous_finsetSum _ (fun _ _ => G.density_continuous _)

lemma outputDensity_nonneg {ι : Type*} {S : ι → Finset ℤ}
    (G : PassagePackets (PassageOutputIndex S)) (i : ι) (z : UnitAddCircle) :
    0 ≤ outputDensity G i z := Finset.sum_nonneg (fun _ _ => G.density_nonneg _ z)

lemma continuous_outputVector {ι : Type*} {S : ι → Finset ℤ}
    (G : PassagePackets (PassageOutputIndex S)) (i : ι) : Continuous (outputVector G i) := by
  apply continuous_finsetSum
  intro j _
  exact continuous_packet (G.continuous_amplitude ⟨i,j⟩)

lemma outputVector_eq_retained {ι : Type*} {S : ι → Finset ℤ}
    (F : PassagePackets ι) (G : PassagePackets (PassageOutputIndex S))
    (ψ : UnitAddCircle → ℝ) (χ : ι → ℝ → UnitAddCircle → ℝ)
    (H : ℕ → UnitAddCircle → UnitAddCircle) (n : ℕ)
    (hm : ∀ i, G.m i = i.2.val)
    (hA : ∀ i, G.A i = retainedAmplitude ψ (χ i.1) (F.m i.1) H (F.A i.1) n i.2.val)
    (i : ι) :
    outputVector G i = retainedPassage (F.m i) (H n) (F.A i) (S i)
      (fun j => χ i ((j:ℝ)/n)) ψ := by
  funext x
  unfold outputVector
  simp_rw [hm,hA]
  exact Finset.sum_coe_sort (S i) (fun j =>
    packet j (retainedAmplitude ψ (χ i) (F.m i) H (F.A i) n j) x)

lemma outputVector_spectral_moment {ι : Type*} {S : ι → Finset ℤ}
    (G : PassagePackets (PassageOutputIndex S))
    (hi : Injective G.m) (hmod : G.SpareIndependent) (i : ι) (k : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (outputVector G i x)*
      outputVector G i (twistIter (fun a => (G.periodic.lift a:UnitAddCircle)) k x) ∂tripleVolume) =
      ∫ z, (outputDensity G i z:ℂ)*fourier k z ∂AddCircle.haarAddCircle := by
  have hφ : Continuous (fun a => (G.periodic.lift a:UnitAddCircle)) :=
    (AddCircle.continuous_mk' 1).comp G.speed_continuous
  have hc := disjoint_packet_list_correlation (fun j : ↥(S i) => G.m ⟨i,j⟩)
    (fun j => G.A ⟨i,j⟩) (fun j => G.continuous_amplitude ⟨i,j⟩) hφ
    (fun a b hab he => (hab (by simpa using hi he)).elim) k
  rw [show (∫ x : TripleTorus, starRingEnd ℂ (outputVector G i x)*
      outputVector G i (twistIter (fun a => (G.periodic.lift a:UnitAddCircle)) k x) ∂tripleVolume) =
    ∑ j : ↥(S i), ∫ z, fourier k z ∂packetSpectralMeasure
      (fun a => (G.periodic.lift a:UnitAddCircle)) (G.m ⟨i,j⟩) (G.A ⟨i,j⟩) from hc]
  simp_rw [G.density_spectral hmod]
  simp_rw [moment_withDensity_real (G.density_continuous _).measurable (G.density_nonneg _) (fourier k)]
  unfold outputDensity
  simp only [Complex.ofReal_sum,Finset.sum_mul]
  have hint (j : ↥(S i)) : Integrable (fun z => (G.density ⟨i,j⟩ z:ℂ)*fourier k z)
      AddCircle.haarAddCircle :=
    (((Complex.continuous_ofReal.comp (G.density_continuous ⟨i,j⟩)).mul (fourier k).continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact (integral_finsetSum _ (fun j _ => hint j)).symm

/-- L1 error of a finite sum, with continuity discharging integrability. -/
lemma integral_abs_sum_sub_le {ι : Type*} [Fintype ι]
    {p q : ι → UnitAddCircle → ℝ} (hp : ∀ i, Continuous (p i)) (hq : ∀ i, Continuous (q i)) :
    (∫ z, |(∑ i, p i z)-(∑ i, q i z)| ∂phaseHaar) ≤
      ∑ i, ∫ z, |p i z-q i z| ∂phaseHaar := by
  have he z : (∑ i, p i z)-(∑ i, q i z) = ∑ i, (p i z-q i z) :=
    (Finset.sum_sub_distrib (s := Finset.univ) (fun i => p i z) (fun i => q i z)).symm
  simp_rw [he]
  have hint (i : ι) : Integrable (fun z => |p i z-q i z|) phaseHaar :=
    continuous_circle_integrable ((hp i).sub (hq i)).abs
  calc
    _ ≤ ∫ z, ∑ i, |p i z-q i z| ∂phaseHaar := integral_mono
      (continuous_circle_integrable (continuous_finsetSum _ (fun i _ => (hp i).sub (hq i))).abs)
      (integrable_finsetSum _ (fun i _ => hint i))
      (fun z => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := integral_finsetSum _ (fun i _ => hint i)

end ThreeTorus
end
end

section

/-! Actual transmission with support-linked tracking and its smooth geometric
family. Its positive strength precedes every later finite literal packet list. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
universe u

theorem exists_signal_tracked_family
    {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ α : ℝ, ∃ L : ℕ, ∃ γ₀ : ℝ,
      0 < α ∧ α < b/2 ∧ 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (ι : Type u) [Fintype ι], ∀ (F : PassagePackets ι),
      Injective F.m → F.SpareIndependent → ∀ B : ℝ, 0 < B →
      (∀ i, b ≤ |(F.m i:ℝ)/B|) →
      ∀ ε η : ℝ, 0 < ε → 0 < η →
      ∃ c : ℕ, 0 < c ∧ ∃ δ : ℝ, ∃ cut : LawCutoffs δ,
      ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      0 < δ ∧ δ < 1/8 ∧
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, (c:ℝ)+F.V t)+Δ n*x):UnitAddCircle)) ∧
      let ρ := signalJitter α γ d (signalPrimeProduct L) B c
      let J := quantileCircleJitter ρ cut
      let J₀ := lawJitter ρ cut
      let σ := fun (n : ℕ) a => (((1+J a/n)/n:ℝ):UnitAddCircle)
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ Integrable ρ ∧
      (∀ y, 0 < ρ y) ∧ (∫ y, ρ y = 1) ∧
      (∀ n, Smooth (torusPassage (H n) (σ n)) ∧ Smooth (torusPassage (H n) (σ n)).symm ∧
        MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
      (∀ n, 0 < n → ∀ x : Cover,
        torusPassage (H n) (σ n) (project x) =
          project (passageFamily (fun t => (c:ℝ)+F.V t) J₀ 1 ((n:ℝ)⁻¹,Δ n) x) ∧
        (torusPassage (H n) (σ n)).symm (project x) =
          project (passageFamily (fun t => (c:ℝ)+F.V t) J₀ (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
      (∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ e : ℕ,
        TendstoUniformlyOn
          (fun (n : ℕ) x => iteratedFDeriv ℝ e
            (passageFamily (fun t => (c:ℝ)+F.V t) J₀ r ((n:ℝ)⁻¹,Δ n)) x)
          (fun x => iteratedFDeriv ℝ e (fun y : Cover => ![y 0+r*((c:ℝ)+F.V (y 1)),y 1,y 2]) x)
          atTop K) ∧
      ∃ S : ℕ → ι → Finset ℤ, ∀ᶠ n : ℕ in atTop, 0 < n ∧
        ∃ G : PassagePackets (PassageOutputIndex (S n)),
          Injective G.m ∧ G.SpareIndependent ∧
          G.V = (fun x => (1+J₀ x/n)/n) ∧ (∀ i, G.m i = i.2.val) ∧
          (∀ i,
            (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
              outputVector G i (passageChart (H n) x)‖^2 ∂tripleVolume) < ε ∧
            (∫ z, |outputDensity G i z-F.density i z*signalCircleModel
              (signalPrimeProduct L) γ B d (F.m i) ((n:ℤ) • z)| ∂phaseHaar) < ε) ∧
          (∀ i, ∃ x ∈ F.core i.1,
            |(G.m i:ℝ)/((n:ℝ)*c*B)-(F.m i.1:ℝ)/B| < η ∧
            ∀ y, dist ((G.m i:ℝ)*G.V y:UnitAddCircle)
              ((F.m i.1:ℝ)*F.V x:UnitAddCircle) < η) := by
  classical
  obtain ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,hfamily⟩ := exists_signal_state_family hb hbD hd hdc hdr hd0 hds
  refine ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,?_⟩
  intro γ hγp hγs
  obtain ⟨hdb,hstate⟩ := hfamily γ hγp hγs
  refine ⟨hdb,?_⟩
  intro ι inst F hi hmod B hB hm ε η hε hη
  obtain ⟨P,_hP,hPV⟩ := F.speed_bound
  obtain ⟨M,_hM,hMm⟩ := F.angular_bound
  have hD i : |(F.m i:ℝ)/B| ≤ M/B := by
    rw [abs_div,abs_of_pos hB]
    exact div_le_div_of_nonneg_right (hMm i) hB.le
  let τ := η/4
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτη : τ < η/2 := by dsimp [τ]; linarith
  obtain ⟨c,hc,hbud⟩ := ((hstate ι F hi hmod B hB hm ε τ hε hτ).and
    (support_drift_budgets (D := M/B) (P := P) (M := M) hB hη)).exists
  obtain ⟨hcp,δ,cut,χ,Δ,H,hδ,hδ',hχ,_hχd,hΔ,hΔt,hHc,hHe,
    hρs,hρi,hρp,hρm,hgeo,hgraph,hlimit,S,_hSd,hS,hgood⟩ := hc
  have hb := hbud.2 τ hτ hτη
  obtain ⟨R,_hR,hRJ⟩ := periodic_real_bound (lawJitter_smooth cut hρs hρi hρp hρm).continuous
    (periodize_periodic _)
  refine ⟨c,hcp,δ,cut,Δ,H,hδ,hδ',hΔ,hΔt,hHc,hHe,hρs,hρi,hρp,hρm,hgeo,hgraph,hlimit,S,?_⟩
  filter_upwards [hgood,hb.2 R] with n hn hnb
  obtain ⟨hnp,haul,G,hGi,hGmod,hGV,hGm,hGA,_hGden,hgroup⟩ := hn
  refine ⟨hnp,G,hGi,hGmod,hGV,hGm,?_,?_⟩
  · intro i
    have hv := outputVector_eq_retained F G (neutralCircleCutoff cut) (fun i s _ => χ i s)
      H n hGm hGA i
    have hp : exactRetainedPacketDensity (Ioo δ (1-δ))
        (lawJitter (signalJitter α γ d (signalPrimeProduct L) B c) cut)
        (neutralCircleCutoff cut) (fun s _ => χ i s) (F.m i) H (F.A i) (S n i) n =
        outputDensity G i := by
      have hh := hgroup i (fun _ => True)
      change _ = fun z => ∑ j : ↥(S n i), G.density ⟨i,j⟩ z
      simpa only [Finset.filter_true,ite_true] using hh
    have hh := haul i
    dsimp only at hh
    rw [← hv,hp] at hh
    exact ⟨hh.1,hh.2.1⟩
  · intro i
    obtain ⟨x,hx,ha,ht⟩ := literal_output_tracking hcp hnp hB hD hPV hMm hRJ
      (fun i j hj => (hS n hnp i j).mp hj) (fun i => (hχ i).2.2.2.2) hGm hGV i
    exact ⟨x,hx,ha.trans_lt hb.1,fun y => (ht y).trans_lt hnb.2⟩

end ThreeTorus
end
end

section

/-! The actual neutral refresh, including arbitrarily small linked angular
and temporal drift. Constants are chosen in the manuscript order: carrier,
then broad jitter, and last the passage integer. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

theorem exists_neutral_tracked_family {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) (hi : Injective F.m) (hmod : F.SpareIndependent)
    {B D ε η : ℝ} (hB : 0 < B) (hD : ∀ i, |(F.m i:ℝ)/B| ≤ D)
    (hε : 0 < ε) (hη : 0 < η) {Q : ℕ} [NeZero Q] (hQ : 0 < Q) :
    ∃ c : ℕ, 0 < c ∧ ∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ L : ℝ,
      ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      0 < δ ∧ δ < 1/8 ∧ 0 < L ∧
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, (c:ℝ)+F.V t)+Δ n*x):UnitAddCircle)) ∧
      let J := neutralJitter cut L 0
      let J₀ := neutralJitterReal cut L 0
      let σ := fun (n : ℕ) a => (((1+J a/n)/n:ℝ):UnitAddCircle)
      (∀ n, Smooth (torusPassage (H n) (σ n)) ∧ Smooth (torusPassage (H n) (σ n)).symm ∧
        MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
      (∀ n, 0 < n → ∀ x : Cover,
        torusPassage (H n) (σ n) (project x) =
          project (passageFamily (fun t => (c:ℝ)+F.V t) J₀ 1 ((n:ℝ)⁻¹,Δ n) x) ∧
        (torusPassage (H n) (σ n)).symm (project x) =
          project (passageFamily (fun t => (c:ℝ)+F.V t) J₀ (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
      (∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ d : ℕ,
        TendstoUniformlyOn
          (fun (n : ℕ) x => iteratedFDeriv ℝ d
            (passageFamily (fun t => (c:ℝ)+F.V t) J₀ r ((n:ℝ)⁻¹,Δ n)) x)
          (fun x => iteratedFDeriv ℝ d (fun y : Cover => ![y 0+r*((c:ℝ)+F.V (y 1)),y 1,y 2]) x)
          atTop K) ∧
      ∃ S : ℕ → ι → Finset ℤ, ∀ᶠ n : ℕ in atTop, 0 < n ∧
        ∃ G : PassagePackets (PassageOutputIndex (S n)),
          Injective G.m ∧ G.SpareIndependent ∧
          G.V = (fun x => (1+J₀ x/n)/n) ∧ (∀ i, G.m i = i.2.val) ∧
          (∀ i,
            (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
              outputVector G i (passageChart (H n) x)‖^2 ∂tripleVolume) < ε ∧
            (∫ z, |outputDensity G i z-F.density i z| ∂phaseHaar) < ε ∧
            (∑ h : Fin Q, ∫ z,
              |(∑ j : ↥(S n i), if signalResidue Q j.val = h then G.density ⟨i,j⟩ z else 0)-
                  (Q:ℝ)⁻¹*F.density i z| ∂phaseHaar) < ε) ∧
          (∀ i, ∃ x ∈ F.core i.1,
            |(G.m i:ℝ)/((n:ℝ)*c*B)-(F.m i.1:ℝ)/B| < η ∧
            ∀ y, dist ((G.m i:ℝ)*G.V y:UnitAddCircle)
              ((F.m i.1:ℝ)*F.V x:UnitAddCircle) < η) := by
  classical
  obtain ⟨P,_hP,hPV⟩ := F.speed_bound
  obtain ⟨M,_hM,hMm⟩ := F.angular_bound
  let τ := η/4
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτη : τ < η/2 := by dsimp [τ]; linarith
  obtain ⟨c,hc,hbud⟩ := ((eventually_neutral_state_family F hi hmod hQ hε hτ).and
    (support_drift_budgets (D := D) (P := P) (M := M) hB hη)).exists
  obtain ⟨hcp,δ,cut,L,χ,Δ,H,hδ,hδ',hL,hχ,_hχd,hΔ,hΔt,hHc,hHe,hgeo,hgraph,hlimit,S,_hSd,hS,hgood⟩ := hc
  have hb := hbud.2 τ hτ hτη
  obtain ⟨R,_hR,hRJ⟩ := periodic_real_bound (neutralJitterReal_smooth cut L 0).continuous
    (neutralJitterReal_periodic cut L 0)
  refine ⟨c,hcp,δ,cut,L,Δ,H,hδ,hδ',hL,hΔ,hΔt,hHc,hHe,hgeo,hgraph,hlimit,S,?_⟩
  filter_upwards [hgood,hb.2 R] with n hn hnb
  obtain ⟨hnp,haul,G,hGi,hGmod,hGV,hGm,hGA,_hGden,hgroup⟩ := hn
  refine ⟨hnp,G,hGi,hGmod,hGV,hGm,?_,?_⟩
  · intro i
    have hv := outputVector_eq_retained F G (neutralCircleCutoff cut) (fun i s _ => χ i s)
      H n hGm hGA i
    have hp : exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal cut L 0)
        (neutralCircleCutoff cut) (fun s _ => χ i s) (F.m i) H (F.A i) (S n i) n =
        outputDensity G i := by
      have hh := hgroup i (fun _ => True)
      change _ = fun z => ∑ j : ↥(S n i), G.density ⟨i,j⟩ z
      simpa only [Finset.filter_true,ite_true] using hh
    have hr (h : Fin Q) : exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal cut L 0)
        (neutralCircleCutoff cut) (fun s _ => χ i s) (F.m i) H (F.A i)
          ((S n i).filter (fun j => j % (Q:ℤ) = (h.val:ℤ) % (Q:ℤ))) n =
        (fun z => ∑ j : ↥(S n i), if signalResidue Q j.val = h then G.density ⟨i,j⟩ z else 0) := by
      rw [hgroup]
      funext z
      apply Finset.sum_congr rfl
      intro j _
      simp only [signalResidue_eq_iff Q]
    have hh := haul i
    dsimp only at hh
    rw [← hv,hp] at hh
    simp_rw [hr] at hh
    exact ⟨hh.1,hh.2.1,hh.2.2.2⟩
  · intro i
    obtain ⟨x,hx,ha,ht⟩ := literal_output_tracking hcp hnp hB hD hPV hMm hRJ
      (fun i j hj => (hS n hnp i j).mp hj) (fun i => (hχ i).2.2.2.2) hGm hGV i
    exact ⟨x,hx,ha.trans_lt hb.1,fun y => (ht y).trans_lt hnb.2⟩

end ThreeTorus
end
end

section

/-! Unconditional constructors of the tracked geometric state data. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
universe u

theorem exists_neutral_geometry_state {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) (hi : Injective F.m) (hmod : F.SpareIndependent)
    {B D ε η : ℝ} (hB : 0 < B) (hD : ∀ i, |(F.m i:ℝ)/B| ≤ D)
    (hε : 0 < ε) (hη : 0 < η) {Q : ℕ} [NeZero Q] (hQ : 0 < Q) :
    ∃ g : PassageGeometryFamily F.V, ∃ S : ℕ → ι → Finset ℤ,
      ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ G : PassagePackets (PassageOutputIndex (S n)),
        Injective G.m ∧ G.SpareIndependent ∧
        G.V = (fun x => (1+g.J₀ x/n)/n) ∧ (∀ i, G.m i = i.2.val) ∧
        (∀ i,
          (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
            outputVector G i (passageChart (g.H n) x)‖^2 ∂tripleVolume) < ε ∧
          (∫ z, |outputDensity G i z-F.density i z| ∂phaseHaar) < ε ∧
          (∑ h : Fin Q, ∫ z,
            |(∑ j : ↥(S n i), if signalResidue Q j.val = h then G.density ⟨i,j⟩ z else 0)-
              (Q:ℝ)⁻¹*F.density i z| ∂phaseHaar) < ε) ∧
        StateTracks F G Sigma.fst B (g.scale B n) η := by
  obtain ⟨c,hc,δ,cut,L,Δ,H,_hδ,_hδ',_hL,hΔ,hΔt,hHc,hHe,hgeo,hgraph,hlimit,S,hgood⟩ :=
    exists_neutral_tracked_family F hi hmod hB hD hε hη hQ
  let g : PassageGeometryFamily F.V :=
    ⟨c,hc,Δ,H,neutralJitter cut L 0,neutralJitterReal cut L 0,(fun _ => rfl),
      continuous_neutralJitter cut L 0,hΔ,hΔt,hHc,hHe,hgeo,hgraph,hlimit⟩
  exact ⟨g,S,hgood⟩

theorem exists_signal_geometry_state
    {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ L : ℕ, ∃ γ₀ : ℝ, 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (ι : Type u) [Fintype ι], ∀ (F : PassagePackets ι),
      Injective F.m → F.SpareIndependent → ∀ B : ℝ, 0 < B →
      (∀ i, b ≤ |(F.m i:ℝ)/B|) →
      ∀ ε η : ℝ, 0 < ε → 0 < η →
      ∃ g : PassageGeometryFamily F.V, ∃ S : ℕ → ι → Finset ℤ,
        ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ G : PassagePackets (PassageOutputIndex (S n)),
          Injective G.m ∧ G.SpareIndependent ∧
          G.V = (fun x => (1+g.J₀ x/n)/n) ∧ (∀ i, G.m i = i.2.val) ∧
          (∀ i,
            (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
              outputVector G i (passageChart (g.H n) x)‖^2 ∂tripleVolume) < ε ∧
            (∫ z, |outputDensity G i z-F.density i z*signalCircleModel
              (signalPrimeProduct L) γ B d (F.m i) ((n:ℤ) • z)| ∂phaseHaar) < ε) ∧
          StateTracks F G Sigma.fst B (g.scale B n) η := by
  obtain ⟨α,L,γ₀,_hα,_hαb,hL,hLD,hγ₀,hfamily⟩ := exists_signal_tracked_family hb hbD hd hdc hdr hd0 hds
  refine ⟨L,γ₀,hL,hLD,hγ₀,?_⟩
  intro γ hγp hγs
  obtain ⟨hdb,hstate⟩ := hfamily γ hγp hγs
  refine ⟨hdb,?_⟩
  intro ι inst F hi hmod B hB hm ε η hε hη
  obtain ⟨c,hc,δ,cut,Δ,H,_hδ,_hδ',hΔ,hΔt,hHc,hHe,
    hρs,hρi,hρp,hρm,hgeo,hgraph,hlimit,S,hgood⟩ := hstate ι F hi hmod B hB hm ε η hε hη
  let ρ := signalJitter α γ d (signalPrimeProduct L) B c
  let g : PassageGeometryFamily F.V :=
    ⟨c,hc,Δ,H,quantileCircleJitter ρ cut,lawJitter ρ cut,(fun _ => rfl),
      continuous_quantileCircleJitter cut hρs hρi hρp hρm,hΔ,hΔt,hHc,hHe,hgeo,hgraph,hlimit⟩
  exact ⟨g,S,hgood⟩

end ThreeTorus
end
end

section

/-! The continuity step in actual refresh--transmit. These estimates are
pointwise on genuine packet supports and require no independence hypothesis. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma normalized_band_under_drift {x y b D e : ℝ}
    (hlo : b+e ≤ |x|) (hhi : |x| ≤ D-e) (hxy : |y-x| < e) :
    b < |y| ∧ |y| < D := by
  have hh := abs_abs_sub_abs_le_abs_sub y x
  have ha := abs_lt.mp (hh.trans_lt hxy)
  constructor <;> linarith

theorem coefficient_match_drift_budget {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) {d : ℝ → ℂ} (hd : Continuous d) (hdc : HasCompactSupport d)
    (a : ι → UnitAddCircle → ℂ) (ha : ∀ i, Continuous (a i))
    {B ω e : ℝ} (he : 0 < e)
    (hmatch : ∀ i x, x ∈ F.core i →
      ‖d ((F.m i:ℝ)/B)-a i ((F.m i:ℝ)*F.V x:UnitAddCircle)‖ ≤ ω) :
    ∃ η : ℝ, 0 < η ∧ ∀ (κ : Type*) (G : PassagePackets κ) (parent : κ → ι) (B' : ℝ),
      (∀ j z, G.density j z ≠ 0 → ∃ x ∈ F.core (parent j),
        |(G.m j:ℝ)/B'-(F.m (parent j):ℝ)/B| < η ∧
        dist z ((F.m (parent j):ℝ)*F.V x:UnitAddCircle) < η) →
      ∀ j z, G.density j z ≠ 0 → ‖d ((G.m j:ℝ)/B')-a (parent j) z‖ ≤ ω+e := by
  obtain ⟨η₁,hη₁,hU₁⟩ := Metric.uniformContinuous_iff.mp
    (hdc.uniformContinuous_of_continuous hd) (e/2) (half_pos he)
  have hau : UniformContinuous (fun z => fun i => a i z) := uniformContinuous_pi.mpr
    (fun i => CompactSpace.uniformContinuous_of_continuous (ha i))
  obtain ⟨η₂,hη₂,hU₂⟩ := Metric.uniformContinuous_iff.mp hau (e/2) (half_pos he)
  refine ⟨min η₁ η₂,lt_min hη₁ hη₂,?_⟩
  intro κ G parent B' htrack j z hz
  obtain ⟨x,hx,hidx,ht⟩ := htrack j z hz
  have h₁ : dist (d ((G.m j:ℝ)/B')) (d ((F.m (parent j):ℝ)/B)) < e/2 :=
    hU₁ (by simpa only [Real.dist_eq] using hidx.trans_le (min_le_left _ _))
  have h₂ : dist (a (parent j) ((F.m (parent j):ℝ)*F.V x:UnitAddCircle))
      (a (parent j) z) < e/2 := by
    apply (dist_le_pi_dist (fun i => a i ((F.m (parent j):ℝ)*F.V x:UnitAddCircle))
      (fun i => a i z) (parent j)).trans_lt
    exact hU₂ (by rw [dist_comm]; exact ht.trans_le (min_le_right _ _))
  have hm := hmatch (parent j) x hx
  rw [← dist_eq_norm] at hm ⊢
  have hh := (dist_triangle (d ((G.m j:ℝ)/B')) (d ((F.m (parent j):ℝ)/B))
    (a (parent j) z)).trans (add_le_add le_rfl
      (dist_triangle (d ((F.m (parent j):ℝ)/B))
        (a (parent j) ((F.m (parent j):ℝ)*F.V x:UnitAddCircle)) (a (parent j) z)))
  linarith

end ThreeTorus
end
end

section

/-! Actual two-passage sums, still expressed in their literal final packet state. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

 def pairOutputVector {ι : Type*} {S : ι → Finset ℤ}
    {T : PassageOutputIndex S → Finset ℤ}
    (K : PassagePackets (PassageOutputIndex T)) (i : ι) (x : TripleTorus) : ℂ :=
  ∑ j : ↥(S i), outputVector K ⟨i,j⟩ x

 def pairOutputDensity {ι : Type*} {S : ι → Finset ℤ}
    {T : PassageOutputIndex S → Finset ℤ}
    (K : PassagePackets (PassageOutputIndex T)) (i : ι) (z : UnitAddCircle) : ℝ :=
  ∑ j : ↥(S i), outputDensity K ⟨i,j⟩ z

lemma continuous_pairOutputVector {ι : Type*} {S : ι → Finset ℤ}
    {T : PassageOutputIndex S → Finset ℤ}
    (K : PassagePackets (PassageOutputIndex T)) (i : ι) : Continuous (pairOutputVector K i) :=
  continuous_finsetSum _ (fun _ _ => continuous_outputVector K _)

lemma continuous_pairOutputDensity {ι : Type*} {S : ι → Finset ℤ}
    {T : PassageOutputIndex S → Finset ℤ}
    (K : PassagePackets (PassageOutputIndex T)) (i : ι) : Continuous (pairOutputDensity K i) :=
  continuous_finsetSum _ (fun _ _ => continuous_outputDensity K _)

lemma transmission_sum_budget {ι : Type*} [Fintype ι] (S : ι → Finset ℤ)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ e : ℝ, 0 < e ∧ ∀ i : ι,
      (Fintype.card ↥(S i):ℝ)*e < τ ∧ (Fintype.card ↥(S i):ℝ)^2*e < τ := by
  classical
  let J : ℝ := Fintype.card (PassageOutputIndex S)
  have hJ : 0 ≤ J := Nat.cast_nonneg _
  obtain ⟨e,he,heb⟩ := exists_pos_mul_lt hτ (J^2+J+1)
  refine ⟨e,he,fun i => ?_⟩
  have hcard : (Fintype.card ↥(S i):ℝ) ≤ J := by
    dsimp [J]
    exact_mod_cast (Fintype.card_le_of_injective (f := fun j : ↥(S i) => (⟨i,j⟩ : PassageOutputIndex S))
      (fun _ _ h => by simpa using h))
  have hcard0 : (0:ℝ) ≤ Fintype.card ↥(S i) := Nat.cast_nonneg _
  have hs : (Fintype.card ↥(S i):ℝ)^2 ≤ J^2 := by gcongr
  constructor <;> nlinarith

lemma transmission_pair_physical {ι : Type*} {S : ι → Finset ℤ}
    {T : PassageOutputIndex S → Finset ℤ}
    (G : PassagePackets (PassageOutputIndex S))
    (K : PassagePackets (PassageOutputIndex T))
    {H : UnitAddCircle → UnitAddCircle} (hH : Continuous H)
    {e τ : ℝ} (i : ι)
    (he : ∀ j, physicalError (packet (G.m j) (G.A j)) (outputVector K j ∘ passageChart H) < e)
    (hτ : (Fintype.card ↥(S i):ℝ)^2*e < τ) :
    physicalError (outputVector G i) (pairOutputVector K i ∘ passageChart H) < τ := by
  have hsum := physicalError_sum
    (fun j : ↥(S i) => continuous_packet (m := G.m ⟨i,j⟩) (G.continuous_amplitude ⟨i,j⟩))
    (fun j => (continuous_outputVector K ⟨i,j⟩).comp (continuous_passageChart hH))
  change physicalError (outputVector G i) (pairOutputVector K i ∘ passageChart H) ≤ _ at hsum
  have hb : (∑ j : ↥(S i), physicalError (packet (G.m ⟨i,j⟩) (G.A ⟨i,j⟩))
      (outputVector K ⟨i,j⟩ ∘ passageChart H)) ≤ (Fintype.card ↥(S i):ℝ)*e := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.univ) (fun j _ => (he ⟨i,j⟩).le))
  apply hsum.trans_lt
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
  simpa only [sq,mul_assoc] using hτ

lemma transmission_pair_density {ι : Type*} {S : ι → Finset ℤ}
    {T : PassageOutputIndex S → Finset ℤ}
    (K : PassagePackets (PassageOutputIndex T))
    (q : PassageOutputIndex S → UnitAddCircle → ℝ) (hq : ∀ j, Continuous (q j))
    {e τ : ℝ} (i : ι)
    (he : ∀ j, (∫ z, |outputDensity K j z-q j z| ∂phaseHaar) < e)
    (hτ : (Fintype.card ↥(S i):ℝ)*e < τ) :
    (∫ z, |pairOutputDensity K i z-(∑ j : ↥(S i), q ⟨i,j⟩ z)| ∂phaseHaar) < τ := by
  apply (integral_abs_sum_sub_le (fun j : ↥(S i) => continuous_outputDensity K ⟨i,j⟩)
    (fun j => hq ⟨i,j⟩)).trans_lt
  apply lt_of_le_of_lt _ hτ
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
    (Finset.sum_le_sum (s := Finset.univ) (fun j _ => (he ⟨i,j⟩).le))

/-- Budget choice independent of passage integers and all future packet lists. -/
lemma refresh_pair_error_budgets {γ ω A M ε : ℝ}
    (hγ : 0 ≤ γ) (hω : 0 ≤ ω) (hA : 0 ≤ A) (_hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ κ r t : ℝ, 0 < κ ∧ 0 < r ∧ 0 < t ∧ 2*r+2*t < ε ∧
      ∀ m E T : ℝ, 0 ≤ m → m ≤ M → 0 ≤ E → E < r → T < t →
        T+(1+2*γ*A)*E+2*γ*(ω+κ)*(m+E) < 2*γ*ω*m+ε := by
  obtain ⟨κ,hκ,hκb⟩ := exists_pos_mul_lt (show 0 < ε/4 by positivity) (2*γ*M)
  obtain ⟨r₀,hr₀,hrb⟩ := exists_pos_mul_lt (show 0 < ε/4 by positivity)
    (1+2*γ*A+2*γ*(ω+κ))
  let r := min r₀ (ε/16)
  have hr : 0 < r := lt_min hr₀ (by positivity)
  have hrr : r ≤ r₀ := min_le_left _ _
  have hre : r ≤ ε/16 := min_le_right _ _
  refine ⟨κ,r,ε/16,hκ,hr,by positivity,by linarith,?_⟩
  intro m E T hm hmM _hE hEr hT
  have hc : 0 ≤ 1+2*γ*A+2*γ*(ω+κ) := by positivity
  have hEb : (1+2*γ*A+2*γ*(ω+κ))*E < ε/4 :=
    (mul_le_mul_of_nonneg_left (hEr.le.trans hrr) hc).trans_lt hrb
  have hmb : 2*γ*κ*m < ε/4 := by
    have hh := mul_le_mul_of_nonneg_left hmM (show 0 ≤ 2*γ*κ by positivity)
    nlinarith
  nlinarith

end ThreeTorus
end
end

section

/-! Refresh then transmission on actual packet states (03-signals, 329--456).
The second passage integer remains arbitrarily large after the first exact
state is fixed. Neither a residue-balancing oracle nor independent model
spectral densities are assumed. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
universe u

lemma finite_circle_coefficients_bound {ι : Type*} [Fintype ι]
    (a : ι → UnitAddCircle → ℂ) (ha : ∀ i, Continuous (a i)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ i z, ‖a i z‖ ≤ A := by
  have hc : Continuous (fun z => fun i => a i z) := continuous_pi ha
  obtain ⟨A,hA⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨max A 0,le_max_right _ _,fun i z =>
    (norm_le_pi_norm (fun i => a i z) i).trans ((hA z (mem_univ z)).trans (le_max_left _ _))⟩

lemma refresh_residue_integral_eq {ι : Type*} {S : ι → Finset ℤ}
    (G : PassagePackets (PassageOutputIndex S)) (q : UnitAddCircle → ℝ)
    (hq : Continuous q) (P : ℕ) [NeZero P]
    (hm : ∀ j, G.m j = j.2.val) (i : ι) :
    (∫ z, refreshResidueError (fun j : ↥(S i) => signalResidue P (G.m ⟨i,j⟩))
      (fun j => G.density ⟨i,j⟩) q z ∂phaseHaar) =
      ∑ h : Fin P, ∫ z,
        |(∑ j : ↥(S i), if signalResidue P j.val = h then G.density ⟨i,j⟩ z else 0)-
          (P:ℝ)⁻¹*q z| ∂phaseHaar := by
  classical
  unfold refreshResidueError
  simp_rw [hm,Fintype.card_fin,div_eq_mul_inv,mul_comm (q _) ((P:ℝ)⁻¹)]
  apply integral_finsetSum
  intro h _
  apply continuous_circle_integrable
  apply Continuous.abs
  apply Continuous.sub _ (hq.const_mul _)
  apply continuous_finsetSum
  intro j _
  split_ifs <;> first | exact G.density_continuous _ | exact continuous_const

/-- Actual refresh/transmit state, with the exact positive strength fixed before
all data and error budgets. Each input packet can carry its original color's
continuous coefficient; finite color grouping is by summation. -/
theorem exists_refresh_transmit_state
    {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ L : ℕ, ∃ γ₀ : ℝ, 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (ι : Type u) [Fintype ι], ∀ (F : PassagePackets ι),
      Injective F.m → F.SpareIndependent → ∀ B : ℝ, 0 < B →
      ∀ margin : ℝ, 0 < margin →
      (∀ i, b+margin ≤ |(F.m i:ℝ)/B| ∧ |(F.m i:ℝ)/B| ≤ D-margin) →
      ∀ (a : ι → UnitAddCircle → ℂ), (∀ i, Continuous (a i)) →
      ∀ ω : ℝ, 0 ≤ ω →
      (∀ i x, x ∈ F.core i →
        ‖d ((F.m i:ℝ)/B)-a i ((F.m i:ℝ)*F.V x:UnitAddCircle)‖ ≤ ω) →
      ∀ ε η : ℝ, 0 < ε → 0 < η →
      ∃ g : PassageGeometryFamily F.V, ∃ S : ℕ → ι → Finset ℤ,
        ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ G : PassagePackets (PassageOutputIndex (S n)),
          Injective G.m ∧ G.SpareIndependent ∧
          G.V = (fun x => (1+g.J₀ x/n)/n) ∧ (∀ i, G.m i = i.2.val) ∧
          ∃ g' : PassageGeometryFamily G.V,
          ∃ T : ℕ → PassageOutputIndex (S n) → Finset ℤ,
          ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∃ K : PassagePackets (PassageOutputIndex (T N)),
            Injective K.m ∧ K.SpareIndependent ∧
            K.V = (fun x => (1+g'.J₀ x/N)/N) ∧ (∀ i, K.m i = i.2.val) ∧
            (∀ i,
              physicalError (packet (F.m i) (F.A i))
                (pairOutputVector K i ∘ passageChart (g'.H N) ∘ passageChart (g.H n)) < ε ∧
              (∫ z, |pairOutputDensity K i z-F.density i z*
                (1+2*refreshedStrength (signalPrimeProduct L) γ*
                  (fourier (-1) ((N:ℤ) • z)*a i z).re)| ∂phaseHaar) <
                2*γ*ω*(∫ z, |F.density i z| ∂phaseHaar)+ε) ∧
            StateTracks F K (Sigma.fst ∘ Sigma.fst) B (g'.scale (g.scale B n) N) η := by
  classical
  obtain ⟨L,γ₀,hL,hLD,hγ₀,hfamily⟩ := exists_signal_geometry_state.{u} hb hbD hd hdc hdr hd0 hds
  refine ⟨L,γ₀,hL,hLD,hγ₀,?_⟩
  intro γ hγp hγs
  obtain ⟨hdb,hsignal⟩ := hfamily γ hγp hγs
  refine ⟨hdb,?_⟩
  intro ι inst F hi hmod B hB margin hmargin hband a ha ω hω hmatch ε η hε hη
  obtain ⟨A,hA,haA⟩ := finite_circle_coefficients_bound a ha
  obtain ⟨M₀,hM₀⟩ := (Set.finite_range (fun i => ∫ z, |F.density i z| ∂phaseHaar)).isCompact.isBounded.exists_norm_le
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hmass i : (∫ z, |F.density i z| ∂phaseHaar) ≤ M :=
    (le_abs_self _).trans ((hM₀ _ (mem_range_self i)).trans (le_max_left _ _))
  obtain ⟨κ,r,t,hκ,hr,ht,hphys,hbud⟩ := refresh_pair_error_budgets hγp.le hω hA hM hε
  obtain ⟨η₀,hη₀,hcoeff⟩ := coefficient_match_drift_budget F hd.continuous hdc a ha hκ hmatch
  let η₁ := min η₀ (min margin (η/2))
  have hη₁ : 0 < η₁ := lt_min hη₀ (lt_min hmargin (half_pos hη))
  have hη₁₀ : η₁ ≤ η₀ := min_le_left _ _
  have hη₁m : η₁ ≤ margin := (min_le_right _ _).trans (min_le_left _ _)
  have hη₁η : η₁ ≤ η/2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨g,S,hrefresh⟩ := exists_neutral_geometry_state F hi hmod hB
    (fun i => (hband i).2.trans (by linarith : D-margin ≤ D)) hr hη₁
    (signalPrimeProduct_pos L)
  refine ⟨g,S,?_⟩
  filter_upwards [hrefresh] with n hn
  obtain ⟨hnp,G,hGi,hGmod,hGV,hGm,hGerror,hGtrack⟩ := hn
  have hB' := g.scale_pos hB hnp
  have hGband j : b ≤ |(G.m j:ℝ)/g.scale B n| := by
    obtain ⟨x,_hx,ha',_ht'⟩ := hGtrack j
    exact (normalized_band_under_drift (hband j.1).1 (hband j.1).2
      (ha'.trans_le hη₁m)).1.le
  have hcm := hcoeff (PassageOutputIndex (S n)) G Sigma.fst (g.scale B n)
    ((hGtrack.mono hη₁₀).density)
  obtain ⟨e,he,heb⟩ := transmission_sum_budget (S n) ht
  obtain ⟨g',T,htransmit⟩ := hsignal (PassageOutputIndex (S n)) G hGi hGmod
    (g.scale B n) hB' hGband e (η/2) he (half_pos hη)
  refine ⟨hnp,G,hGi,hGmod,hGV,hGm,g',T,?_⟩
  filter_upwards [htransmit] with N hN
  obtain ⟨hNp,K,hKi,hKmod,hKV,hKm,hKerror,hKtrack⟩ := hN
  refine ⟨hNp,K,hKi,hKmod,hKV,hKm,?_,?_⟩
  · intro i
    constructor
    · have hsecond := transmission_pair_physical G K (g'.Hcontinuous N) i
        (fun j => (hKerror j).1) (heb i).2
      have hsecond' : physicalError (outputVector G i ∘ passageChart (g.H n))
          (pairOutputVector K i ∘ passageChart (g'.H N) ∘ passageChart (g.H n)) < t := by
        change physicalError (outputVector G i ∘ passageChart (g.H n))
          ((pairOutputVector K i ∘ passageChart (g'.H N)) ∘ passageChart (g.H n)) < t
        rwa [physicalError_chart (g.Hcontinuous n).measurable]
      have hfirst : physicalError (packet (F.m i) (F.A i))
          (outputVector G i ∘ passageChart (g.H n)) < r := (hGerror i).1
      have hh := physicalError_triangle (continuous_packet (m := F.m i) (F.continuous_amplitude i))
        ((continuous_outputVector G i).comp (continuous_passageChart (g.Hcontinuous n)))
        (((continuous_pairOutputVector K i).comp (continuous_passageChart (g'.Hcontinuous N))).comp
          (continuous_passageChart (g.Hcontinuous n)))
      change physicalError (packet (F.m i) (F.A i))
        (pairOutputVector K i ∘ passageChart (g'.H N) ∘ passageChart (g.H n)) ≤ _ at hh
      simp only [Function.comp_assoc] at hh
      linarith
    · let p : ↥(S n i) → UnitAddCircle → ℝ := fun j => G.density ⟨i,j⟩
      let rr : ↥(S n i) → Fin (signalPrimeProduct L) :=
        fun j => signalResidue (signalPrimeProduct L) (G.m ⟨i,j⟩)
      let cc : ↥(S n i) → ℂ := fun j => d ((G.m ⟨i,j⟩:ℝ)/g.scale B n)
      let ee : UnitAddCircle → ℂ := fun z => fourier (-1) ((N:ℤ) • z)
      have hee : Continuous ee := (fourier (-1)).continuous.comp (continuous_zsmul (N:ℤ))
      have hT := transmission_pair_density K
        (fun j z => G.density j z*signalCircleModel (signalPrimeProduct L) γ (g.scale B n) d (G.m j) ((N:ℤ) • z))
        (fun j => (G.density_continuous j).mul
          ((continuous_signalCircleModel _ _ _ _ _).comp (continuous_zsmul (N:ℤ)))) i
        (fun j => (hKerror j).2) (heb i).1
      have hmodel : (fun z => ∑ j : ↥(S n i), G.density ⟨i,j⟩ z*
        signalCircleModel (signalPrimeProduct L) γ (g.scale B n) d (G.m ⟨i,j⟩) ((N:ℤ) • z)) =
          refreshSignalAggregate rr (signalUnitResidues (signalPrimeProduct L)) p cc γ ee := by
        funext z
        exact signal_sum_aggregate _ _ _ _ _ _ _ _
      rw [show (∫ z, |pairOutputDensity K i z-(∑ j : ↥(S n i), G.density ⟨i,j⟩ z*
        signalCircleModel (signalPrimeProduct L) γ (g.scale B n) d (G.m ⟨i,j⟩) ((N:ℤ) • z))| ∂phaseHaar) =
        ∫ z, |pairOutputDensity K i z-refreshSignalAggregate rr
          (signalUnitResidues (signalPrimeProduct L)) p cc γ ee z| ∂phaseHaar by rw [← hmodel]] at hT
      have hE : (∫ z, refreshResidueError rr p (F.density i) z ∂phaseHaar) < r := by
        rw [refresh_residue_integral_eq G (F.density i) (F.density_continuous i) _ hGm i]
        exact (hGerror i).2.2
      have hbound := refresh_transmit_L1 rr (signalUnitResidues (signalPrimeProduct L)) cc
        (fun j => G.density_continuous ⟨i,j⟩) (ha i) hee (F.density_continuous i)
        (continuous_pairOutputDensity K i) hγp.le (by positivity : 0 ≤ ω+κ)
        (fun j z => G.density_nonneg ⟨i,j⟩ z)
        (fun z => by simpa only [ee,fourier_apply,Circle.norm_coe] using (le_refl (1:ℝ)))
        (haA i) (fun j z hj => hcm ⟨i,j⟩ z hj)
      simp only [Fintype.card_fin] at hbound
      change _ ≤ _ at hbound
      apply hbound.trans_lt
      exact hbud _ _ _ (integral_nonneg (fun _ => abs_nonneg _)) (hmass i)
        (integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))) hE hT
  · exact (hGtrack.trans hKtrack).mono (by linarith)

end ThreeTorus
end
end

section

/-! Literal color sums in the concrete packet state. Colors are labels, not
new independent spectral data. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

variable {ι R : Type*} [Fintype ι] [DecidableEq R]

def colorVector (F : PassagePackets ι) (c : ι → R) (r : R) (x : TripleTorus) : ℂ :=
  ∑ i, if c i = r then packet (F.m i) (F.A i) x else 0

def colorDensity (F : PassagePackets ι) (c : ι → R) (r : R) (z : UnitAddCircle) : ℝ :=
  ∑ i, if c i = r then F.density i z else 0

lemma continuous_colorVector (F : PassagePackets ι) (c : ι → R) (r : R) :
    Continuous (colorVector F c r) := by
  apply continuous_finsetSum
  intro i _
  split_ifs <;> first | exact continuous_packet (F.continuous_amplitude i) | exact continuous_const

lemma continuous_colorDensity (F : PassagePackets ι) (c : ι → R) (r : R) :
    Continuous (colorDensity F c r) := by
  apply continuous_finsetSum
  intro i _
  split_ifs <;> first | exact F.density_continuous i | exact continuous_const

lemma colorDensity_nonneg (F : PassagePackets ι) (c : ι → R) (r : R) (z : UnitAddCircle) :
    0 ≤ colorDensity F c r z := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> first | exact F.density_nonneg i z | exact le_refl _

lemma colorDensity_mass (F : PassagePackets ι) (c : ι → R) (r : R) :
    (∫ z, colorDensity F c r z ∂phaseHaar) =
      ∑ i, if c i = r then ∫ z, F.density i z ∂phaseHaar else 0 := by
  unfold colorDensity
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  · intro i _
    split_ifs <;> first | exact continuous_circle_integrable (F.density_continuous i) | exact (integrable_zero UnitAddCircle ℝ phaseHaar)

lemma colorVector_pair {S : ι → Finset ℤ} {T : PassageOutputIndex S → Finset ℤ}
    (K : PassagePackets (PassageOutputIndex T)) (c : ι → R) (r : R) (x : TripleTorus) :
    colorVector K (c ∘ Sigma.fst ∘ Sigma.fst) r x =
      ∑ i, if c i = r then pairOutputVector K i x else 0 := by
  unfold colorVector pairOutputVector outputVector
  rw [Fintype.sum_sigma]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : c i = r
  · simp only [Function.comp_apply,h,ite_true]
  · simp only [Function.comp_apply,h,ite_false,Finset.sum_const_zero]

lemma colorDensity_pair {S : ι → Finset ℤ} {T : PassageOutputIndex S → Finset ℤ}
    (K : PassagePackets (PassageOutputIndex T)) (c : ι → R) (r : R) (z : UnitAddCircle) :
    colorDensity K (c ∘ Sigma.fst ∘ Sigma.fst) r z =
      ∑ i, if c i = r then pairOutputDensity K i z else 0 := by
  unfold colorDensity pairOutputDensity outputDensity
  rw [Fintype.sum_sigma]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : c i = r
  · simp only [Function.comp_apply,h,ite_true]
  · simp only [Function.comp_apply,h,ite_false,Finset.sum_const_zero]

lemma colored_physical_bound {f g : ι → TripleTorus → ℂ}
    (hf : ∀ i, Continuous (f i)) (hg : ∀ i, Continuous (g i))
    (c : ι → R) (r : R) {e ε : ℝ} (he : 0 ≤ e)
    (h : ∀ i, physicalError (f i) (g i) ≤ e)
    (hε : (Fintype.card ι:ℝ)^2*e < ε) :
    physicalError (fun x => ∑ i, if c i = r then f i x else 0)
      (fun x => ∑ i, if c i = r then g i x else 0) < ε := by
  have hf' i : Continuous (fun x => if c i = r then f i x else 0) := by
    split_ifs <;> first | exact hf i | exact continuous_const
  have hg' i : Continuous (fun x => if c i = r then g i x else 0) := by
    split_ifs <;> first | exact hg i | exact continuous_const
  have hb i : physicalError (fun x => if c i = r then f i x else 0)
      (fun x => if c i = r then g i x else 0) ≤ e := by
    split_ifs <;> first | exact h i | simpa [physicalError] using he
  apply (physicalError_sum hf' hg').trans_lt
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i))
    (show (0:ℝ) ≤ Fintype.card ι from Nat.cast_nonneg _)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  apply hh.trans_lt
  simpa only [sq,mul_assoc] using hε

lemma colored_density_bound {p q : ι → UnitAddCircle → ℝ}
    (hp : ∀ i, Continuous (p i)) (hq : ∀ i, Continuous (q i))
    (c : ι → R) (r : R) (mass : ι → ℝ) {e γ ω : ℝ} (he : 0 ≤ e)
    (h : ∀ i, (∫ z, |p i z-q i z| ∂phaseHaar) ≤ γ*ω*mass i+e) :
    (∫ z, |(∑ i, if c i = r then p i z else 0)-(∑ i, if c i = r then q i z else 0)| ∂phaseHaar) ≤
      γ*ω*(∑ i, if c i = r then mass i else 0)+(Fintype.card ι:ℝ)*e := by
  have hp' i : Continuous (fun z => if c i = r then p i z else 0) := by
    split_ifs <;> first | exact hp i | exact continuous_const
  have hq' i : Continuous (fun z => if c i = r then q i z else 0) := by
    split_ifs <;> first | exact hq i | exact continuous_const
  apply (integral_abs_sum_sub_le hp' hq').trans
  calc
    _ ≤ ∑ i, (γ*ω*(if c i = r then mass i else 0)+e) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> first | exact h i | simpa using he
    _ = _ := by rw [Finset.sum_add_distrib,Finset.mul_sum]; simp

/-- Aggregate the SAME literal two-passage output state, without changing its
colors or choosing spectral densities independently. -/
theorem color_pair_errors {S : ι → Finset ℤ} {T : PassageOutputIndex S → Finset ℤ}
    (F : PassagePackets ι) (K : PassagePackets (PassageOutputIndex T))
    (c : ι → R) (a : R → UnitAddCircle → ℂ) (ha : ∀ r, Continuous (a r))
    {H H' : UnitAddCircle → UnitAddCircle} (hH : Continuous H) (hH' : Continuous H')
    (N : ℕ) (ell : ℝ) {γ ω e ε : ℝ} (he : 0 < e)
    (hε : (Fintype.card ι:ℝ)*e < ε) (hε' : (Fintype.card ι:ℝ)^2*e < ε)
    (h : ∀ i,
      physicalError (packet (F.m i) (F.A i))
        (pairOutputVector K i ∘ passageChart H' ∘ passageChart H) < e ∧
      (∫ z, |pairOutputDensity K i z-F.density i z*
        (1+2*ell*(fourier (-1) ((N:ℤ) • z)*a (c i) z).re)| ∂phaseHaar) <
          2*γ*ω*(∫ z, |F.density i z| ∂phaseHaar)+e) :
    ∀ r,
      physicalError (colorVector F c r)
        (colorVector K (c ∘ Sigma.fst ∘ Sigma.fst) r ∘ passageChart H' ∘ passageChart H) < ε ∧
      (∫ z, |colorDensity K (c ∘ Sigma.fst ∘ Sigma.fst) r z-colorDensity F c r z*
        (1+2*ell*(fourier (-1) ((N:ℤ) • z)*a r z).re)| ∂phaseHaar) <
          2*γ*ω*(∫ z, colorDensity F c r z ∂phaseHaar)+ε := by
  intro r
  constructor
  · have hh := colored_physical_bound
      (fun i => continuous_packet (m := F.m i) (F.continuous_amplitude i))
      (fun i => ((continuous_pairOutputVector K i).comp (continuous_passageChart hH')).comp
        (continuous_passageChart hH)) c r he.le (fun i => (h i).1.le) hε'
    change physicalError (colorVector F c r) _ < ε at hh
    have heq : (colorVector K (c ∘ Sigma.fst ∘ Sigma.fst) r ∘ passageChart H' ∘ passageChart H) =
        (fun x => ∑ i, if c i = r then pairOutputVector K i ((passageChart H') ((passageChart H) x)) else 0) := by
      funext x
      exact colorVector_pair K c r _
    rw [heq]
    exact hh
  · let q (i : ι) (z : UnitAddCircle) := F.density i z*
      (1+2*ell*(fourier (-1) ((N:ℤ) • z)*a (c i) z).re)
    have hq i : Continuous (q i) := (F.density_continuous i).mul
      (continuous_const.add (Continuous.const_mul
        (Complex.continuous_re.comp (((fourier (-1)).continuous.comp (continuous_zsmul (N:ℤ))).mul
          (ha (c i)))) _))
    have hh := colored_density_bound (fun i => continuous_pairOutputDensity K i) hq c r
      (fun i => ∫ z, F.density i z ∂phaseHaar) he.le
      (γ := 2*γ) (ω := ω) (fun i => by
        simpa only [q,abs_of_nonneg (F.density_nonneg i _)] using (h i).2.le)
    have hsum z : (∑ i, if c i = r then q i z else 0) = colorDensity F c r z*
        (1+2*ell*(fourier (-1) ((N:ℤ) • z)*a r z).re) := by
      unfold colorDensity
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : c i = r <;> simp only [q,hi,ite_true,ite_false,zero_mul]
    simp_rw [hsum,← colorDensity_pair] at hh
    rw [← colorDensity_mass] at hh
    linarith

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- Uniform continuity controls the entire next packet core, so this estimate
can be used as the input hypothesis of a subsequent actual passage. -/
theorem core_coefficient_drift_budget {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) {d : ℝ → ℂ} (hd : Continuous d) (hdc : HasCompactSupport d)
    (a : ι → UnitAddCircle → ℂ) (ha : ∀ i, Continuous (a i))
    {B ω e : ℝ} (he : 0 < e)
    (hmatch : ∀ i x, x ∈ F.core i →
      ‖d ((F.m i:ℝ)/B)-a i ((F.m i:ℝ)*F.V x:UnitAddCircle)‖ ≤ ω) :
    ∃ η : ℝ, 0 < η ∧ ∀ (κ : Type*) (G : PassagePackets κ) (parent : κ → ι) (B' : ℝ),
      StateTracks F G parent B B' η →
      ∀ j y, ‖d ((G.m j:ℝ)/B')-a (parent j) ((G.m j:ℝ)*G.V y:UnitAddCircle)‖ ≤ ω+e := by
  obtain ⟨η₁,hη₁,hU₁⟩ := Metric.uniformContinuous_iff.mp
    (hdc.uniformContinuous_of_continuous hd) (e/2) (half_pos he)
  have hau : UniformContinuous (fun z => fun i => a i z) := uniformContinuous_pi.mpr
    (fun i => CompactSpace.uniformContinuous_of_continuous (ha i))
  obtain ⟨η₂,hη₂,hU₂⟩ := Metric.uniformContinuous_iff.mp hau (e/2) (half_pos he)
  refine ⟨min η₁ η₂,lt_min hη₁ hη₂,?_⟩
  intro κ G parent B' htrack j y
  obtain ⟨x,hx,hidx,ht⟩ := htrack j
  have h₁ : dist (d ((G.m j:ℝ)/B')) (d ((F.m (parent j):ℝ)/B)) < e/2 :=
    hU₁ (by simpa only [Real.dist_eq] using hidx.trans_le (min_le_left _ _))
  have h₂ : dist (a (parent j) ((F.m (parent j):ℝ)*F.V x:UnitAddCircle))
      (a (parent j) ((G.m j:ℝ)*G.V y:UnitAddCircle)) < e/2 := by
    apply (dist_le_pi_dist (fun i => a i ((F.m (parent j):ℝ)*F.V x:UnitAddCircle))
      (fun i => a i ((G.m j:ℝ)*G.V y:UnitAddCircle)) (parent j)).trans_lt
    exact hU₂ (by rw [dist_comm]; exact (ht y).trans_le (min_le_right _ _))
  have hm := hmatch (parent j) x hx
  rw [← dist_eq_norm] at hm ⊢
  have hh := (dist_triangle (d ((G.m j:ℝ)/B')) (d ((F.m (parent j):ℝ)/B))
    (a (parent j) ((G.m j:ℝ)*G.V y:UnitAddCircle))).trans (add_le_add le_rfl
      (dist_triangle (d ((F.m (parent j):ℝ)/B))
        (a (parent j) ((F.m (parent j):ℝ)*F.V x:UnitAddCircle))
        (a (parent j) ((G.m j:ℝ)*G.V y:UnitAddCircle))))
  linarith

lemma StateTracks.band_margin {ι κ : Type*} {F : PassagePackets ι} {G : PassagePackets κ}
    {parent : κ → ι} {B B' η b D μ : ℝ} (h : StateTracks F G parent B B' η)
    (hb : ∀ i, b+μ ≤ |(F.m i:ℝ)/B| ∧ |(F.m i:ℝ)/B| ≤ D-μ) (hη : η ≤ μ/2) :
    ∀ i, b+μ/2 ≤ |(G.m i:ℝ)/B'| ∧ |(G.m i:ℝ)/B'| ≤ D-μ/2 := by
  intro i
  obtain ⟨x,_hx,ha,_ht⟩ := h i
  have hh := abs_lt.mp ((abs_abs_sub_abs_le_abs_sub ((G.m i:ℝ)/B')
    ((F.m (parent i):ℝ)/B)).trans_lt ha)
  have hi := hb (parent i)
  constructor <;> linarith [hi.1,hi.2,hh.1,hh.2]

end ThreeTorus
end
end

section

/-! A finite colored state and a pair record containing the two ACTUAL
smooth volume-preserving passage families. The existence theorem is derived
from the concrete neutral/signal producers, not supplied as an oracle. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

structure ColoredState (R : Type) where
  Index : Type
  finite : Fintype Index
  packets : PassagePackets Index
  injective : Injective packets.m
  spare : packets.SpareIndependent
  color : Index → R
  scale : ℝ
  scale_pos : 0 < scale

attribute [instance] ColoredState.finite

namespace ColoredState
variable {R : Type} [DecidableEq R] (C : ColoredState R)
def density (r : R) : UnitAddCircle → ℝ := colorDensity C.packets C.color r
def vector (r : R) : TripleTorus → ℂ := colorVector C.packets C.color r
lemma density_continuous (r : R) : Continuous (C.density r) :=
  continuous_colorDensity C.packets C.color r
lemma vector_continuous (r : R) : Continuous (C.vector r) :=
  continuous_colorVector C.packets C.color r
lemma density_nonneg (r : R) (z : UnitAddCircle) : 0 ≤ C.density r z :=
  colorDensity_nonneg C.packets C.color r z

def InBand (b D margin : ℝ) : Prop :=
  ∀ i, b+margin ≤ |(C.packets.m i:ℝ)/C.scale| ∧
    |(C.packets.m i:ℝ)/C.scale| ≤ D-margin

def Matches (d : ℝ → ℂ) (a : R → UnitAddCircle → ℂ) (ω : ℝ) : Prop :=
  ∀ i x, x ∈ C.packets.core i →
    ‖d ((C.packets.m i:ℝ)/C.scale)-a (C.color i)
      ((C.packets.m i:ℝ)*C.packets.V x:UnitAddCircle)‖ ≤ ω
end ColoredState

/-- A pair retaining real passage geometry, not merely a density transition. -/
structure ColoredPair {R : Type} (C : ColoredState R) (N : ℕ) where
  refresh : PassageGeometryFamily C.packets.V
  indices : C.Index → Finset ℤ
  n : ℕ
  n_pos : 0 < n
  middle : PassagePackets (PassageOutputIndex indices)
  middle_injective : Injective middle.m
  middle_spare : middle.SpareIndependent
  middle_speed : middle.V = fun x => (1+refresh.J₀ x/n)/n
  middle_index : ∀ i, middle.m i = i.2.val
  transmit : PassageGeometryFamily middle.V
  indices' : PassageOutputIndex indices → Finset ℤ
  N_pos : 0 < N
  final : PassagePackets (PassageOutputIndex indices')
  final_injective : Injective final.m
  final_spare : final.SpareIndependent
  final_speed : final.V = fun x => (1+transmit.J₀ x/N)/N
  final_index : ∀ i, final.m i = i.2.val

namespace ColoredPair
variable {R : Type} {C : ColoredState R} {N : ℕ} (s : ColoredPair C N)
def output : ColoredState R where
  Index := PassageOutputIndex s.indices'
  finite := inferInstance
  packets := s.final
  injective := s.final_injective
  spare := s.final_spare
  color := C.color ∘ Sigma.fst ∘ Sigma.fst
  scale := s.transmit.scale (s.refresh.scale C.scale s.n) N
  scale_pos := s.transmit.scale_pos (s.refresh.scale_pos C.scale_pos s.n_pos) s.N_pos

def chart : Equiv.Perm TripleTorus :=
  (passageChart (s.refresh.H s.n)).trans (passageChart (s.transmit.H N))
lemma chart_apply (x : TripleTorus) : s.chart x =
    passageChart (s.transmit.H N) (passageChart (s.refresh.H s.n) x) := rfl
lemma chart_continuous : Continuous s.chart :=
  (continuous_passageChart (s.transmit.Hcontinuous N)).comp
    (continuous_passageChart (s.refresh.Hcontinuous s.n))
lemma chart_preserves : MeasurePreserving s.chart tripleVolume tripleVolume :=
  (measurePreserving_passageChart (s.transmit.Hcontinuous N).measurable).comp
    (measurePreserving_passageChart (s.refresh.Hcontinuous s.n).measurable)

def Tracks (η : ℝ) : Prop :=
  StateTracks C.packets s.final (Sigma.fst ∘ Sigma.fst) C.scale s.output.scale η
end ColoredPair

def colorFactor {R : Type} (a : R → UnitAddCircle → ℂ) (ell : ℝ) (N : ℤ)
    (r : R) (z : UnitAddCircle) : ℝ :=
  1+2*ell*(fourier (-1) (N • z)*a r z).re

lemma continuous_colorFactor {R : Type} {a : R → UnitAddCircle → ℂ}
    (ha : ∀ r, Continuous (a r)) (ell : ℝ) (N : ℤ) (r : R) :
    Continuous (colorFactor a ell N r) :=
  continuous_const.add ((Complex.continuous_re.comp
    (((fourier (-1)).continuous.comp (continuous_zsmul N)).mul (ha r))).const_mul _)

lemma finite_card_error_budget (ι : Type*) [Fintype ι] {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℝ, 0 < e ∧ (Fintype.card ι:ℝ)*e < ε ∧ (Fintype.card ι:ℝ)^2*e < ε := by
  let k : ℝ := Fintype.card ι
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hp : 0 < k^2+k+1 := by positivity
  refine ⟨ε/(k^2+k+1),div_pos hε hp,?_,?_⟩
  · have h := (div_lt_iff₀ hp).2 (show k*ε < ε*(k^2+k+1) by nlinarith [sq_nonneg k])
    simpa only [mul_div_assoc] using h
  · have h := (div_lt_iff₀ hp).2 (show k^2*ε < ε*(k^2+k+1) by nlinarith)
    simpa only [mul_div_assoc] using h

/-- Color errors are as small as desired apart from the explicit coefficient
mismatch. Every sufficiently large transmission integer is still available. -/
theorem exists_colored_signal {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ L : ℕ, ∃ γ₀ : ℝ, 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (R : Type) [DecidableEq R], ∀ (C : ColoredState R),
      ∀ margin : ℝ, 0 < margin → C.InBand b D margin →
      ∀ (a : R → UnitAddCircle → ℂ), (∀ r, Continuous (a r)) →
      ∀ ω : ℝ, 0 ≤ ω → C.Matches d a ω →
      ∀ ε η : ℝ, 0 < ε → 0 < η →
      ∀ᶠ N : ℕ in atTop, ∃ s : ColoredPair C N, s.Tracks η ∧ ∀ r,
        physicalError (C.vector r) (s.output.vector r ∘ s.chart) < ε ∧
        (∫ z, |s.output.density r z-C.density r z*
          colorFactor a (refreshedStrength (signalPrimeProduct L) γ) (N:ℤ) r z| ∂phaseHaar) <
            2*γ*ω*(∫ z, C.density r z ∂phaseHaar)+ε := by
  classical
  obtain ⟨L,γ₀,hL,hLD,hγ₀,hfamily⟩ := exists_refresh_transmit_state hb hbD hd hdc hdr hd0 hds
  refine ⟨L,γ₀,hL,hLD,hγ₀,?_⟩
  intro γ hγ hγs
  obtain ⟨hsmall,hpair⟩ := hfamily γ hγ hγs
  refine ⟨hsmall,?_⟩
  intro R inst C margin hmargin hband a ha ω hω hmatch ε η hε hη
  obtain ⟨e,he,hecard,hecard2⟩ := finite_card_error_budget C.Index hε
  obtain ⟨g,S,hG⟩ := hpair C.Index C.packets C.injective C.spare C.scale C.scale_pos
    margin hmargin hband (fun i => a (C.color i)) (fun i => ha (C.color i))
    ω hω hmatch e η he hη
  obtain ⟨n,hn⟩ := hG.exists
  obtain ⟨hnp,G,hGi,hGmod,hGV,hGm,g',T,hK⟩ := hn
  filter_upwards [hK] with N hN
  obtain ⟨hNp,K,hKi,hKmod,hKV,hKm,herror,htrack⟩ := hN
  let s : ColoredPair C N :=
    ⟨g,S n,n,hnp,G,hGi,hGmod,hGV,hGm,g',T N,hNp,K,hKi,hKmod,hKV,hKm⟩
  refine ⟨s,htrack,?_⟩
  exact color_pair_errors C.packets K C.color a ha (g.Hcontinuous n) (g'.Hcontinuous N)
    N (refreshedStrength (signalPrimeProduct L) γ) he hecard hecard2 herror

end ThreeTorus
end
end

end OAI
