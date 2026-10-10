import Mathlib
import OAI.Analysis.CoulombRadii.Screening.OutCap
import OAI.Analysis.CoulombRadii.FieldAnalysis.SortedObservable
import OAI.Analysis.CoulombRadii.SpectralTheory.SectorBottomBridge

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
lemma conditionalOutCost_lower_attraction {J m k:ℕ} (S:Nuclei J) (u:H1Vector (m+k))
    (B:ℝ) (hs:∀ s,∀ᵐ x,mass (u.coreSlice s x)≠0 → ∀ i,attraction S (position x i) ≤ B) :
    -((m:ℝ)*B)*mass u ≤ conditionalOutCost S u := by
  have H: -((m:ℝ)*B)*mass u ≤ sliceExpectation u (fun s x => pairPotential x-∑ i:Fin m,coreScreenedField S (u.coreSlice s x).normalized (position x i)) := by
    rw [←sliceExpectation_number u (-((m:ℝ)*B))]
    apply Finset.sum_le_sum
    intro s _
    apply integral_mono_ae
    · exact (mass_coreSlice_integrable u s).mul_const _
    · exact conditionalOutCost_weight_integrable S u s
    filter_upwards [hs s] with x hx
    by_cases hz:mass (u.coreSlice s x)=0
    · simp [hz]
    apply mul_le_mul_of_nonneg_left _ (mass_nonneg _)
    have hb:(∑ i:Fin m,coreScreenedField S (u.coreSlice s x).normalized (position x i)) ≤ (m:ℝ)*B := by
      calc
        _ ≤ ∑ _i:Fin m,B := Finset.sum_le_sum (fun i _ => (sub_le_self _ (coreCoulombPotential_nonneg _ _)).trans (hx hz i))
        _=_ := by simp
    linarith [pairPotential_nonneg_pointwise x]
  exact H.trans (le_add_of_nonneg_left (outerKinetic_nonneg u))

lemma outLabelCount_eq_zero_iff {n:ℕ} (p:Fin n → Fin 2) : outLabelCount p=0 ↔ p=fun _ => 1 := by
  unfold outLabelCount
  constructor
  · intro h
    funext i
    have hi: (if p i=0 then (1:ℝ) else 0) ≤ 0 := by
      exact (Finset.single_le_sum (f:=fun j:Fin n => if p j=0 then (1:ℝ) else 0)
        (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)).trans_eq h
    have hp:p i≠0 := by intro hz; norm_num [hz] at hi
    apply Fin.ext
    have hv:(p i).val≠0 := by simpa only [ne_eq,Fin.ext_iff,Fin.val_zero] using hp
    have hvlt:=(p i).isLt
    change (p i).val=1
    omega
  · rintro rfl; simp

lemma form_binary_cut_global {J n:ℕ} (S:Nuclei J) (u:H1Vector n)
    (χ:Fin 2 → Space → ℝ) (hc:∀ l,ContDiff ℝ ∞ (χ l))
    (hp:∀ z,∑ l,χ l z^2=1) (D:ℝ) (hD:0 ≤ D)
    (hd:∀ l b z,|fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D) :
    (∑ p:Fin n → Fin 2,form S (u.labelCut χ hc hp D hD hd p)) ≤ form S u+3*(n:ℝ)*D^2*mass u := by
  rw [form_labelCut]
  apply add_le_add_right
  have H (s:Spins n) (a:Fin n × Fin 3) :
      (∫ x,(∑ l:Fin 2,(fderiv ℝ (χ l) (position x a.1) (EuclideanSpace.single a.2 1))^2)*‖u.value s x‖^2) ≤
      2*D^2*(∫ x,‖u.value s x‖^2) := by
    rw [←integral_const_mul]
    apply integral_mono_of_nonneg
    · exact Eventually.of_forall fun x => mul_nonneg (Finset.sum_nonneg fun l _ => sq_nonneg _) (sq_nonneg _)
    · exact ((u.value_L2 s).integrable_norm_pow (by norm_num)).const_mul _
    · exact Eventually.of_forall fun x => mul_le_mul_of_nonneg_right (by
        calc
          _ ≤ ∑ _l:Fin 2,D^2 := Finset.sum_le_sum (fun l _ => by
            simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hD).mpr (hd l a.2 (position x a.1)))
          _=_ := by simp) (sq_nonneg _)
  calc
    _ ≤ (1/2:ℝ)*∑ s,∑ _a:Fin n × Fin 3,2*D^2*(∫ x,‖u.value s x‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun a _ => H s a) (by norm_num)
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat,←Finset.mul_sum,mass]; ring

lemma binary_cut_sector_lower (Z:ℕ) (hZ:1 ≤ Z) {n:ℕ} (hn:0<n)
    (u:H1Vector n) (ha:Antisymmetric u)
    (χ:Fin 2 → Space → ℝ) (hc:∀ l,ContDiff ℝ ∞ (χ l))
    (hp:∀ z,∑ l,χ l z^2=1) (D:ℝ) (hD:0 ≤ D)
    (hd:∀ l b z,|fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (B:ℝ) (hB:0 ≤ B) (hχ:∀ z,χ 0 z≠0 → attraction (atom Z hZ) z ≤ B)
    (E P:ℝ) (hE:(E:EReal) ≤ sectorFormBottom (atom Z hZ) n)
    (hP:(P:EReal) ≤ sectorFormBottom (atom Z hZ) (n-1)) (p:Fin n → Fin 2) :
    ((if p=fun _ => 1 then E else P)-(n:ℝ)*B)*mass (u.labelCut χ hc hp D hD hd p) ≤
      form (atom Z hZ) (u.labelCut χ hc hp D hD hd p) := by
  obtain ⟨m,k,v,e,hmk,hcount,hm,hform,hobs,hanti,hcore,hout⟩ :=
    binary_cut_recorded_outcome (atom Z hZ) u ha χ hc hp D hD hd p univ {z | attraction (atom Z hZ) z ≤ B}
      (by simp) (by intro z hz; by_contra hh; exact hz (hχ z hh))
  rw [←hm,←hform,form_eq_conditionalOutCost]
  have hsector: ((if p=fun _ => 1 then E else P : ℝ):EReal) ≤ sectorFormBottom (atom Z hZ) k := by
    by_cases h:p=fun _ => 1
    · have hm0:m=0 := by
        have H:=hcount
        rw [(outLabelCount_eq_zero_iff p).mpr h] at H
        exact_mod_cast H.symm
      have hk:k=n := by omega
      simpa only [ite_eq_left h,hk] using hE
    · have hm0:0 < m := by
        by_contra hh
        have H:m=0 := by omega
        have H':outLabelCount p=0 := by simpa [H] using hcount
        exact h ((outLabelCount_eq_zero_iff p).mp H')
      have hk:k ≤ n-1 := by omega
      simpa only [ite_eq_right h] using hP.trans (atom_sectorFormBottom_antitone Z hZ hk)
  have H:=slice_core_form_ge_sector (atom Z hZ) v hanti hsector
  have H':=conditionalOutCost_lower_attraction (atom Z hZ) v B hout
  have hmn:(m:ℝ) ≤ n := by exact_mod_cast (show m ≤ n by omega)
  have hmul:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmn hB) (mass_nonneg v)
  linarith

lemma binary_cut_loss_bound (Z:ℕ) (hZ:1 ≤ Z) {n:ℕ} (hn:0<n)
    (u:H1Vector n) (ha:Antisymmetric u)
    (χ:Fin 2 → Space → ℝ) (hc:∀ l,ContDiff ℝ ∞ (χ l))
    (hp:∀ z,∑ l,χ l z^2=1) (D:ℝ) (hD:0 ≤ D)
    (hd:∀ l b z,|fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (B:ℝ) (hB:0 ≤ B) (hχ:∀ z,χ 0 z≠0 → attraction (atom Z hZ) z ≤ B)
    (E P:ℝ) (hE:(E:EReal) ≤ sectorFormBottom (atom Z hZ) n)
    (hP:(P:EReal) ≤ sectorFormBottom (atom Z hZ) (n-1)) :
    (P-E)*(mass u-mass (u.labelCut χ hc hp D hD hd (fun _ => 1))) ≤
      form (atom Z hZ) u-E*mass u+(3*(n:ℝ)*D^2+(n:ℝ)*B)*mass u := by
  have H:=Finset.sum_le_sum (fun p (_:p∈(Finset.univ:Finset (Fin n → Fin 2))) =>
    binary_cut_sector_lower Z hZ hn u ha χ hc hp D hD hd B hB hχ E P hE hP p)
  have H':=form_binary_cut_global (atom Z hZ) u χ hc hp D hD hd
  have he(p:Fin n → Fin 2) :
      ((if p=fun _ => 1 then E else P)-(n:ℝ)*B)*mass (u.labelCut χ hc hp D hD hd p)=
      (P-(n:ℝ)*B)*mass (u.labelCut χ hc hp D hD hd p)+
        (if p=fun _ => 1 then (E-P)*mass (u.labelCut χ hc hp D hD hd (fun _ => 1)) else 0) := by
    by_cases h:p=fun _ => 1 <;> simp only [h,ite_true,ite_false] <;> ring
  simp_rw [he] at H
  rw [Finset.sum_add_distrib,←Finset.mul_sum,mass_labelCut] at H
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] at H
  linarith

end Coulomb
end

end

end OAI
