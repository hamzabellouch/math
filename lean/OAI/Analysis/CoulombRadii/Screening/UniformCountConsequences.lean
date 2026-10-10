import Mathlib
import OAI.Analysis.CoulombRadii.Screening.CountScalar

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

def atomicCountConstant : ℝ := Classical.choose atomic_screenCountParameter_uniform
lemma atomicCountConstant_ge_two : 2 ≤ atomicCountConstant :=
  (Classical.choose_spec atomic_screenCountParameter_uniform).1

theorem screenCountParameter_le_atomicCountConstant {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0 ≤ δ) : screenCountParameter ψ δ ≤ atomicCountConstant :=
  (Classical.choose_spec atomic_screenCountParameter_uniform).2 S hatom ψ hψ hm hE hstate hδ

lemma screenMass_square_bound {δ a : ℝ} (hδ : 0 ≤ δ) (ha : 0 < a) :
    (screenMass δ a)^2 ≤ 2*(max ((a^6)⁻¹) 1+δ*a) := by
  have hroot := Real.sq_sqrt (mul_nonneg hδ ha.le)
  have hb : (screenBaseMass a)^2=max ((a^6)⁻¹) 1 := by
    unfold screenBaseMass
    have he : ((a^3)⁻¹)^2=(a^6)⁻¹ := by rw [←inv_pow,←pow_mul]; norm_num
    rcases le_total ((a^3)⁻¹) 1 with H|H
    · rw [max_eq_right H,one_pow,max_eq_right]
      rw [←he]
      nlinarith [inv_nonneg.mpr (pow_nonneg ha.le 3)]
    · rw [max_eq_left H,max_eq_left]
      · exact he
      · rw [←he]; nlinarith
  unfold screenMass
  nlinarith [sq_nonneg (screenBaseMass a-Real.sqrt (δ*a))]

theorem atomic_local_second_moment {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0 ≤ δ) {y : Space} (hy : y≠0) :
    localCountSecondMoment ψ (Metric.closedBall y (atomicCellScale y)) ≤
      2*atomicCountConstant*(max (((atomicCellScale y)^6)⁻¹) 1+δ*atomicCellScale y) := by
  have hC : 0 ≤ atomicCountConstant := by linarith [atomicCountConstant_ge_two]
  have H := (screenCountParameter_controls ψ hm δ hy).trans
    (mul_le_mul_of_nonneg_right (screenCountParameter_le_atomicCountConstant S hatom ψ hψ hm hE hstate hδ) (sq_nonneg _))
  exact H.trans (by nlinarith [mul_le_mul_of_nonneg_left (screenMass_square_bound hδ (atomicCellScale_pos hy)) hC])

lemma exists_atomic_annular_mesh {α β : ℝ} (hα : 0 < α) : ∃ t : Finset Space,
    (∀ z∈t, α ≤ ‖z‖ ∧ ‖z‖ ≤ β) ∧
    (∀ w : Space, α ≤ ‖w‖ → ‖w‖ ≤ β → ∃ z∈t, ‖w-z‖ < atomicCellScale z) := by
  let B : Set Space := {z | α ≤ ‖z‖ ∧ ‖z‖ ≤ β}
  have hc : IsCompact B := (isCompact_closedBall (0:Space) β).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    (fun z hz => by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.2)
  have hp (z : B) : 0 < atomicCellScale z.val := atomicCellScale_pos (by
    intro he; have H:=z.property.1; simpa [he] using hα.trans_le H)
  have hcover : B ⊆ ⋃ z : B, Metric.ball z.val (atomicCellScale z.val) := by
    intro w hw
    exact Set.mem_iUnion.mpr ⟨⟨w,hw⟩,Metric.mem_ball_self (hp ⟨w,hw⟩)⟩
  obtain ⟨t,ht⟩ := hc.elim_finite_subcover (fun z : B => Metric.ball z.val (atomicCellScale z.val))
    (fun _ => Metric.isOpen_ball) hcover
  refine ⟨t.image Subtype.val,?_,?_⟩
  · intro z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    exact v.property
  · intro w hw1 hw2
    obtain ⟨z,hz⟩ := Set.mem_iUnion.mp (ht ⟨hw1,hw2⟩)
    obtain ⟨hzt,hzw⟩ := Set.mem_iUnion.mp hz
    exact ⟨z.val,Finset.mem_image.mpr ⟨z,hzt,rfl⟩,by simpa only [Metric.mem_ball,dist_eq_norm] using hzw⟩

lemma atomicCellScale_smul {u : ℝ} (hu : 0 ≤ u) (z : Space) :
    atomicCellScale (u • z)=u*atomicCellScale z := by
  simp only [atomicCellScale,norm_smul,Real.norm_eq_abs,abs_of_nonneg hu]
  ring

theorem atomic_annular_second_moment {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal) ≤ unrestrictedFormBottom S → form S ψ ≤ E+δ → 0 ≤ δ →
    ∀ {u : ℝ}, 0 < u →
      localCountSecondMoment ψ {x : Space | α*u < ‖x‖ ∧ ‖x‖ < β*u} ≤ C*(screenMass δ u)^2 := by
  obtain ⟨t,ht,hcover⟩ := exists_atomic_annular_mesh (β:=β) hα
  let q : ℝ := max 1 (max (100000/α) (β/100000))
  have hq : 1 ≤ q := le_max_left _ _
  have hqα : 100000/α ≤ q := (le_max_left _ _).trans (le_max_right _ _)
  have hqβ : β/100000 ≤ q := (le_max_right _ _).trans (le_max_right _ _)
  have hq0 : 0 < q := (div_pos (hα.trans hαβ) (by norm_num)).trans_le hqβ
  let C : ℝ := (Fintype.card {z : Space // z∈t}:ℝ)^2*atomicCountConstant*q^6
  have hC0 : 0 ≤ atomicCountConstant := by linarith [atomicCountConstant_ge_two]
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ u hu
  let A := fun z : {z : Space // z∈t} => Metric.closedBall (u • z.val) (atomicCellScale (u • z.val))
  have hz0 (z : {z : Space // z∈t}) : z.val≠0 := by
    intro he; have H:=(ht z.val z.property).1; simpa [he] using hα.trans_le H
  have hmz (z : {z : Space // z∈t}) : screenMass δ (atomicCellScale (u • z.val)) ≤ q^3*screenMass δ u := by
    apply screenMass_comparable hδ hu hq
    · rw [atomicCellScale_smul hu.le]
      apply (div_le_iff₀ hq0).mpr
      have H := (div_le_iff₀ hα).mp hqα
      have Hz := mul_le_mul_of_nonneg_left (ht z.val z.property).1 hq0.le
      dsimp only [atomicCellScale]
      nlinarith
    · rw [atomicCellScale_smul hu.le]
      apply mul_le_mul_of_nonneg_left _ hu.le
      exact (div_le_div_of_nonneg_right (ht z.val z.property).2 (by norm_num)).trans hqβ
  have hA : {x : Space | α*u < ‖x‖ ∧ ‖x‖ < β*u} ⊆ ⋃ z, A z := by
    intro x hx
    have hn : ‖u⁻¹ • x‖=‖x‖/u := by simp [norm_smul,abs_of_pos hu,div_eq_mul_inv,mul_comm]
    have hlow : α ≤ ‖u⁻¹ • x‖ := by rw [hn]; exact (le_div_iff₀ hu).mpr hx.1.le
    have hhigh : ‖u⁻¹ • x‖ ≤ β := by rw [hn]; exact (div_le_iff₀ hu).mpr hx.2.le
    obtain ⟨z,hz,hxz⟩ := hcover (u⁻¹ • x) hlow hhigh
    refine Set.mem_iUnion.mpr ⟨⟨z,hz⟩,?_⟩
    change ‖x-u • z‖ ≤ atomicCellScale (u • z)
    rw [atomicCellScale_smul hu.le]
    have hid : x-u • z=u • (u⁻¹ • x-z) := by simp [smul_sub,smul_smul,hu.ne']
    rw [hid,norm_smul,Real.norm_eq_abs,abs_of_pos hu]
    exact mul_le_mul_of_nonneg_left hxz.le hu.le
  have H := localCountSecondMoment_cover ψ A (fun _ => measurableSet_closedBall) hA
  have Hc (z : {z : Space // z∈t}) : localCountSecondMoment ψ (A z) ≤
      atomicCountConstant*(q^3*screenMass δ u)^2 := by
    have H0 := (screenCountParameter_controls ψ hm δ (smul_ne_zero hu.ne' (hz0 z))).trans
      (mul_le_mul_of_nonneg_right (screenCountParameter_le_atomicCountConstant S hatom ψ hψ hm hE hstate hδ) (sq_nonneg _))
    exact H0.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (screenMass_pos δ _).le (hmz z) 2) hC0)
  apply H.trans
  have HH := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun z (_ : z∈Finset.univ) => Hc z))
    (show 0 ≤ (Fintype.card {z : Space // z∈t}:ℝ) by positivity)
  apply HH.trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,C]
  ring

end Coulomb
end

end
end

end OAI
