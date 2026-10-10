import Mathlib
import OAI.Analysis.HardSphere.Comparison.ActiveLabels

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates
open scoped BigOperators

lemma interval_subdivision (b : ℝ) {h : ℝ} (hh : 0≤h) (j : ℕ) :
    (volume : Measure ℝ).restrict (Icc b (b+j*h))=
      Measure.sum (fun i : Fin j ↦ volume.restrict (Icc (b+(i:ℝ)*h) (b+((i:ℝ)+1)*h))) := by
  simp_rw [← restrict_Ioc_eq_restrict_Icc,Measure.sum_fintype]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,Nat.cast_add,Nat.cast_one]
    rw [← ih]
    rw [← Measure.restrict_union (Set.Ioc_disjoint_Ioc_of_le (le_refl _)) measurableSet_Ioc,
      Set.Ioc_union_Ioc_eq_Ioc (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hh)) (by nlinarith : b+(j:ℝ)*h≤b+((j:ℝ)+1)*h)]

def subcubeBase {j : ℕ} (b : Point) (h : ℝ) (v : Fin j × Fin j × Fin j) : Point :=
  (b.1+(v.1:ℝ)*h,(b.2.1+(v.2.1:ℝ)*h,b.2.2+(v.2.2:ℝ)*h))

lemma cube_volume (b : Point) (h : ℝ) :
    volume.restrict (cube b h)=
      ((volume : Measure ℝ).restrict (Icc b.1 (b.1+h))).prod
        (((volume : Measure ℝ).restrict (Icc b.2.1 (b.2.1+h))).prod
          ((volume : Measure ℝ).restrict (Icc b.2.2 (b.2.2+h)))) := by
  rw [Measure.prod_restrict,Measure.prod_restrict,← Measure.volume_eq_prod,← Measure.volume_eq_prod]
  congr 1
  ext x
  rcases b with ⟨b1,b2,b3⟩
  rcases x with ⟨x1,x2,x3⟩
  simp only [cube,Set.mem_Icc,Set.mem_prod,Prod.mk_le_mk,Prod.mk_add_mk]
  tauto

lemma cube_subdivision (b : Point) {h : ℝ} (hh : 0≤h) (j : ℕ) :
    volume.restrict (cube b (j*h))=
      Measure.sum (fun v : Fin j × Fin j × Fin j ↦ volume.restrict (cube (subcubeBase b h v) h)) := by
  rw [cube_volume]
  simp_rw [interval_subdivision _ hh j]
  rw [Measure.prod_sum,Measure.prod_sum]
  congr 1
  funext v
  rw [cube_volume]
  simp only [subcubeBase,add_mul,one_mul,add_assoc]

lemma pi_sum_sectors {α ι β : Type*} [Fintype α] [Fintype ι] [MeasurableSpace β]
    (ν : ι → Measure β) [∀v,IsFiniteMeasure (ν v)] :
    Measure.pi (fun _ : α ↦ Measure.sum ν)=
      Measure.sum (fun σ : α → ι ↦ Measure.pi (fun i ↦ ν (σ i))) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [Measure.sum_apply _ (MeasurableSet.pi Set.countable_univ (fun i _ ↦ hs i))]
  simp_rw [Measure.pi_pi,Measure.sum_apply _ (hs _),tsum_fintype]
  exact (Fintype.prod_sum (fun i v ↦ ν v (s i))).symm

lemma cube_configuration_subdivision {n j : ℕ} (b : Point) {h : ℝ} (hh : 0≤h) :
    Measure.pi (fun _ : Fin n ↦ volume.restrict (cube b (j*h)))=
      Measure.sum (fun σ : Fin n → Fin j × Fin j × Fin j ↦
        Measure.pi (fun i ↦ volume.restrict (cube (subcubeBase b h (σ i)) h))) := by
  rw [cube_subdivision b hh j]
  have : ∀v : Fin j × Fin j × Fin j,IsFiniteMeasure (volume.restrict (cube (subcubeBase b h v) h)) :=
    fun v ↦ by rw [cube_volume]; infer_instance
  exact pi_sum_sectors _

lemma subdivision_index {n : ℕ} (hn : 2≤n) :
    ∃j : ℕ, 1≤j ∧ 2*j^3≤n ∧ n≤16*j^3 := by
  have hex : ∃k : ℕ, n<2*k^3 := by
    refine ⟨n+1,?_⟩
    nlinarith [sq_nonneg (n:ℤ)]
  let k := Nat.find hex
  have hk : n<2*k^3 := Nat.find_spec hex
  have hk0 : k≠0 := by intro he; simp [he] at hk
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hmin : 2*j^3≤n := by
    have ht : j<Nat.find hex := by change j<k; omega
    exact Nat.le_of_not_gt (Nat.find_min hex ht)
  have hjpos : 1≤j := by
    by_contra h
    have : j=0 := by omega
    simp [hj,this] at hk
    omega
  refine ⟨j,hjpos,hmin,?_⟩
  have hp : (j+1)^3≤(2*j)^3 := Nat.pow_le_pow_left (by omega : j+1≤2*j) 3
  rw [hj] at hk
  nlinarith

lemma subdivided_cube_capacity {n j : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n+1) → Point) → E} (hF : ContDiff ℝ 1 F)
    {r h : ℝ} (hr : 0<r) (hh : 0≤h) (b : Point)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c)≤r^2 → F X=0) :
    ((n+1-j^3 : ℕ) : ℝ≥0∞)*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun _ ↦ volume.restrict (cube b (j*h)))) ≤
      ENNReal.ofReal (Real.sqrt 3*h^3/r)*
        ∑ i, (∫⁻ X, ENNReal.ofReal (particleGradSq F i X)
          ∂Measure.pi (fun _ ↦ volume.restrict (cube b (j*h)))) := by
  rw [cube_configuration_subdivision b hh]
  simp_rw [lintegral_sum_measure,tsum_fintype]
  rw [Finset.mul_sum,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  have hc : Fintype.card (Fin j × Fin j × Fin j)=j^3 := by simp only [Fintype.card_prod,Fintype.card_fin]; ring
  simpa only [hc] using sector_capacity hF hr hh (subcubeBase b h) σ hz

lemma cube_coefficient {n j : ℕ} (hn : 2≤n) (hj : 1≤j) (hup : 2*j^3≤n) (hlo : n≤16*j^3)
    {r l : ℝ} (hr : 0<r) (hl : 0<l) :
    (1/(64*Real.sqrt 3)*r/l^3*(n:ℝ)*((n:ℝ)-1))*(Real.sqrt 3*(l/(j:ℝ))^3/r) ≤
      ((n-j^3:ℕ):ℝ) := by
  have hjs : (0:ℝ)<j := by exact_mod_cast hj
  have hrr := hr.ne'
  have hlr := hl.ne'
  have hsr : Real.sqrt 3≠0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hjn : j^3≤n := by omega
  rw [Nat.cast_sub hjn,Nat.cast_pow]
  have he : (1/(64*Real.sqrt 3)*r/l^3*(n:ℝ)*((n:ℝ)-1))*(Real.sqrt 3*(l/(j:ℝ))^3/r)=
      (n:ℝ)*((n:ℝ)-1)/(64*(j:ℝ)^3) := by field_simp
  rw [he]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<64*(j:ℝ)^3)).mpr
  have hup' : 2*(j:ℝ)^3≤(n:ℝ) := by exact_mod_cast hup
  have hlo' : (n:ℝ)≤16*(j:ℝ)^3 := by exact_mod_cast hlo
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have ht : (0:ℝ)≤(j:ℝ)^3 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hlo' (show (0:ℝ)≤n by positivity)
  have h2 := mul_le_mul_of_nonneg_left hup' ht
  nlinarith

lemma smooth_cube_energy {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin n → Point) → E} (hF : ContDiff ℝ 1 F)
    {r l : ℝ} (hr : 0<r) (hl : 0<l) (b : Point)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c)≤r^2 → F X=0) :
    ENNReal.ofReal (1/(64*Real.sqrt 3)*r/l^3*(n:ℝ)*((n:ℝ)-1))*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun _ ↦ volume.restrict (cube b l))) ≤
        ∑ i, (∫⁻ X, ENNReal.ofReal (particleGradSq F i X)
          ∂Measure.pi (fun _ ↦ volume.restrict (cube b l))) := by
  by_cases hn : 2≤n
  · obtain ⟨j,hj,hu,hd⟩ := subdivision_index hn
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    have hjr : (0:ℝ)<j := by exact_mod_cast hj
    have hlj : (j:ℝ)*(l/(j:ℝ))=l := by field_simp
    have h := subdivided_cube_capacity (j := j) hF hr (le_of_lt (div_pos hl hjr)) b hz
    rw [hlj] at h
    let A := 1/(64*Real.sqrt 3)*r/l^3*((m+1:ℕ):ℝ)*(((m+1:ℕ):ℝ)-1)
    let C := Real.sqrt 3*(l/(j:ℝ))^3/r
    have hC : 0<C := by dsimp [C]; positivity
    have hA : 0≤A := by
      have hm : (1:ℝ)≤((m+1:ℕ):ℝ) := by norm_num
      have hm' : (0:ℝ)≤((m+1:ℕ):ℝ)-1 := by linarith
      dsimp [A]; positivity
    have hco : ENNReal.ofReal A*ENNReal.ofReal C≤((m+1-j^3:ℕ):ℝ≥0∞) := by
      rw [← ENNReal.ofReal_mul hA]
      have hc := ENNReal.ofReal_le_ofReal (cube_coefficient hn hj hu hd hr hl)
      simpa only [ENNReal.ofReal_natCast] using hc
    apply (ENNReal.mul_le_mul_iff_left (ne_of_gt (ENNReal.ofReal_pos.mpr hC)) ENNReal.ofReal_ne_top).mp
    calc
      _ = (ENNReal.ofReal A*ENNReal.ofReal C)*
          (∫⁻ X,ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun _ ↦ volume.restrict (cube b l))) := by
            dsimp only [A]; ac_rfl
      _ ≤ ((m+1-j^3:ℕ):ℝ≥0∞)*_ := mul_le_mul_of_nonneg_right hco (by positivity)
      _ ≤ ENNReal.ofReal C*∑ i, (∫⁻ X, ENNReal.ofReal (particleGradSq F i X)
          ∂Measure.pi (fun _ ↦ volume.restrict (cube b l))) := h
      _ = _ := mul_comm _ _
  · have hcases : n=0 ∨ n=1 := by omega
    rcases hcases with rfl | rfl <;> simp

end HardSphere.SphericalCoordinates

end

end OAI
