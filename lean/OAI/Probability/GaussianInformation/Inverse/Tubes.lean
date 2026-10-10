import Mathlib
import OAI.Probability.GaussianInformation.Inverse.Ellipsoids

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
noncomputable def synth {q d : ℕ} (e : Fin q → Ambient d) (x : Ambient q) : Ambient d :=
  ∑ j,x j • e j
noncomputable def coordinates {q d : ℕ} (e : Fin q → Ambient d) (x : Ambient d) : Ambient q :=
  WithLp.toLp 2 (fun j => inner ℝ (e j) x)
noncomputable def residual {q d : ℕ} (e : Fin q → Ambient d) (x : Ambient d) : Ambient d :=
  x-synth e (coordinates e x)

lemma synth_norm {q d : ℕ} (e : Fin q → Ambient d) (he : Orthonormal ℝ e) (x : Ambient q) :
    ‖synth e x‖ = ‖x‖ := by
  have hh := he.inner_sum (fun j => x j) (fun j => x j) Finset.univ
  have hsq : ‖synth e x‖^2 = ‖x‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq x]
    simpa only [synth,real_inner_self_eq_norm_sq,starRingEnd_apply,star_trivial,pow_two] using hh
  nlinarith [norm_nonneg (synth e x),norm_nonneg x]

lemma synth_sub {q d : ℕ} (e : Fin q → Ambient d) (x y : Ambient q) :
    synth e (x-y) = synth e x-synth e y := by
  simp [synth,sub_smul,Finset.sum_sub_distrib]
lemma synth_smul {q d : ℕ} (e : Fin q → Ambient d) (r : ℝ) (x : Ambient q) :
    synth e (r • x) = r • synth e x := by
  simp [synth,mul_smul,Finset.smul_sum]

def groupedTube {q d : ℕ} (e : Fin q → Ambient d) (g : Fin q → ℕ) (r : ℝ) : Set (Ambient d) :=
  {x | ‖residual e x‖ ≤ r ∧ ∀ h : ℕ,
    ∑ j ∈ Finset.univ.filter (fun j => g j=h),(inner ℝ (e j) x)^2 ≤ r^2*(4:ℝ)^h}

lemma exists_groupedTube_cover {q d : ℕ} (e : Fin q → Ambient d)
    (he : ∀ x : Ambient q,‖synth e x‖ ≤ ‖x‖)
    (g : Fin q → ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ s : Finset (Ambient d),
      groupedTube e g r ⊆ ⋃ y ∈ s,ball y (3*r) ∧
      (s.card:ℝ) ≤ 5^q*(4:ℝ)^(∑ j,g j) := by
  classical
  let c : Fin q → ℝ := fun j => (1/4:ℝ)^(g j)
  have hc : ∀ j,0 < c j ∧ c j ≤ 1 := fun j =>
    ⟨pow_pos (by norm_num) _,pow_le_one₀ (by norm_num) (by norm_num)⟩
  obtain ⟨s,_,hcov,hcard⟩ := exists_ellipsoid_cover c hc
  refine ⟨s.image (fun y => synth e (r • y)),?_,?_⟩
  · intro x hx
    let a := r⁻¹ • coordinates e x
    have ha : ∀ h : ℕ,∑ j ∈ Finset.univ.filter (fun j => g j=h),(a j)^2 ≤ (4:ℝ)^h := by
      intro h
      have hj : ∑ j ∈ Finset.univ.filter (fun j => g j=h),(a j)^2 =
          (r⁻¹)^2 * ∑ j ∈ Finset.univ.filter (fun j => g j=h),(inner ℝ (e j) x)^2 := by
        simp [a,coordinates,mul_pow,Finset.mul_sum]
      rw [hj]
      calc
        _ ≤ (r⁻¹)^2*(r^2*4^h) := mul_le_mul_of_nonneg_left (hx.2 h) (sq_nonneg _)
        _ = _ := by field_simp [hr.ne']
    obtain ⟨y,hy,hay⟩ := hcov a (weighted_group_bound g a ha)
    refine mem_iUnion₂.mpr ⟨synth e (r • y),Finset.mem_image.mpr ⟨y,hy,rfl⟩,?_⟩
    have hra : r • a = coordinates e x := by simp [a,smul_smul,ne_of_gt hr]
    have hdist : ‖synth e (coordinates e x)-synth e (r • y)‖ ≤ r := by
      rw [← hra,← synth_sub,← smul_sub]
      calc
        _ ≤ ‖r • (a-y)‖ := he _
        _ = r*‖a-y‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
        _ ≤ r := (mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hay) hr.le).trans_eq (mul_one r)
    change ‖x-synth e (r • y)‖ < 3*r
    have hadd := norm_add_le (residual e x) (synth e (coordinates e x)-synth e (r • y))
    have heq : residual e x+(synth e (coordinates e x)-synth e (r • y)) = x-synth e (r • y) := by
      simp only [residual]; abel
    rw [heq] at hadd
    linarith [hx.1]
  · calc
      _ ≤ (s.card:ℝ) := by exact_mod_cast Finset.card_image_le
      _ ≤ 5^q*(∏ j,c j)⁻¹ := hcard
      _ = _ := by
        simp only [c,← Finset.prod_pow_eq_pow_sum,Finset.prod_inv_distrib,one_div,inv_pow,inv_inv]

lemma measure_groupedTube_le {q d : ℕ} (ν : Measure (Ambient d)) (hν : BallBound ν)
    (u : Ambient d) (e : Fin q → Ambient d)
    (he : ∀ x : Ambient q,‖synth e x‖ ≤ ‖x‖)
    (g : Fin q → ℕ) {r : ℝ} (hr : 0 < r) :
    ν {z | z-u ∈ groupedTube e g r} ≤
      ENNReal.ofReal (5^q*(4:ℝ)^(∑ j,g j)*(3*r)^(((d:ℝ)-1)/2)) := by
  classical
  obtain ⟨s,hcov,hcard⟩ := exists_groupedTube_cover e he g hr
  have hsub : {z | z-u ∈ groupedTube e g r} ⊆ ⋃ y ∈ s,ball (u+y) (3*r) := by
    intro z hz
    obtain ⟨y,hy,hzy⟩ := mem_iUnion₂.mp (hcov hz)
    refine mem_iUnion₂.mpr ⟨y,hy,?_⟩
    simpa only [mem_ball,dist_eq_norm,sub_add_eq_sub_sub] using hzy
  calc
    _ ≤ ν (⋃ y ∈ s,ball (u+y) (3*r)) := measure_mono hsub
    _ ≤ ∑ y ∈ s,ν (ball (u+y) (3*r)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ s,ENNReal.ofReal ((3*r)^(((d:ℝ)-1)/2)) :=
      Finset.sum_le_sum (fun y _ => hν (u+y) (3*r) (by positivity))
    _ = (s.card:ℝ≥0∞)*ENNReal.ofReal ((3*r)^(((d:ℝ)-1)/2)) := by simp
    _ ≤ ENNReal.ofReal (5^q*(4:ℝ)^(∑ j,g j))*ENNReal.ofReal ((3*r)^(((d:ℝ)-1)/2)) := by
      gcongr
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcard
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

end AllScaleInverseVolume

end OAI
